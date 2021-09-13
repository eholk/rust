use std::io::{self, Write};
use std::iter;

use crate::expr_use_visitor;
use hir::HirIdMap;
use hir::def::Res;
use hir::def_id::LocalDefId;
use rustc_ast::InlineAsmOptions;
use rustc_hir as hir;
use rustc_hir::{Expr, HirId};
use rustc_index::vec::IndexVec;
use rustc_middle::ty::{self, RootVariableMinCaptureList, TypeckResults};
use rustc_passes::liveness::{IrMaps, LiveNode, LiveNodeKind, VarKind, Variable, rwu_table};

use rustc_span::Span;
use VarKind::*;

impl<'tcx> expr_use_visitor::Delegate<'tcx> for IrMaps<'tcx> {
    fn consume(
        &mut self,
        place_with_id: &rustc_middle::hir::place::PlaceWithHirId<'tcx>,
        _diag_expr_id: rustc_hir::HirId,
    ) {
        self.add_variable(Temporary(place_with_id.hir_id));
    }

    fn borrow(
        &mut self,
        place_with_id: &rustc_middle::hir::place::PlaceWithHirId<'tcx>,
        _diag_expr_id: rustc_hir::HirId,
        _bk: rustc_middle::ty::BorrowKind,
    ) {
        self.add_variable(Temporary(place_with_id.hir_id));
    }

    fn mutate(
        &mut self,
        assignee_place: &rustc_middle::hir::place::PlaceWithHirId<'tcx>,
        _diag_expr_id: rustc_hir::HirId,
    ) {
        self.add_variable(Temporary(assignee_place.hir_id));
    }

    fn fake_read(
        &mut self,
        _place: rustc_middle::hir::place::Place<'tcx>,
        _cause: rustc_middle::mir::FakeReadCause,
        _diag_expr_id: rustc_hir::HirId,
    ) {
    }
}

// ______________________________________________________________________
// Computing liveness sets
//
// Actually we compute just a bit more than just liveness, but we use
// the same basic propagation framework in all cases.

const ACC_READ: u32 = 1;
const ACC_WRITE: u32 = 2;
const ACC_USE: u32 = 4;

pub(super) struct Liveness<'a, 'atcx, 'tcx> {
    pub ir: &'a mut IrMaps<'tcx>,
    typeck_results: &'atcx ty::TypeckResults<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    closure_min_captures: Option<&'atcx RootVariableMinCaptureList<'tcx>>,
    successors: IndexVec<LiveNode, Option<LiveNode>>,
    rwu_table: rwu_table::RWUTable,

    /// A live node representing a point of execution before closure entry &
    /// after closure exit. Used to calculate liveness of captured variables
    /// through calls to the same closure. Used for Fn & FnMut closures only.
    closure_ln: LiveNode,
    /// A live node representing every 'exit' from the function, whether it be
    /// by explicit return, panic, or other means.
    exit_ln: LiveNode,

    // mappings from loop node ID to LiveNode
    // ("break" label should map to loop node ID,
    // it probably doesn't now)
    break_ln: HirIdMap<LiveNode>,
    cont_ln: HirIdMap<LiveNode>,
}

impl<'a, 'atcx, 'tcx> Liveness<'a, 'atcx, 'tcx> {
    pub fn new(
        ir: &'a mut IrMaps<'tcx>,
        body_owner: LocalDefId,
        typeck_results: &'atcx TypeckResults<'tcx>,
    ) -> Self {
        let param_env = ir.tcx.param_env(body_owner);
        let closure_min_captures = typeck_results.closure_min_captures.get(&body_owner.to_def_id());
        let closure_ln = ir.add_live_node(LiveNodeKind::ClosureNode);
        let exit_ln = ir.add_live_node(LiveNodeKind::ExitNode);

        let num_live_nodes = ir.lnks.len();
        let num_vars = ir.var_kinds.len();

        Liveness {
            ir,
            typeck_results,
            param_env,
            closure_min_captures,
            successors: IndexVec::from_elem_n(None, num_live_nodes),
            rwu_table: rwu_table::RWUTable::new(num_live_nodes, num_vars),
            closure_ln,
            exit_ln,
            break_ln: Default::default(),
            cont_ln: Default::default(),
        }
    }

    pub fn live_node(&self, hir_id: HirId, span: Span) -> LiveNode {
        match self.ir.live_node_map.get(&hir_id) {
            Some(&ln) => ln,
            None => {
                // This must be a mismatch between the ir_map construction
                // above and the propagation code below; the two sets of
                // code have to agree about which AST nodes are worth
                // creating liveness nodes for.
                span_bug!(span, "no live node registered for node {:?}", hir_id);
            }
        }
    }

    fn variable(&self, hir_id: HirId, span: Span) -> Variable {
        self.ir.variable(hir_id, span)
    }

    fn define_bindings_in_pat(&mut self, pat: &hir::Pat<'_>, mut succ: LiveNode) -> LiveNode {
        // In an or-pattern, only consider the first pattern; any later patterns
        // must have the same bindings, and we also consider the first pattern
        // to be the "authoritative" set of ids.
        pat.each_binding_or_first(&mut |_, hir_id, pat_sp, ident| {
            let ln = self.live_node(hir_id, pat_sp);
            let var = self.variable(hir_id, ident.span);
            self.init_from_succ(ln, succ);
            self.define(ln, var);
            succ = ln;
        });
        succ
    }

    pub fn live_on_entry(&self, ln: LiveNode, var: Variable) -> bool {
        self.rwu_table.get_reader(ln, var)
    }

    fn write_vars<F>(&self, wr: &mut dyn Write, mut test: F) -> io::Result<()>
    where
        F: FnMut(Variable) -> bool,
    {
        for var_idx in 0..self.ir.var_kinds.len() {
            let var = Variable::from(var_idx);
            if test(var) {
                write!(wr, " {:?}", var)?;
            }
        }
        Ok(())
    }

    #[allow(unused_must_use)]
    fn ln_str(&self, ln: LiveNode) -> String {
        let mut wr = Vec::new();
        {
            let wr = &mut wr as &mut dyn Write;
            write!(wr, "[{:?} of kind {:?} reads", ln, self.ir.lnks[ln]);
            self.write_vars(wr, |var| self.rwu_table.get_reader(ln, var));
            write!(wr, "  writes");
            self.write_vars(wr, |var| self.rwu_table.get_writer(ln, var));
            write!(wr, "  uses");
            self.write_vars(wr, |var| self.rwu_table.get_used(ln, var));

            write!(wr, "  precedes {:?}]", self.successors[ln]);
        }
        String::from_utf8(wr).unwrap()
    }

    fn init_empty(&mut self, ln: LiveNode, succ_ln: LiveNode) {
        self.successors[ln] = Some(succ_ln);

        // It is not necessary to initialize the RWUs here because they are all
        // empty when created, and the sets only grow during iterations.
    }

    fn init_from_succ(&mut self, ln: LiveNode, succ_ln: LiveNode) {
        // more efficient version of init_empty() / merge_from_succ()
        self.successors[ln] = Some(succ_ln);
        self.rwu_table.copy(ln, succ_ln);
        debug!("init_from_succ(ln={}, succ={})", self.ln_str(ln), self.ln_str(succ_ln));
    }

    fn merge_from_succ(&mut self, ln: LiveNode, succ_ln: LiveNode) -> bool {
        if ln == succ_ln {
            return false;
        }

        let changed = self.rwu_table.union(ln, succ_ln);
        debug!("merge_from_succ(ln={:?}, succ={}, changed={})", ln, self.ln_str(succ_ln), changed);
        changed
    }

    // Indicates that a local variable was *defined*; we know that no
    // uses of the variable can precede the definition (resolve checks
    // this) so we just clear out all the data.
    fn define(&mut self, writer: LiveNode, var: Variable) {
        let used = self.rwu_table.get_used(writer, var);
        self.rwu_table.set(writer, var, rwu_table::RWU { reader: false, writer: false, used });
        debug!("{:?} defines {:?}: {}", writer, var, self.ln_str(writer));
    }

    // Either read, write, or both depending on the acc bitset
    fn acc(&mut self, ln: LiveNode, var: Variable, acc: u32) {
        debug!("{:?} accesses[{:x}] {:?}: {}", ln, acc, var, self.ln_str(ln));

        let mut rwu = self.rwu_table.get(ln, var);

        if (acc & ACC_WRITE) != 0 {
            rwu.reader = false;
            rwu.writer = true;
        }

        // Important: if we both read/write, must do read second
        // or else the write will override.
        if (acc & ACC_READ) != 0 {
            rwu.reader = true;
        }

        if (acc & ACC_USE) != 0 {
            rwu.used = true;
        }

        self.rwu_table.set(ln, var, rwu);
    }

    pub(super) fn compute(&mut self, body: &hir::Body<'_>, hir_id: HirId) -> LiveNode {
        debug!("compute: for body {:?}", body.id().hir_id);

        // # Liveness of captured variables
        //
        // When computing the liveness for captured variables we take into
        // account how variable is captured (ByRef vs ByValue) and what is the
        // closure kind (Generator / FnOnce vs Fn / FnMut).
        //
        // Variables captured by reference are assumed to be used on the exit
        // from the closure.
        //
        // In FnOnce closures, variables captured by value are known to be dead
        // on exit since it is impossible to call the closure again.
        //
        // In Fn / FnMut closures, variables captured by value are live on exit
        // if they are live on the entry to the closure, since only the closure
        // itself can access them on subsequent calls.

        if let Some(closure_min_captures) = self.closure_min_captures {
            // Mark upvars captured by reference as used after closure exits.
            for (&var_hir_id, min_capture_list) in closure_min_captures {
                for captured_place in min_capture_list {
                    match captured_place.info.capture_kind {
                        ty::UpvarCapture::ByRef(_) => {
                            let var = self.variable(
                                var_hir_id,
                                captured_place.get_capture_kind_span(self.ir.tcx),
                            );
                            self.acc(self.exit_ln, var, ACC_READ | ACC_USE);
                        }
                        ty::UpvarCapture::ByValue(_) => {}
                    }
                }
            }
        }

        let succ = self.propagate_through_expr(&body.value, self.exit_ln);

        if self.closure_min_captures.is_none() {
            // Either not a closure, or closure without any captured variables.
            // No need to determine liveness of captured variables, since there
            // are none.
            return succ;
        }

        let ty = self.typeck_results.node_type(hir_id);
        match ty.kind() {
            ty::Closure(_def_id, substs) => match substs.as_closure().kind() {
                ty::ClosureKind::Fn => {}
                ty::ClosureKind::FnMut => {}
                ty::ClosureKind::FnOnce => return succ,
            },
            ty::Generator(..) => return succ,
            _ => {
                span_bug!(
                    body.value.span,
                    "{} has upvars so it should have a closure type: {:?}",
                    hir_id,
                    ty
                );
            }
        };

        // Propagate through calls to the closure.
        loop {
            self.init_from_succ(self.closure_ln, succ);
            for param in body.params {
                param.pat.each_binding(|_bm, hir_id, _x, ident| {
                    let var = self.variable(hir_id, ident.span);
                    self.define(self.closure_ln, var);
                })
            }

            if !self.merge_from_succ(self.exit_ln, self.closure_ln) {
                break;
            }
            assert_eq!(succ, self.propagate_through_expr(&body.value, self.exit_ln));
        }

        succ
    }

    fn propagate_through_block(&mut self, blk: &hir::Block<'_>, succ: LiveNode) -> LiveNode {
        if blk.targeted_by_break {
            self.break_ln.insert(blk.hir_id, succ);
        }
        let succ = self.propagate_through_opt_expr(blk.expr, succ);
        blk.stmts.iter().rev().fold(succ, |succ, stmt| self.propagate_through_stmt(stmt, succ))
    }

    fn propagate_through_stmt(&mut self, stmt: &hir::Stmt<'_>, succ: LiveNode) -> LiveNode {
        match stmt.kind {
            hir::StmtKind::Local(ref local) => {
                // Note: we mark the variable as defined regardless of whether
                // there is an initializer.  Initially I had thought to only mark
                // the live variable as defined if it was initialized, and then we
                // could check for uninit variables just by scanning what is live
                // at the start of the function. But that doesn't work so well for
                // immutable variables defined in a loop:
                //     loop { let x; x = 5; }
                // because the "assignment" loops back around and generates an error.
                //
                // So now we just check that variables defined w/o an
                // initializer are not live at the point of their
                // initialization, which is mildly more complex than checking
                // once at the func header but otherwise equivalent.

                let succ = self.propagate_through_opt_expr(local.init, succ);
                self.define_bindings_in_pat(&local.pat, succ)
            }
            hir::StmtKind::Item(..) => succ,
            hir::StmtKind::Expr(ref expr) | hir::StmtKind::Semi(ref expr) => {
                self.propagate_through_expr(&expr, succ)
            }
        }
    }

    fn propagate_through_exprs(&mut self, exprs: &[Expr<'_>], succ: LiveNode) -> LiveNode {
        exprs.iter().rev().fold(succ, |succ, expr| self.propagate_through_expr(&expr, succ))
    }

    fn propagate_through_opt_expr(
        &mut self,
        opt_expr: Option<&Expr<'_>>,
        succ: LiveNode,
    ) -> LiveNode {
        opt_expr.map_or(succ, |expr| self.propagate_through_expr(expr, succ))
    }

    fn propagate_through_expr(&mut self, expr: &Expr<'_>, succ: LiveNode) -> LiveNode {
        debug!("propagate_through_expr: {:?}", expr);

        match expr.kind {
            // Interesting cases with control flow or which gen/kill
            hir::ExprKind::Path(hir::QPath::Resolved(_, ref path)) => {
                self.access_path(expr.hir_id, path, succ, ACC_READ | ACC_USE)
            }

            hir::ExprKind::Field(ref e, _) => self.propagate_through_expr(&e, succ),

            hir::ExprKind::Closure(..) => {
                debug!("{:?} is an ExprKind::Closure", expr);

                // the construction of a closure itself is not important,
                // but we have to consider the closed over variables.
                let caps = self
                    .ir
                    .capture_info_map
                    .get(&expr.hir_id)
                    .cloned()
                    .unwrap_or_else(|| span_bug!(expr.span, "no registered caps"));

                caps.iter().rev().fold(succ, |succ, cap| {
                    self.init_from_succ(cap.ln, succ);
                    let var = self.variable(cap.var_hid, expr.span);
                    self.acc(cap.ln, var, ACC_READ | ACC_USE);
                    cap.ln
                })
            }

            hir::ExprKind::Let(ref pat, ref scrutinee, _) => {
                let succ = self.propagate_through_expr(scrutinee, succ);
                self.define_bindings_in_pat(pat, succ)
            }

            // Note that labels have been resolved, so we don't need to look
            // at the label ident
            hir::ExprKind::Loop(ref blk, ..) => self.propagate_through_loop(expr, &blk, succ),

            hir::ExprKind::Yield(ref e, ..) => {
                let yield_ln = self.live_node(expr.hir_id, expr.span);
                self.init_from_succ(yield_ln, succ);
                self.merge_from_succ(yield_ln, self.exit_ln);
                self.propagate_through_expr(e, yield_ln)
            }

            hir::ExprKind::If(ref cond, ref then, ref else_opt) => {
                //
                //     (cond)
                //       |
                //       v
                //     (expr)
                //     /   \
                //    |     |
                //    v     v
                //  (then)(els)
                //    |     |
                //    v     v
                //   (  succ  )
                //
                let else_ln =
                    self.propagate_through_opt_expr(else_opt.as_ref().map(|e| &**e), succ);
                let then_ln = self.propagate_through_expr(&then, succ);
                let ln = self.live_node(expr.hir_id, expr.span);
                self.init_from_succ(ln, else_ln);
                self.merge_from_succ(ln, then_ln);
                self.propagate_through_expr(&cond, ln)
            }

            hir::ExprKind::Match(ref e, arms, _) => {
                //
                //      (e)
                //       |
                //       v
                //     (expr)
                //     / | \
                //    |  |  |
                //    v  v  v
                //   (..arms..)
                //    |  |  |
                //    v  v  v
                //   (  succ  )
                //
                //
                let ln = self.live_node(expr.hir_id, expr.span);
                self.init_empty(ln, succ);
                for arm in arms {
                    let body_succ = self.propagate_through_expr(&arm.body, succ);

                    let guard_succ = arm.guard.as_ref().map_or(body_succ, |g| match g {
                        hir::Guard::If(e) => self.propagate_through_expr(e, body_succ),
                        hir::Guard::IfLet(pat, e) => {
                            let let_bind = self.define_bindings_in_pat(pat, body_succ);
                            self.propagate_through_expr(e, let_bind)
                        }
                    });
                    let arm_succ = self.define_bindings_in_pat(&arm.pat, guard_succ);
                    self.merge_from_succ(ln, arm_succ);
                }
                self.propagate_through_expr(&e, ln)
            }

            hir::ExprKind::Ret(ref o_e) => {
                // Ignore succ and subst exit_ln.
                self.propagate_through_opt_expr(o_e.as_ref().map(|e| &**e), self.exit_ln)
            }

            hir::ExprKind::Break(label, ref opt_expr) => {
                // Find which label this break jumps to
                let target = match label.target_id {
                    Ok(hir_id) => self.break_ln.get(&hir_id),
                    Err(err) => span_bug!(expr.span, "loop scope error: {}", err),
                }
                .cloned();

                // Now that we know the label we're going to,
                // look it up in the break loop nodes table

                match target {
                    Some(b) => self.propagate_through_opt_expr(opt_expr.as_ref().map(|e| &**e), b),
                    None => span_bug!(expr.span, "`break` to unknown label"),
                }
            }

            hir::ExprKind::Continue(label) => {
                // Find which label this expr continues to
                let sc = label
                    .target_id
                    .unwrap_or_else(|err| span_bug!(expr.span, "loop scope error: {}", err));

                // Now that we know the label we're going to,
                // look it up in the continue loop nodes table
                self.cont_ln
                    .get(&sc)
                    .cloned()
                    .unwrap_or_else(|| span_bug!(expr.span, "continue to unknown label"))
            }

            hir::ExprKind::Assign(ref l, ref r, _) => {
                // see comment on places in
                // propagate_through_place_components()
                let succ = self.write_place(&l, succ, ACC_WRITE);
                let succ = self.propagate_through_place_components(&l, succ);
                self.propagate_through_expr(&r, succ)
            }

            hir::ExprKind::AssignOp(_, ref l, ref r) => {
                // an overloaded assign op is like a method call
                if self.typeck_results.is_method_call(expr) {
                    let succ = self.propagate_through_expr(&l, succ);
                    self.propagate_through_expr(&r, succ)
                } else {
                    // see comment on places in
                    // propagate_through_place_components()
                    let succ = self.write_place(&l, succ, ACC_WRITE | ACC_READ);
                    let succ = self.propagate_through_expr(&r, succ);
                    self.propagate_through_place_components(&l, succ)
                }
            }

            // Uninteresting cases: just propagate in rev exec order
            hir::ExprKind::Array(ref exprs) => self.propagate_through_exprs(exprs, succ),

            hir::ExprKind::Struct(_, ref fields, ref with_expr) => {
                let succ = self.propagate_through_opt_expr(with_expr.as_ref().map(|e| &**e), succ);
                fields
                    .iter()
                    .rev()
                    .fold(succ, |succ, field| self.propagate_through_expr(&field.expr, succ))
            }

            hir::ExprKind::Call(ref f, ref args) => {
                let succ = self.check_is_ty_uninhabited(expr, succ);
                let succ = self.propagate_through_exprs(args, succ);
                self.propagate_through_expr(&f, succ)
            }

            hir::ExprKind::MethodCall(.., ref args, _) => {
                let succ = self.check_is_ty_uninhabited(expr, succ);
                self.propagate_through_exprs(args, succ)
            }

            hir::ExprKind::Tup(ref exprs) => self.propagate_through_exprs(exprs, succ),

            hir::ExprKind::Binary(op, ref l, ref r) if op.node.is_lazy() => {
                let r_succ = self.propagate_through_expr(&r, succ);

                let ln = self.live_node(expr.hir_id, expr.span);
                self.init_from_succ(ln, succ);
                self.merge_from_succ(ln, r_succ);

                self.propagate_through_expr(&l, ln)
            }

            hir::ExprKind::Index(ref l, ref r) | hir::ExprKind::Binary(_, ref l, ref r) => {
                let r_succ = self.propagate_through_expr(&r, succ);
                self.propagate_through_expr(&l, r_succ)
            }

            hir::ExprKind::Box(ref e)
            | hir::ExprKind::AddrOf(_, _, ref e)
            | hir::ExprKind::Cast(ref e, _)
            | hir::ExprKind::Type(ref e, _)
            | hir::ExprKind::DropTemps(ref e)
            | hir::ExprKind::Unary(_, ref e)
            | hir::ExprKind::Repeat(ref e, _) => self.propagate_through_expr(&e, succ),

            hir::ExprKind::InlineAsm(ref asm) => {
                // Handle non-returning asm
                let mut succ = if asm.options.contains(InlineAsmOptions::NORETURN) {
                    self.exit_ln
                } else {
                    succ
                };

                // Do a first pass for writing outputs only
                for (op, _op_sp) in asm.operands.iter().rev() {
                    match op {
                        hir::InlineAsmOperand::In { .. }
                        | hir::InlineAsmOperand::Const { .. }
                        | hir::InlineAsmOperand::Sym { .. } => {}
                        hir::InlineAsmOperand::Out { expr, .. } => {
                            if let Some(expr) = expr {
                                succ = self.write_place(expr, succ, ACC_WRITE);
                            }
                        }
                        hir::InlineAsmOperand::InOut { expr, .. } => {
                            succ = self.write_place(expr, succ, ACC_READ | ACC_WRITE | ACC_USE);
                        }
                        hir::InlineAsmOperand::SplitInOut { out_expr, .. } => {
                            if let Some(expr) = out_expr {
                                succ = self.write_place(expr, succ, ACC_WRITE);
                            }
                        }
                    }
                }

                // Then do a second pass for inputs
                let mut succ = succ;
                for (op, _op_sp) in asm.operands.iter().rev() {
                    match op {
                        hir::InlineAsmOperand::In { expr, .. }
                        | hir::InlineAsmOperand::Sym { expr, .. } => {
                            succ = self.propagate_through_expr(expr, succ)
                        }
                        hir::InlineAsmOperand::Out { expr, .. } => {
                            if let Some(expr) = expr {
                                succ = self.propagate_through_place_components(expr, succ);
                            }
                        }
                        hir::InlineAsmOperand::InOut { expr, .. } => {
                            succ = self.propagate_through_place_components(expr, succ);
                        }
                        hir::InlineAsmOperand::SplitInOut { in_expr, out_expr, .. } => {
                            if let Some(expr) = out_expr {
                                succ = self.propagate_through_place_components(expr, succ);
                            }
                            succ = self.propagate_through_expr(in_expr, succ);
                        }
                        hir::InlineAsmOperand::Const { .. } => {}
                    }
                }
                succ
            }

            hir::ExprKind::LlvmInlineAsm(ref asm) => {
                let ia = &asm.inner;
                let outputs = asm.outputs_exprs;
                let inputs = asm.inputs_exprs;
                let succ = iter::zip(&ia.outputs, outputs).rev().fold(succ, |succ, (o, output)| {
                    // see comment on places
                    // in propagate_through_place_components()
                    if o.is_indirect {
                        self.propagate_through_expr(output, succ)
                    } else {
                        let acc = if o.is_rw { ACC_WRITE | ACC_READ } else { ACC_WRITE };
                        let succ = self.write_place(output, succ, acc);
                        self.propagate_through_place_components(output, succ)
                    }
                });

                // Inputs are executed first. Propagate last because of rev order
                self.propagate_through_exprs(inputs, succ)
            }

            hir::ExprKind::Lit(..)
            | hir::ExprKind::ConstBlock(..)
            | hir::ExprKind::Err
            | hir::ExprKind::Path(hir::QPath::TypeRelative(..))
            | hir::ExprKind::Path(hir::QPath::LangItem(..)) => succ,

            // Note that labels have been resolved, so we don't need to look
            // at the label ident
            hir::ExprKind::Block(ref blk, _) => self.propagate_through_block(&blk, succ),
        }
    }

    fn propagate_through_place_components(&mut self, expr: &Expr<'_>, succ: LiveNode) -> LiveNode {
        // # Places
        //
        // In general, the full flow graph structure for an
        // assignment/move/etc can be handled in one of two ways,
        // depending on whether what is being assigned is a "tracked
        // value" or not. A tracked value is basically a local
        // variable or argument.
        //
        // The two kinds of graphs are:
        //
        //    Tracked place          Untracked place
        // ----------------------++-----------------------
        //                       ||
        //         |             ||           |
        //         v             ||           v
        //     (rvalue)          ||       (rvalue)
        //         |             ||           |
        //         v             ||           v
        // (write of place)     ||   (place components)
        //         |             ||           |
        //         v             ||           v
        //      (succ)           ||        (succ)
        //                       ||
        // ----------------------++-----------------------
        //
        // I will cover the two cases in turn:
        //
        // # Tracked places
        //
        // A tracked place is a local variable/argument `x`.  In
        // these cases, the link_node where the write occurs is linked
        // to node id of `x`.  The `write_place()` routine generates
        // the contents of this node.  There are no subcomponents to
        // consider.
        //
        // # Non-tracked places
        //
        // These are places like `x[5]` or `x.f`.  In that case, we
        // basically ignore the value which is written to but generate
        // reads for the components---`x` in these two examples.  The
        // components reads are generated by
        // `propagate_through_place_components()` (this fn).
        //
        // # Illegal places
        //
        // It is still possible to observe assignments to non-places;
        // these errors are detected in the later pass borrowck.  We
        // just ignore such cases and treat them as reads.

        match expr.kind {
            hir::ExprKind::Path(_) => succ,
            hir::ExprKind::Field(ref e, _) => self.propagate_through_expr(&e, succ),
            _ => self.propagate_through_expr(expr, succ),
        }
    }

    // see comment on propagate_through_place()
    fn write_place(&mut self, expr: &Expr<'_>, succ: LiveNode, acc: u32) -> LiveNode {
        match expr.kind {
            hir::ExprKind::Path(hir::QPath::Resolved(_, ref path)) => {
                self.access_path(expr.hir_id, path, succ, acc)
            }

            // We do not track other places, so just propagate through
            // to their subcomponents.  Also, it may happen that
            // non-places occur here, because those are detected in the
            // later pass borrowck.
            _ => succ,
        }
    }

    fn access_var(
        &mut self,
        hir_id: HirId,
        var_hid: HirId,
        succ: LiveNode,
        acc: u32,
        span: Span,
    ) -> LiveNode {
        let ln = self.live_node(hir_id, span);
        if acc != 0 {
            self.init_from_succ(ln, succ);
            let var = self.variable(var_hid, span);
            self.acc(ln, var, acc);
        }
        ln
    }

    fn access_path(
        &mut self,
        hir_id: HirId,
        path: &hir::Path<'_>,
        succ: LiveNode,
        acc: u32,
    ) -> LiveNode {
        match path.res {
            Res::Local(hid) => self.access_var(hir_id, hid, succ, acc, path.span),
            _ => succ,
        }
    }

    fn propagate_through_loop(
        &mut self,
        expr: &Expr<'_>,
        body: &hir::Block<'_>,
        succ: LiveNode,
    ) -> LiveNode {
        /*
        We model control flow like this:

              (expr) <-+
                |      |
                v      |
              (body) --+

        Note that a `continue` expression targeting the `loop` will have a successor of `expr`.
        Meanwhile, a `break` expression will have a successor of `succ`.
        */

        // first iteration:
        let ln = self.live_node(expr.hir_id, expr.span);
        self.init_empty(ln, succ);
        debug!("propagate_through_loop: using id for loop body {} {:?}", expr.hir_id, body);

        self.break_ln.insert(expr.hir_id, succ);

        self.cont_ln.insert(expr.hir_id, ln);

        let body_ln = self.propagate_through_block(body, ln);

        // repeat until fixed point is reached:
        while self.merge_from_succ(ln, body_ln) {
            assert_eq!(body_ln, self.propagate_through_block(body, ln));
        }

        ln
    }

    fn check_is_ty_uninhabited(&mut self, expr: &Expr<'_>, succ: LiveNode) -> LiveNode {
        let ty = self.typeck_results.expr_ty(expr);
        let m = self.ir.tcx.parent_module(expr.hir_id).to_def_id();
        if self.ir.tcx.is_ty_uninhabited_from(m, ty, self.param_env) { self.exit_ln } else { succ }
    }
}
