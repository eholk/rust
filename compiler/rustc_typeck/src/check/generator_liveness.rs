use crate::expr_use_visitor;
use rustc_passes::liveness::{IrMaps, VarKind};

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
