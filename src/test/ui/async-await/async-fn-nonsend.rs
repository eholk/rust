// edition:2018
// compile-flags: --crate-type lib

use std::{fmt::Debug, rc::Rc};

fn non_send() -> impl Debug {
    Rc::new(())
}

async fn fut() {}

async fn non_send_temporary_in_match() {
    // We could theoretically make this work as well (produce a `Send` future)
    // for scrutinees / temporaries that can or will
    // be dropped prior to the match body
    // (e.g. `Copy` types).
    match Some(non_send()) {
        Some(_) => fut().await,
        None => {}
    }
}

fn assert_send(_: impl Send) {}

pub fn pass_assert() {
    assert_send(non_send_temporary_in_match());
    //~^ ERROR future cannot be sent between threads safely
    //~^^ ERROR future cannot be sent between threads safely
}
