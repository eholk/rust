#![feature(generators)]

use std::cell::Cell;

fn main() {
    fn assert_sync<T: Sync>(_: T) {}
    fn assert_send<T: Send>(_: T) {}

    assert_sync(|| {
        //~^ ERROR: generator cannot be shared between threads safely
        let a = Cell::new(2);
        yield;
        // Explicity drop a so it is live across the yield for liveness-based generator captures.
        drop(a);
    });

    let a = Cell::new(2);
    assert_send(|| {
        //~^ ERROR: E0277
        drop(&a);
        yield;
    });
}
