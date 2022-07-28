// run-pass
#![feature(async_fn_in_traits)]

use std::fmt::Debug;

fn make_dyn_star(i: usize) {
    let _dyn_i: dyn* Debug = i as dyn* Debug;
}

fn main() {
    make_dyn_star(42);
}
