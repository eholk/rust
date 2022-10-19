#![feature(core_intrinsics, generators)]

use core::intrinsics::drop_dead;

fn borrow<T>(_: &T) {}

fn main() {
    let a = || {
        let n = [0u8; 100];
        borrow(&n);
        unsafe {
            drop_dead(n);
        }
        yield;
    };
    println!("{}", core::mem::size_of_val(&a));
}
