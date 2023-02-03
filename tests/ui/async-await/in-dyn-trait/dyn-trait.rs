// edition: 2021
// run-pass

#![feature(async_fn_in_trait, async_fn_in_dyn_trait)]
#![allow(incomplete_features)]

trait MyTrait {
    async fn foo(&self, n: usize) -> i32;
}

impl MyTrait for i32 {
    async fn foo(&self, n: usize) -> i32 {
        n as i32
    }
}

fn main() {
    let x = &0 as &dyn MyTrait;
    let _f = x.foo(42);
}
