// edition: 2021
// check-pass

// Make sure async fn on trait objects return `dyn* Future`

#![feature(async_fn_in_trait, async_fn_in_dyn_trait, dyn_star)]
#![allow(incomplete_features)]

trait MyTrait {
    async fn foo(&self, n: usize) -> i32;
    fn bar(&self) -> i32;
}

impl MyTrait for i32 {
    async fn foo(&self, n: usize) -> i32 {
        n as i32
    }

    fn bar(&self) -> i32 {
        *self
    }
}

fn assert_dyn_star(_: dyn* std::future::Future<Output = i32>) {}

fn body(x: &dyn MyTrait) {
    let g = x.bar();
    let f = x.foo(g as usize);
    assert_dyn_star(f);
}

fn main() {
    let x = &0 as &dyn MyTrait;
    body(x);
}
