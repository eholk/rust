// edition: 2021
// run-pass

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
    let _x = &0 as &dyn MyTrait;
}
