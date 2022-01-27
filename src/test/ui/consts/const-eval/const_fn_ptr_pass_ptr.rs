// Makes sure we can pass fn pointers in const code.
// check-pass

#![feature(const_fn_fn_ptr_basics)]
#![allow(dead_code)]

struct Foo {
    foo: fn(),
}

const fn make_foo() -> Foo {
    Foo { foo: || () }
}

fn main() {
    make_foo();
}
