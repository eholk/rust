// Makes sure we cannot call a fn pointer from const code.

#![feature(const_fn_fn_ptr_basics)]
#![allow(dead_code)]

struct Foo {
    foo: fn(),
}

const fn make_foo(foo: fn()) -> Foo {
    foo();
    //~^ ERROR function pointers are not allowed in const fn

    Foo {
        foo
    }
}

fn main() {
    make_foo(|| ());
}
