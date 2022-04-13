// check-pass

#![feature(async_fn_in_traits)]

pub fn dyn_star_parameter(_: dyn* Send) {
}

fn main() {}
