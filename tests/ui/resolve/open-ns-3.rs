// This test should fail with `utils` being defined multiple times, since open-ns-mod-my_api.rs
// includes a `mod utils` and we also include open-ns-my_api_utils.rs as a namespaced crate at
// my_api::utils.

//@ aux-crate: my_api=open-ns-mod-my_api.rs
//@ aux-crate: my_api::utils=open-ns-my_api_utils.rs
//@ compile-flags: -Z namespaced-crates
//@ edition: 2024

fn main() {
    let _ = my_api::root_function();
    let _ = my_api::utils::root_helper();
    let _ = my_api::utils::utils_helper();
}
