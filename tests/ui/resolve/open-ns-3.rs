//@ aux-crate: my_api=open-ns-mod-my_api.rs
//@ aux-crate: my_api::utils=open-ns-my_api_utils.rs
//@ compile-flags: -Z namespaced-crates

fn test() {
    let _ = my_api::root_function();
    let _ = my_api::utils::root_helper();
    let _ = my_api::utils::utils_helper();
}
