pub mod utils {
    pub fn root_helper() {
        println!("helper function");
    }
}

pub fn root_function() -> String {
    "my_api root!".to_string()
}
