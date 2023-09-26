use eqlog_published::{process_root_with_config, Config};

fn main() {
    let config = Config {
        runtime_crate: "eqlog_runtime_published".to_string(),
        ..Config::default()
    };
    process_root_with_config(&config);
}
