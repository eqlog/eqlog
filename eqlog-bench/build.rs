use std::env;
use std::path::PathBuf;

fn main() -> eqlog::Result<()> {
    println!("cargo:rerun-if-changed=theories");
    eqlog::process(&eqlog::Config {
        in_dir: PathBuf::from("theories"),
        out_dir: PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR")),
        component_build: None,
        options: eqlog::CompileOptions {
            evaluation_mode: eqlog::EvaluationMode::SemiNaive,
            model_mode: eqlog::ModelMode::Native,
        },
    })
}
