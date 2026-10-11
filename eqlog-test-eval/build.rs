use std::env;
use std::fs;
use std::path::PathBuf;

use indoc::formatdoc;

fn build_long_pipeline(options: eqlog::CompileOptions) -> eqlog::Result<()> {
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"));
    let input = out.join("long_pipeline_input");
    fs::create_dir_all(&input)?;
    let mut source = String::from("type El; pred seed(El);\n");
    for i in 0..128 {
        let previous = if i == 0 {
            "seed".to_owned()
        } else {
            let previous = i - 1;
            format!("step_{previous}")
        };
        source.push_str(&formatdoc! {"
            pred gate_{i}(El);
            pred side_{i}(El);
            pred step_{i}(El);
            rule branch_{i} {{ if gate_{i}(x); then side_{i}(x); }}
            rule join_{i} {{ if side_{i}(x); if {previous}(x); then step_{i}(x); }}
        "});
    }
    fs::write(input.join("long_pipeline.eql"), source)?;
    eqlog::process(&eqlog::Config {
        in_dir: input,
        out_dir: out.join("long_pipeline"),
        component_build: None,
        options,
    })
}

fn main() -> eqlog::Result<()> {
    env_logger::builder()
        .filter_level(log::LevelFilter::max())
        .init();
    let mut options = eqlog::CompileOptions::default();
    if cfg!(feature = "naive") {
        options.evaluation_mode = eqlog::EvaluationMode::Naive;
    }
    if cfg!(feature = "desugared") {
        options.model_mode = eqlog::ModelMode::Desugared;
    }
    if cfg!(feature = "stratified") {
        options.scheduling_mode = eqlog::SchedulingMode::Stratified;
    }
    eqlog::process_root_with_options(&options)?;
    build_long_pipeline(options)?;
    Ok(())
}
