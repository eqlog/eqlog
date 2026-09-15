fn main() -> eqlog::Result<()> {
    env_logger::builder()
        .filter_level(log::LevelFilter::max())
        .init();
    if cfg!(feature = "naive") {
        eqlog::process_root_with_options(&eqlog::CompileOptions {
            evaluation_mode: eqlog::EvaluationMode::Naive,
        })?;
    } else {
        eqlog::process_root()?;
    }
    Ok(())
}
