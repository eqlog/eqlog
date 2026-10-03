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
    if cfg!(feature = "simultaneous") {
        options.scheduling_mode = eqlog::SchedulingMode::Simultaneous;
    }
    eqlog::process_root_with_options(&options)?;
    Ok(())
}
