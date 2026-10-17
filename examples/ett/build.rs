fn main() -> eqlog::Result<()> {
    let mut options = eqlog::CompileOptions::default();
    if cfg!(feature = "stratified") {
        options.scheduling_mode = eqlog::SchedulingMode::Stratified;
    }
    eqlog::process_root_with_options(&options)
}
