fn main() -> eqlog::Result<()> {
    env_logger::builder()
        .filter_level(log::LevelFilter::max())
        .init();
    eqlog::process_root()?;
    Ok(())
}
