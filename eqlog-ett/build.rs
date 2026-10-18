fn main() -> eqlog::Result<()> {
    // Most kernel facts are images along substitutions; materializing them in
    // indexed tables saturates the developments faster than native transport.
    eqlog::process_root_with_options(&eqlog::CompileOptions {
        model_mode: eqlog::ModelMode::Desugared,
        ..Default::default()
    })
}
