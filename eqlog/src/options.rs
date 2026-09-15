use clap::ValueEnum;

/// How generated rules match facts during saturation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum EvaluationMode {
    /// Match all facts on every iteration, including previously matched facts.
    Naive,
    /// Match combinations containing new facts to avoid repeating old matches.
    #[default]
    SemiNaive,
}

/// Options controlling the generated evaluator.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CompileOptions {
    /// Defaults to [`EvaluationMode::SemiNaive`].
    pub evaluation_mode: EvaluationMode,
}
