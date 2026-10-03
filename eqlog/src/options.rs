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

/// How member facts are transported along model morphisms.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum ModelMode {
    /// Share inherited facts using specialized morphism propagation.
    #[default]
    Native,
    /// Materialize inherited facts using ordinary rules where the required images exist.
    Desugared,
}

/// How rule groups share a fixed-point schedule.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum SchedulingMode {
    /// Evaluate all rule groups together in each round.
    #[default]
    Simultaneous,
    /// Close dependency components before evaluating their consumers.
    Stratified,
}

/// Options controlling the generated evaluator.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CompileOptions {
    /// Defaults to [`EvaluationMode::SemiNaive`].
    pub evaluation_mode: EvaluationMode,
    /// Defaults to [`ModelMode::Native`], independently of rule evaluation.
    pub model_mode: ModelMode,
    /// Defaults to [`SchedulingMode::Simultaneous`].
    pub scheduling_mode: SchedulingMode,
}
