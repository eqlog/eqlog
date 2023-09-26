#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct Config {
    /// The name of the eqlog-runtime crate.
    ///
    /// This must be in snake_case, not kebap-case.
    pub runtime_crate: String,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            runtime_crate: "eqlog_runtime".to_string(),
        }
    }
}
