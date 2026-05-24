use lalrpop_util::lalrpop_mod;

mod algebra;
mod ast;
mod casing;
mod grammar_util;
lalrpop_mod!(grammar);
mod build;
mod error;
mod flat_eqlog;
mod flatten;
mod fmt_util;
mod ram;
mod rust_gen;
mod scope_checks;
mod scopes;
mod source_display;
mod syntactic;
mod to_ram;
mod unification;

pub use crate::build::{process, process_root, ComponentConfig, Config, Error, Result};
