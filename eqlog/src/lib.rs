use lalrpop_util::lalrpop_mod;

mod ast;
mod ast_to_eqlog;
mod eqlog_util;
mod grammar_util;
mod semantics;
lalrpop_mod!(grammar);
mod build;
mod check_variables;
#[allow(dead_code)]
mod debug;
mod error;
mod flat_eqlog;
mod flatten;
mod fmt_util;
mod ram;
mod rust_gen;
mod scopes;
mod source_display;
mod syntactic;
mod to_ram;
mod unification;

pub use crate::build::{process, process_root, ComponentConfig, Config, Error, Result};
