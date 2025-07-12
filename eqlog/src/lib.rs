use lalrpop_util::lalrpop_mod;

mod eqlog_util;
mod grammar_util;
mod semantics;
lalrpop_mod!(grammar);
mod build;
#[allow(dead_code)]
mod debug;
mod error;
mod flat_eqlog;
mod flatten;
mod fmt_util;
mod ram;
mod rust_gen;
mod source_display;
mod to_ram;
mod unification;

pub use crate::build::{process, process_root, ComponentConfig, Config, Error, Result};
