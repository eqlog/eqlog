mod eqlog_util;
mod grammar_util;
mod semantics;
mod sort_if_stmts_pass;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(grammar);
mod build;
mod error;
mod flat_ast;
mod flat_eqlog;
mod flat_to_llam;
mod flatten;
mod index_selection;
mod llam;
mod rust_gen;
mod slice_group_by;
mod source_display;

pub use crate::build::{process, process_root, Config};
