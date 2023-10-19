mod ast;
mod eqlog_util;
mod grammar_util;
mod module;
mod semantics;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(
    #[allow(unused)]
    grammar
);
lalrpop_mod!(
    #[allow(unused)]
    grammar_new
);
mod build;
mod error;
mod flat_ast;
mod flat_to_llam;
mod flatten;
mod index_selection;
mod llam;
mod rust_gen;
mod source_display;

pub use crate::build::{process, process_root, Config};
