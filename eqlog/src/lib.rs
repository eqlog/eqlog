mod ast;
mod ast_v1;
mod module;
mod semantics;
mod unification;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(
    #[allow(unused)]
    grammar
);
mod build;
//lalrpop_mod!(
//    #[allow(unused)]
//    grammar_v1
//);
mod error;
mod flat_ast;
mod flat_to_llam;
mod flatten;
mod index_selection;
mod llam;
mod rust_gen;
mod source_display;

pub use crate::build::{process_root, process_root_with_config, Config};
