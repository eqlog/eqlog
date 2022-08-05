mod ast;
mod module;
mod unification;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(
    #[allow(unused)]
    grammar
);
mod build;
mod error;
mod flat_ast;
mod flat_to_llam;
mod flatten;
mod index_selection;
mod llam;
mod rust_gen;

pub use crate::build::process_root;
