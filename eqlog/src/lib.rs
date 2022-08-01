#[macro_use]
extern crate lalrpop_util;
extern crate convert_case;
#[cfg(test)]
extern crate indoc;

mod ast;
mod module;
mod unification;
lalrpop_mod!(
    #[allow(unused)]
    grammar
);
mod build;
mod error;
mod flat_ast;
mod index_selection;
mod llam;
mod rust_gen;

pub use crate::build::process_root;
