#[macro_use]
extern crate lalrpop_util;
#[cfg(test)]
#[macro_use]
extern crate maplit;
extern crate convert_case;
#[cfg(test)]
extern crate indoc;

mod ast;
mod signature;
mod unification;
lalrpop_mod!(
    #[allow(unused)]
    grammar
);
mod analysis;
mod build;
mod error;
mod flat_ast;
mod index_selection;
mod query_action;
mod rust_gen;

pub use crate::build::process_root;
