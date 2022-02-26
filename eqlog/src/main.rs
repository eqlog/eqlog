#[macro_use] extern crate lalrpop_util;
#[cfg(test)] #[macro_use]
extern crate maplit;
#[cfg(test)]
extern crate indoc;

mod direct_ast;
mod indirect_ast;
mod signature;
mod unification;
lalrpop_mod!(grammar);
mod analysis;
mod flat_ast;
mod index_selection;
//mod rust_gen;

fn main() {}
