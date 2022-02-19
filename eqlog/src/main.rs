#[macro_use] extern crate lalrpop_util;
#[cfg(test)] #[macro_use]
extern crate maplit;
#[cfg(test)]
extern crate indoc;

mod direct_ast;
mod indirect_ast;
mod theory;
mod unification;
lalrpop_mod!(grammar);
#[cfg(test)]
mod theory_test;

fn main() {}
