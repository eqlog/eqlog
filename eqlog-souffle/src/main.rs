#[macro_use] extern crate lalrpop_util;
lalrpop_mod!(grammar);
#[cfg(test)] #[macro_use]
extern crate maplit;
extern crate ena;
#[cfg(test)]
extern crate indoc;

mod ast;
mod theory;
#[cfg(test)]
mod theory_test;

fn main() {}
