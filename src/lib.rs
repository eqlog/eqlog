#![recursion_limit="128"]
#[macro_use] #[cfg(test)]
extern crate maplit;
extern crate eqlog_util;
use eqlog_util::eqlog_mod;
extern crate lalrpop_util;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(#[allow(unused)] grammar);
eqlog_mod!(cwf);
pub mod ast;

pub mod cwf_checker;
