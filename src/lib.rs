#![recursion_limit="128"]
#[macro_use]
extern crate lazy_static;
#[macro_use] #[cfg(test)]
extern crate maplit;
extern crate eqlog_util;
use eqlog_util::eqlog_mod;
extern crate lalrpop_util;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(#[allow(unused)] grammar);
eqlog_mod!(cwf_new);
pub mod ast;
#[macro_use]
pub mod eqlog;
pub mod cwf;
pub mod cwf_checker;
