#![recursion_limit="128"]
#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate eqlog;
#[macro_use]
extern crate lazy_static;

pub mod cwf;
pub mod lang;
pub mod cwf_checker;
