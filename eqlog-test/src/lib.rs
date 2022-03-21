extern crate maplit;

extern crate eqlog_util;
use eqlog_util::eqlog_mod;

eqlog_mod!(category);
eqlog_mod!(equational_monoid);
eqlog_mod!(monoid);
eqlog_mod!(pointed);

mod monoid_test;
mod pointed_test;
