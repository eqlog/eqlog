extern crate maplit;

extern crate eqlog_util;
use eqlog_util::eqlog_mod;

eqlog_mod!(category);

eqlog_mod!(monoid);
mod monoid_test;

eqlog_mod!(pointed);
mod pointed_test;
