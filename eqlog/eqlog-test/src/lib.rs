use eqlog_util::eqlog_mod;
eqlog_mod!(equational_monoid);
eqlog_mod!(monoid);
eqlog_mod!(pointed);
eqlog_mod!(trivial_idempotent);
eqlog_mod!(logic);

mod category_mod;
mod monoid_test;
mod pointed_test;
#[cfg(test)]
mod logic_test;
