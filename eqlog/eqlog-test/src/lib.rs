use eqlog_util::eqlog_mod;
eqlog_mod!(equational_monoid);
eqlog_mod!(monoid);
eqlog_mod!(pointed);
eqlog_mod!(trivial_idempotent);
eqlog_mod!(logic);
eqlog_mod!(trans_refl);
eqlog_mod!(poset);
eqlog_mod!(semilattice);

mod category_mod;
#[cfg(test)]
mod logic_test;
mod monoid_test;
mod pointed_test;
#[cfg(test)]
mod trans_refl_test;
#[cfg(test)]
mod poset_test;
#[cfg(test)]
mod semilattice_test;
