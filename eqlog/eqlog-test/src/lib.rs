use eqlog_util::eqlog_mod;
eqlog_mod!(equational_monoid);
eqlog_mod!(monoid);
eqlog_mod!(pointed);
eqlog_mod!(trivial_idempotent);
eqlog_mod!(logic);
eqlog_mod!(trans_refl);
eqlog_mod!(poset);
eqlog_mod!(semilattice);
eqlog_mod!(distr_lattice);
eqlog_mod!(group);
eqlog_mod!(product_category);
eqlog_mod!(lex_category);

mod category_mod;
#[cfg(test)]
mod distr_lattice_test;
#[cfg(test)]
mod group_test;
#[cfg(test)]
mod lex_category_test;
#[cfg(test)]
mod logic_test;
mod monoid_test;
mod pointed_test;
#[cfg(test)]
mod poset_test;
#[cfg(test)]
mod product_category_test;
#[cfg(test)]
mod semilattice_test;
#[cfg(test)]
mod trans_refl_test;
