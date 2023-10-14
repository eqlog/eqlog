use eqlog_runtime::eqlog_mod;
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
eqlog_mod!(partial_magma);
eqlog_mod!(pca);
eqlog_mod!(inference);
eqlog_mod!(reduction_from_nullary);

mod category_mod;
#[cfg(test)]
mod distr_lattice_test;
#[cfg(test)]
mod eval_func;
#[cfg(test)]
mod group_test;
#[cfg(test)]
mod lex_category_test;
#[cfg(test)]
mod logic_test;
mod monoid_test;
// Disabled by default because it takes a while to run in debug mode.
//#[cfg(test)]
//mod pca_test;
#[cfg(test)]
mod inference_test;
mod pointed_test;
#[cfg(test)]
mod poset_test;
#[cfg(test)]
mod product_category_test;
#[cfg(test)]
mod semilattice_test;
#[cfg(test)]
mod trans_refl_test;
