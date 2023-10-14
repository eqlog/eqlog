use eqlog_runtime::eqlog_mod;
eqlog_mod!(monoid);
eqlog_mod!(pointed);
eqlog_mod!(trivial_idempotent);
eqlog_mod!(trans_refl);
eqlog_mod!(poset);
eqlog_mod!(semilattice);
eqlog_mod!(product_category);
eqlog_mod!(lex_category);
eqlog_mod!(partial_magma);
eqlog_mod!(pca);
eqlog_mod!(reduction_from_nullary);

#[cfg(test)]
mod eval_func;
#[cfg(test)]
mod lex_category_test;
mod monoid_test;
// Disabled by default because it takes a while to run in debug mode.
//#[cfg(test)]
//mod pca_test;
mod pointed_test;
#[cfg(test)]
mod poset_test;
#[cfg(test)]
mod product_category_test;
#[cfg(test)]
mod semilattice_test;
#[cfg(test)]
mod trans_refl_test;
