use eqlog_runtime::eqlog_mod;
eqlog_mod!(trivial_idempotent);
eqlog_mod!(trans_refl);
eqlog_mod!(semilattice);
eqlog_mod!(product_category);
eqlog_mod!(reduction_from_nullary);

#[cfg(test)]
mod product_category_test;
#[cfg(test)]
mod semilattice_test;
#[cfg(test)]
mod trans_refl_test;
