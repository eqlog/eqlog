use eqlog_runtime::eqlog_mod;
eqlog_mod!(trivial_idempotent);
eqlog_mod!(trans_refl);
eqlog_mod!(semilattice);

#[cfg(test)]
mod semilattice_test;
#[cfg(test)]
mod trans_refl_test;
