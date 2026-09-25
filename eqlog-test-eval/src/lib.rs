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
eqlog_mod!(branches);
eqlog_mod!(branch_results);
eqlog_mod!(nat);
eqlog_mod!(matches);
eqlog_mod!(matches_rel);
eqlog_mod!(triple_join);
eqlog_mod!(int);
eqlog_mod!(indexed_set);
eqlog_mod!(indexed_pointed);
eqlog_mod!(indexed_abelian_group);
eqlog_mod!(empty);
eqlog_mod!(subset);
eqlog_mod!(subset_rules);
eqlog_mod!(consts);
eqlog_mod!(mor_head_forms);
eqlog_mod!(nested);
eqlog_mod!(nested_diagonals);
eqlog_mod!(nested_image_creation);
eqlog_mod!(diagonal_canonicalization);
eqlog_mod!(morphism_helper_names);
eqlog_mod!(morphism_preservation);
eqlog_mod!(morphism_category);
eqlog_mod!(member_parents);
eqlog_mod!(canonicalization);

#[cfg(test)]
mod canonicalization_test;
mod category_mod;
#[cfg(test)]
mod diagonal_canonicalization_test;
#[cfg(test)]
mod distr_lattice_test;
#[cfg(test)]
mod dynamic_correctness_test;
#[cfg(test)]
mod dynamic_signature_test;
#[cfg(test)]
mod dynamic_test;
#[cfg(test)]
mod eval_func;
#[cfg(test)]
mod group_test;
#[cfg(test)]
mod lex_category_test;
#[cfg(test)]
mod logic_test;
#[cfg(test)]
mod model_hom_test;
mod monoid_test;
// Disabled by default because it takes a while to run in debug mode.
//#[cfg(test)]
//mod pca_test;
#[cfg(test)]
mod branch_results_test;
#[cfg(test)]
mod branches_test;
#[cfg(test)]
mod consts_test;
#[cfg(test)]
mod indexed_abelian_group_test;
#[cfg(test)]
mod indexed_pointed_test;
#[cfg(test)]
mod indexed_set_test;
#[cfg(test)]
mod inference_test;
#[cfg(test)]
mod int_test;
#[cfg(test)]
mod matches_rel_test;
#[cfg(test)]
mod matches_test;
#[cfg(test)]
mod member_parents_test;
#[cfg(test)]
mod mor_head_forms_test;
#[cfg(test)]
mod morphism_category_test;
#[cfg(test)]
mod morphism_helper_names_test;
#[cfg(test)]
mod morphism_preservation_test;
#[cfg(test)]
mod nat_test;
#[cfg(test)]
mod nested_diagonals_test;
#[cfg(test)]
mod nested_image_creation_test;
#[cfg(test)]
mod nested_test;
mod pointed_test;
#[cfg(test)]
mod poset_test;
#[cfg(test)]
mod product_category_test;
#[cfg(test)]
mod semilattice_test;
#[cfg(test)]
mod subset_rules_test;
#[cfg(test)]
mod subset_test;
#[cfg(test)]
mod trans_refl_test;
