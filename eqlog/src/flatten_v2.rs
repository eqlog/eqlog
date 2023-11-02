#![allow(dead_code, unused_variables)]

use std::collections::BTreeMap;

use crate::flat_eqlog::*;
use eqlog_eqlog::*;

/// Emits a flat if block to match the delta given by `morphism` with arbitrary (not necessarily
/// fresh) data.
///
/// This function assumes that data of the domain of `morphism` has been matched already, with
/// elements assigned to flat vars according to `dom_el_vars`. The `cod_el_vars` map must assign to
/// each element in the codomain a flat var that is compatible with `dom_el_vars` and `morphism`.
/// That is, if the preimage of some element `el` under `morphism` is non-empty, then the flat var
/// assigned to `el` is one of the flat vars assigned to a preimage.
fn flatten_if_arbitrary(
    morphism: Morphism,
    dom_el_vars: &BTreeMap<El, FlatVar>,
    cod_el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Vec<FlatIfStmt> {
    todo!()
}

/// Emits flat if blocks which together match the delta given by `morphism` with fresh data.
///
/// Each of the resulting `FlatIfBlock`s use the same assignment `cod_el_vars` of codomain elements
/// to flat variables.
fn flatten_if_fresh(
    morphism: Morphism,
    cod_el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Vec<Vec<FlatIfStmt>> {
    todo!()
}

/// Emits a then block to lift against a provided surjective `morphism`.
fn flatten_surjective_then(
    morphism: Morphism,
    cod_el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Vec<FlatSurjThenStmt> {
    todo!()
}

/// Emit a non-surjective flat then stmt to lift against a non-surjective `morphism`, which must be
/// given given by a pushout along making a function defined on a single tuple of arguments.
fn flatten_non_surjective_then(
    morphism: Morphism,
    cod_el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Option<FlatNonSurjThenStmt> {
    todo!()
}

fn flatten_rule(rule: RuleDeclNode, eqlog: &Eqlog) -> Vec<FlatStmt> {
    todo!()
}
