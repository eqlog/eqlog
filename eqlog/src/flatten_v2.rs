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

// /// An iterator over the iterated tails of a [Chain]
// ///
// /// This includes the provided `chain` itself and the final `nil_chain`.
// fn iter_tails<'a>(chain: Chain, eqlog: &'a Eqlog) -> impl 'a + Iterator<Item = Chain> {
//     successors(Some(chain), |prev_chain| {
//         let next_chain = eqlog.chain_tail(*prev_chain);
//         if let None = next_chain {
//             assert!(
//                 eqlog.are_equal_chain(*prev_chain, eqlog.nil_chain().unwrap()),
//                 "Every chain except for the nil chain should have a tail"
//             );
//         }
//         next_chain
//     })
// }
//
// /// An iterator over the transitions in a [Chain].
// fn iter_transitions<'a>(chain: Chain, eqlog: &'a Eqlog) -> impl 'a + Iterator<Item = Morphism> {
//     iter_tails(chain, eqlog).filter_map(|c| eqlog.chain_head_transition(c))
// }
//
// /// Assign compatible [FlatVar] to the elements of structs in a [Chain].
// ///
// /// Since distinct structures have disjoint sets of elements, a single map can hold all assigned
// /// flat variables.
// fn assign_el_vars(chain: Chain, eqlog: &Eqlog) -> BTreeMap<El, FlatVar> {
//     let mut el_vars = BTreeMap::new();
//
//     // Note that if there is no transition at all, then the chain must consist of only the initial
//     // structure. In that case the resulting `BTreeMap` must be empty.
//     for transition in iter_transitions(chain, eqlog) {
//         let dom = eqlog
//             .dom(transition)
//             .expect("Every morphism should have a domain");
//         let cod = eqlog
//             .cod(transition)
//             .expect("Every morphism should have a domain");
//
//         for (m, preimage, image) in eqlog.iter_map_el() {
//             if !eqlog.are_equal_morphism(m, transition) {
//                 continue;
//             }
//
//             if let Some(var) = el_vars.get(&preimage).copied() {
//                 el_vars.insert(image, var);
//             }
//         }
//     }
//
//     el_vars
// }

fn flatten_rule(rule: RuleDeclNode, eqlog: &Eqlog) -> Vec<FlatStmt> {
    // let chain = eqlog
    //     .grouped_rule_chain(rule)
    //     .expect("grouped_rule_chain should be total");
    // let el_vars = assign_el_vars(chain, eqlog);

    todo!()
}
