use std::collections::BTreeSet;

use eqlog_runtime::__private::{MatchProofState, Table};
use eqlog_runtime::PrefixTree1;

fn rows(arity: usize, tuples: impl IntoIterator<Item = Vec<u32>>) -> Table {
    let mut result = Table::new(arity);
    for tuple in tuples {
        result.insert(&tuple);
    }
    result
}

fn unary(values: impl IntoIterator<Item = u32>) -> Table {
    rows(1, values.into_iter().map(|value| vec![value]))
}

fn nullary(present: bool) -> Table {
    let mut result = Table::new(0);
    if present {
        result.insert(&[]);
    }
    result
}

fn keys(tree: &PrefixTree1) -> BTreeSet<u32> {
    tree.iter().map(|[value]| value).collect()
}

fn tuples(table: &Table) -> BTreeSet<Vec<u32>> {
    table.iter().collect()
}

fn uncovered(
    current: &[Table],
    proofs: &[Vec<Table>],
    columns: &[Vec<usize>],
    binding: &[u32],
) -> bool {
    let state = MatchProofState::new(current.to_vec(), proofs.to_vec(), columns.to_vec());
    uncovered_state(state, binding)
}

fn uncovered_state(mut state: Option<MatchProofState>, binding: &[u32]) -> bool {
    for (variable, &value) in binding.iter().enumerate() {
        if let Some(current) = state {
            if current.is_covered() {
                return false;
            }
            if let Some(keys) = current.uncovered_keys(variable) {
                return keys.contains([value]);
            }
            state = current.restrict(variable, value);
        }
    }
    state.is_none_or(|state| !state.is_covered())
}

fn body_holds(relations: &[Table], columns: &[Vec<usize>], binding: &[u32]) -> bool {
    relations.iter().zip(columns).all(|(rows, columns)| {
        let tuple: Vec<_> = columns.iter().map(|&column| binding[column]).collect();
        rows.contains(&tuple)
    })
}

#[test]
fn an_entire_parent_product_is_covered_before_enumerating_bindings() {
    let left = unary(0..4096);
    let right = unary(4096..8192);
    let current = vec![left, right];
    let proof = current.clone();
    let state = MatchProofState::new(current, vec![proof], vec![vec![0], vec![1]]).unwrap();
    assert!(state.is_covered());
}

#[test]
fn overlapping_certificates_subtract_the_union_of_final_keys() {
    let current = vec![unary([1]), unary([10, 11, 12, 13, 14])];
    let proofs = vec![
        vec![unary([1]), unary([10, 11])],
        vec![unary([1]), unary([11, 12])],
        vec![unary([1]), unary([13])],
        vec![unary([2]), unary([14])],
    ];
    let state = MatchProofState::new(current, proofs, vec![vec![0], vec![1]]).unwrap();
    assert!(!state.is_covered());
    let state = state.restrict(0, 1).unwrap();
    assert!(!state.is_covered());
    assert_eq!(
        keys(&state.uncovered_keys(1).unwrap()),
        BTreeSet::from([14])
    );
}

#[test]
fn a_previous_target_certificate_preserves_old_mixed_parent_matches() {
    let current = vec![unary([1, 2]), unary([10, 20])];
    let parents = vec![vec![unary([1]), unary([10])], vec![unary([2]), unary([20])]];
    let columns = vec![vec![0], vec![1]];
    let mut actual = BTreeSet::new();
    for x in [1, 2] {
        for y in [10, 20] {
            if uncovered(&current, &parents, &columns, &[x, y]) {
                actual.insert([x, y]);
            }
        }
    }
    assert_eq!(actual, BTreeSet::from([[1, 20], [2, 10]]));
    let mut proofs = parents;
    proofs.push(vec![unary([1, 2]), unary([10])]);
    actual.retain(|binding| uncovered(&current, &proofs, &columns, binding));
    assert_eq!(actual, BTreeSet::from([[1, 20]]));
}

#[test]
fn certificate_sets_extend_beyond_a_machine_word() {
    let current = vec![unary([0, 1]), unary(0..70)];
    let mut proofs: Vec<_> = (0..70)
        .map(|value| vec![unary([0]), unary([value])])
        .collect();
    proofs.push(vec![unary([1]), unary([69])]);
    let state = MatchProofState::new(current, proofs, vec![vec![0], vec![1]]).unwrap();
    assert!(!state.is_covered());
    let zero = state.restrict(0, 0).unwrap();
    assert!(zero.uncovered_keys(1).unwrap().is_empty());
    let one = state.restrict(0, 1).unwrap();
    assert_eq!(keys(&one.uncovered_keys(1).unwrap()), (0..69).collect());
}

#[test]
fn consecutive_repeated_columns_keep_only_consistent_preimages() {
    let current = vec![
        rows(3, [vec![1, 1, 7], vec![1, 2, 8], vec![2, 2, 8]]),
        unary([7, 8]),
    ];
    let proofs = vec![
        vec![rows(3, [vec![1, 1, 7]]), unary([7])],
        vec![rows(3, [vec![1, 2, 8]]), unary([8])],
    ];
    let columns = vec![vec![0, 0, 1], vec![1]];
    let state = MatchProofState::new(current.clone(), proofs.clone(), columns.clone()).unwrap();
    assert!(state.uncovered_keys(0).is_none());
    let one = state.restrict(0, 1).unwrap();
    assert!(one.uncovered_keys(1).unwrap().is_empty());
    assert!(state.restrict(0, 2).is_none());
    assert!(!uncovered(&current, &proofs, &columns, &[1, 7]));
    assert!(uncovered(&current, &proofs, &columns, &[2, 8]));
}

#[test]
fn restrictions_wait_for_an_earlier_index_column_to_be_bound() {
    let current = vec![rows(2, [vec![10, 1], vec![20, 1]]), unary([1])];
    let proofs = vec![
        vec![rows(2, [vec![10, 1]]), unary([1])],
        vec![rows(2, [vec![20, 2]]), unary([1])],
    ];
    let state = MatchProofState::new(current, proofs, vec![vec![1, 0], vec![0]]).unwrap();
    let state = state.restrict(0, 1).unwrap();
    assert_eq!(
        keys(&state.uncovered_keys(1).unwrap()),
        BTreeSet::from([20])
    );
    assert!(state.restrict(1, 10).unwrap().is_covered());
    assert!(state.restrict(1, 20).is_none());
}

#[test]
fn private_witness_growth_does_not_reopen_an_already_proved_product() {
    let current = vec![
        rows(2, (0..4096).map(|witness| vec![1, witness])),
        unary(0..1024),
    ];
    let proof = vec![rows(2, [vec![1, 5000]]), current[1].clone()];
    let state = MatchProofState::new(current, vec![proof], vec![vec![0, 2], vec![1]])
        .unwrap()
        .with_relevant_variables(&[0, 1]);
    assert!(state.is_covered());
}

#[test]
fn final_relevant_keys_are_subtracted_before_private_suffixes() {
    let current = vec![
        unary([1]),
        rows(2, [vec![10, 100], vec![20, 200], vec![30, 300]]),
    ];
    let proofs = vec![
        vec![unary([1]), rows(2, [vec![10, 999]])],
        vec![unary([1]), rows(2, [vec![20, 888]])],
    ];
    let state = MatchProofState::new(current, proofs, vec![vec![0], vec![1, 2]])
        .unwrap()
        .with_relevant_variables(&[0, 1]);
    let state = state.restrict(0, 1).unwrap();
    assert_eq!(
        keys(&state.uncovered_keys(1).unwrap()),
        BTreeSet::from([30])
    );
}

#[test]
fn final_key_projection_respects_a_later_previously_bound_column() {
    let current = vec![
        rows(3, [vec![10, 1, 100], vec![20, 2, 200], vec![30, 1, 300]]),
        unary([1]),
    ];
    let proofs = vec![
        vec![rows(3, [vec![10, 1, 999]]), unary([1])],
        vec![rows(3, [vec![30, 2, 888]]), unary([1])],
    ];
    let state = MatchProofState::new(current, proofs, vec![vec![1, 0, 2], vec![0]])
        .unwrap()
        .with_relevant_variables(&[0, 1]);
    let state = state.restrict(0, 1).unwrap();
    assert_eq!(
        keys(&state.uncovered_keys(1).unwrap()),
        BTreeSet::from([30])
    );
}

#[test]
fn private_prefixes_preserve_shared_output_keys_without_sharing_witnesses() {
    let current = vec![
        rows(2, [vec![100, 1], vec![200, 1], vec![300, 2]]),
        unary([10, 20]),
    ];
    let proofs = vec![
        vec![rows(2, [vec![999, 1]]), unary([10])],
        vec![rows(2, [vec![888, 2]]), unary([20])],
    ];
    let state = MatchProofState::new(current, proofs, vec![vec![2, 0], vec![1]])
        .unwrap()
        .with_relevant_variables(&[0, 1]);
    assert_eq!(
        keys(&state.restrict(0, 1).unwrap().uncovered_keys(1).unwrap()),
        BTreeSet::from([20])
    );
    assert_eq!(
        keys(&state.restrict(0, 2).unwrap().uncovered_keys(1).unwrap()),
        BTreeSet::from([10])
    );
}

#[test]
fn all_small_projected_products_match_existential_set_difference() {
    for private_first in [false, true] {
        let columns = vec![
            if private_first {
                vec![2, 0]
            } else {
                vec![0, 2]
            },
            vec![1],
        ];
        for pattern in 0..15625 {
            let mut remaining = pattern;
            let mut current = vec![Table::new(2), Table::new(1)];
            let mut proofs = vec![vec![Table::new(2), Table::new(1)]; 2];
            for slot in 0..6 {
                let state = remaining % 5;
                remaining /= 5;
                if state == 0 {
                    continue;
                }
                let (atom, row) = if slot < 4 {
                    let x = slot / 2;
                    let witness = slot % 2;
                    (
                        0,
                        if private_first {
                            vec![witness, x]
                        } else {
                            vec![x, witness]
                        },
                    )
                } else {
                    (1, vec![slot - 4])
                };
                current[atom].insert(&row);
                let membership = state - 1;
                for (proof, relations) in proofs.iter_mut().enumerate() {
                    if membership & (1 << proof) != 0 {
                        relations[atom].insert(&row);
                    }
                }
            }
            for x in 0..2 {
                for y in 0..2 {
                    let body = |relations: &[Table]| {
                        (0..2).any(|witness| body_holds(relations, &columns, &[x, y, witness]))
                    };
                    if !body(&current) {
                        continue;
                    }
                    let expected = !proofs.iter().any(|proof| body(proof));
                    let state =
                        MatchProofState::new(current.clone(), proofs.clone(), columns.clone())
                            .map(|state| state.with_relevant_variables(&[0, 1]));
                    assert_eq!(
                        uncovered_state(state, &[x, y]),
                        expected,
                        "private_first={private_first}, pattern={pattern}, binding=({x},{y})"
                    );
                }
            }
        }
    }
}

#[test]
fn raw_parent_snapshots_do_not_certify_a_join_created_by_equality() {
    let current = vec![unary([0]), unary([0])];
    let proofs = vec![vec![unary([0]), unary([1])]];
    let state = MatchProofState::new(current, proofs, vec![vec![0], vec![0]]).unwrap();
    assert!(!state.is_covered());
    assert_eq!(keys(&state.uncovered_keys(0).unwrap()), BTreeSet::from([0]));
}

#[test]
fn nullary_facts_must_be_covered_by_the_same_certificate() {
    let current = vec![nullary(true), unary([1])];
    let proofs = vec![
        vec![nullary(false), unary([1])],
        vec![nullary(true), unary([2])],
    ];
    let state = MatchProofState::new(current, proofs, vec![vec![], vec![0]]).unwrap();
    assert_eq!(keys(&state.uncovered_keys(0).unwrap()), BTreeSet::from([1]));
    let impossible = MatchProofState::new(
        vec![nullary(false), unary([1])],
        vec![vec![nullary(true), unary([1])]],
        vec![vec![], vec![0]],
    )
    .unwrap();
    assert!(impossible.is_covered());
}

#[test]
fn all_small_two_parent_products_match_exact_set_difference() {
    let columns = vec![vec![0], vec![1]];
    for mut pattern in 0..625 {
        let mut current = vec![Table::new(1), Table::new(1)];
        let mut proofs = vec![vec![Table::new(1), Table::new(1)]; 2];
        for atom in 0..2 {
            for value in 0..2 {
                let state = pattern % 5;
                pattern /= 5;
                if state == 0 {
                    continue;
                }
                current[atom].insert(&[value]);
                let membership = state - 1;
                for (proof, relations) in proofs.iter_mut().enumerate() {
                    if membership & (1 << proof) != 0 {
                        relations[atom].insert(&[value]);
                    }
                }
            }
        }
        for x in 0..2 {
            for y in 0..2 {
                let binding = [x, y];
                if !body_holds(&current, &columns, &binding) {
                    continue;
                }
                let expected = !proofs
                    .iter()
                    .any(|proof| body_holds(proof, &columns, &binding));
                assert_eq!(uncovered(&current, &proofs, &columns, &binding), expected);
            }
        }
    }
}

fn random_word(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state >> 32
}

#[test]
fn three_atom_shared_variable_joins_match_independent_certificates() {
    let columns = vec![vec![0, 1], vec![1, 2], vec![2, 3]];
    let mut random = 17;
    for _ in 0..1024 {
        let mut current = vec![Table::new(2); 3];
        let mut proofs = vec![vec![Table::new(2); 3]; 3];
        for atom in 0..3 {
            for x in 0..2 {
                for y in 0..2 {
                    let mask = random_word(&mut random) & 15;
                    if mask & 8 == 0 {
                        continue;
                    }
                    current[atom].insert(&[x, y]);
                    for (proof, relations) in proofs.iter_mut().enumerate() {
                        if mask & (1 << proof) != 0 {
                            relations[atom].insert(&[x, y]);
                        }
                    }
                }
            }
        }
        for assignment in 0..16 {
            let binding = std::array::from_fn::<_, 4, _>(|column| (assignment >> column) & 1);
            if !body_holds(&current, &columns, &binding) {
                continue;
            }
            let expected = !proofs
                .iter()
                .any(|proof| body_holds(proof, &columns, &binding));
            assert_eq!(uncovered(&current, &proofs, &columns, &binding), expected);
        }
    }
}

#[test]
fn table_set_operations_preserve_all_arities_and_shared_snapshots() {
    for arity in 0..=10 {
        let universe: Vec<Vec<u32>> = (0..12)
            .map(|row| {
                (0..arity)
                    .map(|column| {
                        if column == 0 {
                            row % 3
                        } else if column + 1 == arity {
                            row / 3
                        } else {
                            u32::try_from(column).unwrap()
                        }
                    })
                    .collect()
            })
            .collect();
        let left = rows(arity, universe.iter().step_by(2).cloned());
        let right = rows(arity, universe.iter().step_by(3).cloned());
        let left_rows = tuples(&left);
        let right_rows = tuples(&right);
        assert_eq!(
            tuples(&left.union(&right)),
            left_rows.union(&right_rows).cloned().collect()
        );
        assert_eq!(
            tuples(&left.intersection(&right)),
            left_rows.intersection(&right_rows).cloned().collect()
        );
        assert_eq!(
            tuples(&left.difference(&right)),
            left_rows.difference(&right_rows).cloned().collect()
        );
        assert_eq!(left.is_subset(&right), left_rows.is_subset(&right_rows));
        assert!(Table::new(arity).is_subset(&left));
        assert!(left.is_subset(&left));
        assert!(left.intersection(&left).shares_storage_with(&left));
        assert!(left.difference(&left).is_empty());
        assert!(left
            .difference(&Table::new(arity))
            .shares_storage_with(&left));
        let mut changed = left.clone();
        let first = left_rows.iter().next().unwrap();
        assert!(changed.remove(first));
        assert_eq!(tuples(&left), left_rows);
        assert!(!changed.contains(first));
        let mut suffix = left.clone();
        for &column in first {
            suffix = suffix.first_column(column).unwrap();
        }
        assert_eq!(suffix.arity(), 0);
        assert!(suffix.contains(&[]));
    }
}

#[test]
fn disjoint_suffixes_do_not_leave_nonempty_long_table_prefixes() {
    for arity in 2..=10 {
        let mut left = vec![0; arity];
        let mut right = vec![0; arity];
        left[arity - 1] = 1;
        right[arity - 1] = 2;
        let left = rows(arity, [left]);
        let right = rows(arity, [right]);
        assert!(left.intersection(&right).is_empty());
        assert_eq!(left.intersection(&right).iter().count(), 0);
        assert!(!left.is_subset(&right));
        assert_eq!(tuples(&left.difference(&right)), tuples(&left));
    }
}
