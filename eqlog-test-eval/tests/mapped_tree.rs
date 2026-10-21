use eqlog_runtime::wbtree::map::WBTreeMap;
use eqlog_runtime::wbtree::mapping::MonotoneMap;
use eqlog_runtime::PrefixTree2;
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

#[test]
fn monotone_maps_compress_offsets_without_filling_gaps() {
    let mut relation = PrefixTree2::new();
    for key in 0..128 {
        relation.insert([key, key + 150]);
    }
    let mapping = MonotoneMap::new(&relation).unwrap();
    assert_eq!(mapping.run_count(), 1);
    for key in 0..128 {
        assert_eq!(mapping.apply(key), Some(key + 150));
        assert_eq!(mapping.preimage(key + 150), Some(key));
    }
    assert_eq!(mapping.apply(128), None);
    assert_eq!(mapping.preimage(149), None);
    assert_eq!(mapping.preimage(278), None);

    relation.insert([200, 300]);
    relation.insert([201, 301]);
    relation.insert([u32::MAX - 1, u32::MAX - 2]);
    relation.insert([u32::MAX, u32::MAX - 1]);
    let mapping = MonotoneMap::new(&relation).unwrap();
    assert_eq!(mapping.run_count(), 3);
    for [source, target] in relation.iter() {
        assert_eq!(mapping.apply(source), Some(target));
        assert_eq!(mapping.preimage(target), Some(source));
    }
    for key in [128, 199, 202, u32::MAX - 2] {
        assert_eq!(mapping.apply(key), None);
    }
    for key in [278, 299, 302, u32::MAX] {
        assert_eq!(mapping.preimage(key), None);
    }
}

#[test]
fn monotone_maps_reject_collisions_reordering_and_multiple_images() {
    for rows in [[[0, 2], [1, 2]], [[0, 2], [1, 1]], [[0, 1], [0, 2]]] {
        let mut relation = PrefixTree2::new();
        for row in rows {
            relation.insert(row);
        }
        assert!(MonotoneMap::new(&relation).is_none());
    }
}

struct CountClones(Rc<Cell<usize>>);

impl Clone for CountClones {
    fn clone(&self) -> Self {
        self.0.set(self.0.get() + 1);
        Self(self.0.clone())
    }
}

#[test]
fn offset_mapping_and_lookup_share_values_until_mutation() {
    let clones = Rc::new(Cell::new(0));
    let mut base = WBTreeMap::new();
    let mut mapping = PrefixTree2::new();
    for key in 0..1024 {
        base.insert(key, CountClones(clones.clone()));
        mapping.insert([key, key + 2048]);
    }
    clones.set(0);
    let mut mapped = base.mapped(mapping);
    for key in 2048..3072 {
        assert!(mapped.get(&key).is_some());
    }
    assert_eq!(mapped.iter().count(), 1024);
    assert_eq!(clones.get(), 0);
    mapped.remove(&2048);
    assert!(base.get(&0).is_some());
    assert!(mapped.get(&2048).is_none());
}

#[test]
fn entry_mappings_defer_values_and_cache_them_across_snapshots() {
    let clones = Rc::new(Cell::new(0));
    let calls = Rc::new(Cell::new(0));
    let mut base = WBTreeMap::new();
    let mut relation = PrefixTree2::new();
    for key in 0..1024 {
        base.insert(key, CountClones(clones.clone()));
        relation.insert([key, key + 2048]);
    }
    clones.set(0);
    let transform_calls = calls.clone();
    let mapped = base.mapped_entries(Some(MonotoneMap::new(&relation).unwrap()), move |value| {
        transform_calls.set(transform_calls.get() + 1);
        Some(value.clone())
    });
    let snapshot = mapped.clone();
    assert_eq!(clones.get(), 0);
    assert_eq!(calls.get(), 0);
    assert!(mapped.get(&0).is_none());
    assert_eq!(calls.get(), 0);

    let value = mapped.get(&2700).unwrap();
    assert_eq!(calls.get(), 1);
    assert_eq!(clones.get(), 1);
    assert!(std::ptr::eq(value, mapped.get(&2700).unwrap()));
    assert!(std::ptr::eq(value, snapshot.get(&2700).unwrap()));
    assert_eq!(calls.get(), 1);

    let mut iter = mapped.iter();
    assert_eq!(calls.get(), 1);
    assert_eq!(iter.next().unwrap().0, 2048);
    assert_eq!(calls.get(), 2);
    assert_eq!(mapped.iter().count(), 1024);
    assert_eq!(snapshot.iter().count(), 1024);
    assert_eq!(calls.get(), 1024);
    assert_eq!(clones.get(), 1024);
}

#[test]
fn materialized_pivots_prove_nonempty_without_forcing_mapped_children() {
    let mut source = WBTreeMap::new();
    for key in 0..128 {
        source.insert(key, key);
    }
    let calls = Rc::new(Cell::new(0));
    let transform_calls = calls.clone();
    let mut mapped = source.mapped_entries(None, move |value| {
        transform_calls.set(transform_calls.get() + 1);
        Some(value + 1)
    });
    let snapshot = mapped.clone();
    mapped.insert(256, 257);
    calls.set(0);

    assert!(!mapped.is_empty());
    assert_eq!(calls.get(), 0);
    assert_eq!(mapped.iter().count(), 129);
    assert_eq!(snapshot.iter().count(), 128);
    assert!(snapshot.get(&256).is_none());
    assert_eq!(mapped.get(&256), Some(&257));

    let mut filtered = source.mapped_entries(None, |_| None);
    assert!(filtered.is_empty());
    filtered.insert(256, 257);
    assert!(!filtered.is_empty());
    filtered.remove(&256);
    assert!(filtered.is_empty());
}

#[test]
fn layered_entry_mappings_compose_keys_values_and_filters() {
    let mut base = WBTreeMap::new();
    let mut first = PrefixTree2::new();
    let mut second = PrefixTree2::new();
    let mut expected = BTreeMap::new();
    for key in 0..128 {
        base.insert(key, key);
        first.insert([key, key + 100]);
        if key % 4 != 0 {
            second.insert([key + 100, key * 2 + 1000]);
            if key % 3 != 0 && (key + 10) % 5 != 0 {
                expected.insert(key * 2 + 1000, (key + 10) * 10 + 1);
            }
        }
    }
    let mapped = base
        .mapped_entries(Some(MonotoneMap::new(&first).unwrap()), |value| {
            (value % 3 != 0).then_some(value + 10)
        })
        .mapped_entries(Some(MonotoneMap::new(&second).unwrap()), |value| {
            (value % 5 != 0).then_some(value * 10)
        })
        .mapped_entries(None, |value| Some(value + 1));
    assert_eq!(mapped.len(), expected.len());
    assert_eq!(
        mapped
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<BTreeMap<_, _>>(),
        expected,
    );
    for key in 1000..1256 {
        assert_eq!(mapped.get(&key), expected.get(&key));
    }

    let calls = Rc::new(Cell::new(0));
    let transform_calls = calls.clone();
    let empty = base.mapped_entries(None, move |_| {
        transform_calls.set(transform_calls.get() + 1);
        None
    });
    assert_eq!(calls.get(), 0);
    assert!(empty.get(&64).is_none());
    assert!(empty.get(&64).is_none());
    assert_eq!(calls.get(), 1);
    assert!(empty.is_empty());
    assert_eq!(empty.len(), 0);
    assert_eq!(empty.iter().count(), 0);
    assert_eq!(calls.get(), 128);
}

#[test]
fn entry_mapping_set_operations_distinguish_value_transformations() {
    let mut base = WBTreeMap::new();
    let mut relation = PrefixTree2::new();
    for key in 0..128 {
        base.insert(key, key);
        relation.insert([key, key + 256]);
    }
    let mapping = MonotoneMap::new(&relation).unwrap();
    let left = base.mapped_entries(Some(mapping.clone()), |value| Some(value + 1));
    let right = base.mapped_entries(Some(mapping), |value| Some(value + 2));
    assert_eq!(
        left.difference_entries(&right)
            .map(|(key, &left, right)| (key, left, right.copied()))
            .collect::<Vec<_>>(),
        (0..128)
            .map(|key| (key + 256, key + 1, Some(key + 2)))
            .collect::<Vec<_>>(),
    );
    let union = left.union(&right, |_, left, right| left + right);
    let difference = left.difference(&right, |_, left, right| Some(right - left));
    assert_eq!(
        union
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<Vec<_>>(),
        (0..128)
            .map(|key| (key + 256, key * 2 + 3))
            .collect::<Vec<_>>(),
    );
    assert_eq!(
        difference
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<Vec<_>>(),
        (0..128).map(|key| (key + 256, 1)).collect::<Vec<_>>(),
    );
    assert_eq!(left.difference_entries(&left.clone()).count(), 0);
}

#[test]
fn entry_mapping_mutations_preserve_transformed_snapshots() {
    let mut base = WBTreeMap::new();
    let mut relation = PrefixTree2::new();
    for key in 0..128 {
        base.insert(key, key);
        relation.insert([key, key + 256]);
    }
    let mut mapped = base.mapped_entries(Some(MonotoneMap::new(&relation).unwrap()), |value| {
        (value % 2 == 0).then_some(value + 100)
    });
    let snapshot = mapped.clone();
    let mut expected: BTreeMap<_, _> = (0..128)
        .filter(|key| key % 2 == 0)
        .map(|key| (key + 256, key + 100))
        .collect();
    for (key, value) in mapped.iter_mut() {
        *value *= 2;
        *expected.get_mut(&key).unwrap() *= 2;
    }
    assert_eq!(mapped.insert(257, 9), expected.insert(257, 9));
    assert_eq!(mapped.insert(258, 7), expected.insert(258, 7));
    assert_eq!(mapped.remove(&256), expected.remove(&256));
    assert_eq!(mapped.remove(&259), expected.remove(&259));
    *mapped.get_mut(&260).unwrap() = 11;
    *expected.get_mut(&260).unwrap() = 11;
    assert_eq!(
        mapped
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<BTreeMap<_, _>>(),
        expected,
    );
    assert_eq!(
        snapshot
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<Vec<_>>(),
        (0..128)
            .filter(|key| key % 2 == 0)
            .map(|key| (key + 256, key + 100))
            .collect::<Vec<_>>(),
    );
    assert_eq!(base.get(&0), Some(&0));
    assert_eq!(base.get(&2), Some(&2));
}

#[test]
fn entry_mapping_edits_and_set_operations_agree_with_btree_maps() {
    for seed in 0..16u64 {
        let mut state = seed;
        let mut actual = WBTreeMap::new();
        let mut expected = BTreeMap::new();
        for step in 0..96 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let key = (state >> 32) as u32 % 64;
            let snapshot = actual.clone();
            let previous = expected.clone();
            match step % 6 {
                0 => assert_eq!(actual.insert(key, step), expected.insert(key, step)),
                1 => {
                    let mut relation = PrefixTree2::new();
                    for source in 0..64 {
                        if (state >> source) & 1 == 0 {
                            relation.insert([source, source + 1]);
                        }
                    }
                    actual = actual
                        .mapped_entries(Some(MonotoneMap::new(&relation).unwrap()), |value| {
                            (value % 5 != 0).then_some(value + 2)
                        });
                    expected = expected
                        .into_iter()
                        .filter_map(|(key, value)| {
                            (value % 5 != 0 && relation.get(key).is_some())
                                .then_some((key + 1, value + 2))
                        })
                        .collect();
                }
                2 | 3 => {
                    let mut other = WBTreeMap::new();
                    let mut other_rows = BTreeMap::new();
                    for offset in 0..8 {
                        other.insert(key + offset, offset);
                        other_rows.insert(key + offset, offset + 10);
                    }
                    let other = other.mapped_entries(None, |value| Some(value + 10));
                    if step % 6 == 2 {
                        actual = actual.union(&other, |_, left, right| left + right);
                        for (key, value) in other_rows {
                            *expected.entry(key).or_default() += value;
                        }
                    } else {
                        actual = actual.difference(&other, |_, left, right| {
                            ((left + right) % 3 != 0).then_some(left + right)
                        });
                        expected = expected
                            .into_iter()
                            .filter_map(|(key, value)| match other_rows.get(&key) {
                                Some(other) => {
                                    ((value + other) % 3 != 0).then_some((key, value + other))
                                }
                                None => Some((key, value)),
                            })
                            .collect();
                    }
                }
                4 => assert_eq!(actual.remove(&key), expected.remove(&key)),
                5 => {
                    for (key, value) in actual.iter_mut() {
                        *value += 1;
                        *expected.get_mut(&key).unwrap() += 1;
                    }
                }
                _ => unreachable!(),
            }
            assert_eq!(
                actual
                    .iter()
                    .map(|(key, &value)| (key, value))
                    .collect::<BTreeMap<_, _>>(),
                expected,
                "seed {seed}, step {step}",
            );
            assert_eq!(
                snapshot
                    .iter()
                    .map(|(key, &value)| (key, value))
                    .collect::<BTreeMap<_, _>>(),
                previous,
                "snapshot for seed {seed}, step {step}",
            );
            assert_eq!(actual.len(), expected.len());
            for key in 0..72 {
                assert_eq!(
                    actual.get(&key),
                    expected.get(&key),
                    "seed {seed}, step {step}, key {key}"
                );
            }
        }
    }
}

#[test]
fn fragmented_mappings_compare_by_snapshot_without_cancelling_distinct_images() {
    let mut base = WBTreeMap::new();
    let mut mapping = PrefixTree2::new();
    for key in 0..4096 {
        base.insert(key, ());
        mapping.insert([key, key * 2]);
    }
    let first = base.mapped(mapping.clone());
    let same = base.mapped(mapping.clone());
    assert_eq!(first.difference_entries(&same).count(), 0);
    mapping.remove([4095, 8190]);
    mapping.insert([4095, u32::MAX]);
    let second = base.mapped(mapping);
    assert_eq!(
        first
            .difference_entries(&second)
            .filter_map(|(key, (), right)| right.is_none().then_some(key))
            .collect::<Vec<_>>(),
        [8190],
    );
    assert_eq!(second.get(&u32::MAX), Some(&()));
}

fn mapped_tree() -> WBTreeMap<u32> {
    let mut base = WBTreeMap::new();
    let mut mapping = PrefixTree2::new();
    for key in 0..4 {
        base.insert(key, key);
        if key % 2 == 0 {
            mapping.insert([key, key + 10]);
        }
    }
    base.mapped(mapping)
}

#[test]
fn mapped_lookup_skips_filtered_search_pivots() {
    let mut mapped = mapped_tree();
    assert_eq!(mapped.get(&10), Some(&0));
    assert_eq!(mapped.get(&12), Some(&2));
    assert_eq!(mapped.len(), 2);
    *mapped.get_mut(&12).unwrap() = 20;
    assert_eq!(mapped.get(&12), Some(&20));
}

#[test]
fn mapped_mutations_use_visible_keys() {
    let mut removed = mapped_tree();
    assert_eq!(removed.remove(&10), Some(0));
    assert_eq!(removed.remove(&12), Some(2));
    assert!(removed.is_empty());

    let mut mapped = mapped_tree();
    let snapshot = mapped.clone();
    assert_eq!(mapped.insert(12, 20), Some(2));
    assert_eq!(mapped.insert(11, 10), None);
    assert_eq!(mapped.remove(&10), Some(0));
    assert_eq!(
        mapped.iter().map(|(k, &v)| (k, v)).collect::<Vec<_>>(),
        vec![(11, 10), (12, 20)]
    );
    assert_eq!(
        snapshot.iter().map(|(k, &v)| (k, v)).collect::<Vec<_>>(),
        vec![(10, 0), (12, 2)]
    );
}

#[test]
fn mapped_set_operations_use_visible_keys() {
    let mapped = mapped_tree();
    let mut other = WBTreeMap::new();
    other.insert(12, 20);
    other.insert(13, 30);
    let union = mapped.union(&other, |_, left, right| left + right);
    assert_eq!(
        union.iter().map(|(k, &v)| (k, v)).collect::<Vec<_>>(),
        vec![(10, 0), (12, 22), (13, 30)]
    );
    let difference = mapped.difference(&other, |_, _, _| None);
    assert_eq!(
        difference.iter().map(|(k, &v)| (k, v)).collect::<Vec<_>>(),
        vec![(10, 0)]
    );
    let difference = other.difference(&mapped, |_, _, _| None);
    assert_eq!(
        difference.iter().map(|(k, &v)| (k, v)).collect::<Vec<_>>(),
        vec![(13, 30)]
    );
    assert!(mapped.difference(&mapped, |_, _, _| None).is_empty());
    let empty = mapped.mapped(PrefixTree2::new());
    assert!(empty.is_empty());
    assert_eq!(empty.len(), 0);
}

#[test]
fn mapped_edits_agree_with_a_btree_map() {
    for seed in 0..64u64 {
        let mut state = seed;
        let mut actual = WBTreeMap::new();
        let mut expected = BTreeMap::new();
        for step in 0..100 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let key = (state >> 32) as u32 % 32;
            match step % 5 {
                0 | 1 => assert_eq!(actual.insert(key, step), expected.insert(key, step)),
                2 => {
                    let mut mapping = PrefixTree2::new();
                    for key in 0..32 {
                        if (state >> key) & 1 == 0 {
                            mapping.insert([key, key + 1]);
                        }
                    }
                    actual = actual.mapped(mapping.clone());
                    expected = expected
                        .into_iter()
                        .filter_map(|(key, value)| {
                            mapping
                                .get(key)
                                .map(|row| (row.iter().next().unwrap()[0], value))
                        })
                        .collect();
                }
                3 => assert_eq!(actual.remove(&key), expected.remove(&key)),
                4 => {
                    let snapshot = actual.clone();
                    for (key, value) in actual.iter_mut() {
                        *value += 1;
                        *expected.get_mut(&key).unwrap() += 1;
                    }
                    for (key, value) in snapshot.iter() {
                        assert_eq!(Some(*value + 1), expected.get(&key).copied());
                    }
                }
                _ => unreachable!(),
            }
            assert_eq!(actual.len(), expected.len(), "seed {seed}, step {step}");
            assert_eq!(actual.is_empty(), expected.is_empty());
            assert_eq!(
                actual.iter().map(|(k, &v)| (k, v)).collect::<Vec<_>>(),
                expected.iter().map(|(&k, &v)| (k, v)).collect::<Vec<_>>()
            );
            for key in 0..34 {
                assert_eq!(
                    actual.get(&key),
                    expected.get(&key),
                    "seed {seed}, step {step}, key {key}"
                );
            }
        }
    }
}

#[test]
fn sparse_mapped_edits_leave_unvisited_values_lazy() {
    let calls = Rc::new(Cell::new(0));
    let mut source = WBTreeMap::new();
    let mut relation = PrefixTree2::new();
    for key in 0..4096 {
        source.insert(key, key);
        relation.insert([key, key + 8192]);
    }
    let counted_calls = calls.clone();
    let mut edited =
        source.mapped_entries(Some(MonotoneMap::new(&relation).unwrap()), move |value| {
            counted_calls.set(counted_calls.get() + 1);
            Some(value + 100)
        });
    let original = edited.clone();
    *edited.get_mut(&10240).unwrap() += 7;
    assert_eq!(edited.remove(&8193), Some(101));
    assert_eq!(edited.insert(13000, 17), None);
    let mut delta = WBTreeMap::new();
    delta.insert(8194, 3);
    edited = edited.union(&delta, |_, left, right| left + right);
    delta.clear();
    delta.insert(8195, 5);
    edited = edited.difference(&delta, |_, _, _| None);
    assert!(calls.get() < 128, "a sparse edit forced unrelated values");
    assert_eq!(edited.get(&10240), Some(&2155));
    assert_eq!(edited.get(&8194), Some(&105));
    assert_eq!(edited.get(&8193), None);
    assert_eq!(edited.get(&8195), None);
    assert_eq!(edited.get(&13000), Some(&17));
    assert_eq!(original.get(&10240), Some(&2148));
    assert_eq!(original.get(&8193), Some(&101));
    assert_eq!(original.get(&8195), Some(&103));
    assert_eq!(original.get(&13000), None);
    assert_eq!(edited.len(), 4095);
    assert_eq!(original.len(), 4096);
    assert_eq!(source.len(), 4096);
}

#[test]
fn repeated_mapping_and_sparse_edits_keep_cache_coordinates_stable() {
    for seed in 0..12u64 {
        let mut state = seed;
        let mut actual = WBTreeMap::new();
        let mut expected = BTreeMap::new();
        for key in 0..256 {
            actual.insert(key, key);
            expected.insert(key, key);
        }
        for step in 0..512 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let key = (state >> 32) as u32 % 768;
            let snapshot = actual.clone();
            let previous = expected.clone();
            match step % 5 {
                0 => {
                    let mut relation = PrefixTree2::new();
                    for &source in expected.keys() {
                        if source % 5 != 0 {
                            relation.insert([source, source + 1]);
                        }
                    }
                    actual = actual
                        .mapped_entries(Some(MonotoneMap::new(&relation).unwrap()), |value| {
                            (value % 7 != 0).then_some(value + 3)
                        });
                    expected = expected
                        .into_iter()
                        .filter_map(|(key, value)| {
                            (key % 5 != 0 && value % 7 != 0).then_some((key + 1, value + 3))
                        })
                        .collect();
                }
                1 => assert_eq!(actual.insert(key, step), expected.insert(key, step)),
                2 => {
                    if let Some(value) = actual.get_mut(&key) {
                        *value += 2;
                    }
                    if let Some(value) = expected.get_mut(&key) {
                        *value += 2;
                    }
                }
                3 => assert_eq!(actual.remove(&key), expected.remove(&key)),
                4 => {
                    let mut right = WBTreeMap::new();
                    for offset in 0..7 {
                        right.insert(key + offset, offset);
                        *expected.entry(key + offset).or_default() += offset;
                    }
                    actual = actual.union(&right, |_, left, right| left + right);
                }
                _ => unreachable!(),
            }
            assert_eq!(
                actual
                    .iter()
                    .map(|(key, &value)| (key, value))
                    .collect::<BTreeMap<_, _>>(),
                expected,
                "seed {seed}, step {step}"
            );
            assert_eq!(
                snapshot
                    .iter()
                    .map(|(key, &value)| (key, value))
                    .collect::<BTreeMap<_, _>>(),
                previous,
                "snapshot for seed {seed}, step {step}"
            );
            assert_eq!(actual.len(), expected.len());
            for key in 0..768 {
                assert_eq!(
                    actual.get(&key),
                    expected.get(&key),
                    "seed {seed}, step {step}, key {key}"
                );
            }
        }
    }
}

#[test]
fn sparse_difference_visits_only_requested_mapped_values() {
    let mut source = WBTreeMap::new();
    let mut relation = PrefixTree2::new();
    for key in 0..128 {
        source.insert(key, key);
        if key != 127 {
            relation.insert([key, key + 1000]);
        }
    }
    let applied = Rc::new(Cell::new(0));
    let counter = applied.clone();
    let target = source.mapped_entries(MonotoneMap::new(&relation), move |value| {
        counter.set(counter.get() + 1);
        (value % 5 != 0).then_some(value * 10)
    });
    let mut candidate = WBTreeMap::new();
    for key in [1124, 1125, 1127, 2000] {
        candidate.insert(key, key);
    }
    let mut actual = Vec::new();
    assert!(
        candidate.all_difference_entries(&target, |key, left, right| {
            actual.push((key, *left, right.copied()));
            true
        })
    );
    assert_eq!(
        actual,
        [
            (1124, 1124, Some(1240)),
            (1125, 1125, None),
            (1127, 1127, None),
            (2000, 2000, None),
        ]
    );
    assert_eq!(applied.get(), 2);

    let mut candidate_mapping = PrefixTree2::new();
    for key in [1124, 1125, 1127, 2000] {
        candidate_mapping.insert([key, key]);
    }
    let candidate = candidate.mapped(candidate_mapping);
    let mut visited = 0;
    assert!(!candidate.all_difference_entries(&target, |_, _, _| {
        visited += 1;
        false
    }));
    assert_eq!(visited, 1);
    assert!(target.all_difference_entries(&target.clone(), |_, _, _| {
        panic!("identical snapshots need no value comparison")
    }));
}

#[test]
fn deep_mapping_chains_remain_editable() {
    let mut relation = PrefixTree2::new();
    relation.insert([0, 0]);
    relation.insert([u32::MAX, u32::MAX]);
    let mapping = MonotoneMap::new(&relation).unwrap();
    for operation in 0..5 {
        let mut source = WBTreeMap::new();
        source.insert(0, 7);
        source.insert(u32::MAX, 11);
        for _ in 0..10_000 {
            source = source.mapped_keys(mapping.clone());
        }
        let snapshot = source.clone();
        match operation {
            0 => {
                assert_eq!(source.insert(1, 13), None);
                assert_eq!(source.get(&1), Some(&13));
            }
            1 => {
                assert_eq!(source.remove(&0), Some(7));
                assert_eq!(source.get(&0), None);
            }
            2 => {
                *source.get_mut(&u32::MAX).unwrap() = 17;
                assert_eq!(source.get(&u32::MAX), Some(&17));
            }
            3 => {
                let mut other = WBTreeMap::new();
                other.insert(u32::MAX, 1);
                source = source.difference(&other, |_, _, _| None);
                assert_eq!(source.get(&u32::MAX), None);
            }
            4 => {
                let mut other = WBTreeMap::new();
                other.insert(u32::MAX, 1);
                source = source.union(&other, |_, left, right| left + right);
                assert_eq!(source.get(&u32::MAX), Some(&12));
            }
            _ => unreachable!(),
        }
        assert_eq!(snapshot.get(&0), Some(&7));
        assert_eq!(snapshot.get(&u32::MAX), Some(&11));
    }
}

#[test]
fn deep_value_mapping_chains_remain_editable() {
    let mut source = WBTreeMap::new();
    source.insert(0, 7);
    source.insert(1, 9);
    source.insert(u32::MAX, 11);
    for _ in 0..4_000 {
        source = source.mapped_entries(None, |value| Some(value + 1));
    }
    let snapshot = source.clone();
    *source.get_mut(&0).unwrap() += 1;
    assert_eq!(source.remove(&u32::MAX), Some(4011));
    assert_eq!(source.get(&0), Some(&4008));
    assert_eq!(snapshot.get(&0), Some(&4007));
    assert_eq!(snapshot.get(&u32::MAX), Some(&4011));
    drop(snapshot);
    assert_eq!(source.get(&1), Some(&4009));
}

#[test]
fn deep_prefix_views_drop_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut rows = PrefixTree2::new();
            rows.insert([0, u32::MAX]);
            let expected = rows.clone();
            let mut relation = PrefixTree2::new();
            relation.insert([0, 0]);
            let mapping = MonotoneMap::new(&relation).unwrap();
            for _ in 0..10_000 {
                rows.map = rows.map.mapped_keys(mapping.clone());
            }
            assert_eq!(
                rows.intersection(&expected).iter().collect::<Vec<_>>(),
                [[0, u32::MAX]]
            );
            assert_eq!(
                expected.intersection(&rows).iter().collect::<Vec<_>>(),
                [[0, u32::MAX]]
            );
            let alias = rows.clone();
            drop(rows);
            assert!(alias.contains([0, u32::MAX]));
            drop(alias);

            let mut identity = PrefixTree2::new();
            identity.insert([0, 0]);
            for _ in 0..4_000 {
                let mapping = MonotoneMap::new(&identity).unwrap();
                identity.map = identity.map.mapped_keys(mapping);
            }
            assert_eq!(identity.iter().collect::<Vec<_>>(), [[0, 0]]);
            drop(identity);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn deeply_filtered_pivots_survive_boundary_edits() {
    let mut source = WBTreeMap::new();
    let mut expected = BTreeMap::new();
    for offset in 0..2048 {
        for key in [offset, u32::MAX - offset] {
            source.insert(key, offset);
            if offset % 127 == 0 {
                expected.insert(key, offset);
            }
        }
    }
    for _ in 0..64 {
        source = source.mapped_entries(None, |value| (value % 127 == 0).then_some(*value));
    }
    let snapshot = source.clone();
    for key in [0, 1, 126, 127, u32::MAX - 127, u32::MAX - 1, u32::MAX] {
        assert_eq!(source.remove(&key), expected.remove(&key));
        assert_eq!(source.insert(key, 17), expected.insert(key, 17));
        *source.get_mut(&key).unwrap() += 1;
        *expected.get_mut(&key).unwrap() += 1;
    }
    assert_eq!(
        source
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<BTreeMap<_, _>>(),
        expected
    );
    assert!(snapshot.iter().all(|(_, value)| value % 127 == 0));
    assert_eq!(snapshot.len(), 34);
}

#[test]
fn deep_mapping_chains_propagate_an_empty_inner_view() {
    let mut source = WBTreeMap::new();
    source.insert(0, 7);
    source = source.mapped_entries(None, |_| None);
    let mut relation = PrefixTree2::new();
    relation.insert([0, 0]);
    let mapping = MonotoneMap::new(&relation).unwrap();
    for _ in 0..10_000 {
        source = source.mapped_keys(mapping.clone());
    }
    let snapshot = source.clone();
    assert_eq!(source.get_mut(&0), None);
    assert_eq!(source.insert(u32::MAX, 11), None);
    assert_eq!(source.get(&u32::MAX), Some(&11));
    assert_eq!(source.len(), 1);
    assert!(snapshot.is_empty());
}

#[test]
fn lookups_keep_value_coordinates_across_key_only_layers() {
    let mut source = WBTreeMap::new();
    let mut first = PrefixTree2::new();
    let mut middle = PrefixTree2::new();
    let mut last = PrefixTree2::new();
    for key in 0..32 {
        source.insert(key, key);
        first.insert([key, key + 100]);
        if key % 3 != 0 {
            middle.insert([key + 100, key + 1000]);
        }
        last.insert([key + 1000, key + 2000]);
    }
    let mapped = source
        .mapped_entries(MonotoneMap::new(&first), |value| Some(value + 10))
        .mapped_keys(MonotoneMap::new(&middle).unwrap())
        .mapped_entries(None, |value| (value % 5 != 0).then_some(value * 2))
        .mapped_keys(MonotoneMap::new(&last).unwrap());
    for key in 0..32 {
        let expected = (key % 3 != 0 && (key + 10) % 5 != 0).then_some((key + 10) * 2);
        assert_eq!(mapped.get(&(key + 2000)), expected.as_ref());
        assert_eq!(mapped.get(&key), None);
    }
    let mut edited = mapped.clone();
    *edited.get_mut(&2001).unwrap() = 777;
    edited.remove(&2002);
    drop(mapped);
    assert_eq!(edited.get(&2001), Some(&777));
    assert_eq!(edited.get(&2002), None);
    assert_eq!(edited.get(&2004), Some(&28));
    assert_eq!(source.get(&1), Some(&1));
}

#[test]
fn cache_origins_survive_offset_views_around_edited_subtrees() {
    let mut source = WBTreeMap::new();
    let mut first = PrefixTree2::new();
    let mut second = PrefixTree2::new();
    let mut third = PrefixTree2::new();
    let mut fourth = PrefixTree2::new();
    for key in 0..128 {
        first.insert([1000 + key, 3000 + key]);
        second.insert([2999 + key, 6999 + key]);
        third.insert([6999 + key, 199 + key]);
        fourth.insert([199 + key, 499 + key]);
        if key % 2 == 0 {
            source.insert(1000 + key, key);
        }
    }
    let mut edited = source.mapped_entries(MonotoneMap::new(&first), |value| Some(value + 1));
    let snapshot = edited.clone();
    *edited.get_mut(&3050).unwrap() = 900;
    edited.insert(2999, 88);
    edited.remove(&3100);
    let expected: BTreeMap<_, _> = edited
        .iter()
        .filter_map(|(key, value)| (value % 3 != 0).then_some((key - 2500, value + 9)))
        .collect();
    let mapped = edited
        .mapped_keys(MonotoneMap::new(&second).unwrap())
        .mapped_entries(None, |value| (value % 3 != 0).then_some(value + 2))
        .mapped_keys(MonotoneMap::new(&third).unwrap())
        .mapped_entries(MonotoneMap::new(&fourth), |value| Some(value + 7));
    drop(edited);
    assert_eq!(
        mapped
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<BTreeMap<_, _>>(),
        expected
    );
    for key in 0..700 {
        assert_eq!(mapped.get(&key), expected.get(&key));
    }
    assert_eq!(snapshot.get(&3050), Some(&51));
    assert_eq!(snapshot.get(&3100), Some(&101));
    assert_eq!(source.get(&1050), Some(&50));
}

#[test]
fn cache_origins_preserve_clipped_affine_domains_at_integer_limits() {
    let mut source = WBTreeMap::new();
    let mut clipped = PrefixTree2::new();
    let mut upper = PrefixTree2::new();
    for key in 0..128 {
        source.insert(key, key);
    }
    for key in 32..64 {
        clipped.insert([key, key + 200]);
        upper.insert([key + 200, u32::MAX - 63 + key]);
    }
    let mapped = source
        .mapped_entries(MonotoneMap::new(&clipped), |value| Some(value + 1))
        .mapped_entries(MonotoneMap::new(&upper), |value| Some(value + 2))
        .mapped_entries(None, |value| Some(value + 3));
    for offset in 0..64 {
        let key = u32::MAX - offset;
        assert_eq!(
            mapped.get(&key).copied(),
            (offset < 32).then_some(69 - offset)
        );
    }
    assert_eq!(mapped.len(), 32);
    assert_eq!(mapped.get(&0), None);
    assert_eq!(source.len(), 128);
}

#[test]
fn cache_origins_follow_shared_descriptors_over_proper_subtrees() {
    let mut source = WBTreeMap::new();
    source.insert(10, 10);
    source.insert(11, 11);
    let mut first = PrefixTree2::new();
    first.insert([10, 100]);
    first.insert([11, 101]);
    let mut edited = source.mapped_entries(MonotoneMap::new(&first), |value| Some(value + 1));
    let snapshot = edited.clone();
    assert_eq!(edited.remove(&100), Some(11));

    let mut middle = PrefixTree2::new();
    middle.insert([101, 501]);
    let mut last = PrefixTree2::new();
    last.insert([501, 1]);
    let mapped = edited
        .mapped_keys(MonotoneMap::new(&middle).unwrap())
        .mapped_keys(MonotoneMap::new(&last).unwrap())
        .mapped_entries(None, |value| Some(value * 3));
    drop(source);
    drop(snapshot);
    drop(edited);
    assert_eq!(mapped.get(&1), Some(&36));
    assert_eq!(mapped.get(&100), None);
    assert_eq!(
        mapped
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<Vec<_>>(),
        [(1, 36)]
    );
}

#[test]
fn cache_origins_compose_alternating_offsets_at_integer_limits() {
    let mut mapped = WBTreeMap::new();
    let mut expected = BTreeMap::new();
    for key in 0..256 {
        mapped.insert(key, key);
        expected.insert(key, key);
    }
    let original = mapped.clone();
    let mut source_base = 0;
    for layer in 0..32 {
        let target_base = if layer % 2 == 0 { u32::MAX - 255 } else { 17 };
        let mut relation = PrefixTree2::new();
        for key in 3..253 {
            relation.insert([source_base + key, target_base + key]);
        }
        let mapping = MonotoneMap::new(&relation).unwrap();
        mapped = if layer % 3 == 0 {
            mapped.mapped_keys(mapping)
        } else {
            mapped.mapped_entries(Some(mapping), |value| {
                (value % 67 != 0).then_some(value + 1)
            })
        };
        expected = expected
            .into_iter()
            .filter_map(|(key, value)| {
                let index = key - source_base;
                if !(3..253).contains(&index) || (layer % 3 != 0 && value % 67 == 0) {
                    return None;
                }
                let value = value + u32::from(layer % 3 != 0);
                Some((target_base + index, value))
            })
            .collect();
        source_base = target_base;
    }
    assert!(!expected.is_empty());
    for key in 0..300 {
        assert_eq!(mapped.get(&key), expected.get(&key));
    }
    assert_eq!(
        mapped
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<BTreeMap<_, _>>(),
        expected
    );
    assert_eq!(original.len(), 256);
    assert_eq!(original.get(&255), Some(&255));
}

#[test]
fn sparse_domains_seek_across_nested_maps_and_edited_siblings() {
    let mut source = WBTreeMap::new();
    for key in 0..8192 {
        source.insert(key, key);
    }
    for positions in [
        vec![0, 1, 17],
        vec![4096, 4113, 4129],
        vec![8174, 8190, 8191],
        vec![0, 4096, 8191],
        vec![8192, 9000],
    ] {
        let mut first = PrefixTree2::new();
        for key in 0..8192 {
            first.insert([key, key * 2 + 1]);
        }
        let mut second = PrefixTree2::new();
        let mut expected = BTreeMap::new();
        for (index, key) in positions.iter().copied().enumerate() {
            let target = u32::MAX - positions.len() as u32 + index as u32;
            second.insert([key * 2 + 1, target]);
            if key < 8192 && key % 3 != 1 {
                expected.insert(target, key + 10);
            }
        }
        let mut actual = source
            .mapped_keys(MonotoneMap::new(&first).unwrap())
            .mapped_entries(None, |value| (value % 3 != 1).then_some(value + 10))
            .mapped_keys(MonotoneMap::new(&second).unwrap());
        let snapshot = actual.clone();
        assert_eq!(actual.is_empty(), expected.is_empty());
        assert_eq!(
            actual
                .iter()
                .map(|(key, &value)| (key, value))
                .collect::<BTreeMap<_, _>>(),
            expected
        );
        actual.insert(0, 7);
        actual.insert(u32::MAX, 11);
        expected.insert(0, 7);
        expected.insert(u32::MAX, 11);
        assert_eq!(
            actual
                .iter()
                .map(|(key, &value)| (key, value))
                .collect::<BTreeMap<_, _>>(),
            expected
        );
        assert_eq!(snapshot.len(), expected.len() - 2);
    }
}

#[test]
fn sparse_domain_boundaries_preserve_zero_and_maximum_keys() {
    let mut source = WBTreeMap::new();
    for key in [0, 1, 17, 31, u32::MAX - 1, u32::MAX] {
        source.insert(key, key);
    }
    let mut first = PrefixTree2::new();
    first.insert([0, 0]);
    first.insert([u32::MAX, u32::MAX]);
    let actual = source.mapped_keys(MonotoneMap::new(&first).unwrap());
    assert_eq!(
        actual
            .iter()
            .map(|(key, &value)| (key, value))
            .collect::<Vec<_>>(),
        [(0, 0), (u32::MAX, u32::MAX)]
    );
    let mut second = PrefixTree2::new();
    second.insert([u32::MAX - 1, 0]);
    assert!(actual
        .mapped_keys(MonotoneMap::new(&second).unwrap())
        .is_empty());
}

#[test]
fn composed_sparse_domains_match_an_eager_oracle_after_edits() {
    let mut actual = WBTreeMap::new();
    let mut expected = BTreeMap::new();
    for key in 0..2048 {
        actual.insert(key, key);
        expected.insert(key, key);
    }
    for layer in 0..12 {
        let mut candidates = BTreeSet::new();
        for &key in expected.keys() {
            candidates.extend([key, key + 1, key + 17]);
        }
        let mut relation = PrefixTree2::new();
        let mut images = BTreeMap::new();
        for key in candidates {
            if (key + layer) % 3 != 0 {
                relation.insert([key, key * 2 + 1]);
                images.insert(key, key * 2 + 1);
            }
        }
        actual = actual.mapped_entries(MonotoneMap::new(&relation), |value| {
            (value % 7 != 0).then_some(value + 1)
        });
        expected = expected
            .into_iter()
            .filter_map(|(key, value)| {
                images
                    .get(&key)
                    .and_then(|&image| (value % 7 != 0).then_some((image, value + 1)))
            })
            .collect();
        let snapshot = actual.clone();
        let snapshot_rows = expected.clone();
        let inserted = (2048 << layer) + 19;
        actual.insert(inserted, layer);
        expected.insert(inserted, layer);
        assert_eq!(
            actual
                .iter()
                .map(|(key, &value)| (key, value))
                .collect::<BTreeMap<_, _>>(),
            expected,
            "layer {layer}",
        );
        assert_eq!(
            snapshot
                .iter()
                .map(|(key, &value)| (key, value))
                .collect::<BTreeMap<_, _>>(),
            snapshot_rows,
            "snapshot layer {layer}",
        );
    }
}
