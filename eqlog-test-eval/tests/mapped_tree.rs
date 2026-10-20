use eqlog_runtime::wbtree::map::WBTreeMap;
use eqlog_runtime::wbtree::mapping::MonotoneMap;
use eqlog_runtime::PrefixTree2;
use std::cell::Cell;
use std::collections::BTreeMap;
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
        for step in 0..160 {
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
