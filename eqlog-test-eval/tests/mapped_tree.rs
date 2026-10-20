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
