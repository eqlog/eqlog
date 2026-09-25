use eqlog_runtime::wbtree::map::WBTreeMap;
use eqlog_runtime::PrefixTree2;
use std::collections::BTreeMap;

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
