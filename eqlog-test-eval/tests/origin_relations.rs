use std::collections::BTreeSet;

use eqlog_runtime::__private::{OriginRelation, OriginRewriteStats, Table};
use eqlog_runtime::PrefixTree2;

fn rows(relation: &OriginRelation) -> BTreeSet<Vec<u32>> {
    let tuples: Vec<_> = relation.rows().iter().collect();
    let distinct: BTreeSet<_> = tuples.iter().cloned().collect();
    assert_eq!(tuples.len(), distinct.len());
    assert_eq!(relation.len(), distinct.len());
    distinct
}

#[test]
fn equality_visits_only_the_losing_representative_bucket() {
    let mut relation = OriginRelation::new(&[None, Some(0), Some(0)]);
    for key in 0..4096 {
        assert!(relation.insert(&[key, key + 100, key + 100]));
    }
    assert!(relation.insert(&[5000, 7, 7]));
    assert!(relation.insert(&[5001, 7, 8]));
    let before = relation.clone();
    assert!(relation.shares_storage_with(&before));
    assert_eq!(
        relation.replace_representative(0, 7, 9),
        OriginRewriteStats {
            visited_rows: 2,
            rewritten_rows: 2,
            merged_rows: 0,
        }
    );
    assert_eq!(relation.len(), 4098);
    assert!(relation.contains(&[5000, 9, 9]));
    assert!(relation.contains(&[5001, 9, 8]));
    assert!(!relation.contains(&[5000, 7, 7]));
    assert!(before.contains(&[5000, 7, 7]));
    assert!(!before.contains(&[5000, 9, 9]));
    for key in 0..4096 {
        assert!(relation.contains(&[key, key + 100, key + 100]));
    }
    let unchanged = relation.clone();
    assert!(!relation.insert(&[5000, 9, 9]));
    assert_eq!(
        relation.replace_representative(0, 7, 9),
        OriginRewriteStats::default()
    );
    assert_eq!(
        relation.replace_representative(0, 9, 9),
        OriginRewriteStats::default()
    );
    assert_eq!(
        relation.replace_representative(1, 9, 7),
        OriginRewriteStats::default()
    );
    assert!(relation.shares_storage_with(&unchanged));
}

#[test]
fn repeated_columns_and_collisions_keep_the_remaining_incidence() {
    let mut relation = OriginRelation::new(&[Some(0), None, Some(0)]);
    for tuple in [[7, 7, 7], [7, 7, 2], [2, 7, 7], [2, 7, 2]] {
        assert!(relation.insert(&tuple));
    }
    let before = relation.clone();
    assert_eq!(
        relation.replace_representative(0, 7, 2),
        OriginRewriteStats {
            visited_rows: 3,
            rewritten_rows: 0,
            merged_rows: 3,
        }
    );
    assert_eq!(rows(&relation), BTreeSet::from([vec![2, 7, 2]]));
    assert_eq!(
        relation.replace_representative(0, 2, 3),
        OriginRewriteStats {
            visited_rows: 1,
            rewritten_rows: 1,
            merged_rows: 0,
        }
    );
    assert_eq!(rows(&relation), BTreeSet::from([vec![3, 7, 3]]));
    assert_eq!(rows(&before).len(), 4);
}

#[test]
fn member_types_and_global_columns_keep_separate_coordinate_spaces() {
    let mut relation = OriginRelation::new(&[Some(0), None, Some(1), Some(0)]);
    assert!(relation.insert(&[5, 5, 5, 5]));
    assert!(relation.insert(&[9, 5, 5, 9]));
    assert_eq!(
        relation.replace_representative(0, 5, 9),
        OriginRewriteStats {
            visited_rows: 1,
            rewritten_rows: 0,
            merged_rows: 1,
        }
    );
    assert_eq!(rows(&relation), BTreeSet::from([vec![9, 5, 5, 9]]));
    assert_eq!(relation.replace_representative(1, 5, 6).visited_rows, 1);
    assert_eq!(rows(&relation), BTreeSet::from([vec![9, 5, 6, 9]]));
    assert_eq!(relation.replace_representative(0, 9, 10).visited_rows, 1);
    assert_eq!(rows(&relation), BTreeSet::from([vec![10, 5, 6, 10]]));
}

#[test]
fn tables_remove_rows_and_share_snapshots_at_every_storage_arity() {
    for arity in 0..=12 {
        let mut table = Table::new(arity);
        let tuple: Vec<_> = (0..arity as u32).collect();
        assert!(table.is_empty());
        assert!(table.insert(&tuple));
        let mut expected = BTreeSet::from([tuple.clone()]);
        if arity > 0 {
            let mut sibling = tuple.clone();
            sibling[arity - 1] += 100;
            assert!(table.insert(&sibling));
            expected.insert(sibling);
            let mut other_prefix = tuple.clone();
            other_prefix[0] += 200;
            assert!(table.insert(&other_prefix));
            expected.insert(other_prefix);
        }
        let before = table.clone();
        assert!(table.shares_storage_with(&before));
        assert!(table.remove(&tuple));
        assert!(!table.remove(&tuple));
        assert!(before.contains(&tuple));
        assert_eq!(before.iter().collect::<BTreeSet<_>>(), expected);
        expected.remove(&tuple);
        assert_eq!(table.iter().collect::<BTreeSet<_>>(), expected);
        for remaining in expected {
            assert!(table.remove(&remaining));
        }
        assert!(table.is_empty());
        assert!(!table.shares_storage_with(&before));
        assert!(!table.shares_storage_with(&Table::new(arity + 1)));
    }
}

#[test]
fn origin_relations_cover_nullary_and_long_relations() {
    for arity in 0..=12 {
        let member_types: Vec<_> = (0..arity)
            .map(|column| (column % 3 != 1).then_some((column % 2) as u32))
            .collect();
        let mut relation = OriginRelation::new(&member_types);
        assert!(relation.is_empty());
        let tuple = vec![4; arity];
        assert!(relation.insert(&tuple));
        let before = relation.clone();
        let mut expected = tuple.clone();
        for (member_type, value) in member_types.iter().zip(&mut expected) {
            if *member_type == Some(0) {
                *value = 7;
            }
        }
        let affected = usize::from(expected != tuple);
        assert_eq!(
            relation.replace_representative(0, 4, 7),
            OriginRewriteStats {
                visited_rows: affected,
                rewritten_rows: affected,
                merged_rows: 0,
            }
        );
        assert_eq!(rows(&relation), BTreeSet::from([expected]));
        assert_eq!(rows(&before), BTreeSet::from([tuple]));
    }
}

#[test]
fn each_inherited_snapshot_rewrites_only_its_local_row() {
    let mut parent = OriginRelation::new(&[Some(0), None]);
    assert!(parent.insert(&[0, 0]));
    let mut snapshots = vec![parent.clone()];
    let mut visited = 0;
    for origin in 1..=512 {
        let mut child = parent.clone();
        assert!(child.shares_storage_with(&parent));
        assert!(child.insert(&[origin, origin]));
        let stats = child.replace_representative(0, origin, 0);
        assert_eq!(stats.visited_rows, 1);
        visited += stats.visited_rows;
        let index = PrefixTree2::try_from(child.rows()).unwrap();
        assert!(index.get(0).unwrap().contains([origin]));
        assert_eq!(child.len(), origin as usize + 1);
        snapshots.push(child.clone());
        parent = child;
    }
    assert_eq!(visited, 512);
    for (owner, snapshot) in snapshots.iter().enumerate() {
        assert_eq!(snapshot.len(), owner + 1);
        assert!(snapshot.contains(&[0, owner as u32]));
        assert!(!snapshot.contains(&[0, owner as u32 + 1]));
    }
}

#[test]
fn snapshot_replacement_preserves_local_rows_and_ordered_merges() {
    let mut parent = OriginRelation::new(&[None, Some(0)]);
    for tuple in [[10, 1], [20, 2], [30, 3]] {
        parent.insert(&tuple);
    }
    let mut previous_child = parent.clone();
    previous_child.insert(&[40, 4]);
    previous_child.replace_representative(0, 3, 4);
    let previous = previous_child.clone();

    parent.replace_representative(0, 1, 2);
    parent.replace_representative(0, 3, 2);
    let mut current = parent.clone();
    assert!(current.shares_storage_with(&parent));
    current.insert(&[40, 4]);
    current.replace_representative(0, 2, 4);
    assert_eq!(
        rows(&current),
        BTreeSet::from([vec![10, 4], vec![20, 4], vec![30, 4], vec![40, 4]])
    );
    assert_eq!(
        rows(&previous),
        BTreeSet::from([vec![10, 1], vec![20, 2], vec![30, 4], vec![40, 4]])
    );
    assert_eq!(
        rows(&parent),
        BTreeSet::from([vec![10, 2], vec![20, 2], vec![30, 2]])
    );
}

#[test]
fn indexed_replacements_match_an_independent_row_oracle() {
    let member_types = [Some(0), None, Some(1), Some(0), Some(1)];
    let mut relation = OriginRelation::new(&member_types);
    let mut expected = BTreeSet::<Vec<u32>>::new();
    let mut random = 29u64;
    for step in 0..300 {
        random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
        let mut tuple: Vec<_> = (0..5)
            .map(|column| ((random >> (column * 8)) % 12) as u32)
            .collect();
        tuple[3] = tuple[0];
        assert_eq!(relation.insert(&tuple), expected.insert(tuple));
        if step % 3 == 0 {
            let member_type = (random % 2) as u32;
            let loser = ((random >> 8) % 12) as u32;
            let winner = (loser + 1) % 12;
            let before = relation.clone();
            let old_expected = expected.clone();
            let mut affected = Vec::new();
            expected.retain(|tuple| {
                let changes = member_types
                    .iter()
                    .zip(tuple)
                    .any(|(typ, origin)| *typ == Some(member_type) && *origin == loser);
                if changes {
                    affected.push(tuple.clone());
                }
                !changes
            });
            let mut stats = OriginRewriteStats::default();
            for mut tuple in affected {
                stats.visited_rows += 1;
                for (typ, origin) in member_types.iter().zip(&mut tuple) {
                    if *typ == Some(member_type) && *origin == loser {
                        *origin = winner;
                    }
                }
                if expected.insert(tuple) {
                    stats.rewritten_rows += 1;
                } else {
                    stats.merged_rows += 1;
                }
            }
            assert_eq!(
                relation.replace_representative(member_type, loser, winner),
                stats
            );
            assert_eq!(rows(&before), old_expected);
        }
        assert_eq!(rows(&relation), expected);
    }
}
