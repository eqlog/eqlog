use std::collections::BTreeSet;

use eqlog_runtime::__private::{
    CompactIndexSpec, CompactOwnerIndices, CompactRebaseStats, CompactRecordResult,
};

fn item_specs() -> Vec<CompactIndexSpec> {
    [vec![0, 1], vec![1, 0]]
        .into_iter()
        .map(|order| CompactIndexSpec {
            relation: 10,
            order,
            member_types: vec![None, Some(0)],
        })
        .collect()
}

#[test]
fn inherited_duplicates_retain_only_requested_local_support() {
    let mut indices = CompactOwnerIndices::new(item_specs());
    assert!(!indices.has_owner(0));
    indices.create_owner(0);
    assert!(indices.has_owner(0));
    indices.create_owner(1);
    assert_eq!(
        indices.record(0, 10, &[4, 9], false),
        CompactRecordResult {
            inserted: true,
            retained_support: true
        }
    );
    let stats = indices.rebase(1, 0, false, |_, _| panic!("no local support"), &[]);
    assert!(stats.refreshed);
    assert_eq!(stats.local_rows_replayed, 0);
    assert!(indices.rows(1, 0).shares_storage_with(indices.rows(0, 0)));
    assert!(indices.rows(1, 1).shares_storage_with(indices.rows(0, 1)));
    let revision = indices.revision(1);
    assert_eq!(
        indices.record(1, 10, &[4, 9], false),
        CompactRecordResult::default()
    );
    assert!(indices.local_rows(1, 10).is_empty());
    assert_eq!(
        indices.record(1, 10, &[4, 9], true),
        CompactRecordResult {
            inserted: false,
            retained_support: true
        }
    );
    assert_eq!(
        indices.record(1, 10, &[4, 9], true),
        CompactRecordResult::default()
    );
    assert_eq!(indices.revision(1), revision);
    assert!(indices.rows(1, 0).shares_storage_with(indices.rows(0, 0)));
    let before = indices.snapshot(1);
    assert_eq!(indices.rewrite(1, 0, 9, 8).visited_rows, 2);
    assert!(indices.rows(1, 0).contains(&[4, 8]));
    assert!(indices.rows(1, 1).contains(&[8, 4]));
    assert!(indices.local_rows(1, 10).contains(&[4, 9]));
    assert!(before.rows(0).contains(&[4, 9]));
    assert!(before.local_rows(10).contains(&[4, 9]));
    let stats = indices.rebase(1, 0, true, |_, origin| origin, &[(0, 9, 8)]);
    assert_eq!(stats.local_rows_replayed, 1);
    assert_eq!(stats.rewrite.visited_rows, 2);
    assert!(indices.rows(1, 0).contains(&[4, 8]));
}

#[test]
fn parent_replacement_replays_local_support_before_local_equations() {
    let mut indices = CompactOwnerIndices::new(item_specs());
    indices.create_owner(0);
    indices.create_owner(1);
    for tuple in [[10, 1], [20, 2], [30, 3]] {
        indices.record(0, 10, &tuple, false);
    }
    indices.record(1, 10, &[40, 4], false);
    let first = indices.rebase(1, 0, false, |_, origin| origin, &[(0, 3, 4)]);
    assert_eq!(first.local_rows_replayed, 1);
    assert_eq!(first.rewrite.visited_rows, 2);
    let before = indices.snapshot(1);
    indices.rewrite(0, 0, 1, 2);
    indices.rewrite(0, 0, 3, 2);
    let refreshed = indices.rebase(
        1,
        0,
        false,
        |typ, origin| {
            assert_eq!(typ, 0);
            if origin == 1 || origin == 3 {
                2
            } else {
                origin
            }
        },
        &[(0, 2, 4)],
    );
    assert_eq!(refreshed.local_rows_replayed, 1);
    assert_eq!(refreshed.rewrite.visited_rows, 6);
    assert_eq!(indices.source(1), Some(0));
    assert_eq!(indices.source_revision(1), Some(indices.revision(0)));
    assert_eq!(
        indices.rows(1, 0).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![10, 4], vec![20, 4], vec![30, 4], vec![40, 4]])
    );
    assert_eq!(
        before.rows(0).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![10, 1], vec![20, 2], vec![30, 4], vec![40, 4]])
    );
    assert!(indices.rows(0, 0).contains(&[10, 2]));
    assert!(!indices.rows(0, 0).contains(&[40, 4]));
    let current = indices.snapshot(1);
    assert_eq!(
        indices.rebase(1, 0, false, |_, _| panic!("unchanged parent"), &[(0, 4, 8)]),
        CompactRebaseStats::default()
    );
    assert_eq!(current.revision(), indices.revision(1));
    assert!(current.rows(0).shares_storage_with(indices.rows(1, 0)));
}

#[test]
fn partition_changes_can_force_refresh_without_parent_row_changes() {
    let mut indices = CompactOwnerIndices::new(item_specs());
    indices.create_owner(0);
    indices.create_owner(1);
    indices.record(0, 10, &[10, 1], false);
    indices.record(1, 10, &[5, 5], false);
    indices.rebase(1, 0, false, |_, origin| origin, &[]);
    let parent_revision = indices.revision(0);
    let before = indices.snapshot(1);
    assert_eq!(
        indices.rebase(1, 0, false, |_, _| panic!("unchanged parent"), &[]),
        CompactRebaseStats::default()
    );
    let mut normalized = 0;
    let stats = indices.rebase(
        1,
        0,
        true,
        |typ, origin| {
            normalized += 1;
            assert_eq!((typ, origin), (0, 5));
            6
        },
        &[],
    );
    assert!(stats.refreshed);
    assert_eq!(stats.local_rows_replayed, 1);
    assert_eq!(stats.rewrite.visited_rows, 0);
    assert_eq!(normalized, 1);
    assert_eq!(indices.revision(0), parent_revision);
    assert!(indices.rows(1, 0).contains(&[5, 6]));
    assert!(indices.rows(1, 1).contains(&[6, 5]));
    assert!(indices.local_rows(1, 10).contains(&[5, 5]));
    assert!(before.rows(0).contains(&[5, 5]));
    assert!(before.revision() < indices.revision(1));
}

#[test]
fn chain_rebases_visit_only_local_support_and_local_losing_buckets() {
    let specs = vec![
        CompactIndexSpec {
            relation: 10,
            order: vec![0, 1, 2],
            member_types: vec![Some(0), None, Some(1)],
        },
        CompactIndexSpec {
            relation: 10,
            order: vec![2, 0, 1],
            member_types: vec![Some(0), None, Some(1)],
        },
        CompactIndexSpec {
            relation: 20,
            order: vec![0, 1],
            member_types: vec![None, Some(0)],
        },
        CompactIndexSpec {
            relation: 20,
            order: vec![1, 0],
            member_types: vec![None, Some(0)],
        },
    ];
    let mut indices = CompactOwnerIndices::new(specs);
    for owner in 0..=200 {
        indices.create_owner(owner);
    }
    indices.record(0, 10, &[0, 0, 0], false);
    indices.record(0, 20, &[0, 0], false);
    let mut before = vec![indices.snapshot(0)];
    let mut first_visits = 0;
    for owner in 1..=200 {
        let stats = indices.rebase(owner, owner - 1, false, |_, _| panic!("no local rows"), &[]);
        assert_eq!(stats.local_rows_replayed, 0);
        for index in 0..4 {
            assert!(indices
                .rows(owner, index)
                .shares_storage_with(indices.rows(owner - 1, index)));
        }
        indices.record(owner, 10, &[owner, owner, owner], false);
        indices.record(owner, 20, &[owner, owner], false);
        first_visits += indices.rewrite(owner, 0, owner, 0).visited_rows;
        first_visits += indices.rewrite(owner, 1, owner, 0).visited_rows;
        before.push(indices.snapshot(owner));
    }
    assert_eq!(first_visits, 200 * 6);
    indices.record(0, 10, &[0, 1000, 0], false);
    let mut replayed = 0;
    let mut revisited = 0;
    let mut normalized = 0;
    for owner in 1..=200 {
        let stats = indices.rebase(
            owner,
            owner - 1,
            false,
            |_, origin| {
                normalized += 1;
                if origin < owner {
                    0
                } else {
                    origin
                }
            },
            &[(0, owner, 0), (1, owner, 0)],
        );
        assert!(stats.refreshed);
        assert_eq!(stats.local_rows_replayed, 1);
        assert_eq!(stats.reused_indices, 2);
        assert_eq!(stats.rewrite.visited_rows, 4);
        replayed += stats.local_rows_replayed;
        revisited += stats.rewrite.visited_rows;
        assert!(indices.rows(owner, 0).contains(&[0, 1000, 0]));
        assert!(indices.rows(owner, 1).contains(&[0, 0, 1000]));
        assert!(indices.rows(owner, 2).contains(&[owner, 0]));
        assert!(indices.rows(owner, 3).contains(&[0, owner]));
        assert!(before[owner as usize]
            .rows(2)
            .shares_storage_with(indices.rows(owner, 2)));
        assert!(before[owner as usize]
            .rows(3)
            .shares_storage_with(indices.rows(owner, 3)));
        assert_eq!(indices.rows(owner, 0).iter().count(), owner as usize + 2);
        assert_eq!(indices.local_rows(owner, 10).iter().count(), 1);
        assert_eq!(indices.local_rows(owner, 20).iter().count(), 1);
        assert!(!before[owner as usize].rows(0).contains(&[0, 1000, 0]));
        assert_eq!(
            before[owner as usize].rows(0).iter().count(),
            owner as usize + 1
        );
    }
    assert_eq!(replayed, 200);
    assert_eq!(revisited, 200 * 4);
    assert_eq!(normalized, 200 * 2);
    assert!(indices.owners().eq(0..=200));
    for owner in 1..=200 {
        assert_eq!(
            indices.rebase(
                owner,
                owner - 1,
                false,
                |_, _| panic!("unchanged parent"),
                &[]
            ),
            CompactRebaseStats::default()
        );
    }
}

#[test]
fn unrelated_parent_changes_preserve_current_local_edits_and_incidence() {
    let mut specs = item_specs();
    specs.push(CompactIndexSpec {
        relation: 20,
        order: vec![0],
        member_types: vec![None],
    });
    specs.push(CompactIndexSpec {
        relation: 30,
        order: vec![0],
        member_types: vec![Some(0)],
    });
    let mut indices = CompactOwnerIndices::new(specs);
    indices.create_owner(0);
    indices.create_owner(1);
    indices.record(0, 10, &[10, 1], false);
    indices.record(0, 20, &[20], false);
    indices.record(0, 30, &[1], false);
    indices.record(1, 10, &[40, 4], false);
    indices.record(1, 20, &[21], false);
    indices.record(1, 30, &[4], false);
    indices.rebase(1, 0, false, |_, origin| origin, &[(0, 4, 1)]);
    let before = indices.snapshot(1);

    indices.record(0, 30, &[2], false);
    let mut normalized = 0;
    let stats = indices.rebase(
        1,
        0,
        false,
        |_, origin| {
            normalized += 1;
            assert_eq!(origin, 4);
            origin
        },
        &[(0, 4, 1)],
    );
    assert_eq!(stats.reused_indices, 3);
    assert_eq!(stats.local_rows_replayed, 1);
    assert_eq!(stats.rewrite.visited_rows, 1);
    assert_eq!(normalized, 1);
    for index in 0..3 {
        assert!(before
            .rows(index)
            .shares_storage_with(indices.rows(1, index)));
    }
    assert_eq!(
        indices.rows(1, 3).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![1], vec![2]])
    );

    indices.record(1, 10, &[50, 5], false);
    indices.rewrite(1, 0, 5, 1);
    indices.record(1, 20, &[22], false);
    let edited = indices.snapshot(1);
    indices.record(0, 30, &[3], false);
    let stats = indices.rebase(1, 0, false, |_, origin| origin, &[(0, 4, 1), (0, 5, 1)]);
    assert_eq!(stats.reused_indices, 3);
    assert_eq!(stats.local_rows_replayed, 1);
    for index in 0..3 {
        assert!(edited
            .rows(index)
            .shares_storage_with(indices.rows(1, index)));
    }
    assert!(indices.rows(1, 0).contains(&[50, 1]));
    assert!(indices.local_rows(1, 10).contains(&[50, 5]));

    let before_quotient = indices.snapshot(1);
    indices.rewrite(0, 0, 1, 2);
    let stats = indices.rebase(
        1,
        0,
        true,
        |_, origin| {
            if origin == 1 {
                2
            } else {
                origin
            }
        },
        &[(0, 4, 2), (0, 5, 2)],
    );
    assert_eq!(stats.reused_indices, 1);
    assert_eq!(stats.local_rows_replayed, 3);
    assert_eq!(stats.rewrite.visited_rows, 5);
    assert!(before_quotient
        .rows(2)
        .shares_storage_with(indices.rows(1, 2)));
    assert_eq!(
        indices.rows(1, 2).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![20], vec![21], vec![22]])
    );
    assert_eq!(
        indices.rows(1, 0).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![10, 2], vec![40, 2], vec![50, 2]])
    );
    assert!(before_quotient.rows(0).contains(&[50, 1]));
    assert!(indices.local_rows(1, 10).contains(&[40, 4]));
    assert!(indices.local_rows(1, 10).contains(&[50, 5]));
    assert_eq!(indices.rewrite(1, 0, 2, 7).visited_rows, 7);
    assert!(indices.rows(1, 0).contains(&[50, 7]));
}

#[test]
fn quotient_refresh_reuses_member_free_indexes_without_changing_row_revision() {
    let mut indices = CompactOwnerIndices::new(vec![CompactIndexSpec {
        relation: 10,
        order: vec![0],
        member_types: vec![None],
    }]);
    indices.create_owner(0);
    indices.create_owner(1);
    indices.record(0, 10, &[1], false);
    indices.record(1, 10, &[2], false);
    indices.rebase(1, 0, false, |_, _| panic!("no member columns"), &[]);
    let before = indices.snapshot(1);
    let stats = indices.rebase(1, 0, true, |_, _| panic!("no member columns"), &[(0, 1, 2)]);
    assert!(stats.refreshed);
    assert_eq!(stats.reused_indices, 1);
    assert_eq!(stats.local_rows_replayed, 0);
    assert_eq!(stats.rewrite.visited_rows, 0);
    assert_eq!(before.revision(), indices.revision(1));
    assert!(before.rows(0).shares_storage_with(indices.rows(1, 0)));
}

#[test]
fn nullary_and_long_indexes_follow_the_same_snapshot_contract() {
    for arity in [0, 11] {
        let member_types: Vec<_> = (0..arity)
            .map(|column| (column % 2 == 0).then_some(0))
            .collect();
        let order: Vec<_> = (0..arity).rev().collect();
        let mut indices = CompactOwnerIndices::new(vec![CompactIndexSpec {
            relation: 10,
            order,
            member_types,
        }]);
        indices.create_owner(0);
        indices.create_owner(1);
        let tuple = vec![1; arity];
        indices.record(0, 10, &tuple, false);
        indices.rebase(1, 0, false, |_, _| panic!("no local rows"), &[]);
        assert!(indices.rows(1, 0).shares_storage_with(indices.rows(0, 0)));
        assert_eq!(
            indices.record(1, 10, &tuple, false),
            CompactRecordResult::default()
        );
        let snapshot = indices.snapshot(1);
        indices.rewrite(1, 0, 1, 2);
        let expected: Vec<_> = (0..arity)
            .rev()
            .map(|column| if column % 2 == 0 { 2 } else { 1 })
            .collect();
        assert!(indices.rows(1, 0).contains(&expected));
        assert!(snapshot.rows(0).contains(&tuple));
        assert_eq!(snapshot.source(), Some(0));
        assert_eq!(snapshot.source_revision(), Some(indices.revision(0)));
    }
}

#[test]
#[should_panic(expected = "full signature permutation")]
fn diagonal_indexes_are_rejected() {
    CompactOwnerIndices::new(vec![CompactIndexSpec {
        relation: 10,
        order: vec![0, 0],
        member_types: vec![None, Some(0)],
    }]);
}

#[test]
#[should_panic(expected = "inconsistent relation signature")]
fn index_schemas_must_agree() {
    let mut specs = item_specs();
    specs[1].member_types[1] = Some(1);
    CompactOwnerIndices::new(specs);
}

#[test]
#[should_panic(expected = "cyclic compact inheritance")]
fn inherited_indexes_reject_cycles_without_walking_ancestor_rows() {
    let mut indices = CompactOwnerIndices::new(Vec::new());
    indices.create_owner(0);
    indices.create_owner(1);
    indices.rebase(1, 0, false, |_, origin| origin, &[]);
    indices.rebase(0, 1, false, |_, origin| origin, &[]);
}

#[test]
#[should_panic(expected = "cyclic compact inheritance")]
fn a_leaf_index_owner_rejects_its_own_incoming_edge() {
    let mut indices = CompactOwnerIndices::new(Vec::new());
    indices.create_owner(0);
    indices.register_edge(0, 0);
}

#[test]
#[should_panic(expected = "already has another source")]
fn inherited_indexes_reject_multiple_sources() {
    let mut indices = CompactOwnerIndices::new(Vec::new());
    for owner in 0..3 {
        indices.create_owner(owner);
    }
    indices.rebase(2, 0, false, |_, origin| origin, &[]);
    indices.rebase(2, 1, false, |_, origin| origin, &[]);
}

#[test]
#[should_panic(expected = "unknown compact index")]
fn snapshot_index_access_checks_its_boundary() {
    let mut indices = CompactOwnerIndices::new(Vec::new());
    indices.create_owner(0);
    indices.rows(0, 0);
}

#[test]
fn shared_indexes_union_sources_but_keep_one_raw_inherited_baseline() {
    let mut specs = item_specs();
    specs.push(CompactIndexSpec {
        relation: 20,
        order: vec![0],
        member_types: vec![Some(0)],
    });
    let mut indices = CompactOwnerIndices::new(specs);
    for owner in 0..4 {
        indices.create_owner(owner);
    }
    indices.record(0, 10, &[10, 1], false);
    indices.record(0, 20, &[1], false);
    for owner in [1, 2] {
        indices.rebase(owner, 0, false, |_, origin| origin, &[]);
    }
    indices.record(1, 10, &[20, 2], false);
    indices.record(1, 20, &[2], false);
    indices.record(2, 10, &[30, 3], false);
    indices.record(2, 20, &[3], false);
    indices.record(3, 10, &[40, 4], false);
    indices.rebase(3, 1, false, |_, origin| origin, &[]);
    let before = indices.snapshot(3);
    assert!(indices.inherit_shared(3, 2).refreshed);
    assert_eq!(
        indices.rows(3, 0).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![10, 1], vec![20, 2], vec![30, 3], vec![40, 4]])
    );
    assert_eq!(
        indices.rows(3, 1).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![1, 10], vec![2, 20], vec![3, 30], vec![4, 40]])
    );
    assert!(!before.rows(0).contains(&[30, 3]));
    let baseline = indices.inherited_rows(3, 0).unwrap();
    assert!(baseline.shares_storage_with(indices.rows(1, 0)));
    assert!(baseline.contains(&[20, 2]));
    assert!(!baseline.contains(&[30, 3]));
    assert!(!baseline.contains(&[40, 4]));
    assert_eq!(
        indices.record(3, 10, &[30, 3], true),
        CompactRecordResult {
            inserted: false,
            retained_support: true,
        }
    );
    indices.record(3, 20, &[4], false);
    let combined = indices.snapshot(3);
    indices.record(2, 10, &[50, 5], false);
    let refreshed = indices.rebase(3, 1, false, |_, _| panic!("unchanged partition"), &[]);
    assert!(refreshed.refreshed);
    assert_eq!(refreshed.reused_indices, 1);
    assert_eq!(refreshed.local_rows_replayed, 2);
    assert!(indices.rows(3, 2).shares_storage_with(combined.rows(2)));
    assert!(indices.rows(3, 0).contains(&[50, 5]));
    assert!(indices.rows(3, 0).contains(&[40, 4]));
    assert!(!combined.rows(0).contains(&[50, 5]));
    assert!(!indices.inherited_rows(3, 0).unwrap().contains(&[50, 5]));
    assert_eq!(
        indices.rebase(3, 1, false, |_, _| panic!("unchanged sources"), &[]),
        CompactRebaseStats::default()
    );
    let rewrite = indices.rewrite(3, 0, 3, 2);
    assert_eq!(rewrite.visited_rows, 3);
    assert_eq!(rewrite.merged_rows, 1);
    assert!(indices.rows(3, 0).contains(&[30, 2]));
    assert!(indices.rows(3, 1).contains(&[2, 30]));
    assert!(!indices.rows(3, 2).contains(&[3]));
    assert!(indices.rows(2, 0).contains(&[30, 3]));
    assert!(combined.rows(0).contains(&[30, 3]));
}

#[test]
fn additional_sources_extend_rows_without_replaying_local_support() {
    let mut indices = CompactOwnerIndices::new(item_specs());
    for owner in 0..=6 {
        indices.create_owner(owner);
    }
    for source in 0..6 {
        indices.record(source, 10, &[10 * (source + 1), source + 1], false);
    }
    indices.record(6, 10, &[90, 9], false);
    indices.rebase(6, 0, false, |_, origin| origin, &[]);
    let before = indices.snapshot(6);
    assert_eq!(indices.inherit_shared(6, 1).local_rows_replayed, 0);
    indices.record(6, 10, &[91, 10], false);
    assert_eq!(indices.inherit_shared(6, 2).local_rows_replayed, 0);
    assert!(!before.rows(0).contains(&[20, 2]));

    indices.record(0, 10, &[70, 7], false);
    assert_eq!(indices.inherit_shared(6, 3).local_rows_replayed, 2);
    assert!(indices.rows(6, 0).contains(&[70, 7]));
    indices.record(1, 10, &[80, 8], false);
    assert_eq!(indices.inherit_shared(6, 4).local_rows_replayed, 2);
    assert_eq!(indices.inherit_shared(6, 5).local_rows_replayed, 0);

    assert_eq!(
        indices.rows(6, 0).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([
            vec![10, 1],
            vec![20, 2],
            vec![30, 3],
            vec![40, 4],
            vec![50, 5],
            vec![60, 6],
            vec![70, 7],
            vec![80, 8],
            vec![90, 9],
            vec![91, 10],
        ])
    );
    let baseline = indices.inherited_rows(6, 0).unwrap();
    assert!(baseline.shares_storage_with(indices.rows(0, 0)));
    assert!(baseline.contains(&[70, 7]));
    assert!(!baseline.contains(&[80, 8]));
    assert!(!baseline.contains(&[90, 9]));
    assert_eq!(indices.rewrite(6, 0, 10, 9).visited_rows, 2);
    assert!(indices.rows(6, 0).contains(&[91, 9]));
    assert!(indices.rows(6, 1).contains(&[9, 91]));
}

#[test]
fn shared_adoption_rebuilds_rewritten_or_normalized_support() {
    for rewrite in [false, true] {
        let mut indices = CompactOwnerIndices::new(item_specs());
        for owner in 0..4 {
            indices.create_owner(owner);
        }
        indices.record(0, 10, &[10, 1], false);
        indices.record(1, 10, &[20, 2], false);
        indices.record(2, 10, &[30, 3], false);
        indices.record(3, 10, &[40, 4], false);
        indices.rebase(
            3,
            0,
            false,
            |_, origin| {
                if !rewrite && origin == 4 {
                    5
                } else {
                    origin
                }
            },
            &[],
        );
        if rewrite {
            indices.rewrite(3, 0, 4, 5);
        }
        assert!(indices.rows(3, 0).contains(&[40, 5]));
        assert_eq!(indices.inherit_shared(3, 1).local_rows_replayed, 1);
        assert!(indices.rows(3, 0).contains(&[40, 4]));
        assert!(!indices.rows(3, 0).contains(&[40, 5]));
        assert_eq!(indices.inherit_shared(3, 2).local_rows_replayed, 0);
        assert!(indices.rows(3, 0).contains(&[30, 3]));
        assert!(indices.rows(3, 0).contains(&[40, 4]));
    }
}

#[test]
fn partial_shared_rebases_keep_rewrites_ineligible_for_extension() {
    let mut specs = item_specs();
    specs.push(CompactIndexSpec {
        relation: 20,
        order: vec![0],
        member_types: vec![Some(0)],
    });
    let mut indices = CompactOwnerIndices::new(specs);
    for owner in 0..4 {
        indices.create_owner(owner);
    }
    indices.record(0, 10, &[10, 1], false);
    indices.record(1, 10, &[20, 2], false);
    indices.record(2, 10, &[30, 3], false);
    indices.record(3, 10, &[40, 4], false);
    indices.rebase(3, 0, false, |_, origin| origin, &[]);
    indices.inherit_shared(3, 1);
    indices.rewrite(3, 0, 4, 5);
    indices.record(1, 20, &[2], false);
    let rebase = indices.rebase(3, 0, false, |_, origin| origin, &[]);
    assert_eq!(rebase.reused_indices, 2);
    assert!(indices.rows(3, 0).contains(&[40, 5]));
    assert_eq!(indices.inherit_shared(3, 2).local_rows_replayed, 1);
    assert!(indices.rows(3, 0).contains(&[40, 4]));
    assert!(!indices.rows(3, 0).contains(&[40, 5]));
}

#[test]
fn late_primary_edges_can_complete_an_acyclic_shared_component() {
    let mut indices = CompactOwnerIndices::new(item_specs());
    for owner in 0..3 {
        indices.create_owner(owner);
    }
    indices.record(0, 10, &[10, 1], false);
    indices.record(1, 10, &[20, 2], false);
    indices.rebase(2, 0, false, |_, origin| origin, &[]);
    indices.inherit_shared(2, 1);
    assert!(
        indices
            .rebase(1, 0, false, |_, origin| origin, &[])
            .refreshed
    );
    assert!(
        indices
            .rebase(2, 0, false, |_, origin| origin, &[])
            .refreshed
    );
    assert_eq!(
        indices.rows(2, 0).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![10, 1], vec![20, 2]])
    );
}

#[test]
#[should_panic(expected = "already has another source")]
fn shared_rebases_reject_an_unrelated_primary_source() {
    let mut indices = CompactOwnerIndices::new(Vec::new());
    for owner in 0..4 {
        indices.create_owner(owner);
    }
    indices.rebase(2, 0, false, |_, origin| origin, &[]);
    indices.inherit_shared(2, 1);
    indices.rebase(2, 3, false, |_, origin| origin, &[]);
}

#[test]
#[should_panic(expected = "cyclic compact inheritance")]
fn shared_edges_reject_directed_cycles() {
    let mut indices = CompactOwnerIndices::new(Vec::new());
    for owner in 0..4 {
        indices.create_owner(owner);
    }
    indices.rebase(1, 0, false, |_, origin| origin, &[]);
    indices.rebase(2, 3, false, |_, origin| origin, &[]);
    indices.inherit_shared(2, 1);
    indices.inherit_shared(1, 2);
}

#[test]
fn pending_index_edges_do_not_install_source_snapshots() {
    let mut indices = CompactOwnerIndices::new(item_specs());
    for owner in 0..4 {
        indices.create_owner(owner);
    }
    for (source, target) in [(0, 1), (0, 2), (1, 3), (2, 3)] {
        indices.register_edge(source, target);
        assert_eq!(indices.source(target), None);
        assert!(indices.rows(target, 0).is_empty());
    }
    indices.record(0, 10, &[10, 1], false);
    indices.rebase(1, 0, false, |_, origin| origin, &[]);
    indices.rebase(2, 0, false, |_, origin| origin, &[]);
    indices.record(1, 10, &[20, 2], false);
    indices.record(2, 10, &[30, 3], false);
    indices.rebase(3, 1, false, |_, origin| origin, &[]);
    indices.inherit_shared(3, 2);
    assert_eq!(
        indices.rows(3, 0).iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![10, 1], vec![20, 2], vec![30, 3]])
    );
}

#[test]
#[should_panic(expected = "cyclic compact inheritance")]
fn pending_index_edges_reject_cycles_before_installing_snapshots() {
    let mut indices = CompactOwnerIndices::new(Vec::new());
    for owner in 0..3 {
        indices.create_owner(owner);
    }
    indices.register_edge(0, 1);
    indices.register_edge(1, 2);
    indices.register_edge(0, 2);
    indices.register_edge(2, 0);
}
