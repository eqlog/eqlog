use eqlog_runtime::__private::{AgeView, RelationVersions};
use eqlog_runtime::{
    PrefixTree0, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6,
    PrefixTree7, PrefixTree8, PrefixTree9,
};

fn check0(view: &AgeView<PrefixTree0>, expected: &PrefixTree0) {
    assert_eq!(view.is_empty(), expected.is_empty());
    assert_eq!(view.contains([]), expected.contains([]));
    for limit in [0, 1, 5] {
        assert_eq!(view.key_count_up_to(limit), expected.key_count_up_to(limit));
        assert_eq!(view.row_count_up_to(limit), expected.row_count_up_to(limit));
    }
}

fn check1(view: &AgeView<PrefixTree1>, expected: &PrefixTree1) {
    assert_eq!(view.is_empty(), expected.is_empty());
    let children: Vec<_> = view.iter_restrictions().collect();
    let keys: Vec<_> = children.iter().map(|(key, _)| *key).collect();
    assert_eq!(keys, expected.iter().map(|[key]| key).collect::<Vec<_>>());
    for (key, child) in children {
        check0(&child, expected.get(key).unwrap());
    }
    for key in 0..10 {
        assert_eq!(view.contains([key]), expected.contains([key]));
        assert_eq!(view.get(key).is_some(), expected.get(key).is_some());
        check0(
            &view.restrict(key),
            expected.get(key).unwrap_or_else(|| PrefixTree0::empty()),
        );
    }
    for limit in [0, 1, 5, 100] {
        let count = expected.iter().count().min(limit + 1);
        assert_eq!(view.key_count_up_to(limit), count);
        assert_eq!(view.row_count_up_to(limit), count);
        assert_eq!(expected.key_count_up_to(limit), count);
        assert_eq!(expected.row_count_up_to(limit), count);
    }
}

macro_rules! checks {
    ($(($check:ident, $tree:ident, $child:ident, $check_child:ident)),*) => {$(
        fn $check(view: &AgeView<$tree>, expected: &$tree) {
            assert_eq!(view.is_empty(), expected.is_empty());
            if expected.is_empty() {
                assert_eq!(view.key_count_up_to(0), 0);
                assert_eq!(view.row_count_up_to(0), 0);
                assert!(view.iter_restrictions().next().is_none());
                for key in [0, 4, 9] {
                    assert!(view.get(key).is_none());
                }
                return;
            }
            let children: Vec<_> = view.iter_restrictions().collect();
            let keys: Vec<_> = children.iter().map(|(key, _)| *key).collect();
            assert_eq!(
                keys,
                expected.iter_restrictions().map(|(key, _)| key).collect::<Vec<_>>()
            );
            for row in expected.iter() {
                assert!(view.contains(row));
            }
            for (key, child) in children {
                $check_child(&child, expected.get(key).unwrap());
            }
            for key in 0..10 {
                assert_eq!(view.get(key).is_some(), expected.get(key).is_some());
                $check_child(
                    &view.restrict(key),
                    expected.get(key).unwrap_or_else(|| $child::empty()),
                );
            }
            for limit in [0, 1, 5, 100] {
                let rows = expected.iter().count().min(limit + 1);
                let keys = expected.iter_restrictions().count().min(limit + 1);
                assert_eq!(view.key_count_up_to(limit), keys);
                assert_eq!(view.row_count_up_to(limit), rows);
                assert_eq!(expected.key_count_up_to(limit), keys);
                assert_eq!(expected.row_count_up_to(limit), rows);
            }
            assert_eq!(
                view.materialize().iter().collect::<Vec<_>>(),
                expected.iter().collect::<Vec<_>>(),
            );
        }
    )*};
}

checks!(
    (check2, PrefixTree2, PrefixTree1, check1),
    (check3, PrefixTree3, PrefixTree2, check2),
    (check4, PrefixTree4, PrefixTree3, check3),
    (check5, PrefixTree5, PrefixTree4, check4),
    (check6, PrefixTree6, PrefixTree5, check5),
    (check7, PrefixTree7, PrefixTree6, check6),
    (check8, PrefixTree8, PrefixTree7, check7),
    (check9, PrefixTree9, PrefixTree8, check8)
);

#[test]
fn restriction_and_iteration_preserve_every_age_through_nine_columns() {
    let mut previous = PrefixTree9::new();
    previous.insert([0, 1, 2, 3, 4, 5, 6, 7, 8]);
    previous.insert([0, 1, 2, 3, 4, 5, 6, 7, 9]);
    previous.insert([1, 0, 0, 0, 0, 0, 0, 0, 0]);
    let mut current = previous.clone();
    current.remove([0, 1, 2, 3, 4, 5, 6, 7, 9]);
    current.insert([0, 1, 2, 3, 4, 5, 6, 7, 0]);
    current.insert([2, 0, 0, 0, 0, 0, 0, 0, 0]);
    check9(&AgeView::all(current.clone()), &current);
    check9(
        &AgeView::difference(current.clone(), previous.clone()),
        &current.difference(&previous),
    );
    check9(
        &AgeView::intersection(current.clone(), previous.clone()),
        &current.intersection(&previous),
    );
}

#[test]
fn old_and_new_views_survive_replacements_and_independent_consumer_progress() {
    let mut eager = RelationVersions::new();
    let mut lazy = RelationVersions::new();
    let mut rows = PrefixTree3::new();
    let mut random = 19_u64;
    for step in 0..96 {
        random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
        let row = [
            (random % 4) as u32,
            ((random >> 16) % 4) as u32,
            ((random >> 32) % 4) as u32,
        ];
        rows.insert(row);
        if step % 3 == 0 {
            rows.remove([row[0], row[1], (row[2] + 1) % 4]);
        }
        eager.publish(&rows);
        lazy.publish(&rows);
        let consumer = step % 4;
        let expected = eager.consume(consumer);
        let actual = lazy.consume_lazy_required::<true, true>(consumer);
        check3(&actual.old, &expected.old);
        check3(&actual.new, &expected.new);
        for a in 0..4 {
            for b in 0..4 {
                for c in 0..4 {
                    assert_eq!(
                        actual.old.contains([a, b, c]),
                        expected.old.contains([a, b, c])
                    );
                    assert_eq!(
                        actual.new.contains([a, b, c]),
                        expected.new.contains([a, b, c])
                    );
                }
            }
        }
    }
    let historical = lazy.consume_lazy_required::<true, true>(0);
    let expected = historical.old.materialize().clone();
    rows.insert([9, 9, 9]);
    lazy.publish(&rows);
    lazy.consume_lazy_required::<true, true>(0);
    check3(&historical.old, &expected);
}

#[test]
fn sparse_new_suffixes_and_changed_but_empty_pivots_have_exact_counts() {
    let mut previous = PrefixTree2::new();
    for key in 0..10_000 {
        previous.insert([key, key]);
    }
    let mut current = previous.clone();
    current.remove([0, 0]);
    current.insert([9_999, 10_000]);
    let view = AgeView::difference(current, previous);
    assert!(view.get(0).is_none());
    assert!(view.get(1).is_none());
    assert_eq!(view.key_count_up_to(2), 1);
    assert_eq!(view.row_count_up_to(2), 1);
    assert!(view.get(9_999).unwrap().contains([10_000]));
    assert!(!view.get(9_999).unwrap().contains([9_999]));

    let mut previous = PrefixTree1::new();
    for key in 0..10_000 {
        previous.insert([key]);
    }
    let mut current = previous.clone();
    current.insert([10_000]);
    let view = AgeView::difference(current, previous);
    assert_eq!(view.key_count_up_to(2), 1);
    assert_eq!(view.row_count_up_to(0), 1);
}

#[test]
fn row_budgets_count_fanout_after_a_single_prefix_key() {
    let mut rows = PrefixTree3::new();
    for key in 0..100 {
        rows.insert([1, key, 0]);
        rows.insert([1, key, 1]);
    }
    let view = AgeView::difference(rows.clone(), PrefixTree3::new());
    assert_eq!(view.key_count_up_to(5), 1);
    assert_eq!(view.row_count_up_to(5), 6);
    assert_eq!(view.row_count_up_to(199), 200);
    assert_eq!(view.row_count_up_to(200), 200);
    assert_eq!(rows.key_count_up_to(5), 1);
    assert_eq!(rows.row_count_up_to(5), 6);
}

#[test]
fn mapped_snapshots_keep_sparse_changes_and_counts_semantic() {
    let mut rows = PrefixTree2::new();
    let mut mapping = PrefixTree2::new();
    for key in 0..32 {
        rows.insert([key, key]);
        if key % 3 != 0 {
            mapping.insert([key, key + 100]);
        }
    }
    let previous = PrefixTree2 {
        map: rows.map.mapped(mapping.clone()),
    };
    rows.insert([31, 32]);
    rows.remove([29, 29]);
    let current = PrefixTree2 {
        map: rows.map.mapped(mapping),
    };
    check2(
        &AgeView::difference(current.clone(), previous.clone()),
        &current.difference(&previous),
    );
    check2(
        &AgeView::intersection(current.clone(), previous.clone()),
        &current.intersection(&previous),
    );
    check2(&AgeView::all(current.clone()), &current);
}

#[test]
fn retained_empty_pivots_do_not_become_age_witnesses() {
    let mut rows = PrefixTree3::new();
    rows.insert([1, 2, 3]);
    let previous = rows.clone();
    rows.get_mut(1).unwrap().get_mut(2).unwrap().remove([3]);
    assert!(!rows.is_empty());
    assert_eq!(rows.iter().count(), 0);
    for view in [
        AgeView::all(rows.clone()),
        AgeView::difference(rows.clone(), PrefixTree3::new()),
        AgeView::difference(rows.clone(), previous.clone()),
        AgeView::intersection(rows.clone(), previous),
    ] {
        assert!(view.is_empty());
        assert!(view.get(1).is_none());
        assert!(view.restrict(1).is_empty());
        assert!(view.iter_restrictions().next().is_none());
        assert_eq!(view.key_count_up_to(10), 0);
        assert_eq!(view.row_count_up_to(10), 0);
    }
    rows.insert([4, 5, 6]);
    let view = AgeView::difference(rows, PrefixTree3::new());
    assert!(!view.is_empty());
    assert!(view.get(1).is_none());
    assert!(view.get(4).unwrap().get(5).unwrap().contains([6]));
    assert_eq!(view.key_count_up_to(10), 1);
    assert_eq!(view.row_count_up_to(10), 1);
}

#[test]
fn lazy_membership_retains_alias_witnesses_without_relabeling_them() {
    let mut versions = RelationVersions::new();
    let mut rows = PrefixTree2::new();
    rows.insert([0, 1]);
    rows.insert([2, 3]);
    versions.publish(&rows);
    for consumer in 0..4 {
        versions.consume(consumer);
    }
    rows.remove([0, 1]);
    rows.insert([0, 0]);
    versions.publish(&rows);
    let historical = versions.consume_lazy_membership::<true, true>(0);
    let filtered = versions.consume_lazy_required::<true, true>(1);
    assert!(historical.old.contains([0, 1]));
    assert!(!filtered.old.contains([0, 1]));
    assert!(!historical.old.contains([0, 0]));
    assert!(historical.new.contains([0, 0]));
    assert!(filtered.new.contains([0, 0]));
    let old_only = versions.consume_lazy_required::<true, false>(2);
    let new_only = versions.consume_lazy_required::<false, true>(3);
    assert!(old_only.new.is_empty());
    assert!(new_only.old.is_empty());
    assert_eq!(old_only.old.row_count_up_to(10), 1);
    assert_eq!(new_only.new.row_count_up_to(10), 1);
    assert!(versions
        .consume_lazy_required::<true, true>(3)
        .new
        .is_empty());
}
