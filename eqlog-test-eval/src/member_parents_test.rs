use crate::member_parents::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn membership_rejects_other_parents_before_and_after_closure() {
    for closed in [false, true] {
        let mut model = MemberParents::new();
        let a = model.new_outer();
        let b = model.new_outer();
        let i = model.new_inner(a);
        let j = model.new_inner(a);
        let x = model.new_el(a, i);
        let f = model.new_inner_mor(a);
        let label = model.define_label_value(a, i);
        if closed {
            model.close();
        }

        assert!(catch_unwind(AssertUnwindSafe(|| model.insert_outer_member_inner(b, i))).is_err());
        assert!(catch_unwind(AssertUnwindSafe(|| model.insert_inner_member_el(a, j, x))).is_err());
        assert!(catch_unwind(AssertUnwindSafe(
            || model.insert_outer_member_inner_mor(b, f)
        ))
        .is_err());
        assert!(catch_unwind(AssertUnwindSafe(
            || model.insert_inner_member_label(a, j, label)
        ))
        .is_err());
        model.close();
        assert_eq!(model.iter_outer_member_inner().count(), 2);
        assert_eq!(
            model.iter_inner_member_el().collect::<Vec<_>>(),
            vec![(a, i, x)]
        );
        assert_eq!(
            model.iter_outer_member_inner_mor().collect::<Vec<_>>(),
            vec![(a, f)]
        );
        assert_eq!(
            model.iter_inner_member_label().collect::<Vec<_>>(),
            vec![(a, i, label)]
        );
    }
}

#[test]
fn equality_rejects_other_parents_before_and_after_closure() {
    for closed in [false, true] {
        let mut model = MemberParents::new();
        let a = model.new_outer();
        let b = model.new_outer();
        let i = model.new_inner(a);
        let j = model.new_inner(b);
        let x = model.new_el(a, i);
        let y = model.new_el(b, j);
        let f = model.new_inner_mor(a);
        let g = model.new_inner_mor(b);
        let label0 = model.define_label_value(a, i);
        let label1 = model.define_label_value(b, j);
        if closed {
            model.close();
        }

        assert!(catch_unwind(AssertUnwindSafe(|| model.equate_inner(a, i, j))).is_err());
        assert!(catch_unwind(AssertUnwindSafe(|| model.equate_el(a, i, x, y))).is_err());
        assert!(catch_unwind(AssertUnwindSafe(|| model.equate_inner_mor(a, f, g))).is_err());
        assert!(
            catch_unwind(AssertUnwindSafe(|| model.equate_label(a, i, label0, label1))).is_err()
        );
        assert!(!model.are_equal_inner(i, j));
        assert!(!model.are_equal_el(x, y));
        assert!(!model.are_equal_inner_mor(f, g));
        assert!(!model.are_equal_label(label0, label1));
        model.close();
    }
}

#[test]
fn invalid_constructor_does_not_allocate_an_element() {
    let mut model = MemberParents::new();
    let a = model.new_outer();
    let b = model.new_outer();
    let i = model.new_inner(a);
    assert!(catch_unwind(AssertUnwindSafe(|| model.new_el(b, i))).is_err());
    assert_eq!(model.iter_el().count(), 0);
    model.close();
}

#[test]
fn parent_equalities_take_effect_before_indices_are_rebuilt() {
    let mut model = MemberParents::new();
    let a = model.new_outer();
    let b = model.new_outer();
    let i = model.new_inner(a);
    let j = model.new_inner(b);
    let x = model.new_el(a, i);
    let y = model.new_el(b, j);
    model.close();

    model.equate_outer(a, b);
    assert!(catch_unwind(AssertUnwindSafe(|| model.equate_el(a, i, x, y))).is_err());
    model.equate_inner(b, i, j);
    model.equate_el(b, j, x, y);
    model.insert_outer_member_inner(b, j);
    model.insert_inner_member_el(b, j, y);
    model.new_el(b, j);
    model.close();
    assert_eq!(model.iter_outer_member_inner().count(), 1);
    assert_eq!(model.iter_inner_member_el().count(), 2);
    for (outer, inner, el) in model.iter_inner_member_el() {
        assert_eq!(outer, model.root_outer(a));
        assert_eq!(inner, model.root_inner(i));
        assert_eq!(el, model.root_el(el));
    }
}

#[test]
fn membership_checks_follow_either_representative_without_rewriting_rows() {
    for closed in [false, true] {
        for reverse in [false, true] {
            let mut model = MemberParents::new();
            let a = model.new_outer();
            let b = model.new_outer();
            let i = model.new_inner(a);
            let j = model.new_inner(b);
            let x = model.new_el(a, i);
            let y = model.new_el(b, j);
            if closed {
                model.close();
            }
            let rows: Vec<_> = model.iter_inner_member_el().collect();
            let (outer, other_outer, inner, other_inner, el, other_el) = if reverse {
                (b, a, j, i, y, x)
            } else {
                (a, b, i, j, x, y)
            };

            model.equate_outer(outer, other_outer);
            assert_eq!(model.root_outer(a), outer);
            assert!(model.outer_member_inner(a, j));
            assert!(model.outer_member_inner(b, i));
            model.equate_inner(other_outer, inner, other_inner);
            assert_eq!(model.root_inner(i), inner);
            assert!(model.inner_member_el(a, i, y));
            assert!(model.inner_member_el(b, j, x));
            model.equate_el(other_outer, other_inner, el, other_el);
            assert_eq!(model.root_el(x), el);
            assert!(model.inner_member_el(a, i, y));
            assert!(model.inner_member_el(b, j, x));
            assert_eq!(model.iter_inner_member_el().collect::<Vec<_>>(), rows);

            model.close();
            assert_eq!(
                model.iter_inner_member_el().collect::<Vec<_>>(),
                vec![(outer, inner, el)]
            );
        }
    }
}

#[test]
fn stale_membership_index_rows_do_not_allow_other_owners() {
    let mut model = MemberParents::new();
    let a = model.new_outer();
    let b = model.new_outer();
    let c = model.new_outer();
    let i = model.new_inner(a);
    let j = model.new_inner(b);
    let k = model.new_inner(c);
    let x = model.new_el(a, i);
    let y = model.new_el(b, j);
    let z = model.new_el(c, k);
    model.close();

    model.equate_outer(b, a);
    model.equate_inner(a, j, i);
    model.equate_el(a, i, y, x);
    model.close();
    model.equate_outer(c, b);
    model.equate_inner(b, k, j);
    model.equate_el(b, j, z, y);

    let unrelated = model.new_outer();
    let other_inner = model.new_inner(c);
    let before: Vec<_> = model.iter_inner_member_el().collect();
    assert!(catch_unwind(AssertUnwindSafe(|| model.new_el(unrelated, i))).is_err());
    for (outer, inner) in [(unrelated, i), (c, other_inner)] {
        assert!(catch_unwind(AssertUnwindSafe(|| {
            model.insert_inner_member_el(outer, inner, x);
        }))
        .is_err());
    }
    assert_eq!(model.iter_inner_member_el().collect::<Vec<_>>(), before);
    assert_eq!(model.iter_el().count(), 1);
    assert!(model.inner_member_el(a, i, x));
    assert!(model.inner_member_el(b, j, y));
    assert!(model.inner_member_el(c, k, z));
    model.close();
    assert_eq!(model.iter_inner_member_el().count(), 1);
}

#[test]
fn membership_insertion_rejects_unallocated_members_before_mutation() {
    let mut model = MemberParents::new();
    let a = model.new_outer();
    let i = model.new_inner(a);
    let x = model.new_el(a, i);
    assert!(catch_unwind(AssertUnwindSafe(|| {
        model.insert_inner_member_el(a, i, El(x.0 + 1));
    }))
    .is_err());
    model.close();
    assert_eq!(model.iter_el().collect::<Vec<_>>(), vec![x]);
    assert_eq!(
        model.iter_inner_member_el().collect::<Vec<_>>(),
        vec![(a, i, x)]
    );
}

#[test]
fn equality_checks_both_members_against_the_supplied_parents() {
    for closed in [false, true] {
        let mut model = MemberParents::new();
        let a = model.new_outer();
        let b = model.new_outer();
        let i = model.new_inner(a);
        let j = model.new_inner(a);
        let x = model.new_el(a, i);
        let y = model.new_el(a, i);
        let z = model.new_el(a, j);
        if closed {
            model.close();
        }

        for (outer, inner, lhs, rhs) in [
            (b, i, x, y),
            (a, j, x, y),
            (a, i, x, z),
            (a, i, z, x),
            (b, i, x, x),
        ] {
            assert!(catch_unwind(AssertUnwindSafe(|| {
                model.equate_el(outer, inner, lhs, rhs);
            }))
            .is_err());
            assert_eq!(model.iter_el().count(), 3);
            assert!(!model.are_equal_el(x, y));
            assert!(!model.are_equal_el(x, z));
        }

        model.equate_el(a, i, x, y);
        assert!(model.are_equal_el(x, y));
        assert!(catch_unwind(AssertUnwindSafe(|| model.equate_el(a, j, x, y))).is_err());
        assert_eq!(model.iter_el().count(), 2);
        model.close();
        assert_eq!(model.iter_inner_member_el().count(), 2);
    }
}

#[test]
fn rule_equalities_merge_parents_before_members() {
    let mut model = MemberParents::new();
    let a = model.new_outer();
    let b = model.new_outer();
    let i = model.new_inner(a);
    let j = model.new_inner(b);
    let x = model.new_el(a, i);
    let y = model.new_el(b, j);
    model.insert_merge(a, b);
    model.close();
    assert!(model.are_equal_outer(a, b));
    assert!(model.are_equal_inner(i, j));
    assert!(model.are_equal_el(x, y));
    assert_eq!(model.iter_inner_member_el().count(), 1);
}

#[test]
fn morphism_congruence_preserves_unique_ownership_during_closure() {
    let mut model = MemberParents::new();
    let source = model.new_outer();
    let other_target = model.new_outer();
    let target = model.new_outer();
    let i0 = model.new_inner(source);
    let i1 = model.new_inner(source);
    let j0 = model.new_inner(target);
    let j1 = model.new_inner(target);
    let g = model.new_inner_mor(source);
    model.insert_inner_mor_dom(source, g, i0);
    model.insert_inner_mor_cod(source, g, i1);
    let image_g = model.new_inner_mor(target);
    let h = model.new_outer_mor();
    model.insert_outer_mor_dom(h, source);
    model.insert_outer_mor_cod(h, target);
    model.insert_inner_mor_app(h, i0, j0);
    model.insert_inner_mor_app(h, i1, j1);
    model.insert_inner_mor_mor_app(h, g, image_g);
    model.close();

    model.insert_outer_mor_cod(h, other_target);
    model.close_until(|model| {
        assert_eq!(
            model.iter_outer_member_inner().count(),
            model.iter_inner().count()
        );
        assert_eq!(
            model.iter_outer_member_inner_mor().count(),
            model.iter_inner_mor().count()
        );
        false
    });
    assert!(model.are_equal_outer(target, other_target));
    assert_eq!(model.inner_mor_dom(target, image_g), Some(j0));
    assert_eq!(model.inner_mor_cod(target, image_g), Some(j1));
}
