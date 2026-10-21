use std::panic::{catch_unwind, AssertUnwindSafe};

use eqlog_runtime::CompiledModel;

use crate::compact_member_views::{CompactMemberViews, World, WorldMor};

fn inherit(model: &mut CompactMemberViews, source: World, target: World) -> WorldMor {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.inherit_total_world_members(morphism);
    morphism
}

#[test]
fn copied_global_equality_keeps_total_inheritance_live() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let first = model.new_el(source);
    let left = model.new_label();
    let right = model.new_label();
    model.insert_tagged(source, first, left);
    let morphism = inherit(&mut model, source, target);
    model.close();
    let first_image = model.el_mor_app(morphism, first).unwrap();
    model.equate_label(left, right);
    let late = model.new_el(source);
    model.insert_tagged(source, late, right);
    model.close();
    let late_image = model.el_mor_app(morphism, late).unwrap();
    assert!(model.tagged(target, first_image, right));
    assert!(model.tagged(target, late_image, left));
    assert_eq!(model.iter_el().count(), 4);
}

#[test]
fn acyclic_owner_merge_keeps_future_images_and_distinct_members() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let first_source = model.new_world();
    let second_source = model.new_world();
    let first_target = model.new_world();
    let second_target = model.new_world();
    let first = model.new_el(first_source);
    let second = model.new_el(second_source);
    let first_morphism = inherit(&mut model, first_source, first_target);
    let second_morphism = inherit(&mut model, second_source, second_target);
    model.close();
    let first_image = model.el_mor_app(first_morphism, first).unwrap();
    let second_image = model.el_mor_app(second_morphism, second).unwrap();
    model.equate_world(first_target, second_target);
    model.close();
    assert!(!model.are_equal_el(first_image, second_image));
    let late = model.new_el(first_source);
    model.close();
    let late_image = model.el_mor_app(first_morphism, late).unwrap();
    assert!(model.world_member_el(second_target, late_image));
}

#[test]
fn an_unregistered_edge_closes_with_ordinary_partial_maps() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let member = model.new_el(source);
    let image = model.new_el(target);
    let label = model.new_label();
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.close();
    assert_eq!(model.el_mor_app(morphism, member), None);
    model.insert_el_mor_app(morphism, member, image);
    model.insert_tagged(source, member, label);
    model.close();
    assert!(model.tagged(target, image, label));
    let late = model.new_el(source);
    model.close();
    assert_eq!(model.el_mor_app(morphism, late), None);
}

#[test]
fn dynamic_export_keeps_unpropagated_source_alias_images() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let left = model.new_el(source);
    let right = model.new_el(source);
    let label = model.new_label();
    model.insert_tagged(source, right, label);
    let morphism = inherit(&mut model, source, target);
    let left_image = model.el_mor_app(morphism, left).unwrap();
    let right_image = model.el_mor_app(morphism, right).unwrap();
    model.equate_el(source, left, right);
    let dynamic = model.to_dynamic();
    let mut restored = CompactMemberViews::from_dynamic(&dynamic).unwrap();
    restored.close();
    assert!(restored.are_equal_el(left_image, right_image));
    assert!(restored.tagged(target, left_image, label));
    assert!(restored.world_member_el(source, right));
}

#[test]
fn total_cycles_are_rejected_before_owner_equality() {
    for materialized in [false, true] {
        let mut model = CompactMemberViews::new();
        model.enable_compact_world();
        let source = model.new_world();
        let target = model.new_world();
        let member = model.new_el(source);
        let morphism = inherit(&mut model, source, target);
        model.close();
        let image = model.el_mor_app(morphism, member).unwrap();
        if materialized {
            let left = model.new_label();
            let right = model.new_label();
            model.equate_label(left, right);
        }
        let rejected = match catch_unwind(AssertUnwindSafe(|| model.equate_world(source, target))) {
            Ok(()) => false,
            Err(_) => true,
        };
        assert!(rejected);
        assert!(!model.are_equal_world(source, target));
        assert_eq!(model.el_mor_app(morphism, member), Some(image));
    }
}

#[test]
fn scoped_functionality_keeps_member_outputs_in_the_owner_namespace() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let unused = model.new_world();
    let owner = model.new_world();
    model.new_el(unused);
    let member = model.new_el(owner);
    let left = model.new_el(owner);
    let right = model.new_el(owner);
    let label = model.new_label();
    model.insert_class_image(owner, member, left);
    model.insert_class_image(owner, member, right);
    model.insert_tagged(owner, right, label);
    model.close();
    assert!(model.are_equal_el(left, right));
    assert!(model.tagged(owner, left, label));
}

#[test]
fn total_cycles_are_rejected_before_morphism_equality() {
    for materialized in [false, true] {
        let mut model = CompactMemberViews::new();
        model.enable_compact_world();
        let source = model.new_world();
        let middle = model.new_world();
        let target = model.new_world();
        let member = model.new_el(source);
        let first = inherit(&mut model, source, middle);
        let second = inherit(&mut model, middle, target);
        model.close();
        if materialized {
            let left = model.new_label();
            let right = model.new_label();
            model.equate_label(left, right);
        }
        let rejected =
            match catch_unwind(AssertUnwindSafe(|| model.equate_world_mor(first, second))) {
                Ok(()) => false,
                Err(_) => true,
            };
        assert!(rejected);
        assert!(!model.are_equal_world_mor(first, second));
        assert!(!model.are_equal_world(source, middle));
        assert!(!model.are_equal_world(middle, target));
        model.close();
        let image = model.el_mor_app(first, member).unwrap();
        assert!(model.el_mor_app(second, image).is_some());
    }
}

#[test]
fn parallel_total_morphism_equality_keeps_future_images() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let member = model.new_el(source);
    let first = inherit(&mut model, source, target);
    let second = inherit(&mut model, source, target);
    model.close();
    let first_image = model.el_mor_app(first, member).unwrap();
    let second_image = model.el_mor_app(second, member).unwrap();
    model.equate_world_mor(first, second);
    model.close();
    assert!(model.are_equal_el(first_image, second_image));
    let late = model.new_el(source);
    model.close();
    assert_eq!(
        model.el_mor_app(first, late),
        model.el_mor_app(second, late)
    );
    assert!(model.el_mor_app(first, late).is_some());
}

#[test]
fn total_endpoint_changes_preflight_owner_merges() {
    for materialized in [false, true] {
        let mut model = CompactMemberViews::new();
        model.enable_compact_world();
        let source = model.new_world();
        let target = model.new_world();
        let other = model.new_world();
        let member = model.new_el(source);
        let morphism = inherit(&mut model, source, target);
        model.close();
        if materialized {
            let left = model.new_label();
            let right = model.new_label();
            model.equate_label(left, right);
        }
        let rejected = match catch_unwind(AssertUnwindSafe(|| {
            model.insert_world_mor_cod(morphism, source)
        })) {
            Ok(()) => false,
            Err(_) => true,
        };
        assert!(rejected);
        assert_eq!(model.world_mor_cod(morphism), Some(target));
        model.insert_world_mor_cod(morphism, other);
        model.close();
        assert!(model.are_equal_world(target, other));
        let image = model.el_mor_app(morphism, member).unwrap();
        assert!(model.world_member_el(other, image));
        let late = model.new_el(source);
        model.close();
        let late_image = model.el_mor_app(morphism, late).unwrap();
        assert!(model.world_member_el(other, late_image));
    }
}

#[test]
fn total_cycle_checks_include_pending_endpoint_equalities() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let outside = model.new_world();
    let first = model.new_world();
    let second = model.new_world();
    let middle = model.new_world();
    let last = model.new_world();
    let incoming = inherit(&mut model, outside, first);
    inherit(&mut model, second, middle);
    let outgoing = inherit(&mut model, middle, last);
    model.close();
    model.insert_world_mor_cod(incoming, second);
    let rejected = match catch_unwind(AssertUnwindSafe(|| {
        model.insert_world_mor_cod(outgoing, first)
    })) {
        Ok(()) => false,
        Err(_) => true,
    };
    assert!(rejected);
    assert_eq!(model.world_mor_cod(outgoing), Some(last));
    model.close();
    assert!(model.are_equal_world(first, second));
    assert!(!model.are_equal_world(first, last));
}

#[test]
fn total_registration_rejects_cyclic_ambiguous_endpoints() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let member = model.new_el(source);
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_dom(morphism, target);
    model.insert_world_mor_cod(morphism, target);
    let rejected = match catch_unwind(AssertUnwindSafe(|| {
        model.inherit_total_world_members(morphism)
    })) {
        Ok(_) => false,
        Err(_) => true,
    };
    assert!(rejected);
    assert!(!model.are_equal_world(source, target));
    assert_eq!(model.el_mor_app(morphism, member), None);
    model.close();
    assert!(model.are_equal_world(source, target));
    assert_eq!(model.el_mor_app(morphism, member), None);
}

#[test]
fn acyclic_ambiguous_endpoints_keep_both_sources_live() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let source = model.new_world();
    let other = model.new_world();
    let target = model.new_world();
    let first = model.new_el(source);
    let second = model.new_el(other);
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_dom(morphism, other);
    model.insert_world_mor_cod(morphism, target);
    model.inherit_total_world_members(morphism);
    model.close();
    assert!(model.are_equal_world(source, other));
    let first_image = model.el_mor_app(morphism, first).unwrap();
    let second_image = model.el_mor_app(morphism, second).unwrap();
    assert!(!model.are_equal_el(first_image, second_image));
    let late = model.new_el(other);
    model.close();
    let late_image = model.el_mor_app(morphism, late).unwrap();
    assert!(model.world_member_el(target, late_image));
}
