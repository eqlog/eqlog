#![cfg(not(feature = "desugared"))]

mod generated {
    include!(concat!(
        env!("EQLOG_OUT_DIR"),
        "/tests/compact_functionality.eql.rs"
    ));

    pub fn checked(model: &CompactFunctionality, owner: World) -> bool {
        model.__compact_is_checked_item(owner.0)
    }

    pub fn try_normalize(model: &mut CompactFunctionality, owner: World) -> Option<bool> {
        model.__compact_normalize_item(owner.0)
    }
}

use generated::{checked, try_normalize, CompactFunctionality, World, WorldMor};

fn inherit(model: &mut CompactFunctionality, source: World, target: World) -> WorldMor {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.inherit_total_world_members(morphism);
    morphism
}

#[test]
fn conflicting_local_keys_wait_for_close_and_keep_siblings_distinct() {
    let mut model = CompactFunctionality::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let sibling = model.new_world();
    let child = model.new_world();
    let key = model.new_key();
    let source_value = model.new_el(source);
    model.insert_item(source, key, source_value);
    model.insert_marked(source, source_value);
    model.close();
    assert!(checked(&model, source));
    let to_target = inherit(&mut model, source, target);
    let to_sibling = inherit(&mut model, source, sibling);
    let target_image = model.el_mor_app(to_target, source_value).unwrap();
    let sibling_image = model.el_mor_app(to_sibling, source_value).unwrap();
    let local = model.new_el(target);
    model.insert_item(target, key, local);
    let to_child = inherit(&mut model, target, child);
    let child_image = model.el_mor_app(to_child, target_image).unwrap();
    let child_local = model.el_mor_app(to_child, local).unwrap();
    assert!(!model.are_equal_el(target_image, local));
    assert!(!model.are_equal_el(child_image, child_local));
    model.close();
    assert!(model.are_equal_el(target_image, local));
    assert!(model.are_equal_el(child_image, child_local));
    assert!(checked(&model, target));
    assert!(checked(&model, child));
    assert_eq!(model.item(sibling, key), Some(sibling_image));
    assert!(model.observed(target, local));
    assert!(model.observed(child, child_local));
    assert!(model.observed(sibling, sibling_image));
    assert!(!model.are_equal_el(source_value, sibling_image));
}

#[test]
fn late_parent_key_collision_rechecks_local_support() {
    let mut model = CompactFunctionality::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let key = model.new_key();
    let local = model.new_el(target);
    model.insert_item(target, key, local);
    let morphism = inherit(&mut model, source, target);
    model.close();
    assert!(checked(&model, target));
    let source_value = model.new_el(source);
    model.insert_item(source, key, source_value);
    assert!(!checked(&model, source));
    model.close();
    let image = model.el_mor_app(morphism, source_value).unwrap();
    assert!(model.are_equal_el(local, image));
    assert!(checked(&model, target));
}

#[test]
fn range_equality_preserves_valid_certificates_only() {
    let mut model = CompactFunctionality::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let first_key = model.new_key();
    let second_key = model.new_key();
    let left = model.new_el(source);
    let right = model.new_el(source);
    model.insert_item(source, first_key, left);
    model.insert_item(source, second_key, right);
    model.close();
    let morphism = inherit(&mut model, source, target);
    model.close();
    let left_image = model.el_mor_app(morphism, left).unwrap();
    let right_image = model.el_mor_app(morphism, right).unwrap();
    model.equate_el(source, left, right);
    assert!(checked(&model, source));
    model.close();
    assert!(model.are_equal_el(left_image, right_image));
    assert!(checked(&model, target));
    let conflict = model.new_el(source);
    model.insert_item(source, first_key, conflict);
    assert!(!checked(&model, source));
    let other = model.new_el(source);
    model.equate_el(source, conflict, other);
    assert!(!checked(&model, source));
    model.close();
    assert!(model.are_equal_el(left, conflict));
}

#[test]
fn missing_source_certificate_falls_back_and_partial_close_resumes() {
    let mut model = CompactFunctionality::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let key = model.new_key();
    let left = model.new_el(source);
    let right = model.new_el(source);
    model.insert_item(source, key, left);
    model.insert_item(source, key, right);
    let morphism = inherit(&mut model, source, target);
    let left_image = model.el_mor_app(morphism, left).unwrap();
    let right_image = model.el_mor_app(morphism, right).unwrap();
    assert_eq!(try_normalize(&mut model, target), None);
    assert!(!model.are_equal_el(left, right));
    assert!(!model.are_equal_el(left_image, right_image));
    assert!(model.close_until(|model| model.are_equal_el(left, right)));
    assert!(checked(&model, source));
    model.close();
    assert!(model.are_equal_el(left_image, right_image));
    assert!(checked(&model, target));
}

#[test]
fn member_argument_quotients_keep_full_collision_checks() {
    let mut model = CompactFunctionality::new();
    model.enable_compact_argument_world();
    let source = model.new_argument_world();
    let target = model.new_argument_world();
    let left = model.new_arg(source);
    let right = model.new_arg(source);
    let left_result = model.new_arg(source);
    let right_result = model.new_arg(source);
    model.insert_next(source, left, left_result);
    model.insert_next(source, right, right_result);
    model.close();
    let morphism = model.new_argument_world_mor();
    model.insert_argument_world_mor_dom(morphism, source);
    model.insert_argument_world_mor_cod(morphism, target);
    model.inherit_total_argument_world_members(morphism);
    let left_image = model.arg_mor_app(morphism, left).unwrap();
    let right_image = model.arg_mor_app(morphism, right).unwrap();
    let left_result_image = model.arg_mor_app(morphism, left_result).unwrap();
    let right_result_image = model.arg_mor_app(morphism, right_result).unwrap();
    model.equate_arg(target, left_image, right_image);
    assert!(!model.are_equal_arg(left_result_image, right_result_image));
    model.close();
    assert!(model.are_equal_arg(left_result_image, right_result_image));
    assert!(!model.are_equal_arg(left_result, right_result));
}

#[test]
fn stale_source_certificates_do_not_authorize_inherited_checks() {
    let mut model = CompactFunctionality::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let key = model.new_key();
    let left = model.new_el(source);
    let right = model.new_el(source);
    model.insert_item(source, key, left);
    model.close();
    inherit(&mut model, source, target);
    model.insert_item(source, key, right);
    assert!(!checked(&model, source));
    assert_eq!(try_normalize(&mut model, target), None);
    assert!(!model.are_equal_el(left, right));
    model.close();
    assert!(model.are_equal_el(left, right));
    assert!(checked(&model, source));
    assert!(checked(&model, target));
}

#[test]
fn nullary_function_checks_the_single_local_domain() {
    let mut model = CompactFunctionality::new();
    model.enable_compact_nullary_world();
    let source = model.new_nullary_world();
    let target = model.new_nullary_world();
    let source_value = model.new_nullary_el(source);
    model.insert_point(source, source_value);
    model.close();
    let morphism = model.new_nullary_world_mor();
    model.insert_nullary_world_mor_dom(morphism, source);
    model.insert_nullary_world_mor_cod(morphism, target);
    model.inherit_total_nullary_world_members(morphism);
    let image = model.nullary_el_mor_app(morphism, source_value).unwrap();
    let local = model.new_nullary_el(target);
    model.insert_point(target, local);
    assert!(!model.are_equal_nullary_el(image, local));
    model.close();
    assert!(model.are_equal_nullary_el(image, local));
}

#[test]
fn multiple_domain_columns_keep_unrelated_keys_distinct() {
    let mut model = CompactFunctionality::new();
    model.enable_compact_pair_world();
    let source = model.new_pair_world();
    let target = model.new_pair_world();
    let first_key = model.new_key();
    let second_key = model.new_key();
    let third_key = model.new_key();
    let source_value = model.new_pair_el(source);
    model.insert_pair(source, first_key, second_key, source_value);
    model.close();
    let morphism = model.new_pair_world_mor();
    model.insert_pair_world_mor_dom(morphism, source);
    model.insert_pair_world_mor_cod(morphism, target);
    model.inherit_total_pair_world_members(morphism);
    let image = model.pair_el_mor_app(morphism, source_value).unwrap();
    let local = model.new_pair_el(target);
    let unrelated = model.new_pair_el(target);
    model.insert_pair(target, first_key, second_key, local);
    model.insert_pair(target, first_key, third_key, unrelated);
    assert!(!model.are_equal_pair_el(image, local));
    model.close();
    assert!(model.are_equal_pair_el(image, local));
    assert!(!model.are_equal_pair_el(local, unrelated));
    assert_eq!(model.pair(target, first_key, third_key), Some(unrelated));
}
