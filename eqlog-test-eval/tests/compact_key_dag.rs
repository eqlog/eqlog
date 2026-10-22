#![cfg(not(feature = "desugared"))]

use eqlog_test_eval as _;

mod generated {
    include!(concat!(
        env!("EQLOG_OUT_DIR"),
        "/eqlog-test-eval/src/compact_key_dag.eql.rs"
    ));
}

use generated::{CompactKeyDag, World, WorldMor};

fn inherit(model: &mut CompactKeyDag, source: World, target: World) -> WorldMor {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.inherit_total_world_members(morphism);
    morphism
}

#[test]
fn predicate_uniqueness_preserves_mixed_incoming_matches() {
    let mut model = CompactKeyDag::new();
    model.enable_compact_world();
    let source = model.new_world();
    let left = model.new_world();
    let right = model.new_world();
    let target = model.new_world();
    let key = model.new_key();
    let member = model.new_el(source);
    model.insert_named(source, member, key);
    let source_left = inherit(&mut model, source, left);
    let source_right = inherit(&mut model, source, right);
    let left_member = model.el_mor_app(source_left, member).unwrap();
    let right_member = model.el_mor_app(source_right, member).unwrap();
    model.insert_left(left, left_member);
    model.insert_right(right, right_member);
    let left_target = inherit(&mut model, left, target);
    let left_image = model.el_mor_app(left_target, left_member).unwrap();
    let right_target = inherit(&mut model, right, target);
    assert_eq!(model.el_mor_app(right_target, right_member), None);
    model.close();
    let right_image = model.el_mor_app(right_target, right_member).unwrap();
    assert!(model.are_equal_el(left_image, right_image));
    assert!(model.joined(target, right_image));
    assert!(!model.joined(left, left_member));
    assert!(!model.joined(right, right_member));
    assert!(!model.are_equal_el(left_member, right_member));
}

#[test]
fn guarded_uniqueness_does_not_identify_independent_images() {
    let mut model = CompactKeyDag::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let key = model.new_key();
    let member = model.new_el(source);
    model.insert_conditional(source, key, member);
    let first = inherit(&mut model, source, target);
    let first_image = model.el_mor_app(first, member).unwrap();
    let second = inherit(&mut model, source, target);
    model.close();
    let second_image = model.el_mor_app(second, member).unwrap();
    assert!(!model.are_equal_el(first_image, second_image));
    model.insert_enabled(target);
    model.close();
    assert!(model.are_equal_el(first_image, second_image));
}

#[test]
fn unrelated_witnesses_do_not_make_a_diamond_commute() {
    let mut model = CompactKeyDag::new();
    model.enable_compact_world();
    let source = model.new_world();
    let left = model.new_world();
    let right = model.new_world();
    let target = model.new_world();
    let first_key = model.new_key();
    let second_key = model.new_key();
    let member = model.new_el(source);
    let source_left = inherit(&mut model, source, left);
    let source_right = inherit(&mut model, source, right);
    let left_member = model.el_mor_app(source_left, member).unwrap();
    let right_member = model.el_mor_app(source_right, member).unwrap();
    model.insert_named(left, left_member, first_key);
    model.insert_named(right, right_member, second_key);
    model.insert_left(left, left_member);
    model.insert_right(right, right_member);
    let left_target = inherit(&mut model, left, target);
    let right_target = inherit(&mut model, right, target);
    model.close();
    let left_image = model.el_mor_app(left_target, left_member).unwrap();
    let right_image = model.el_mor_app(right_target, right_member).unwrap();
    assert!(!model.are_equal_el(left_image, right_image));
    assert!(!model.joined(target, left_image));
    assert!(!model.joined(target, right_image));
    assert!(model.named(target, left_image, first_key));
    assert!(model.named(target, right_image, second_key));
}
