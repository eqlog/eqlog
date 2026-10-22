#![cfg(not(feature = "desugared"))]

use eqlog_test_eval as _;

mod generated {
    include!(concat!(
        env!("EQLOG_OUT_DIR"),
        "/eqlog-test-eval/src/compact_shared_types.eql.rs"
    ));
}

use generated::{CompactSharedTypes, World, WorldMor};

fn inherit(model: &mut CompactSharedTypes, source: World, target: World) -> WorldMor {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.inherit_total_world_members(morphism);
    morphism
}

#[test]
fn incoming_images_require_proofs_for_every_member_type() {
    for witness_second in [false, true] {
        let mut model = CompactSharedTypes::new();
        model.enable_compact_world();
        let source = model.new_world();
        let left = model.new_world();
        let right = model.new_world();
        let target = model.new_world();
        let key = model.new_key();
        let first = model.new_first(source);
        let second = model.new_second(source);
        model.insert_named_first(source, key, first);
        if witness_second {
            model.insert_named_second(source, key, second);
        }
        let source_left = inherit(&mut model, source, left);
        let source_right = inherit(&mut model, source, right);
        let first_left = model.first_mor_app(source_left, first).unwrap();
        let second_left = model.second_mor_app(source_left, second).unwrap();
        let first_right = model.first_mor_app(source_right, first).unwrap();
        let second_right = model.second_mor_app(source_right, second).unwrap();
        model.insert_left(left, first_left, second_left);
        model.insert_right(right, first_right, second_right);
        let left_target = inherit(&mut model, left, target);
        let right_target = inherit(&mut model, right, target);
        assert_eq!(model.first_mor_app(right_target, first_right), None);
        assert_eq!(model.second_mor_app(right_target, second_right), None);
        model.close();
        let first_target = model.first_mor_app(left_target, first_left).unwrap();
        let second_target = model.second_mor_app(left_target, second_left).unwrap();
        let other_first = model.first_mor_app(right_target, first_right).unwrap();
        let other_second = model.second_mor_app(right_target, second_right).unwrap();
        assert!(model.are_equal_first(first_target, other_first));
        assert_eq!(
            model.are_equal_second(second_target, other_second),
            witness_second
        );
        assert!(model.left(target, first_target, second_target));
        assert!(model.right(target, other_first, other_second));
        assert_eq!(
            model.joined(target, first_target, second_target),
            witness_second
        );
        assert_eq!(
            model.joined(target, other_first, other_second),
            witness_second
        );
        assert!(!model.joined(left, first_left, second_left));
        assert!(!model.joined(right, first_right, second_right));
    }
}
