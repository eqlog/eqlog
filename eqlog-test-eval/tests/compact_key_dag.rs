#![cfg(not(feature = "desugared"))]

use eqlog_runtime::CompiledModel;
use eqlog_test_eval as _;

mod generated {
    include!(concat!(
        env!("EQLOG_OUT_DIR"),
        "/eqlog-test-eval/src/compact_key_dag.eql.rs"
    ));
}

use generated::{CompactKeyDag, El, World, WorldMor};

fn inherit(model: &mut CompactKeyDag, source: World, target: World) -> WorldMor {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.inherit_total_world_members(morphism);
    morphism
}

#[test]
fn ordinary_cycles_propagate_nullary_facts_to_later_components() {
    let mut model = CompactKeyDag::new();
    model.enable_compact_world();
    let [left, right, child] = std::array::from_fn(|_| model.new_world());
    for (source, target) in [(left, right), (right, left), (right, child)] {
        let morphism = model.new_world_mor();
        model.insert_world_mor_dom(morphism, source);
        model.insert_world_mor_cod(morphism, target);
    }
    model.insert_enabled(left);
    model.close();
    for owner in [left, right, child] {
        assert!(model.enabled(owner));
    }
    assert_eq!(model.iter_el().count(), 0);
    assert_eq!(model.iter_world().count(), 3);
    model.close();
    assert!(model.enabled(child));
}

fn named_diamond() -> (CompactKeyDag, [World; 4], [WorldMor; 4], [El; 2]) {
    let mut model = CompactKeyDag::new();
    model.enable_compact_world();
    let owners = std::array::from_fn(|_| model.new_world());
    let [source, left, right, target] = owners;
    let members = std::array::from_fn(|_| {
        let key = model.new_key();
        let member = model.new_el(source);
        model.insert_named(source, member, key);
        member
    });
    let morphisms = [
        inherit(&mut model, source, left),
        inherit(&mut model, source, right),
        inherit(&mut model, left, target),
        inherit(&mut model, right, target),
    ];
    model.close();
    (model, owners, morphisms, members)
}

fn images(model: &CompactKeyDag, morphisms: [WorldMor; 4], member: El) -> [El; 4] {
    let [source_left, source_right, left_target, right_target] = morphisms;
    let left = model.el_mor_app(source_left, member).unwrap();
    let right = model.el_mor_app(source_right, member).unwrap();
    [
        left,
        right,
        model.el_mor_app(left_target, left).unwrap(),
        model.el_mor_app(right_target, right).unwrap(),
    ]
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
    assert_eq!(model.el_mor_app(left_target, right_member), None);
    assert_eq!(model.el_mor_app(right_target, left_member), None);
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
fn parallel_incoming_edges_keep_distinct_unproved_images_after_growth() {
    for witnessed in [false, true] {
        let mut model = CompactKeyDag::new();
        model.enable_compact_world();
        let source = model.new_world();
        let target = model.new_world();
        let key = model.new_key();
        let first = model.new_el(source);
        if witnessed {
            model.insert_named(source, first, key);
        }
        model.insert_left(source, first);
        let morphisms = std::array::from_fn::<_, 3, _>(|_| inherit(&mut model, source, target));
        let primary = model.el_mor_app(morphisms[0], first).unwrap();
        for morphism in &morphisms[1..] {
            assert_eq!(model.el_mor_app(*morphism, first), None);
        }
        model.close();
        let first_images = morphisms.map(|morphism| model.el_mor_app(morphism, first).unwrap());
        assert_eq!(first_images[0], primary);
        for left in 0..morphisms.len() {
            assert!(model.left(target, first_images[left]));
            for right in left + 1..morphisms.len() {
                assert_eq!(
                    model.are_equal_el(first_images[left], first_images[right]),
                    witnessed
                );
            }
        }

        let key = model.new_key();
        let late = model.new_el(source);
        if witnessed {
            model.insert_named(source, late, key);
        }
        model.insert_right(source, late);
        for morphism in morphisms {
            assert_eq!(model.el_mor_app(morphism, late), None);
        }
        model.close();
        let late_images = morphisms.map(|morphism| model.el_mor_app(morphism, late).unwrap());
        for left in 0..morphisms.len() {
            assert!(model.right(target, late_images[left]));
            assert_eq!(
                model.el_mor_app(morphisms[left], first),
                Some(first_images[left])
            );
            for right in left + 1..morphisms.len() {
                assert_eq!(
                    model.are_equal_el(late_images[left], late_images[right]),
                    witnessed
                );
            }
        }
        model.close();
        assert_eq!(
            morphisms.map(|morphism| model.el_mor_app(morphism, late).unwrap()),
            late_images
        );
    }
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

#[test]
fn late_named_members_and_cross_source_facts_reach_existing_joins() {
    let (mut model, [source, left, right, target], morphisms, [first, _]) = named_diamond();
    let original = images(&model, morphisms, first);
    let key = model.new_key();
    let late = model.new_el(source);
    model.insert_named(source, late, key);
    model.close();
    let [left_late, right_late, target_left, target_right] = images(&model, morphisms, late);
    assert!(model.are_equal_el(target_left, target_right));
    model.insert_left(left, left_late);
    model.insert_right(right, right_late);
    model.close();
    assert!(model.joined(target, target_left));
    assert!(!model.joined(source, late));
    assert!(!model.joined(left, left_late));
    assert!(!model.joined(right, right_late));
    assert_eq!(images(&model, morphisms, first), original);
}

#[test]
fn late_bare_overlap_preserves_independent_images_and_existing_handles() {
    let (mut model, [source, _, _, target], morphisms, [first, _]) = named_diamond();
    let original = images(&model, morphisms, first);
    let bare = model.new_el(source);
    model.close();
    let [_, _, target_left, target_right] = images(&model, morphisms, bare);
    assert!(!model.are_equal_el(target_left, target_right));
    assert!(model.world_member_el(target, target_left));
    assert!(model.world_member_el(target, target_right));
    assert_eq!(images(&model, morphisms, first), original);
}

#[test]
fn unequal_paths_do_not_export_an_unadopted_bare_image() {
    for reverse in [false, true] {
        let mut model = CompactKeyDag::new();
        model.enable_compact_world();
        let source = model.new_world();
        let mut branches = [model.new_world(), model.new_world()];
        if reverse {
            branches.reverse();
        }
        let [short, long] = branches;
        let middle = model.new_world();
        let target = model.new_world();
        let key = model.new_key();
        let named = model.new_el(source);
        model.insert_named(source, named, key);
        let to_short = inherit(&mut model, source, short);
        let to_long = inherit(&mut model, source, long);
        let to_middle = inherit(&mut model, long, middle);
        let from_short = inherit(&mut model, short, target);
        let from_middle = inherit(&mut model, middle, target);
        model.close();
        let short_named = model.el_mor_app(to_short, named).unwrap();
        let original = model.el_mor_app(from_short, short_named).unwrap();
        let bare = model.new_el(source);
        model.close();
        let short_bare = model.el_mor_app(to_short, bare).unwrap();
        let long_bare = model.el_mor_app(to_long, bare).unwrap();
        let middle_bare = model.el_mor_app(to_middle, long_bare).unwrap();
        let first_image = model.el_mor_app(from_short, short_bare).unwrap();
        let second_image = model.el_mor_app(from_middle, middle_bare).unwrap();
        assert!(!model.are_equal_el(first_image, second_image));
        assert_eq!(model.el_mor_app(from_short, short_named), Some(original));
    }
}

#[test]
fn staggered_refresh_does_not_publish_an_unadopted_secondary_image() {
    let (mut model, [source, _, _, _], morphisms, _) = named_diamond();
    let [source_left, source_right, left_target, right_target] = morphisms;
    let bare = model.new_el(source);
    assert!(model.inherit_total_world_members(source_left));
    let left_bare = model.el_mor_app(source_left, bare).unwrap();
    assert!(model.inherit_total_world_members(left_target));
    let left_image = model.el_mor_app(left_target, left_bare).unwrap();
    assert!(model.inherit_total_world_members(source_right));
    let right_bare = model.el_mor_app(source_right, bare).unwrap();
    assert_eq!(model.el_mor_app(right_target, right_bare), None);
    let dynamic = model.to_dynamic();
    let restored = CompactKeyDag::from_dynamic(&dynamic).unwrap();
    assert_eq!(restored.el_mor_app(right_target, right_bare), None);
    assert_eq!(
        restored.el_mor_app(left_target, left_bare),
        Some(left_image)
    );
    model.close();
    let right_image = model.el_mor_app(right_target, right_bare).unwrap();
    assert!(!model.are_equal_el(left_image, right_image));
}

#[test]
fn registering_an_existing_primary_refreshes_its_current_images() {
    let mut model = CompactKeyDag::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let first = model.new_el(source);
    let morphism = inherit(&mut model, source, target);
    let original = model.el_mor_app(morphism, first).unwrap();
    let late = model.new_el(source);
    model.insert_left(source, late);
    assert!(model.inherit_total_world_members(morphism));
    let image = model.el_mor_app(morphism, late).unwrap();
    assert!(model.left(target, image));
    assert_eq!(model.el_mor_app(morphism, first), Some(original));
    assert!(!model.inherit_total_world_members(morphism));
}

#[test]
fn source_equality_keeps_both_incoming_maps_live() {
    let (mut model, [source, left, right, target], morphisms, [first, second]) = named_diamond();
    let first_images = images(&model, morphisms, first);
    let second_images = images(&model, morphisms, second);
    model.insert_left(left, first_images[0]);
    model.insert_right(right, second_images[1]);
    model.equate_el(source, first, second);
    model.close();
    for (first, second) in first_images.into_iter().zip(second_images) {
        assert!(model.are_equal_el(first, second));
    }
    assert!(model.joined(target, first_images[2]));
    assert!(model.world_member_el(source, second));
    let key = model.new_key();
    let late = model.new_el(source);
    model.insert_named(source, late, key);
    model.close();
    let [_, _, target_left, target_right] = images(&model, morphisms, late);
    assert!(model.are_equal_el(target_left, target_right));
}

#[test]
fn target_equality_after_partial_close_keeps_pending_function_requests() {
    let (mut model, [source, left, right, target], morphisms, [first, second]) = named_diamond();
    let first_images = images(&model, morphisms, first);
    let second_images = images(&model, morphisms, second);
    let target_first = first_images[2];
    let target_second = second_images[2];
    model.insert_left(target, target_first);
    model.insert_right(target, target_second);
    model.insert_wanted(target, target_second);
    assert!(model.close_until(|model| {
        model.ready(target, target_second) && model.next(target, target_second).is_none()
    }));
    model.equate_el(target, target_first, target_second);
    model.close();
    assert!(model.are_equal_el(target_first, target_second));
    assert!(model.joined(target, target_first));
    let next = model.next(target, target_second).unwrap();
    assert!(model.world_member_el(target, next));
    assert!(!model.world_member_el(source, next));
    assert!(!model.are_equal_el(first, second));
    assert!(!model.are_equal_el(first_images[0], second_images[0]));
    assert!(!model.are_equal_el(first_images[1], second_images[1]));
    assert_eq!(model.next(left, first_images[0]), None);
    assert_eq!(model.next(right, second_images[1]), None);
}

#[test]
fn parallel_named_maps_share_only_images_with_a_uniqueness_witness() {
    let mut model = CompactKeyDag::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let key = model.new_key();
    let member = model.new_el(source);
    model.insert_named(source, member, key);
    let first = inherit(&mut model, source, target);
    let first_image = model.el_mor_app(first, member).unwrap();
    let second = inherit(&mut model, source, target);
    model.close();
    let second_image = model.el_mor_app(second, member).unwrap();
    assert!(model.are_equal_el(first_image, second_image));
    let bare = model.new_el(source);
    model.close();
    let first_bare = model.el_mor_app(first, bare).unwrap();
    let second_bare = model.el_mor_app(second, bare).unwrap();
    assert!(!model.are_equal_el(first_bare, second_bare));
    assert_eq!(model.el_mor_app(first, member), Some(first_image));
    assert!(model.are_equal_el(model.el_mor_app(second, member).unwrap(), second_image));
}

#[test]
fn exporting_before_secondary_adoption_preserves_only_existing_images() {
    let mut model = CompactKeyDag::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let key = model.new_key();
    let member = model.new_el(source);
    model.insert_named(source, member, key);
    let first = inherit(&mut model, source, target);
    let first_image = model.el_mor_app(first, member).unwrap();
    let second = inherit(&mut model, source, target);
    let dynamic = model.to_dynamic();
    let restored = CompactKeyDag::from_dynamic(&dynamic).unwrap();
    assert_eq!(restored.el_mor_app(first, member), Some(first_image));
    assert_eq!(restored.el_mor_app(second, member), None);
    model.close();
    let second_image = model.el_mor_app(second, member).unwrap();
    assert!(model.are_equal_el(first_image, second_image));
}
