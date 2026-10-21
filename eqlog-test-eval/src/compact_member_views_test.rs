use std::collections::BTreeSet;

use crate::compact_member_views::{CompactMemberViews, El, World, WorldMor};

fn inherit(model: &mut CompactMemberViews, source: World, target: World) -> WorldMor {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.inherit_total_world_members(morphism);
    morphism
}

#[test]
fn compact_public_views_keep_owner_handles_and_local_quotients() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let sibling = model.new_world();
    let first = model.new_el(source);
    let second = model.new_el(source);
    let label = model.new_label();
    model.insert_tagged(source, first, label);
    model.insert_tagged(source, second, label);
    model.insert_labelled_edge(source, first, label, second);
    let to_target = inherit(&mut model, source, target);
    let to_sibling = inherit(&mut model, source, sibling);
    let target_first = model.el_mor_app(to_target, first).unwrap();
    let target_second = model.el_mor_app(to_target, second).unwrap();
    let sibling_first = model.el_mor_app(to_sibling, first).unwrap();
    let sibling_second = model.el_mor_app(to_sibling, second).unwrap();
    model.equate_el(target, target_first, target_second);
    model.close();

    assert!(model.are_equal_el(target_first, target_second));
    assert!(!model.are_equal_el(first, second));
    assert!(!model.are_equal_el(sibling_first, sibling_second));
    assert!(!model.tagged(target, first, label));
    assert!(!model.tagged(target, El(u32::MAX), label));
    assert!(!model.world_member_el(target, first));
    assert!(model.world_member_el(target, target_second));
    assert!(model.labelled_edge(target, target_second, label, target_first));

    let expected = BTreeSet::from([
        (source, first, label),
        (source, second, label),
        (target, model.root_el(target_first), label),
        (sibling, sibling_first, label),
        (sibling, sibling_second, label),
    ]);
    let rows: Vec<_> = model.iter_tagged().collect();
    assert_eq!(rows.len(), expected.len());
    assert_eq!(rows.into_iter().collect::<BTreeSet<_>>(), expected);

    let late = model.new_label();
    model.insert_tagged(source, second, late);
    model.close();
    assert!(model.tagged(target, target_first, late));
    assert!(model.tagged(sibling, sibling_second, late));
    assert!(!model.tagged(sibling, sibling_first, late));

    let third = model.new_el(source);
    model.insert_tagged(source, third, late);
    model.equate_el(source, first, second);
    model.close();
    let target_third = model.el_mor_app(to_target, third).unwrap();
    assert!(model.tagged(target, target_third, late));
    assert!(model.are_equal_el(sibling_first, sibling_second));
    assert!(model
        .iter_tagged()
        .all(|(_, member, _)| model.root_el(member) == member));
}

#[test]
fn compact_activation_preserves_preexisting_handles() {
    let mut model = CompactMemberViews::new();
    let world = model.new_world();
    let first = model.new_el(world);
    let second = model.new_el(world);
    let label = model.new_label();
    model.insert_tagged(world, first, label);
    model.equate_el(world, first, second);
    model.close();
    model.enable_compact_world();
    assert!(model.tagged(world, first, label));
    assert!(model.tagged(world, second, label));
    assert!(model.world_member_el(world, first));
    assert!(model.are_equal_el(first, second));
    model.close();
    assert_eq!(model.iter_tagged().count(), 1);
}

#[test]
fn compact_function_queries_translate_arguments_and_results() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let first = model.new_el(source);
    let second = model.new_el(source);
    let label = model.new_label();
    model.insert_class_image(source, first, second);
    model.insert_class_image(source, second, second);
    model.insert_item(source, label, second);
    let morphism = inherit(&mut model, source, target);
    let target_first = model.el_mor_app(morphism, first).unwrap();
    let target_second = model.el_mor_app(morphism, second).unwrap();
    model.close();
    assert_eq!(model.class_image(target, target_first), Some(target_second));
    assert_eq!(model.class_image(target, first), None);
    assert_eq!(model.class_image(target, El(u32::MAX)), None);
    assert_eq!(model.item(target, label), Some(target_second));
    model.equate_el(target, target_first, target_second);
    model.close();
    assert_eq!(
        model.class_image(target, target_second),
        Some(model.root_el(target_first))
    );
    assert_eq!(model.item(target, label), Some(model.root_el(target_first)));
    assert_eq!(
        model.iter_item().collect::<BTreeSet<_>>(),
        BTreeSet::from([
            (source, label, second),
            (target, label, model.root_el(target_first)),
        ])
    );
}

#[test]
fn distinct_total_morphisms_do_not_identify_unconstrained_images() {
    let mut model = CompactMemberViews::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let member = model.new_el(source);
    let first = inherit(&mut model, source, target);
    let original_image = model.el_mor_app(first, member).unwrap();
    let second = inherit(&mut model, source, target);
    model.close();
    assert_eq!(model.el_mor_app(first, member), Some(original_image));
    let other_image = model.el_mor_app(second, member).unwrap();
    assert!(!model.are_equal_el(original_image, other_image));
    let late = model.new_el(source);
    model.close();
    let first_late = model.el_mor_app(first, late).unwrap();
    let second_late = model.el_mor_app(second, late).unwrap();
    assert!(!model.are_equal_el(first_late, second_late));
    assert!(model.world_member_el(target, first_late));
    assert!(model.world_member_el(target, second_late));
}

#[test]
#[should_panic(expected = "outside one World scope")]
fn compact_activation_rejects_global_member_consumers() {
    let mut model = crate::member_mapping::MemberMapping::new();
    model.enable_compact_world();
}

#[test]
#[should_panic(expected = "before assigning morphism endpoints")]
fn compact_activation_rejects_an_existing_ordinary_graph() {
    let mut model = CompactMemberViews::new();
    let source = model.new_world();
    let target = model.new_world();
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.enable_compact_world();
}
