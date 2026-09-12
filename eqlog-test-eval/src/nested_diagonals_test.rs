use crate::nested_diagonals::*;

#[test]
fn outer_morphism_can_break_a_parent_argument_diagonal() {
    let mut model = NestedDiagonals::new();
    let source = model.new_bundle();
    let target = model.new_bundle();
    let f = model.new_fiber(source);
    let g = model.new_fiber(target);
    let x = model.new_el(source, f);
    let y = model.new_el(target, g);
    let h = model.new_bundle_mor();
    model.insert_bundle_mor_dom(h, source);
    model.insert_bundle_mor_cod(h, target);
    model.insert_fiber_mor_app(h, f, g);
    model.insert_bundle_el_mor_app(h, x, y);
    model.insert_tagged_by(source, f, source, x);
    model.insert_selected(source, f, source, x);

    model.close();

    assert!(model.self_tagged(source));
    assert!(model.self_selected(source));
    assert!(model.tagged_by(target, g, source, y));
    assert_eq!(model.selected(target, g, source), Some(y));
    assert!(!model.tagged_by(target, g, target, y));
    assert_eq!(model.selected(target, g, target), None);
    assert!(!model.self_tagged(target));
    assert!(!model.self_selected(target));
    model.close();
    assert!(!model.self_tagged(target));
    assert!(!model.self_selected(target));
}

#[test]
fn late_images_can_create_predicate_and_function_diagonals() {
    let mut model = NestedDiagonals::new();
    let source = model.new_bundle();
    let target = model.new_bundle();
    let f = model.new_fiber(source);
    let g = model.new_fiber(target);
    let x0 = model.new_el(source, f);
    let x1 = model.new_el(source, f);
    let y = model.new_el(target, g);
    let h = model.new_bundle_mor();
    model.insert_bundle_mor_dom(h, source);
    model.insert_bundle_mor_cod(h, target);
    model.insert_fiber_mor_app(h, f, g);
    model.insert_bundle_el_mor_app(h, x0, y);
    model.insert_pair(source, f, x0, x1);
    model.insert_next(source, f, x0, x1);
    model.close();
    assert!(!model.diagonal_pair(source));
    assert!(!model.fixed_point(source));
    assert!(!model.diagonal_pair(target));
    assert!(!model.fixed_point(target));

    model.insert_bundle_el_mor_app(h, x1, y);
    assert!(model.close_until(|model| model.pair(target, g, y, y)));
    model.close();

    assert!(model.pair(target, g, y, y));
    assert_eq!(model.next(target, g, y), Some(y));
    assert!(model.diagonal_pair(target));
    assert!(model.fixed_point(target));

    model.equate_el(x0, x1);
    model.close();
    assert!(model.diagonal_pair(source));
    assert!(model.fixed_point(source));
    model.close();
    assert!(model.diagonal_pair(target));
    assert!(model.fixed_point(target));
}

#[test]
fn all_repeated_argument_equalities_must_hold() {
    let mut model = NestedDiagonals::new();
    let b = model.new_bundle();
    let f = model.new_fiber(b);
    let x = model.new_el(b, f);
    let y = model.new_el(b, f);
    model.insert_two_pairs(b, f, x, x, x, y);
    model.insert_two_pairs(b, f, x, y, y, y);

    model.close();

    assert!(!model.two_diagonal_pairs(b));
    model.insert_two_pairs(b, f, x, x, y, y);
    model.close();
    assert!(model.two_diagonal_pairs(b));
}

#[test]
fn unparented_diagonals_require_all_equalities() {
    let mut model = NestedDiagonals::new();
    let x = model.new_bundle();
    let y = model.new_bundle();
    model.insert_global_two_pairs(x, x, x, y);
    model.insert_global_two_pairs(x, y, y, y);
    model.close();
    assert!(!model.global_two_diagonal_pairs());

    model.insert_global_two_pairs(x, x, y, y);
    model.close();
    assert!(model.global_two_diagonal_pairs());
}
