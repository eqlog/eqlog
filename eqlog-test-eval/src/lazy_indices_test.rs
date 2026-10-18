use crate::lazy_indices::LazyIndices;
use eqlog_runtime::CompiledModel;

#[test]
fn later_readers_see_accumulated_rows_and_equality_replacements() {
    let mut model = LazyIndices::new();
    let a = model.new_el();
    let b = model.new_el();
    let c = model.new_el();
    let d = model.new_el();
    model.insert_edge(a, b);
    model.insert_edge(c, d);
    model.close();
    model.insert_end(b);
    model.close();
    assert!(model.backward(a));

    model.insert_edge(b, c);
    model.canonicalize();
    model.equate_el(c, d);
    model.canonicalize();
    model.equate_el(b, a);
    model.canonicalize();
    model.insert_start(a);
    model.insert_start(c);
    model.insert_end(d);
    model.close();
    assert!(model.forward(a));
    assert!(model.forward(c));
    assert!(model.backward(b));
    assert!(model.backward(c));
    assert!(model.diagonal(a));
    assert!(model.diagonal(c));
    assert_eq!(model.iter_edge().count(), 3);

    let mut imported = LazyIndices::from_dynamic(&model.to_dynamic()).unwrap();
    let e = imported.new_el();
    imported.insert_edge(e, c);
    imported.close();
    assert!(imported.backward(e));
    assert_eq!(imported.iter_edge().count(), 4);
}

#[test]
fn skewed_joins_keep_rows_from_overlapping_age_prefixes() {
    let mut model = LazyIndices::new();
    let source = model.new_el();
    let middle: Vec<_> = (0..32).map(|_| model.new_el()).collect();
    let left = model.new_el();
    let right = model.new_el();
    for &value in &middle {
        model.insert_edge(source, value);
    }
    model.insert_edge(middle[0], left);
    model.close();
    assert_eq!(model.iter_joined().count(), 0);

    model.insert_edge(source, source);
    model.insert_edge(middle[0], right);
    model.insert_start(source);
    model.close();
    for target in middle.iter().copied().chain([source, left, right]) {
        assert!(model.joined(source, target));
    }
    assert_eq!(model.iter_joined().count(), 35);

    model.equate_el(middle[0], middle[1]);
    model.insert_start(middle[1]);
    model.close();
    assert!(model.joined(source, left));
    assert!(model.joined(source, right));
    assert_eq!(model.iter_joined().count(), 34);
}

#[test]
fn residual_joins_keep_both_skews_and_owner_scopes_after_equality() {
    let mut model = LazyIndices::new();
    let wide = model.new_joins();
    let narrow = model.new_joins();
    let x = model.new_el();
    let extra_x = model.new_el();
    let c = model.new_el();
    let missing_c = model.new_el();
    let g = model.new_el();
    let extra_g = model.new_el();
    let extra_y = model.new_el();
    let functions: Vec<_> = (0..32).map(|_| model.new_el()).collect();
    let values: Vec<_> = (0..32).map(|_| model.new_el()).collect();
    for (&f, &y) in functions.iter().zip(&values) {
        model.insert_action(wide, f, x, y);
        model.insert_product(narrow, f, g, c);
    }
    model.insert_product(wide, functions[0], g, c);
    model.insert_unindexed_product(wide, functions[0], g, c);
    model.insert_action(narrow, functions[0], x, values[0]);
    // Advance each consumer before querying its historical inputs.
    for owner in [wide, narrow] {
        model.insert_query(owner, missing_c, x);
    }
    model.close();
    for owner in [wide, narrow] {
        model.insert_query(owner, c, x);
    }
    model.close();
    assert_eq!(model.iter_resolved().count(), 2);
    assert!(model.resolved(wide, g, x, values[0]));
    assert!(model.resolved(narrow, g, x, values[0]));
    assert!(model.fallback_resolved(wide, g, x, values[0]));
    assert!(!model.fallback_resolved(narrow, g, x, values[0]));

    model.insert_action(wide, functions[0], extra_x, extra_y);
    model.insert_product(wide, functions[1], extra_g, c);
    model.insert_query(wide, c, extra_x);
    model.close();
    assert!(model.resolved(wide, g, extra_x, extra_y));
    assert!(model.resolved(wide, extra_g, x, values[1]));
    assert!(!model.resolved(wide, extra_g, extra_x, extra_y));
    assert_eq!(model.iter_resolved().count(), 4);

    model.equate_el(functions[0], functions[1]);
    model.close();
    assert!(model.are_equal_el(values[0], values[1]));
    assert!(model.resolved(wide, extra_g, extra_x, extra_y));
    assert!(model.fallback_resolved(wide, g, extra_x, extra_y));
    assert!(!model.resolved(narrow, extra_g, extra_x, extra_y));
    assert_eq!(model.iter_resolved().count(), 5);
    model.close();
    assert_eq!(model.iter_resolved().count(), 5);
}
