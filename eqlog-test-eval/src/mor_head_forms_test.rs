use crate::mor_head_forms::*;

/// Exercises ambient-const, application-head, and member-const morphism
/// applications, including a match pattern whose head is a bound morphism.
#[test]
fn const_and_app_and_member_mor_heads() {
    let mut model = MorHeadForms::new();

    // Ambient const morphism c: Set -> Set that maps x to y.
    let s0 = model.new_set();
    let s1 = model.new_set();
    let x = model.new_s(s0);
    let y = model.new_s(s1);

    let c = model.define_c();
    model.insert_set_mor_dom(c, s0);
    model.insert_set_mor_cod(c, s1);
    model.insert_s_mor_app(c, x, y);

    // pick(s0) is the same morphism; close should make pick(s0)(x) total.
    model.insert_pick(s0, c);

    // Member const bundle.mor: Bundle -> Bundle.
    let b0 = model.new_bundle();
    let b1 = model.new_bundle();
    let e0 = model.new_elem(b0);
    let e1 = model.new_elem(b1);
    let bm = model.define_mor(b0);
    model.insert_bundle_mor_dom(bm, b0);
    model.insert_bundle_mor_cod(bm, b1);
    model.insert_elem_mor_app(bm, e0, e1);

    model.close();

    // const_mor_total / picked_mor_total make the image defined via the rules.
    assert!(model.s_mor_app(c, x).is_some());
    assert!(model.are_equal_s(model.s_mor_app(c, x).unwrap(), y));

    // mor_app_pattern: match y { f(x) => then reached(s) } with f = pick(s0).
    assert!(model.reached(s0));

    // bundle_mor_total
    assert!(model.elem_mor_app(bm, e0).is_some());
    assert!(model.are_equal_elem(model.elem_mor_app(bm, e0).unwrap(), e1));
}
