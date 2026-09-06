use crate::nested_image_creation::*;

#[test]
fn conclusion_creates_nested_image() {
    let mut model = NestedImageCreation::new();
    let source = model.new_m();
    let target = model.new_m();
    let n = model.new_n(source);
    let x = model.new_t(source, n);
    let h = model.new_m_mor();
    model.insert_m_mor_dom(h, source);
    model.insert_m_mor_cod(h, target);

    assert_eq!(model.n_mor_app(h, n), None);
    assert_eq!(model.m_t_mor_app(h, x), None);
    model.close();

    let image_n = model.n_mor_app(h, n).unwrap();
    let image_x = model.m_t_mor_app(h, x).unwrap();
    assert!(model.m_member_n(target, image_n));
    assert!(model.n_member_t(target, image_n, image_x));
    assert!(!model.are_equal_t(x, image_x));
    assert_eq!(model.iter_t().count(), 2);

    model.close();
    assert_eq!(model.m_t_mor_app(h, x), Some(image_x));
    assert_eq!(model.iter_t().count(), 2);
}

#[test]
fn conclusion_creates_deep_image() {
    let mut model = NestedImageCreation::new();
    let source = model.new_m();
    let target = model.new_m();
    let n = model.new_n(source);
    let o = model.new_o(source, n);
    let x = model.new_u(source, n, o);
    let h = model.new_m_mor();
    model.insert_m_mor_dom(h, source);
    model.insert_m_mor_cod(h, target);

    model.close();

    let image_n = model.n_mor_app(h, n).unwrap();
    let image_o = model.m_o_mor_app(h, o).unwrap();
    let image_x = model.m_u_mor_app(h, x).unwrap();
    assert!(model.m_member_n(target, image_n));
    assert!(model.n_member_o(target, image_n, image_o));
    assert!(model.o_member_u(target, image_n, image_o, image_x));
    assert!(!model.are_equal_u(x, image_x));
    assert_eq!(model.iter_n().count(), 2);
    assert_eq!(model.iter_o().count(), 2);
    assert_eq!(model.iter_u().count(), 2);
}

#[test]
fn conclusion_preserves_outer_parent() {
    let mut model = NestedImageCreation::new();
    let m = model.new_m();
    let source = model.new_n(m);
    let target = model.new_n(m);
    let o = model.new_o(m, source);
    let x = model.new_u(m, source, o);
    let f = model.new_n_mor(m);
    model.insert_n_mor_dom(m, f, source);
    model.insert_n_mor_cod(m, f, target);

    model.close();

    let image_o = model.o_mor_app(m, f, o).unwrap();
    let image_x = model.n_u_mor_app(m, f, x).unwrap();
    assert!(model.n_member_o(m, target, image_o));
    assert!(model.o_member_u(m, target, image_o, image_x));
    assert!(!model.are_equal_u(x, image_x));
    assert_eq!(model.iter_m().count(), 1);
    assert_eq!(model.iter_u().count(), 2);
}

#[test]
fn define_uses_membership_with_defined_parent_image() {
    let mut model = NestedImageCreation::new();
    let source = model.new_m();
    let target = model.new_m();
    let unmapped_n = model.new_n(source);
    let mapped_n = model.new_n(source);
    let image_n = model.new_n(target);
    let x = model.new_t(source, unmapped_n);
    model.insert_n_member_t(source, mapped_n, x);
    let h = model.new_m_mor();
    model.insert_m_mor_dom(h, source);
    model.insert_m_mor_cod(h, target);
    model.insert_n_mor_app(h, mapped_n, image_n);

    let image_x = model.define_m_t_mor_app(h, x);

    assert!(model.n_member_t(target, image_n, image_x));
    assert_eq!(model.n_mor_app(h, unmapped_n), None);
    assert_eq!(model.define_m_t_mor_app(h, x), image_x);
    assert_eq!(model.iter_t().count(), 2);
}

#[test]
fn define_accepts_noncanonical_argument() {
    let mut model = NestedImageCreation::new();
    let source = model.new_m();
    let target = model.new_m();
    let n = model.new_n(source);
    let x0 = model.new_t(source, n);
    let x1 = model.new_t(source, n);
    model.equate_t(x0, x1);
    model.close();

    let h = model.new_m_mor();
    model.insert_m_mor_dom(h, source);
    model.insert_m_mor_cod(h, target);
    let image_n = model.define_n_mor_app(h, n);
    let noncanonical = if model.root_t(x0) == x0 { x1 } else { x0 };
    let image_x = model.define_m_t_mor_app(h, noncanonical);

    assert!(model.n_member_t(target, image_n, image_x));
    assert_eq!(model.m_t_mor_app(h, x0), Some(image_x));
    assert_eq!(model.m_t_mor_app(h, x1), Some(image_x));
    assert_eq!(model.iter_t().count(), 2);
}
