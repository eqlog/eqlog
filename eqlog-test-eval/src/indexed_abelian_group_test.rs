use crate::indexed_abelian_group::*;

#[test]
fn empty_model() {
    let mut model = IndexedAbelianGroup::new();
    model.close();
}

#[test]
fn single_trivial_group() {
    let mut model = IndexedAbelianGroup::new();
    let _ = model.new_abelian_group();

    model.close();
    assert_eq!(model.iter_abelian_group().count(), 1);
    assert_eq!(model.iter_el().count(), 1);
}

#[test]
fn single_z2() {
    let mut model = IndexedAbelianGroup::new();

    let z2 = model.new_abelian_group();

    let a = model.new_el(z2);

    let a_squared = model.define_mul(z2, a, a);
    let id = model.define_id(z2);
    model.equate_el(a_squared, id);

    model.close();

    // Check we have exactly 4 elements in the product
    let product_elements: Vec<_> = model
        .iter_abelian_group_member_el()
        .filter(|(g, _)| model.are_equal_abelian_group(*g, z2))
        .map(|(_, el)| el)
        .collect();

    assert_eq!(product_elements.len(), 2);
}

#[test]
fn id_on_z2() {
    let mut model = IndexedAbelianGroup::new();

    let z2 = model.new_abelian_group();

    let a = model.new_el(z2);

    let a_squared = model.define_mul(z2, a, a);
    let id = model.define_id(z2);
    model.equate_el(a_squared, id);

    let z2_copy = model.new_abelian_group();

    let f = model.new_abelian_group_mor();

    model.insert_abelian_group_mor_dom(f, z2);
    model.insert_abelian_group_mor_cod(f, z2_copy);

    model.close();

    assert_eq!(model.iter_el().count(), 4);
}

#[test]
fn z2_times_z2_coproduct() {
    let mut model = IndexedAbelianGroup::new();

    // Create three groups: two copies of Z/2Z and their coproduct
    let z2_1 = model.new_abelian_group();
    let z2_2 = model.new_abelian_group();
    let product = model.new_abelian_group();

    // Create generators for the two Z/2Z groups
    let a = model.new_el(z2_1);
    let b = model.new_el(z2_2);

    // Z/2Z relations: a^2 = id, b^2 = id
    let a_squared = model.define_mul(z2_1, a, a);
    let id1 = model.define_id(z2_1);
    model.equate_el(a_squared, id1);

    let b_squared = model.define_mul(z2_2, b, b);
    let id2 = model.define_id(z2_2);
    model.equate_el(b_squared, id2);

    // Create morphisms from both Z/2Z groups to the product
    let f1 = model.new_abelian_group_mor();
    let f2 = model.new_abelian_group_mor();

    model.insert_abelian_group_mor_dom(f1, z2_1);
    model.insert_abelian_group_mor_cod(f1, product);
    model.insert_abelian_group_mor_dom(f2, z2_2);
    model.insert_abelian_group_mor_cod(f2, product);

    model.close();

    // Make `model` non-mut so that we don't accidentally change it.
    let model = model;

    // Map the generators to elements in the product
    let a_image = model.el_mor_app(f1, a).unwrap();
    let b_image = model.el_mor_app(f2, b).unwrap();

    // In Z/2Z x Z/2Z, we should have 4 elements: id, a, b, ab
    let product_id = model.id(product).unwrap();
    let ab = model.mul(product, a_image, b_image).unwrap();

    // Verify that a, b commute (they should since it's abelian)
    let ba = model.mul(product, b_image, a_image).unwrap();
    assert!(model.are_equal_el(ab, ba));

    // Verify that a^2 = id, b^2 = id, (ab)^2 = id
    let a_img_squared = model.mul(product, a_image, a_image).unwrap();
    assert!(model.are_equal_el(a_img_squared, product_id));

    let b_img_squared = model.mul(product, b_image, b_image).unwrap();
    assert!(model.are_equal_el(b_img_squared, product_id));

    let ab_squared = model.mul(product, ab, ab).unwrap();
    assert!(model.are_equal_el(ab_squared, product_id));

    // Check we have exactly 4 elements in the product
    let product_elements: Vec<_> = model
        .iter_abelian_group_member_el()
        .filter(|(g, _)| model.are_equal_abelian_group(*g, product))
        .map(|(_, el)| el)
        .collect();

    assert_eq!(product_elements.len(), 4);
}

#[test]
fn z2_plus_z3_equals_z6_coproduct() {
    let mut model = IndexedAbelianGroup::new();

    // Create three groups: Z/2Z, Z/3Z, and their coproduct (which should be Z/6Z)
    let z2 = model.new_abelian_group();
    let z3 = model.new_abelian_group();
    let z6 = model.new_abelian_group();

    // Create generator for Z/2Z
    let a = model.new_el(z2);
    let a_squared = model.define_mul(z2, a, a);
    let id2 = model.define_id(z2);
    model.equate_el(a_squared, id2);

    // Create generator for Z/3Z
    let b = model.new_el(z3);
    let b_squared = model.define_mul(z3, b, b);
    let b_cubed = model.define_mul(z3, b_squared, b);
    let id3 = model.define_id(z3);
    model.equate_el(b_cubed, id3);

    // Create morphisms from Z/2Z and Z/3Z to Z/6Z
    let f = model.new_abelian_group_mor();
    let g = model.new_abelian_group_mor();

    model.insert_abelian_group_mor_dom(f, z2);
    model.insert_abelian_group_mor_cod(f, z6);
    model.insert_abelian_group_mor_dom(g, z3);
    model.insert_abelian_group_mor_cod(g, z6);

    model.close();

    let a_in_z6 = model.el_mor_app(f, a).unwrap();
    let b_in_z6 = model.el_mor_app(g, b).unwrap();

    model.close();
    let model = model;

    // In Z/6Z, we should have 6 elements
    // Since gcd(2,3) = 1, the coproduct should be Z/6Z
    // We can verify this by checking that a_in_z6 has order 2, b_in_z6 has order 3,
    // and their product has order 6

    let id6 = model.id(z6).unwrap();

    // Verify a has order 2
    let a_z6_squared = model.mul(z6, a_in_z6, a_in_z6).unwrap();
    assert!(model.are_equal_el(a_z6_squared, id6));

    // Verify b has order 3
    let b_z6_squared = model.mul(z6, b_in_z6, b_in_z6).unwrap();
    let b_z6_cubed = model.mul(z6, b_z6_squared, b_in_z6).unwrap();
    assert!(model.are_equal_el(b_z6_cubed, id6));

    // Verify that ab has order 6
    let ab = model.mul(z6, a_in_z6, b_in_z6).unwrap();

    let ab_2 = model.mul(z6, ab, ab).unwrap();
    let ab_3 = model.mul(z6, ab_2, ab).unwrap();
    let ab_4 = model.mul(z6, ab_3, ab).unwrap();
    let ab_5 = model.mul(z6, ab_4, ab).unwrap();
    let ab_6 = model.mul(z6, ab_5, ab).unwrap();

    // ab should not equal id until the 6th power
    assert!(!model.are_equal_el(ab, id6));
    assert!(!model.are_equal_el(ab_2, id6));
    assert!(!model.are_equal_el(ab_3, id6));
    assert!(!model.are_equal_el(ab_4, id6));
    assert!(!model.are_equal_el(ab_5, id6));
    assert!(model.are_equal_el(ab_6, id6));

    // Count elements in Z/6Z
    let z6_elements: Vec<_> = model
        .iter_abelian_group_member_el()
        .filter(|(g, _)| model.are_equal_abelian_group(*g, z6))
        .map(|(_, el)| el)
        .collect();

    assert_eq!(z6_elements.len(), 6);
}

#[test]
fn morphism_composition() {
    let mut model = IndexedAbelianGroup::new();

    let g1 = model.new_abelian_group();
    let g2 = model.new_abelian_group();
    let g3 = model.new_abelian_group();

    let f = model.new_abelian_group_mor();
    let g = model.new_abelian_group_mor();

    model.insert_abelian_group_mor_dom(f, g1);
    model.insert_abelian_group_mor_cod(f, g2);
    model.insert_abelian_group_mor_dom(g, g2);
    model.insert_abelian_group_mor_cod(g, g3);

    let x = model.new_el(g1);
    let x_squared = model.define_mul(g1, x, x);
    let id = model.define_id(g1);
    model.equate_el(x_squared, id);

    model.close();

    let fx = model.el_mor_app(f, x).unwrap();
    let gfx = model.el_mor_app(g, fx).unwrap();

    let mut g1_count = 0;
    let mut g2_count = 0;
    let mut g3_count = 0;

    for (grp, el) in model.iter_abelian_group_member_el() {
        if model.are_equal_abelian_group(grp, g1) {
            g1_count += 1;
        } else if model.are_equal_abelian_group(grp, g2) {
            g2_count += 1;
        } else if model.are_equal_abelian_group(grp, g3) {
            g3_count += 1;
        } else {
            panic!("Unexpected group: {grp}");
        }
    }

    assert_eq!(g1_count, 2);
    assert_eq!(g2_count, 2);
    assert_eq!(g3_count, 2);
}
