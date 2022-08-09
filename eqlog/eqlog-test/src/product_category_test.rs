use crate::product_category::*;

#[test]
fn test_products_are_isomorphic() {
    let mut cat = ProductCategory::new();
    let x = cat.new_obj();
    let y = cat.new_obj();
    let p1 = cat.new_prod();
    let p2 = cat.new_prod();
    for p in [p1, p2] {
        cat.insert_left(Left(p, x));
        cat.insert_right(Right(p, y));
    }
    let p1_obj = cat.define_prod_obj(p1);
    let p2_obj = cat.define_prod_obj(p2);

    // The ProductCategory only formalizes the properties of binary products but doesn't enforce
    // that they exist. This means that the generated category is finite here, and we can close the
    // model without exit condition.
    cat.close();
    assert!(cat.is_iso(p1_obj, p2_obj));
}

#[test]
fn test_products_are_commutative() {
    let mut cat = ProductCategory::new();
    let x = cat.new_obj();
    let y = cat.new_obj();

    let xy = cat.new_prod();
    cat.insert_left(Left(xy, x));
    cat.insert_right(Right(xy, y));

    let yx = cat.new_prod();
    cat.insert_left(Left(yx, y));
    cat.insert_right(Right(yx, x));

    let xy_obj = cat.define_prod_obj(xy);
    let yx_obj = cat.define_prod_obj(yx);

    cat.close();
    assert!(cat.is_iso(xy_obj, yx_obj));
}

#[test]
fn test_products_are_associative() {
    let mut cat = ProductCategory::new();
    let x = cat.new_obj();
    let y = cat.new_obj();
    let z = cat.new_obj();

    let xy = cat.new_prod();
    cat.insert_left(Left(xy, x));
    cat.insert_right(Right(xy, y));
    let xy_obj = cat.define_prod_obj(xy);

    let xy_z = cat.new_prod();
    cat.insert_left(Left(xy_z, xy_obj));
    cat.insert_right(Right(xy_z, z));
    let xy_z_obj = cat.define_prod_obj(xy_z);

    let yz = cat.new_prod();
    cat.insert_left(Left(yz, y));
    cat.insert_right(Right(yz, z));
    let yz_obj = cat.define_prod_obj(yz);

    let x_yz = cat.new_prod();
    cat.insert_left(Left(x_yz, x));
    cat.insert_right(Right(x_yz, yz_obj));
    let x_yz_obj = cat.define_prod_obj(x_yz);

    cat.close();
    assert!(cat.is_iso(xy_z_obj, x_yz_obj));
}
