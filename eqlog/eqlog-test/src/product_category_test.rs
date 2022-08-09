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
    assert!(cat.is_iso(cat.obj_root(p1_obj), cat.obj_root(p2_obj)));
}
