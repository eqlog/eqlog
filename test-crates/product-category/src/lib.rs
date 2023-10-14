use eqlog_runtime::eqlog_mod;
eqlog_mod!(product_category);
pub use crate::product_category::*;

pub fn iter_mor_with_signature<'a>(
    dom: Obj,
    cod: Obj,
    cat: &'a ProductCategory,
) -> impl 'a + Iterator<Item = Mor> {
    cat.iter_mor().filter_map(move |mor| {
        let mor_dom = cat.dom(mor)?;
        cat.are_equal_obj(dom, mor_dom).then_some(())?;
        let mor_cod = cat.cod(mor)?;
        cat.are_equal_obj(cod, mor_cod).then_some(())?;
        Some(mor)
    })
}

pub fn are_isomorphic(lhs: Obj, rhs: Obj, cat: &ProductCategory) -> bool {
    let lhs_id = match cat.id(lhs) {
        Some(lhs_id) => lhs_id,
        None => {
            return false;
        }
    };
    let rhs_id = match cat.id(rhs) {
        Some(rhs_id) => rhs_id,
        None => {
            return false;
        }
    };

    for lhs_rhs in iter_mor_with_signature(lhs, rhs, cat) {
        for rhs_lhs in iter_mor_with_signature(rhs, lhs, cat) {
            let lhs_comp = match cat.comp(rhs_lhs, lhs_rhs) {
                Some(lhs_comp) => lhs_comp,
                None => {
                    continue;
                }
            };
            let rhs_comp = match cat.comp(lhs_rhs, rhs_lhs) {
                Some(rhs_comp) => rhs_comp,
                None => {
                    continue;
                }
            };
            if cat.are_equal_mor(lhs_comp, lhs_id) && cat.are_equal_mor(rhs_comp, rhs_id) {
                return true;
            }
        }
    }

    false
}

#[test]
fn test_products_are_isomorphic() {
    let mut cat = ProductCategory::new();
    let x = cat.new_obj();
    let y = cat.new_obj();
    let p1 = cat.new_prod();
    let p2 = cat.new_prod();
    for p in [p1, p2] {
        cat.insert_left(p, x);
        cat.insert_right(p, y);
    }
    let p1_obj = cat.define_prod_obj(p1);
    let p2_obj = cat.define_prod_obj(p2);

    // The ProductCategory only formalizes the properties of binary products but doesn't enforce
    // that they exist. This means that the generated category is finite here, and we can close the
    // model without exit condition.
    cat.close();
    assert!(are_isomorphic(p1_obj, p2_obj, &cat));
}

#[test]
fn test_products_are_commutative() {
    let mut cat = ProductCategory::new();
    let x = cat.new_obj();
    let y = cat.new_obj();

    let xy = cat.new_prod();
    cat.insert_left(xy, x);
    cat.insert_right(xy, y);

    let yx = cat.new_prod();
    cat.insert_left(yx, y);
    cat.insert_right(yx, x);

    let xy_obj = cat.define_prod_obj(xy);
    let yx_obj = cat.define_prod_obj(yx);

    cat.close();
    assert!(are_isomorphic(xy_obj, yx_obj, &cat));
}

#[test]
fn test_products_are_associative() {
    let mut cat = ProductCategory::new();
    let x = cat.new_obj();
    let y = cat.new_obj();
    let z = cat.new_obj();

    let xy = cat.new_prod();
    cat.insert_left(xy, x);
    cat.insert_right(xy, y);
    let xy_obj = cat.define_prod_obj(xy);

    let xy_z = cat.new_prod();
    cat.insert_left(xy_z, xy_obj);
    cat.insert_right(xy_z, z);
    let xy_z_obj = cat.define_prod_obj(xy_z);

    let yz = cat.new_prod();
    cat.insert_left(yz, y);
    cat.insert_right(yz, z);
    let yz_obj = cat.define_prod_obj(yz);

    let x_yz = cat.new_prod();
    cat.insert_left(x_yz, x);
    cat.insert_right(x_yz, yz_obj);
    let x_yz_obj = cat.define_prod_obj(x_yz);

    cat.close();
    assert!(are_isomorphic(xy_z_obj, x_yz_obj, &cat));
}
