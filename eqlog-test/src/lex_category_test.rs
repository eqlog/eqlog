use crate::lex_category::*;

#[test]
fn test_fibre_products_are_isomorphic() {
    let mut cat = LexCategory::new();
    let f = cat.new_mor();
    let g = cat.new_mor();
    let prod0 = cat.new_fibre_prod();
    let prod1 = cat.new_fibre_prod();
    for prod in [prod0, prod1] {
        cat.insert_left(prod, f);
        cat.insert_right(prod, g);
    }
    let prod0_obj = cat.define_fibre_prod_obj(prod0);
    let prod1_obj = cat.define_fibre_prod_obj(prod1);

    cat.close();
    assert!(cat.is_iso(prod0_obj, prod1_obj));
}

#[test]
fn test_fibre_products_are_associative() {
    let mut cat = LexCategory::new();

    let f0 = cat.new_mor();
    let f1 = cat.new_mor();
    let f = cat.define_comp(f1, f0);

    let g = cat.new_mor();

    let prod_f1_g = cat.new_fibre_prod();
    cat.insert_left(prod_f1_g, f1);
    cat.insert_right(prod_f1_g, g);

    let left_proj_f1_g = cat.define_left_proj(prod_f1_g);

    let prod_f1_f0_g = cat.new_fibre_prod();
    cat.insert_left(prod_f1_f0_g, f0);
    cat.insert_right(prod_f1_f0_g, left_proj_f1_g);
    let prod_f1_f0_g_obj = cat.define_fibre_prod_obj(prod_f1_f0_g);

    let prod_f_g = cat.new_fibre_prod();
    cat.insert_left(prod_f_g, f);
    cat.insert_right(prod_f_g, g);
    let prod_f_g_obj = cat.define_fibre_prod_obj(prod_f_g);

    cat.close();
    assert!(cat.is_iso(prod_f_g_obj, prod_f1_f0_g_obj));
}
