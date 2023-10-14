use eqlog_runtime::eqlog_mod;
eqlog_mod!(lex_category);
pub use crate::lex_category::*;

pub fn iter_mor_with_signature<'a>(
    dom: Obj,
    cod: Obj,
    cat: &'a LexCategory,
) -> impl 'a + Iterator<Item = Mor> {
    cat.iter_mor().filter_map(move |mor| {
        let mor_dom = cat.dom(mor)?;
        cat.are_equal_obj(dom, mor_dom).then_some(())?;
        let mor_cod = cat.cod(mor)?;
        cat.are_equal_obj(cod, mor_cod).then_some(())?;
        Some(mor)
    })
}

pub fn are_isomorphic(lhs: Obj, rhs: Obj, cat: &LexCategory) -> bool {
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
    assert!(are_isomorphic(prod0_obj, prod1_obj, &cat));
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
    assert!(are_isomorphic(prod_f_g_obj, prod_f1_f0_g_obj, &cat));
}
