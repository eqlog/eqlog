use crate::subset_rules::*;

#[test]
fn test_ab_inclusion_no_dom() {
    let mut subset = SubsetRules::new();

    let a_b = subset.define_a_b();

    subset.close();
    assert!(subset.subs_mor_dom(a_b).is_none());
}

#[test]
fn test_ab_inclusion_dom() {
    let mut subset = SubsetRules::new();

    let a = subset.define_a();
    let a_b = subset.define_a_b();

    subset.close();
    let a_b_dom = subset.subs_mor_dom(a_b).unwrap();
    assert!(subset.are_equal_subs(a_b_dom, a));
}

#[test]
fn test_ab_inclusion_no_cod() {
    let mut subset = SubsetRules::new();

    let a_b = subset.define_a_b();

    subset.close();
    assert!(subset.subs_mor_cod(a_b).is_none());
}

#[test]
fn test_ab_inclusion_cod() {
    let mut subset = SubsetRules::new();

    let b = subset.define_b();
    let a_b = subset.define_a_b();

    subset.close();
    let a_b_cod = subset.subs_mor_cod(a_b).unwrap();
    assert!(subset.are_equal_subs(a_b_cod, b));
}

#[test]
fn test_singleton_subset_propagates() {
    let mut subset = SubsetRules::new();

    let a = subset.define_a();
    let b = subset.define_b();
    let _a_b = subset.define_a_b();

    let c0 = subset.new_carrier();

    subset.insert_element(a, c0);

    subset.close();

    assert!(subset.element(b, c0));
}

#[test]
fn test_member_pred_rule_fires() {
    let mut subset = SubsetRules::new();

    let a = subset.define_a();
    let b = subset.define_b();
    let x = subset.new_carrier();

    subset.insert_element(a, x);
    subset.insert_element(b, x);

    subset.close();

    assert!(subset.ab_element(x));
}
