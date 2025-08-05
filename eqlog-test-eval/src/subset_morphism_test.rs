use crate::subset_morphism::*;

#[test]
fn test_ab_inclusion_no_dom() {
    let mut subset = SubsetMorphism::new();

    let a_b = subset.define_a_b();

    subset.close();
    assert!(subset.subs_mor_dom(a_b).is_none());
}

#[test]
fn test_ab_inclusion_dom() {
    let mut subset = SubsetMorphism::new();

    let a = subset.define_a();
    let a_b = subset.define_a_b();

    subset.close();
    let a_b_dom = subset.subs_mor_dom(a_b).unwrap();
    assert!(subset.are_equal_subs(a_b_dom, a));
}
