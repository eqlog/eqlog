use crate::partial_magma::*;

#[test]
fn test_eval() {
    let mut m = PartialMagma::new();
    let el0 = m.new_el();
    let el1 = m.new_el();
    assert_eq!(m.mul(el0, el1), None);

    let el2 = m.define_mul(el0, el1);
    assert!(m.mul(el0, el1) == None || m.mul(el0, el1) == Some(el2));

    m.equate_el(el0, el1);
    assert!(m.mul(el0, el1) == None || m.mul(el0, el1) == Some(el2));

    m.close();
    assert!(m.mul(el0, el0) == Some(el2));
    assert!(m.mul(el0, el1) == Some(el2));
    assert!(m.mul(el1, el0) == Some(el2));
    assert!(m.mul(el1, el1) == Some(el2));

    let el3 = m.new_el();
    m.equate_el(el2, el3);
    m.close();
    assert_eq!(m.root_el(el2), m.root_el(el3));

    assert!(m.mul(el0, el0) == Some(m.root_el(el2)));
    assert!(m.mul(el0, el1) == Some(m.root_el(el2)));
    assert!(m.mul(el1, el0) == Some(m.root_el(el2)));
    assert!(m.mul(el1, el1) == Some(m.root_el(el2)));
}
