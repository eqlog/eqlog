use crate::group::*;

#[test]
fn left_identity_test() {
    let mut grp = Group::new();

    let x = grp.new_el();
    let id = grp.define_id();
    let id_x = grp.define_mul(id, x);

    assert!(grp.close_until(|grp| grp.el_root(x) == grp.el_root(id_x)));
}

#[test]
fn left_inverse_test() {
    let mut grp = Group::new();

    let x = grp.new_el();
    let xinv = grp.define_inv(x);
    let x_xinv = grp.define_mul(x, xinv);
    let id = grp.define_id();

    assert!(grp.close_until(|grp| grp.el_root(x_xinv) == grp.el_root(id)));
}

#[test]
fn hemd_und_jacke_test() {
    let mut grp = Group::new();

    let x = grp.new_el();
    let y = grp.new_el();

    let xy = grp.define_mul(x, y);
    let xyinv = grp.define_inv(xy);

    let xinv = grp.define_inv(x);
    let yinv = grp.define_inv(y);
    let yinv_xinv = grp.define_mul(yinv, xinv);

    assert!(grp.close_until(|grp| grp.el_root(xyinv) == grp.el_root(yinv_xinv)));
}
