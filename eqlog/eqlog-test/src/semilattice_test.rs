use crate::semilattice::*;

#[test]
fn test_associative() {
    let mut sl = Semilattice::new();
    let x = sl.new_el();
    let y = sl.new_el();
    let z = sl.new_el();
    let xy = sl.define_meet(x, y);
    let xy_z = sl.define_meet(xy, z);
    let yz = sl.define_meet(y, z);
    let x_yz = sl.define_meet(x, yz);
    let is_true = sl.close_until(|sl| sl.el_root(xy_z) == sl.el_root(x_yz));
    assert!(is_true);
}
