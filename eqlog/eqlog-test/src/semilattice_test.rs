use crate::semilattice::*;

#[test]
fn test_semilattice_associative() {
    let mut sl = Semilattice::new();
    let x = sl.new_el();
    let y = sl.new_el();
    let z = sl.new_el();
    sl.close();
    let xy = sl.meet(x, y).unwrap();
    let xy_z = sl.meet(xy, z).unwrap();
    let yz = sl.meet(y, z).unwrap();
    let x_yz = sl.meet(x, yz).unwrap();
    assert!(sl.are_equal_el(xy_z, x_yz));
}
