use eqlog_runtime::eqlog_mod;
eqlog_mod!(distr_lattice);

pub use crate::distr_lattice::*;

#[test]
fn test_meet_over_join() {
    let mut dl = DistrLattice::new();
    let x = dl.new_el();
    let y = dl.new_el();
    let z = dl.new_el();

    let y_join_z = dl.define_join(y, z);
    let lhs = dl.define_meet(x, y_join_z);

    let x_meet_y = dl.define_meet(x, y);
    let x_meet_z = dl.define_meet(x, z);
    let rhs = dl.define_join(x_meet_y, x_meet_z);
    assert!(dl.close_until(|dl| dl.are_equal_el(lhs, rhs)));
}
