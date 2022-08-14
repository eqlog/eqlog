// main.rs

use eqlog_runtime::eqlog_mod;
eqlog_mod!(semilattice);
use crate::semilattice::*;

fn main() {
    // Create an empty semilattice structure and add three elements to it.
    let mut sl = Semilattice::new();
    let x = sl.new_el();
    let y = sl.new_el();
    let z = sl.new_el();

    // Close the semilattice structure by matching premises of axioms and
    // adding conclusions until we reach a fixed point.
    sl.close();
    // sl satisfies all semilattice axioms now.

    // Evaluate the left-associated meet xy_z = (x /\ y) /\ z.
    let xy = sl.meet(x, y).unwrap();
    let xy_z = sl.meet(xy, z).unwrap();

    // Evaluate the right-associated meet x_yz = x /\ (y /\ z).
    let yz = sl.meet(y, z).unwrap();
    let x_yz = sl.meet(x, yz).unwrap();

    // Check that the two elements are equal.
    if sl.are_equal_el(xy_z, x_yz) {
        println!("Meet is associative.");
    } else {
        println!("Meet is not associative.");
    }
}
