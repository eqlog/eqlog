use crate::nat::*;

#[test]
fn one_plus_zero() {
    let mut nats = Nat::new();

    let zero = nats.define_zero();
    let one = nats.define_succ(zero);
    let one_plus_zero = nats.define_plus(one, zero);

    nats.close();

    assert!(nats.are_equal_n(one_plus_zero, one));
}
