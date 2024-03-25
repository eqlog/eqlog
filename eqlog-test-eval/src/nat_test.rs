use crate::nat::*;

#[test]
fn one_plus_zero() {
    let mut nats = Nat::new();

    let zero = nats.new_n(NEnum::Zero());
    let one = nats.new_n(NEnum::Succ(zero));
    let two = nats.new_n(NEnum::Succ(one));

    let zero0 = nats.define_zero();
    let one0 = nats.define_succ(zero0);
    let two0 = nats.define_succ(one0);

    nats.close();

    assert!(nats.are_equal_n(zero, zero0));
    assert!(nats.are_equal_n(one, one0));
    assert!(nats.are_equal_n(two, two0));
}
