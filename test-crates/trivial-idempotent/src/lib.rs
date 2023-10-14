use eqlog_runtime::eqlog_mod;
eqlog_mod!(trivial_idempotent);
pub use crate::trivial_idempotent::*;

#[test]
fn trivial_idempotent() {
    use crate::trivial_idempotent::*;

    let mut m = TrivialIdempotent::new();

    let el0 = m.new_m();
    m.insert_e(el0);
    let el1 = m.new_m();
    m.insert_mul(el1, el1, el1);

    m.close();

    assert!(m.are_equal_m(el0, el1));
    assert_eq!(m.iter_m().count(), 1);
}
