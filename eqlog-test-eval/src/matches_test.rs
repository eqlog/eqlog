use crate::matches::*;

#[test]
fn branching_same_variable_after() {
    let mut matches = Matches::new();

    let a = matches.new_a();
    let b = matches.new_a();
    matches.define_baz(a);

    matches.close();

    assert!(matches.pred_a_0(a));
    assert!(matches.pred_a_1(a));
    assert!(matches.pred_a_1(b));
}
