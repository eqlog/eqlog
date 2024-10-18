use crate::int::*;
use maplit::btreeset;
use std::collections::BTreeSet;

#[test]
fn one_plus_zero() {
    let mut model = Int::new();
    let zero = model.define_zero();
    let succ_zero = model.define_succ(zero);
    let _ = model.define_prede(succ_zero);

    model.close();
    let zero_cases: BTreeSet<ZCase> = model.z_cases(zero).collect();
    assert_eq!(
        zero_cases,
        btreeset! {ZCase::Zero(), ZCase::Prede(succ_zero)}
    );
}
