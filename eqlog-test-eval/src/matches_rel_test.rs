use crate::matches_rel::*;

// This test should check that the fix 4cc0faf2e86e57c9b162b36abe29a0d3b800a864 works as intended.
#[test]
fn different_pred_func_works() {
    let mut matches_rel = MatchesRel::new();

    let pred = matches.new_pred();
    let func = matches.new_func();

    let pred_rel = matches.define_pred_rel(pred);
    let func_rel = matches.define_func_rel(func);

    matches.close();

    assert!(matches_rel.is_pred(pred_rel));
    assert!(!matches_rel.is_pred(func_rel));

    assert!(!matches_rel.is_func(pred_rel));
    assert!(matches_rel.is_func(func_rel));
}
