use crate::inference::*;

#[test]
fn test_boolean_typing() {
    let mut stlc = Inference::new();

    let true_tm = stlc.define_true_tm();
    let false_tm = stlc.define_false_tm();

    let sigma = stlc.new_ty();
    let ty_var = stlc.new_tm();
    stlc.insert_tm_ty(ty_var, sigma);

    let id = stlc.define_lambda(ty_var, ty_var);
    let const_true = stlc.define_lambda(ty_var, true_tm);

    // The term `if true then id else const_true`. This term should force `id` and `const_true` to
    // be of type `bool -> bool`.
    let id_or_const_true = stlc.define_if_tm(true_tm, id, const_true);

    stlc.close();

    assert!(!stlc.absurd());

    // Check that boolean terms have the appropriate types.
    let bool_ty = stlc.bool().unwrap();
    assert!(stlc.are_equal_ty(stlc.tm_ty(true_tm).unwrap(), bool_ty));
    assert!(stlc.are_equal_ty(stlc.tm_ty(false_tm).unwrap(), bool_ty));

    // Check that sigma and bool_ty are unified due. This should have happened because of the
    // `id_or_const_true` tm.
    assert!(stlc.are_equal_ty(bool_ty, sigma));

    let fun_bool_bool_ty = stlc.fun(bool_ty, bool_ty).unwrap();

    assert!(stlc.are_equal_ty(stlc.tm_ty(id).unwrap(), fun_bool_bool_ty));
    assert!(stlc.are_equal_ty(stlc.tm_ty(const_true).unwrap(), fun_bool_bool_ty));
    assert!(stlc.are_equal_ty(stlc.tm_ty(id_or_const_true).unwrap(), fun_bool_bool_ty));
}
