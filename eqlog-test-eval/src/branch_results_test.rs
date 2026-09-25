use crate::branch_results::*;

#[test]
fn branch_continuation_binds_shared_function_results() {
    let mut model = BranchResults::new();
    let x = model.new_input();
    let y = model.new_input();
    model.close();

    let x_middle = model.make_middle(x).unwrap();
    let y_middle = model.make_middle(y).unwrap();
    let x_output = model.make_output(x_middle).unwrap();
    let y_output = model.make_output(y_middle).unwrap();
    assert!(model.joined(x, x_output));
    assert!(model.joined(y, y_output));
    assert!(!model.joined(x, y_output));
    assert!(!model.joined(y, x_output));
    assert_eq!(model.iter_middle().count(), 2);
    assert_eq!(model.iter_output().count(), 2);
}

#[test]
fn match_continuation_binds_shared_function_results() {
    let mut model = BranchResults::new();
    let x = model.new_input();
    let left = model.define_left(x);
    let right = model.define_right(x);
    model.close();

    let left_output = model.chosen(left).unwrap();
    let right_output = model.chosen(right).unwrap();
    assert!(model.matched(left, left_output));
    assert!(model.matched(right, right_output));
    assert!(!model.matched(left, right_output));
    assert!(!model.matched(right, left_output));
}

#[test]
fn branch_continuation_checks_shared_predicates() {
    let mut model = BranchResults::new();
    let x = model.new_input();
    let y = model.new_input();
    model.insert_guard(x);
    model.close();

    assert!(model.checked(x));
    assert!(!model.checked(y));

    model.insert_guard(y);
    model.close();
    assert!(model.checked(y));
}

#[test]
fn branch_continuation_checks_shared_equalities() {
    let mut model = BranchResults::new();
    let x = model.new_input();
    let y = model.new_input();
    model.insert_pair(x, y);
    model.close();

    assert!(!model.same(x));
    assert!(!model.same(y));

    model.equate_input(x, y);
    model.close();
    assert!(model.same(x));
    assert!(model.same(y));
}
