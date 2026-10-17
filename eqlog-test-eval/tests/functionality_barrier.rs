use eqlog_test_eval as _;

include!(concat!(
    env!("EQLOG_OUT_DIR"),
    "/eqlog-test-eval/src/functionality_barrier.eql.rs"
));

#[test]
fn functionality_fixed_point_preserves_other_consumers_and_deferred_allocations() {
    let mut model = FunctionalityBarrier::new();
    let key = model.new_key();
    let a = model.new_value();
    let b = model.new_value();
    let c = model.new_value();
    let d = model.new_value();
    model.insert_pick(key, a);
    model.insert_pick(key, b);
    model.insert_next(a, c);
    model.insert_next(b, d);
    model.insert_left(c);
    model.insert_right(d);

    assert!(model.close_until(|model| model.are_equal_value(a, b)));
    model.canonicalize();
    assert!(model.close_until(|model| model.staged(key)));
    assert!(model.are_equal_value(c, d));
    assert!(model.selected(key, c));
    assert!(model.witness(key).is_none());

    let existing = model.new_value();
    model.insert_witness(key, existing);
    model.close();
    assert_eq!(model.witness(key), Some(existing));
    assert_eq!(model.iter_witness().count(), 1);

    let e = model.new_value();
    let f = model.new_value();
    model.insert_request(key, e);
    model.insert_next(e, f);
    model.insert_right(f);
    assert!(model.close_until(|model| model.are_equal_value(a, e)));
    model.close();
    assert!(model.are_equal_value(c, f));
    assert!(model.selected(key, f));
    assert_eq!(model.iter_selected().count(), 1);
    assert_eq!(model.iter_witness().count(), 1);
}
