use eqlog_test_eval as _;

include!(concat!(
    env!("EQLOG_OUT_DIR"),
    "/eqlog-test-eval/src/owner_join_plans.eql.rs"
));

#[test]
fn owner_prefix_plans_preserve_ages_fanout_and_equalities() {
    let mut model = OwnerJoinPlans::new();
    let sparse = model.new_scope();
    let dense = model.new_scope();
    let fanout = model.new_scope();
    let empty = model.new_scope();
    let keys: Vec<_> = (0..128).map(|_| model.new_key()).collect();
    let values: Vec<_> = (0..128).map(|_| model.new_value()).collect();
    let tag = model.new_tag();
    let alias = model.new_tag();
    for (&key, &value) in keys.iter().zip(&values) {
        for scope in [sparse, dense, fanout, empty] {
            model.insert_at(scope, key, value);
        }
        model.insert_task(dense, key, key, tag);
        model.insert_task(fanout, keys[0], key, tag);
    }
    for i in [1, 17] {
        model.insert_task(sparse, keys[i], keys[i], tag);
    }
    model.insert_task(sparse, keys[1], keys[1], alias);
    model.close();
    for &value in &values {
        for scope in [sparse, fanout, empty] {
            model.insert_active(scope, value);
        }
    }
    model.insert_active(dense, values[7]);
    model.close();
    for i in [1, 17] {
        assert!(model.output(sparse, keys[i]));
    }
    assert!(model.output(dense, keys[7]));
    for &key in &keys {
        assert!(model.output(fanout, key));
        assert!(!model.output(empty, key));
    }
    assert_eq!(model.iter_output().count(), 131);

    model.equate_value(values[7], values[9]);
    model.equate_tag(tag, alias);
    model.insert_active(dense, values[23]);
    model.insert_task(sparse, keys[31], keys[31], tag);
    model.insert_request(dense, keys[9]);
    model.close();
    assert!(model.output(dense, keys[9]));
    assert!(model.output(dense, keys[23]));
    assert!(model.output(sparse, keys[31]));
    assert!(model.fetched(dense, values[7]));
    assert_eq!(model.iter_output().count(), 134);
    model.close();
    assert_eq!(model.iter_output().count(), 134);
}
