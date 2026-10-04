#![cfg(not(feature = "naive"))]

// The library carries the link metadata for separately compiled rule components.
use eqlog_test_eval as _;

include!(concat!(
    env!("EQLOG_OUT_DIR"),
    "/eqlog-test-eval/src/lazy_indices.eql.rs"
));

#[test]
fn rules_accept_prepared_secondary_inputs() {
    let mut ends = PrefixTree1::new();
    ends.insert([2]);
    let mut reverse_edges = PrefixTree2::new();
    reverse_edges.insert([2, 1]);
    let mut output = Vec::new();
    let env = BackwardStepEnv {
        phantom: std::marker::PhantomData,
        end_old_order_0: PrefixTree1::empty(),
        end_new_order_0: &ends,
        edge_new_order_0_1: PrefixTree2::empty(),
        edge_old_order_1_0: &reverse_edges,
        new_backward: &mut output,
    };
    backward_step(env);
    assert_eq!(output, vec![[1]]);
}
