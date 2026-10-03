#![cfg(not(feature = "naive"))]

// The library carries the link metadata for separately compiled rule components.
use eqlog_test_eval as _;

include!(concat!(
    env!("EQLOG_OUT_DIR"),
    "/eqlog-test-eval/src/lazy_indices.eql.rs"
));

#[test]
fn an_empty_earlier_join_leaves_the_secondary_input_unforced() {
    let mut output = Vec::new();
    let env = BackwardStepEnv {
        phantom: std::marker::PhantomData,
        end_old_order_0: PrefixTree1::empty(),
        end_new_order_0: PrefixTree1::empty(),
        edge_new_order_0_1: PrefixTree2::empty(),
        edge_old_order_1_0: &|| panic!("unreachable index was forced"),
        new_backward: &mut output,
    };
    backward_step(env);
    assert!(output.is_empty());
}
