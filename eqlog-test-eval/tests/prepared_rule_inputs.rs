#![cfg(not(feature = "naive"))]

// The library carries the link metadata for separately compiled rule components.
use eqlog_test_eval as _;

include!(concat!(
    env!("EQLOG_OUT_DIR"),
    "/eqlog-test-eval/src/lazy_indices.eql.rs"
));

#[cfg(not(feature = "desugared"))]
#[test]
fn rules_accept_prepared_secondary_inputs() {
    let mut ends = PrefixTree1::new();
    ends.insert([2]);
    let mut reverse_edges = PrefixTree2::new();
    reverse_edges.insert([2, 1]);
    let mut output = Vec::new();
    let env = BackwardStepEnv {
        phantom: std::marker::PhantomData,
        __canonical_el: &[true; 3],
        end_old_order_0: PrefixTree1::empty(),
        end_new_order_0: &ends,
        edge_new_order_0_1: PrefixTree2::empty(),
        edge_old_order_1_0: &reverse_edges,
        new_backward: &mut output,
    };
    backward_step(env);
    assert_eq!(output, vec![[1]]);
}

#[cfg(feature = "desugared")]
#[test]
fn rules_accept_prepared_secondary_inputs() {
    let mut edges = IndexedTable::<2>::new(&[(&[1, 0], &[], true)]);
    edges.insert([1, 2]);
    let ends = [[2]];
    let mut output = Vec::new();
    let env = BackwardStepEnv {
        phantom: std::marker::PhantomData,
        end_new_order_0: RowsView::new(&ends),
        end_all_order_0: TrieView::empty(),
        edge_new_order_0_1: RowsView::empty(),
        edge_old_order_1_0: edges.view_before(0, u32::MAX),
        new_backward: &mut output,
    };
    backward_step(env);
    assert_eq!(output, vec![[1]]);
}

// Desugared tables never hold rows with noncanonical elements.
#[cfg(not(feature = "desugared"))]
#[test]
fn private_old_witnesses_survive_aliases_without_becoming_bound_variables() {
    let mut starts = PrefixTree1::new();
    starts.insert([1]);
    let mut old_edges = PrefixTree2::new();
    old_edges.insert([1, 2]);
    let mut output = Vec::new();
    private_outgoing(PrivateOutgoingEnv {
        phantom: std::marker::PhantomData,
        start_old_order_0: PrefixTree1::empty(),
        start_new_order_0: &starts,
        edge_old_order_0_1: &old_edges,
        edge_new_order_0_1: PrefixTree2::empty(),
        new_has_outgoing: &mut output,
    });
    assert_eq!(output, vec![[1]]);
}

#[cfg(not(feature = "desugared"))]
#[test]
fn all_age_scans_filter_aliases_at_each_bound_column() {
    let mut old_edges = PrefixTree2::new();
    for row in [[0, 6], [1, 2], [4, 5]] {
        old_edges.insert(row);
    }
    let mut new_edges = PrefixTree2::new();
    for row in [[1, 3], [1, 6]] {
        new_edges.insert(row);
    }
    let mut output = Vec::new();
    scan_edges(ScanEdgesEnv {
        phantom: std::marker::PhantomData,
        __canonical_el: &[false, true, false, true, true, true, true],
        scan_old_order_: PrefixTree0::empty(),
        scan_new_order_: &PrefixTree0(Some(())),
        edge_old_order_0_1: &old_edges,
        edge_new_order_0_1: &new_edges,
        new_scanned: &mut output,
    });
    output.sort_unstable();
    assert_eq!(output, vec![[1, 3], [1, 6], [4, 5]]);
}
