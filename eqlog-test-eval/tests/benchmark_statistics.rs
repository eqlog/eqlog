use eqlog_bench::analysis::{relative_growth, summarize, Expected, Pair, Verdict};

fn ratios(values: &[u64]) -> Vec<Pair> {
    values
        .iter()
        .map(|&value| Pair {
            native_ns: value,
            cow_ns: 100,
        })
        .collect()
}

#[test]
fn median_intervals_use_order_statistics_without_discarding_samples() {
    let summary = summarize(&ratios(&[900, 100, 800, 200, 700, 300, 600, 400, 500]));
    assert_eq!(summary.ratio, 5.0);
    assert_eq!((summary.lower, summary.upper), (Some(2.0), Some(8.0)));
    assert_eq!(summary.native_ns, 500.0);
    assert_eq!(summary.cow_ns, 100.0);
    assert_eq!(summary.samples, 9);
    let sparse = summarize(&ratios(&[100, 100, 100]));
    assert_eq!((sparse.lower, sparse.upper), (None, None));
    assert!(Expected::from_summary(sparse, 0.2).is_err());
}

#[test]
fn expectation_checks_report_speedups_and_slowdowns() {
    let reference = summarize(&ratios(&[100; 9]));
    let expected = Expected::from_summary(reference.clone(), 0.2).unwrap();
    assert_eq!(expected.check(&reference), Verdict::Within);
    assert_eq!(
        expected.check(&summarize(&ratios(&[200; 9]))),
        Verdict::Slower
    );
    assert_eq!(
        expected.check(&summarize(&ratios(&[50; 9]))),
        Verdict::Faster
    );
    assert_eq!(
        expected.check(&summarize(&ratios(&[
            100, 100, 100, 100, 100, 130, 140, 150, 150
        ]))),
        Verdict::Uncertain
    );
    assert!(Expected::from_summary(reference.clone(), f64::NAN).is_err());
    assert!(Expected::from_summary(reference, 1.0).is_err());
}

#[test]
fn relative_growth_normalizes_both_cell_intervals_to_a_doubling() {
    let before = summarize(&ratios(&[100, 100, 200, 200, 200, 200, 200, 400, 400]));
    let after = summarize(&ratios(&[400, 400, 800, 800, 800, 800, 800, 1600, 1600]));
    let doubling = relative_growth(&before, &after, 2.0);
    assert_eq!(doubling.per_doubling, 4.0);
    assert_eq!((doubling.lower, doubling.upper), (Some(1.0), Some(16.0)));
    let quadrupling = relative_growth(&before, &after, 4.0);
    assert_eq!(quadrupling.per_doubling, 2.0);
    assert_eq!(
        (quadrupling.lower, quadrupling.upper),
        (Some(1.0), Some(4.0))
    );
}

#[test]
fn relative_growth_requires_intervals_for_both_sizes() {
    let complete = summarize(&ratios(&[200; 9]));
    let sparse = summarize(&ratios(&[800; 3]));
    let increasing = relative_growth(&complete, &sparse, 2.0);
    assert_eq!(increasing.per_doubling, 4.0);
    assert_eq!((increasing.lower, increasing.upper), (None, None));
    let decreasing = relative_growth(&sparse, &complete, 2.0);
    assert_eq!(decreasing.per_doubling, 0.25);
    assert_eq!((decreasing.lower, decreasing.upper), (None, None));
}
