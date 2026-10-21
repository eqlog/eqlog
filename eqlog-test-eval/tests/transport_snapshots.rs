use eqlog_runtime::__private::{
    MorphismGraphCache, SnapshotSet, TransportCheckpoint, TransportFrontier, TransportWork,
};
use eqlog_runtime::{MorphismWithSignature, PrefixTree1, PrefixTree2, PrefixTree3};

#[test]
fn shared_image_deltas_require_shared_current_and_previous_snapshots() {
    let mut source = PrefixTree1::new();
    source.insert([10]);
    let mut first = PrefixTree2::new();
    first.insert([0, 100]);
    let mut second = PrefixTree2::new();
    second.insert([1, 101]);
    let mut checkpoint = TransportCheckpoint::new();
    checkpoint.prepare(&source, &[first.clone(), second.clone()], false);

    let mut full = first.union(&second);
    full.insert([2, 102]);
    let (source_delta, deltas) = checkpoint.prepare(&source, &[full.clone(), full.clone()], false);
    assert!(source_delta.is_empty());
    assert_eq!(
        deltas[0].iter().collect::<Vec<_>>(),
        vec![[1, 101], [2, 102]]
    );
    assert_eq!(
        deltas[1].iter().collect::<Vec<_>>(),
        vec![[0, 100], [2, 102]]
    );

    full.insert([3, 103]);
    let (_, deltas) = checkpoint.prepare(&source, &[full.clone(), full.clone()], false);
    assert_eq!(deltas[0].iter().collect::<Vec<_>>(), vec![[3, 103]]);
    assert!(SnapshotSet::shares_root(&deltas[0], &deltas[1]));
    let [mut changed, snapshot] = deltas;
    changed.insert([3, 999]);
    assert_eq!(snapshot.iter().collect::<Vec<_>>(), vec![[3, 103]]);
    assert!(!full.contains([3, 999]));

    let (_, deltas) = checkpoint.prepare(&source, &[full.clone(), full.clone()], false);
    assert!(deltas.iter().all(PrefixTree2::is_empty));
    source.insert([11]);
    let (source_delta, deltas) = checkpoint.prepare(&source, &[full.clone(), full.clone()], false);
    assert_eq!(source_delta.iter().collect::<Vec<_>>(), vec![[11]]);
    assert!(deltas.iter().all(PrefixTree2::is_empty));

    let (source_delta, deltas) = checkpoint.prepare(&source, &[full.clone(), full], true);
    assert_eq!(source_delta.iter().collect::<Vec<_>>(), vec![[10], [11]]);
    assert!(deltas.iter().all(PrefixTree2::is_empty));
}

#[test]
fn shared_frontier_maps_preserve_distinct_histories() {
    let mut objects = PrefixTree1::new();
    for owner in 0..3 {
        objects.insert([owner]);
    }
    let mut dom = PrefixTree2::new();
    let mut cod = PrefixTree2::new();
    for (morph, target) in [(10, 1), (11, 2)] {
        dom.insert([0, morph]);
        cod.insert([morph, target]);
    }
    let cache = MorphismGraphCache::new();
    let graph = cache.components([], &dom, &cod, &objects);
    let first_edge = MorphismWithSignature {
        morph: 10,
        dom: 0,
        cod: 1,
    };
    let second_edge = MorphismWithSignature {
        morph: 11,
        dom: 0,
        cod: 2,
    };
    let source = PrefixTree2::new();
    let mut first = PrefixTree3::new();
    first.insert([10, 0, 100]);
    let mut second = PrefixTree3::new();
    second.insert([11, 1, 101]);
    let mut frontier = TransportFrontier::new();
    frontier.prepare(
        &source,
        &[first.clone(), second.clone()],
        &graph,
        false,
        &mut TransportWork::default(),
    );

    let mut full = first.union(&second);
    let mut work = TransportWork::default();
    frontier.prepare(
        &source,
        &[full.clone(), full.clone()],
        &graph,
        false,
        &mut work,
    );
    assert!(work.needs_visit(&first_edge));
    assert!(work.needs_visit(&second_edge));

    let mut work = TransportWork::default();
    frontier.prepare(
        &source,
        &[full.clone(), full.clone()],
        &graph,
        false,
        &mut work,
    );
    assert!(work.is_empty());
    full.insert([10, 2, 102]);
    let mut work = TransportWork::default();
    frontier.prepare(&source, &[full.clone(), full], &graph, false, &mut work);
    assert!(work.needs_visit(&first_edge));
    assert!(!work.needs_visit(&second_edge));
}
