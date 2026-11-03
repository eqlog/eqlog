use eqlog_bench::{
    ambient, chain, congruence, dag, graph::Graph, join, propagation, Case, Metrics, Workload,
};

fn check<C: Case>(case: C) -> Metrics {
    let mut native = case.native();
    native.close();
    let expected = native.verify();
    native.close();
    assert_eq!(
        native.verify(),
        expected,
        "native closure must be idempotent"
    );
    drop(native);
    let mut cow = case.cow();
    cow.close();
    assert_eq!(cow.verify(), expected, "native and COW closures differ");
    cow.close();
    assert_eq!(cow.verify(), expected, "COW closure must be idempotent");
    expected
}

#[test]
fn isolated_member_propagation_preserves_exact_images_and_rows() {
    for vertices in [1, 2, 9, 65] {
        for members in [1, 3] {
            for graph in [Graph::chain(vertices), Graph::merge(vertices, 91)] {
                let params = propagation::Params {
                    vertices,
                    members,
                    seed: 17,
                };
                eprintln!("member propagation: {params:?}, {:?}", graph.edges);
                let carrier = check(propagation::carrier(&params, graph.clone()));
                assert_eq!(carrier.owned_elements, vertices * members);
                assert_eq!(carrier.local_size, vertices * members);
                check(propagation::member_predicate(&params, graph.clone()));
                check(propagation::mixed_predicate(&params, graph.clone()));
                check(propagation::from_ambient(&params, graph.clone()));
                check(propagation::to_ambient(&params, graph.clone()));
                check(propagation::member_function(&params, graph.clone()));
                check(propagation::marking(&params, graph));
            }
        }
    }
}

#[test]
fn ambient_propagation_handles_overlapping_paths_and_finite_cycles() {
    for vertices in [1, 7, 17] {
        let params = ambient::Params {
            vertices,
            members: 3,
        };
        for graph in [
            Graph::chain(vertices),
            Graph::merge(vertices, 17),
            Graph::sparse(vertices, 3, 91),
            Graph::dense(vertices),
            Graph::cycle(vertices),
        ] {
            eprintln!("ambient propagation: N={vertices}, {:?}", graph.edges);
            check(ambient::propagation(&params, graph.clone()));
            check(ambient::marking(&params, graph));
        }
    }
}

#[test]
fn ambient_cycles_propagate_across_component_boundaries() {
    let params = ambient::Params {
        vertices: 6,
        members: 3,
    };
    let graph = Graph::new(vec![
        vec![],
        vec![0, 2],
        vec![1],
        vec![2],
        vec![],
        vec![3, 4],
    ]);
    check(ambient::propagation(&params, graph.clone()));
    check(ambient::marking(&params, graph));
}

#[test]
fn function_collisions_merge_exactly_the_required_classes() {
    for vertices in [1, 2, 9] {
        for keys in [1, 3] {
            check(congruence::one_step::case(&congruence::one_step::Params {
                vertices,
                keys,
            }));
            for depth in [1, 4] {
                eprintln!("recursive congruence: N={vertices}, K={keys}, D={depth}");
                check(congruence::recursive::case(
                    &congruence::recursive::Params {
                        vertices,
                        keys,
                        depth,
                    },
                ));
            }
        }
    }
}

#[test]
fn compound_benchmark_families_still_match_their_oracles() {
    for vertices in [1, 2, 5, 17] {
        for seed in [17, 91] {
            let chain = chain::Params {
                vertices,
                seed,
                seed_mask: 255,
            };
            check(chain::plain(&chain));
            check(chain::equation(&chain));
            let dag = dag::Params {
                vertices,
                parents: 4,
                width: 4,
                seed,
                seed_mask: 255,
            };
            for variant in [
                dag::Variant::Forward,
                dag::Variant::Layered,
                dag::Variant::Wide,
                dag::Variant::Comb,
                dag::Variant::Chain,
            ] {
                check(dag::case(&dag, variant));
            }
            let join = join::Params {
                vertices,
                parents: 4,
                width: 4,
                members: 3,
                seed,
            };
            for variant in [
                join::Variant::Fanout,
                join::Variant::Overlap,
                join::Variant::Split,
                join::Variant::Diamonds,
                join::Variant::Layered,
                join::Variant::Comb,
                join::Variant::Chain,
            ] {
                check(join::case(&join, variant));
            }
        }
    }
}

#[test]
fn compound_jobs_preserve_inactive_and_partial_propagation() {
    for seed_mask in [0, 1, 85] {
        let chain = chain::Params {
            vertices: 65,
            seed: 17,
            seed_mask,
        };
        check(chain::plain(&chain));
        check(chain::equation(&chain));
        let dag = dag::Params {
            vertices: 65,
            parents: 4,
            width: 8,
            seed: 17,
            seed_mask,
        };
        for variant in [
            dag::Variant::Forward,
            dag::Variant::Layered,
            dag::Variant::Wide,
            dag::Variant::Comb,
            dag::Variant::Chain,
        ] {
            check(dag::case(&dag, variant));
        }
    }
}

#[test]
fn grouped_joins_cover_large_fanin() {
    let params = join::Params {
        vertices: 19,
        parents: 9,
        width: 8,
        members: 3,
        seed: 17,
    };
    for variant in [
        join::Variant::Fanout,
        join::Variant::Overlap,
        join::Variant::Split,
    ] {
        check(join::case(&params, variant));
    }
}
