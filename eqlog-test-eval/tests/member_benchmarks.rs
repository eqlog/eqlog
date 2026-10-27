use eqlog_bench::{case, Config, Engine, Family, Metrics};

fn check(family: Family, config: &Config) -> Metrics {
    eprintln!("{family:?}: {config:?}");
    let fixture = case(family, config);
    let mut expected = None;
    for engine in [Engine::Native, Engine::Cow] {
        let mut workload = fixture.prepare(engine);
        workload.close();
        let result = workload.verify();
        workload.close();
        assert_eq!(workload.verify(), result, "closure must be idempotent");
        if let Some(previous) = &expected {
            assert_eq!(&result, previous, "native and COW closures differ");
        } else {
            expected = Some(result);
        }
    }
    expected.unwrap()
}

#[test]
fn member_benchmark_families_match_their_oracles() {
    for family in Family::ALL {
        for seed in [17, 91] {
            let config = Config {
                vertices: 17,
                parents: 4,
                width: 4,
                members: 3,
                seed,
                ..Config::default()
            };
            check(family, &config);
        }
    }
}

#[test]
fn member_benchmarks_handle_singletons_and_short_graphs() {
    for family in Family::ALL {
        for vertices in [1, 2, 5] {
            let config = Config {
                vertices,
                members: 1,
                ..Config::default()
            };
            check(family, &config);
        }
    }
}

#[test]
fn member_benchmarks_check_inactive_and_partial_propagation() {
    for family in [
        Family::ChainPlain,
        Family::ChainEquation,
        Family::DagForward,
        Family::DagLayered,
        Family::DagWide,
        Family::DagComb,
        Family::DagChain,
    ] {
        for seed_mask in [0, 1, 85] {
            let config = Config {
                vertices: 65,
                seed_mask,
                ..Config::default()
            };
            check(family, &config);
        }
    }
}

#[test]
fn member_join_benchmarks_check_large_fanin() {
    for family in [Family::JoinFanout, Family::JoinOverlap, Family::JoinSplit] {
        let config = Config {
            vertices: 19,
            parents: 9,
            members: 3,
            ..Config::default()
        };
        check(family, &config);
    }
}
