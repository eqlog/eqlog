use eqlog_bench::{cases, Phase};

#[test]
fn scheduling_benchmarks_reach_the_expected_closures() {
    for case in cases() {
        for phase in [Phase::Initial, Phase::Incremental, Phase::Unchanged] {
            let name = case.name;
            let mode = case.mode;
            let phase_name = phase.name();
            eprintln!("{name} / {mode} / {phase_name}");
            let mut workload = (case.prepare)(1, phase);
            workload.close();
            workload.check();
            workload.close();
            workload.check();
        }
    }
}
