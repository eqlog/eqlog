use std::fs;

use eqlog::{process, CompileOptions, Config, SchedulingMode};
use indoc::indoc;
use tempdir::TempDir;

fn stratum_of(generated: &str, rule: &str) -> usize {
    let call = format!("{rule}(env);");
    generated
        .split("fn __run_stratum_")
        .skip(1)
        .find_map(|body| {
            let (number, body) = body.split_once('(').unwrap();
            let body = body.split("pub fn close_until").next().unwrap();
            body.contains(&call).then(|| number.parse().unwrap())
        })
        .unwrap_or_else(|| panic!("no stratum invokes {rule}"))
}

#[test]
fn allocation_feedback_wraps_an_ordered_inner_schedule() {
    let input = TempDir::new("eqlog-strata-source").unwrap();
    let output = TempDir::new("eqlog-strata-output").unwrap();
    fs::write(
        input.path().join("theory.eql"),
        indoc! {"
        type El;
        type Value;
        pred a(El);
        pred b(El);
        pred c(El);
        pred edge(El, El);
        func make_value(El) -> Value;
        rule request { if c(x); then make_value(x)!; }
        rule recursive { if c(x); if edge(x, y); then c(y); }
        rule second { if b(x); then c(x); }
        rule first { if a(x); then b(x); }
        rule feedback { if make_value(x)!; if edge(x, y); then a(y); }
    "},
    )
    .unwrap();
    let mut config = Config {
        in_dir: input.path().to_owned(),
        out_dir: output.path().to_owned(),
        component_build: None,
        options: CompileOptions::default(),
    };
    process(&config).unwrap();
    let path = output.path().join("theory.eql.rs");
    let simultaneous = fs::read_to_string(&path).unwrap();
    assert!(!simultaneous.contains("fn __run_stratum_"));

    config.options.scheduling_mode = SchedulingMode::Stratified;
    process(&config).unwrap();
    let generated = fs::read_to_string(&path).unwrap();
    let feedback = stratum_of(&generated, "feedback");
    let first = stratum_of(&generated, "first");
    let second = stratum_of(&generated, "second");
    let recursive = stratum_of(&generated, "recursive");
    let request = stratum_of(&generated, "request");
    assert!(feedback < first && first < second && second < recursive && recursive < request);
    assert!(generated.contains(&format!("while self.__run_stratum_{recursive}")));
    assert!(generated.contains(&format!("if self.__run_stratum_{first}")));

    config.options.scheduling_mode = SchedulingMode::Simultaneous;
    process(&config).unwrap();
    assert_eq!(simultaneous, fs::read_to_string(&path).unwrap());
    config.options.scheduling_mode = SchedulingMode::Stratified;
    process(&config).unwrap();
    assert_eq!(generated, fs::read_to_string(&path).unwrap());
}
