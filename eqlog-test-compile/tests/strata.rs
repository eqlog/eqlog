use std::fs;

use eqlog::{process, CompileOptions, Config, SchedulingMode};
use indoc::indoc;
use tempdir::TempDir;

#[test]
fn local_rules_receive_bound_model_parameters() {
    let input = TempDir::new("eqlog-model-scope-source").unwrap();
    let output = TempDir::new("eqlog-model-scope-output").unwrap();
    fs::write(
        input.path().join("theory.eql"),
        include_str!("../../eqlog-test-eval/src/model_strata.eql"),
    )
    .unwrap();
    process(&Config {
        in_dir: input.path().to_owned(),
        out_dir: output.path().to_owned(),
        component_build: None,
        options: CompileOptions {
            scheduling_mode: SchedulingMode::Stratified,
            ..CompileOptions::default()
        },
    })
    .unwrap();
    let generated = fs::read_to_string(output.path().join("theory.eql.rs")).unwrap();
    assert!(generated.contains("__owners: [u32; 1]"));
    assert!(generated.contains("__owners: [u32; 2]"));
    let routine = function_body(&generated, "start_0_0");
    assert!(routine.contains("env.__owners[0]"));
    assert!(generated.contains("history.publish_shared(current)"));
    assert!(generated
        .contains("BTreeMap<[u32; 1], eqlog_runtime::__private::RelationVersions<PrefixTree2, (usize, Vec<u32>)>>"));
    assert!(generated
        .contains("self.__transport_component_0_world(parents, &component.internal, true)"));
    assert!(generated
        .contains("self.__transport_component_0_world(parents, &component.outgoing, false)"));
    assert!(!function_body(&generated, "fallback_start_0_0").contains("env.__owners"));
    assert!(function_body(&generated, "return_to_model_0_0").contains("env.__owners"));
}

fn stratum_of(generated: &str, rule: &str) -> usize {
    let call = format!("{rule}(env);");
    generated
        .split("fn __run_stratum_")
        .skip(1)
        .find_map(|body| {
            let (number, body) = body.split_once('(').unwrap();
            let body = body.split("pub fn close_until").next().unwrap();
            body.contains(&call)
                .then(|| number.trim_end_matches("_at").parse().unwrap())
        })
        .unwrap_or_else(|| panic!("no stratum invokes {rule}"))
}

#[test]
fn dependency_levels_share_inputs_without_delaying_consumers() {
    let input = TempDir::new("eqlog-levels-source").unwrap();
    let output = TempDir::new("eqlog-levels-output").unwrap();
    fs::write(
        input.path().join("theory.eql"),
        include_str!("../../eqlog-test-eval/src/strata_levels.eql"),
    )
    .unwrap();
    process(&Config {
        in_dir: input.path().to_owned(),
        out_dir: output.path().to_owned(),
        component_build: None,
        options: CompileOptions {
            scheduling_mode: SchedulingMode::Stratified,
            ..CompileOptions::default()
        },
    })
    .unwrap();
    let generated = fs::read_to_string(output.path().join("theory.eql.rs")).unwrap();
    for (level, rules) in [
        ["make_left", "make_right", "seed_left", "seed_right"].as_slice(),
        ["next_right", "walk_left", "right_out", "right_back"].as_slice(),
        ["join", "summarize"].as_slice(),
        ["output"].as_slice(),
    ]
    .into_iter()
    .enumerate()
    {
        for rule in rules {
            assert_eq!(stratum_of(&generated, rule), level, "{rule}");
        }
    }
    assert_eq!(generated.matches("fn __run_stratum_").count(), 4);
}

#[test]
fn parent_rules_and_child_traversals_share_one_model_schedule() {
    let input = TempDir::new("eqlog-hierarchy-source").unwrap();
    let output = TempDir::new("eqlog-hierarchy-output").unwrap();
    fs::write(
        input.path().join("theory.eql"),
        include_str!("../../eqlog-test-eval/src/model_hierarchy.eql"),
    )
    .unwrap();
    process(&Config {
        in_dir: input.path().to_owned(),
        out_dir: output.path().to_owned(),
        component_build: None,
        options: CompileOptions {
            scheduling_mode: SchedulingMode::Stratified,
            ..CompileOptions::default()
        },
    })
    .unwrap();
    let generated = fs::read_to_string(output.path().join("theory.eql.rs")).unwrap();
    let close = function_body(&generated, "__close_until");
    assert_eq!(
        close.matches("self.recompute_model_indices_model_").count(),
        1
    );
    let parent = stratum_of(&generated, "prepare");
    let child = stratum_of(&generated, "receive");
    assert_eq!(child, stratum_of(&generated, "copy_pair"));
    let finish = stratum_of(&generated, "finish");
    assert_eq!(finish, stratum_of(&generated, "pair_seen"));
    assert!(child < finish);
    assert_ne!(parent, child);
    let parent_call = close
        .find(&format!("self.__run_stratum_{parent}_at"))
        .unwrap();
    let child_call = close
        .find(&format!("self.__run_stratum_{child}_at"))
        .unwrap();
    assert!(parent_call < child_call);
    for rule in [
        "observe_child",
        "observe_sibling",
        "reverse_child",
        "reverse_any_child",
        "reverse_passive",
    ] {
        let s = stratum_of(&generated, rule);
        let body = function_body(&generated, &format!("__run_stratum_{s}_at"));
        let prepare = body
            .find(&format!("self.__prepare_descendants_{s}"))
            .unwrap();
        assert!(prepare < body.find(".publish").unwrap());
    }
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
    assert!(generated.contains("if !active_0 { break; }"));
    assert!(generated.contains(&format!("if self.__run_stratum_{first}")));

    config.options.scheduling_mode = SchedulingMode::Simultaneous;
    process(&config).unwrap();
    assert_eq!(simultaneous, fs::read_to_string(&path).unwrap());
    config.options.scheduling_mode = SchedulingMode::Stratified;
    process(&config).unwrap();
    assert_eq!(generated, fs::read_to_string(&path).unwrap());
}

fn function_body<'a>(generated: &'a str, name: &str) -> &'a str {
    let signature = format!("fn {name}(");
    let rest = generated.split_once(&signature).unwrap().1;
    let body = rest.split_once('{').unwrap().1;
    let mut depth = 1;
    for (end, ch) in body.char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => depth -= 1,
            _ => {}
        }
        if depth == 0 {
            return &body[..end];
        }
    }
    panic!("unterminated function {name}");
}

#[test]
fn strata_prepare_only_their_inputs_and_transport_dependencies() {
    let input = TempDir::new("eqlog-preparation-source").unwrap();
    let output = TempDir::new("eqlog-preparation-output").unwrap();
    fs::write(
        input.path().join("theory.eql"),
        indoc! {"
        type Atom;
        model Container {
            pred pair(Atom, Atom);
            pred spare(Atom);
            model Child { pred nested(Atom); }
        }
        model Unused { pred ignored(Atom); }
        pred a(Atom);
        pred b(Atom);
        pred forward(Container, Atom);
        pred backward(Container, Atom);
        pred result(Container, Atom);
        pred nested_result(Container, Atom);
        rule ambient { if a(x); then b(x); }
        rule first { if b(x); if forward(c, x); if c.pair(x, y); then result(c, y); }
        rule second { if b(y); if backward(c, y); if c.pair(x, y); then result(c, x); }
        rule third {
            if c: Container;
            if child: c.Child;
            if child.nested(x);
            if b(x);
            then nested_result(c, x);
        }
    "},
    )
    .unwrap();
    let config = Config {
        in_dir: input.path().to_owned(),
        out_dir: output.path().to_owned(),
        component_build: None,
        options: CompileOptions {
            scheduling_mode: SchedulingMode::Stratified,
            ..CompileOptions::default()
        },
    };
    process(&config).unwrap();
    let generated = fs::read_to_string(output.path().join("theory.eql.rs")).unwrap();
    let ambient = stratum_of(&generated, "ambient");
    let body = function_body(&generated, &format!("__run_stratum_{ambient}"));
    assert!(!body.contains("recompute_model_indices"));
    assert!(!body.contains("__prepare_native_index"));
    assert!(!generated.contains("&'a dyn Fn"));

    for rule in ["first", "second"] {
        let s = stratum_of(&generated, rule);
        let body = function_body(&generated, &format!("__run_stratum_{s}"));
        let prepare = format!("recompute_model_indices_stratum_{s}");
        assert!(body.find(&prepare).unwrap() < body.find(".consume(").unwrap());
        assert!(!body.contains("recompute_model_indices();"));
        let propagation = function_body(&generated, &prepare);
        assert!(propagation.contains("pair_"));
        assert!(!propagation.contains("spare_"));
        assert!(!propagation.contains("unused"));
        assert!(!generated.contains(&format!("fn __propagate_unused_morphisms_stratum_{s}")));
    }
    let nested = stratum_of(&generated, "third");
    let propagation = function_body(
        &generated,
        &format!("recompute_model_indices_stratum_{nested}"),
    );
    assert!(propagation.contains("child_mor_dom_"));
    assert!(propagation.contains("child_mor_cod_"));
    assert!(generated.contains(&format!(
        "fn __propagate_container_morphisms_stratum_{nested}"
    )));
    assert!(generated.contains(&format!("fn __propagate_child_morphisms_stratum_{nested}")));
    assert!(function_body(&generated, "close").contains("__close_until(None)"));
}

#[test]
fn separated_readers_advance_one_typed_secondary_index() {
    let input = TempDir::new("eqlog-shared-index-source").unwrap();
    let output = TempDir::new("eqlog-shared-index-output").unwrap();
    fs::write(
        input.path().join("theory.eql"),
        include_str!("../../eqlog-test-eval/src/shared_index.eql"),
    )
    .unwrap();
    process(&Config {
        in_dir: input.path().to_owned(),
        out_dir: output.path().to_owned(),
        component_build: None,
        options: CompileOptions {
            scheduling_mode: SchedulingMode::Stratified,
            ..CompileOptions::default()
        },
    })
    .unwrap();
    let generated = fs::read_to_string(output.path().join("theory.eql.rs")).unwrap();
    let a = stratum_of(&generated, "a");
    let b = stratum_of(&generated, "b");
    let c = stratum_of(&generated, "c");
    assert!(a < b && b < c);
    let body_a = function_body(&generated, &format!("__run_stratum_{a}"));
    let body_b = function_body(&generated, &format!("__run_stratum_{b}"));
    let body_c = function_body(&generated, &format!("__run_stratum_{c}"));
    let index_a = body_a
        .split_once("edge_old_order_1_0: &index_")
        .unwrap()
        .1
        .split_once('.')
        .unwrap()
        .0;
    let index_c = body_c
        .split_once("edge_old_order_1_0: &index_")
        .unwrap()
        .1
        .split_once('.')
        .unwrap()
        .0;
    assert_eq!(index_a, index_c);
    let field = format!("__rule_index_{index_a}");
    let update = format!("self.{field}.update(self.__rule_input_");
    assert!(body_a.contains(&update));
    assert!(body_c.contains(&update));
    assert!(!body_b.contains(&field));
    assert_eq!(
        generated
            .matches(&format!(
                "{field}: eqlog_runtime::__private::IndexSeed<PrefixTree2, PrefixTree2>,"
            ))
            .count(),
        1
    );
    assert_eq!(
        generated
            .matches(&format!(
                "{field}_versions: eqlog_runtime::__private::RelationVersions<PrefixTree2, (usize, Vec<u32>)>,"
            ))
            .count(),
        1
    );
    assert!(!generated.contains(&format!("{field}_old:")));
    assert!(!generated.contains(&format!("{field}_new:")));
}
