use eqlog_runtime::{CompiledModel, Element};
use rand::{rngs::StdRng, seq::SliceRandom, RngExt, SeedableRng};

use super::{compare, setting, Evaluator, State};

struct Run {
    inputs: State,
    images: Vec<Element>,
    closures: Vec<(State, State)>,
}

impl Run {
    fn new<M: CompiledModel>(model: &M) -> Self {
        let mut model = model.to_dynamic();
        model.canonicalize();
        let elements: Vec<_> = model
            .signature()
            .types()
            .flat_map(|(type_, _)| model.elements(type_).unwrap())
            .collect();
        Self {
            images: elements.clone(),
            inputs: State { model, elements },
            closures: Vec::new(),
        }
    }

    fn input(&mut self, type_name: &str, index: u32, parents: &[u32]) {
        let signature = self.inputs.model.signature();
        let type_ = signature.type_named(type_name).unwrap();
        let parent_types = &signature.type_(type_).unwrap().parents;
        assert_eq!(parent_types.len(), parents.len());
        let parents: Vec<_> = parent_types
            .iter()
            .zip(parents)
            .map(|(&type_, &index)| {
                let position = self
                    .images
                    .iter()
                    .position(|&image| image == Element { type_, index })
                    .expect("supplied parents are tracked inputs");
                self.inputs.elements[position]
            })
            .collect();
        let element = self.inputs.model.new_element(type_, &parents).unwrap();
        self.inputs.elements.push(element);
        self.images.push(Element { type_, index });
    }

    fn close<M: Evaluator>(&mut self, model: &mut M) {
        model.close_bounded();
        let mut copy = model.to_dynamic();
        copy.canonicalize();
        self.closures.push((
            State {
                model: self.inputs.model.clone(),
                elements: self.inputs.elements.clone(),
            },
            State {
                model: copy,
                elements: self.images.clone(),
            },
        ));
    }
}

fn assert_equivalent(runs: [(&str, Run); 4]) {
    let (reference_name, reference) = &runs[0];
    assert!(!reference.closures.is_empty());
    for (name, run) in &runs[1..] {
        assert_eq!(reference.closures.len(), run.closures.len());
        for (step, ((inputs, left), (_, right))) in
            reference.closures.iter().zip(&run.closures).enumerate()
        {
            eprintln!("closure {step}: {reference_name} vs {name}");
            compare(inputs, left, right);
        }
    }
}

macro_rules! late_gate {
    ($model:ty) => {{
        let mut model = <$model>::new();
        let x = model.new_key();
        let y = model.new_key();
        let z = model.new_key();
        model.insert_requested(x);
        model.insert_requested(y);
        model.insert_edge(x, y);
        model.insert_edge(y, z);
        let mut run = Run::new(&model);
        run.close(&mut model);

        let u = model.witness(x).unwrap();
        let v = model.witness(y).unwrap();
        assert!(!model.are_equal_value(u, v));
        assert!(!model.reached(x));
        model.equate_value(u, v);
        run.close(&mut model);
        assert!(!model.reached(x));

        model.insert_gate();
        run.close(&mut model);
        assert!(model.marked(u));
        assert!(model.reached(x));
        assert!(model.reached(y));
        assert!(model.reached(z));
        run.close(&mut model);
        run
    }};
}

#[test]
fn a_late_gate_enables_a_join_through_merged_witnesses() {
    assert_equivalent(witness_join_variants!(late_gate));
}

macro_rules! diamond {
    ($model:ty) => {{
        let mut model = <$model>::new();
        let source = model.new_world();
        let left = model.new_world();
        let right = model.new_world();
        let target = model.new_world();
        let x = model.new_el(source);
        let y = model.new_el(source);
        let tag = model.new_label();
        model.insert_edge(source, x, y);
        model.insert_tagged(source, x, tag);
        model.insert_marked(source, x);
        let mut run = Run::new(&model);
        run.close(&mut model);
        assert!(!model.marked(source, y));

        let mut arrows = Vec::new();
        for (dom, cod) in [
            (source, left),
            (source, right),
            (left, target),
            (right, target),
        ] {
            let h = model.new_world_mor();
            run.input("WorldMor", h.0, &[]);
            model.insert_world_mor_dom(h, dom);
            model.insert_world_mor_cod(h, cod);
            arrows.push(h);
        }
        run.close(&mut model);
        let left_x = model.el_mor_app(arrows[0], x).unwrap();
        let right_x = model.el_mor_app(arrows[1], x).unwrap();
        let left_y = model.el_mor_app(arrows[0], y).unwrap();
        let right_y = model.el_mor_app(arrows[1], y).unwrap();
        let target_x = model.el_mor_app(arrows[2], left_x).unwrap();
        let other_x = model.el_mor_app(arrows[3], right_x).unwrap();
        let target_y = model.el_mor_app(arrows[2], left_y).unwrap();
        let other_y = model.el_mor_app(arrows[3], right_y).unwrap();
        assert!(!model.are_equal_el(target_x, other_x));
        assert!(!model.marked(target, target_y));

        model.insert_next(left, left_x, left_y);
        model.insert_next(right, right_x, right_y);
        model.equate_el(target, target_x, other_x);
        run.close(&mut model);
        assert!(model.are_equal_el(target_y, other_y));
        assert!(model.tagged(target, other_x, tag));
        assert!(!model.observed(target));

        model.equate_world(left, right);
        model.equate_world_mor(arrows[0], arrows[1]);
        model.equate_world_mor(arrows[2], arrows[3]);
        run.close(&mut model);
        assert!(model.are_equal_el(left_x, right_x));
        assert!(model.are_equal_el(left_y, right_y));

        model.insert_ready(source);
        run.close(&mut model);
        assert!(model.marked(target, target_y));
        assert!(model.observed(target));
        run.close(&mut model);
        run
    }};
}

#[test]
fn a_morphism_diamond_merges_function_results_before_late_facts_arrive() {
    assert_equivalent(transport_variants!(diamond));
}

macro_rules! nested_images {
    ($model:ty) => {{
        let mut model = <$model>::new();
        let source = model.new_world();
        let target = model.new_world();
        let first = model.new_fiber(source);
        let second = model.new_fiber(source);
        let x = model.new_el(source, first);
        let y = model.new_el(source, first);
        model.insert_edge(source, first, x, y);
        let inner = model.new_fiber_mor(source);
        model.insert_fiber_mor_dom(source, inner, first);
        model.insert_fiber_mor_cod(source, inner, second);
        let mut run = Run::new(&model);
        run.close(&mut model);
        let second_x = model.el_mor_app(source, inner, x).unwrap();
        let second_y = model.el_mor_app(source, inner, y).unwrap();

        let outer = model.new_world_mor();
        run.input("WorldMor", outer.0, &[]);
        model.insert_world_mor_dom(outer, source);
        model.insert_world_mor_cod(outer, target);
        run.close(&mut model);
        let target_first = model.fiber_mor_app(outer, first).unwrap();
        let target_second = model.fiber_mor_app(outer, second).unwrap();
        let target_x = model.world_el_mor_app(outer, second_x).unwrap();
        let target_y = model.world_el_mor_app(outer, second_y).unwrap();
        assert!(!model.marked(target, target_second, target_y));

        model.insert_marked(source, first, x);
        run.close(&mut model);
        assert!(model.marked(source, second, second_y));
        assert!(model.marked(target, target_second, target_x));
        assert!(model.marked(target, target_second, target_y));

        let z = model.new_el(source, first);
        run.input("World::Fiber::El", z.0, &[source.0, first.0]);
        model.insert_edge(source, first, y, z);
        run.close(&mut model);
        let target_z = model.world_el_mor_app(outer, z).unwrap();
        assert!(model.marked(target, target_first, target_z));
        run.close(&mut model);
        run
    }};
}

#[test]
fn nested_morphisms_transport_late_facts_and_new_members() {
    assert_equivalent(nested_transport_variants!(nested_images));
}

macro_rules! random_morphism_graph {
    ($model:ty, $seed:expr) => {{
        let mut rng = StdRng::seed_from_u64($seed);
        let mut model = <$model>::new();
        let worlds: Vec<_> = (0..rng.random_range(3..=6))
            .map(|_| model.new_world())
            .collect();
        let mut members: Vec<Vec<_>> = worlds
            .iter()
            .map(|&world| {
                (0..rng.random_range(2..=4))
                    .map(|_| model.new_el(world))
                    .collect()
            })
            .collect();
        let mut edges = Vec::new();
        for source in 0..worlds.len() {
            for target in source + 1..worlds.len() {
                if target == source + 1 || rng.random_bool(0.4) {
                    edges.push((source, target));
                }
            }
            let x = members[source][0];
            let y = members[source][1];
            model.insert_marked(worlds[source], x);
            model.insert_edge(worlds[source], x, y);
            model.insert_next(worlds[source], x, y);
        }
        edges.push((0, 1));
        edges.shuffle(&mut rng);
        let mut run = Run::new(&model);
        run.close(&mut model);
        let mut arrows = Vec::new();
        for batch in edges.chunks(3) {
            let pending: Vec<_> = batch
                .iter()
                .map(|&(source, target)| {
                    let h = model.new_world_mor();
                    run.input("WorldMor", h.0, &[]);
                    model.insert_world_mor_dom(h, worlds[source]);
                    (source, target, h)
                })
                .collect();
            run.close(&mut model);
            for &(source, target, h) in &pending {
                model.insert_world_mor_cod(h, worlds[target]);
                for &x in &members[source] {
                    if rng.random_bool(0.75) {
                        let y = members[target][rng.random_range(0..members[target].len())];
                        model.insert_el_mor_app(h, x, y);
                    }
                }
            }
            arrows.extend(pending);
            run.close(&mut model);
        }
        for _ in 0..3 {
            let source = rng.random_range(0..worlds.len() - 1);
            let old = members[source][rng.random_range(0..members[source].len())];
            let fresh = model.new_el(worlds[source]);
            run.input("World::El", fresh.0, &[worlds[source].0]);
            members[source].push(fresh);
            model.insert_edge(worlds[source], old, fresh);
            model.insert_marked(worlds[source], old);
            model.insert_ready(worlds[source]);
            run.close(&mut model);
            assert!(model.marked(worlds[source], fresh));

            let other = members[source][rng.random_range(0..members[source].len())];
            model.equate_el(worlds[source], fresh, other);
            if rng.random_bool(0.5) {
                model.canonicalize();
            }
            run.close(&mut model);
            for &(dom, cod, h) in &arrows {
                for &x in &members[dom] {
                    let image = model.el_mor_app(h, x).unwrap();
                    assert!(model.world_member_el(worlds[cod], image));
                    if model.marked(worlds[dom], x) {
                        assert!(model.marked(worlds[cod], image));
                    }
                    if let Some(next) = model.next(worlds[dom], x) {
                        let next_image = model.el_mor_app(h, next).unwrap();
                        let image_next = model.next(worlds[cod], image).unwrap();
                        assert!(model.are_equal_el(next_image, image_next));
                    }
                }
            }
        }
        let parallel: Vec<_> = arrows
            .iter()
            .filter(|&&(dom, cod, _)| dom == 0 && cod == 1)
            .map(|&(_, _, h)| h)
            .collect();
        model.equate_world_mor(parallel[0], parallel[1]);
        run.close(&mut model);
        for &x in &members[0] {
            let first = model.el_mor_app(parallel[0], x).unwrap();
            let second = model.el_mor_app(parallel[1], x).unwrap();
            assert!(model.are_equal_el(first, second));
        }
        run.close(&mut model);
        run
    }};
}

#[test]
fn random_morphism_graphs_preserve_facts_functions_and_late_equalities() {
    let first_seed = setting("EQLOG_OPT_INPUT_SEED", 0);
    let count = setting("EQLOG_OPT_TRACES", 16);
    assert!(count > 0, "the morphism test needs at least one input seed");
    for offset in 0..count {
        let seed = first_seed.wrapping_add(offset);
        eprintln!("morphism graph seed {seed}");
        assert_equivalent(transport_variants!(random_morphism_graph, seed));
    }
}
