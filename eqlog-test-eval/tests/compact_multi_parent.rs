#![cfg(not(feature = "desugared"))]

use eqlog_test_eval as _;

mod generated {
    include!(concat!(
        env!("EQLOG_OUT_DIR"),
        "/eqlog-test-eval/src/compact_multi_parent.eql.rs"
    ));
}

use generated::{CompactMultiParent, El, World, WorldMor};

fn inherit(model: &mut CompactMultiParent, source: World, target: World) -> WorldMor {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    assert!(model.inherit_total_world_members(morphism));
    morphism
}

fn named(model: &mut CompactMultiParent, owner: World) -> El {
    let key = model.new_key();
    let member = model.new_el(owner);
    model.insert_named(owner, member, key);
    member
}

struct FanIn {
    model: CompactMultiParent,
    source: World,
    parents: [World; 3],
    target: World,
    child: World,
    members: Vec<El>,
    to_parent: [WorldMor; 3],
    from_parent: [WorldMor; 3],
    to_child: WorldMor,
}

impl FanIn {
    fn new(member_count: usize) -> Self {
        let mut model = CompactMultiParent::new();
        model.enable_compact_world();
        let source = model.new_world();
        let parents = std::array::from_fn(|_| model.new_world());
        let target = model.new_world();
        let child = model.new_world();
        let members = (0..member_count)
            .map(|_| named(&mut model, source))
            .collect();
        let to_parent = parents.map(|parent| inherit(&mut model, source, parent));
        let from_parent = parents.map(|parent| inherit(&mut model, parent, target));
        let to_child = inherit(&mut model, target, child);
        Self {
            model,
            source,
            parents,
            target,
            child,
            members,
            to_parent,
            from_parent,
            to_child,
        }
    }

    fn at_parent(&self, parent: usize, member: usize) -> El {
        self.model
            .el_mor_app(self.to_parent[parent], self.members[member])
            .unwrap()
    }

    fn at_target(&self, member: usize) -> El {
        self.model
            .el_mor_app(self.from_parent[0], self.at_parent(0, member))
            .unwrap()
    }

    fn at_child(&self, member: usize) -> El {
        self.model
            .el_mor_app(self.to_child, self.at_target(member))
            .unwrap()
    }
}

#[test]
fn shared_facts_keep_every_parent_membership_without_hiding_mixed_joins() {
    let mut run = FanIn::new(5);
    let memberships = [
        (
            [true, true, true, false, false],
            [false, false, true, false, false],
            [false, false, true, false, false],
        ),
        (
            [false, true, false, false, false],
            [true, true, false, false, false],
            [false; 5],
        ),
        (
            [false, false, false, true, false],
            [false, true, false, true, false],
            [true, true, false, true, false],
        ),
    ];
    for (parent, (p, q, r)) in memberships.into_iter().enumerate() {
        for member in 0..5 {
            let value = run.at_parent(parent, member);
            if p[member] {
                run.model.insert_p(run.parents[parent], value);
            }
            if q[member] {
                run.model.insert_q(run.parents[parent], value);
            }
            if r[member] {
                run.model.insert_r(run.parents[parent], value);
            }
        }
    }
    run.model.close();
    for (parent, (p, q, r)) in memberships.into_iter().enumerate() {
        for member in 0..5 {
            let value = run.at_parent(parent, member);
            assert_eq!(
                run.model.pq(run.parents[parent], value),
                p[member] && q[member]
            );
            assert_eq!(
                run.model.pqr(run.parents[parent], value),
                p[member] && q[member] && r[member]
            );
        }
    }
    for member in 0..5 {
        assert_eq!(run.model.pqr(run.target, run.at_target(member)), member < 4);
        assert_eq!(run.model.pqr(run.child, run.at_child(member)), member < 4);
        assert!(!run.model.pqr(run.source, run.members[member]));
    }
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..5 {
                let expected = x < 4 && y < 4 && z < 4;
                assert_eq!(
                    run.model.triple(
                        run.target,
                        run.at_target(x),
                        run.at_target(y),
                        run.at_target(z)
                    ),
                    expected
                );
                assert_eq!(
                    run.model
                        .triple(run.child, run.at_child(x), run.at_child(y), run.at_child(z)),
                    expected
                );
            }
        }
    }
    let count = run.model.iter_triple().count();
    run.model.close();
    assert_eq!(run.model.iter_triple().count(), count);
}

#[test]
fn late_parent_inputs_join_previous_target_work_and_local_rows() {
    let mut run = FanIn::new(3);
    run.model.insert_p(run.parents[0], run.at_parent(0, 0));
    run.model.insert_q(run.parents[1], run.at_parent(1, 0));
    run.model.insert_q(run.parents[0], run.at_parent(0, 1));
    run.model.insert_p(run.parents[2], run.at_parent(2, 1));
    run.model.insert_p(run.target, run.at_target(2));
    run.model.close();
    for member in 0..2 {
        assert!(run.model.pq(run.target, run.at_target(member)));
        assert!(!run.model.pqr(run.target, run.at_target(member)));
    }
    run.model.insert_r(run.parents[0], run.at_parent(0, 0));
    run.model.insert_r(run.parents[2], run.at_parent(2, 1));
    run.model.insert_q(run.parents[1], run.at_parent(1, 2));
    run.model.close();
    for member in 0..2 {
        assert!(run.model.pqr(run.target, run.at_target(member)));
        assert!(run.model.pqr(run.child, run.at_child(member)));
        for parent in 0..3 {
            assert!(!run
                .model
                .pqr(run.parents[parent], run.at_parent(parent, member)));
        }
    }
    assert!(run.model.pq(run.target, run.at_target(2)));
    assert!(!run.model.pqr(run.target, run.at_target(2)));
    run.model.insert_r(run.parents[2], run.at_parent(2, 2));
    run.model.close();
    assert!(run.model.pqr(run.target, run.at_target(2)));
    assert!(run.model.pqr(run.child, run.at_child(2)));

    let late = named(&mut run.model, run.parents[2]);
    run.model.insert_p(run.parents[2], late);
    run.model.close();
    let target_late = run.model.el_mor_app(run.from_parent[2], late).unwrap();
    run.model.insert_q(run.target, target_late);
    run.model.close();
    let child_late = run.model.el_mor_app(run.to_child, target_late).unwrap();
    assert!(run.model.pq(run.target, target_late));
    assert!(run.model.pq(run.child, child_late));
    assert!(!run.model.pq(run.parents[2], late));
}

#[test]
fn a_target_equation_creates_a_join_absent_from_every_parent() {
    let mut run = FanIn::new(4);
    run.model
        .insert_edge(run.parents[0], run.at_parent(0, 0), run.at_parent(0, 1));
    run.model
        .insert_tail(run.parents[1], run.at_parent(1, 2), run.at_parent(1, 3));
    run.model.close();
    assert_eq!(run.model.iter_path().count(), 0);
    run.model
        .equate_el(run.target, run.at_target(1), run.at_target(2));
    run.model.close();
    assert!(run
        .model
        .path(run.target, run.at_target(0), run.at_target(3)));
    assert!(run.model.path(run.child, run.at_child(0), run.at_child(3)));
    assert_eq!(run.model.iter_path().count(), 2);
    for parent in 0..3 {
        assert!(!run
            .model
            .are_equal_el(run.at_parent(parent, 1), run.at_parent(parent, 2)));
    }
    run.model.close();
    assert_eq!(run.model.iter_path().count(), 2);
}

#[test]
fn a_parent_certificate_does_not_include_joins_created_by_target_equality() {
    let mut model = CompactMultiParent::new();
    model.enable_compact_world();
    let [source, target, child] = std::array::from_fn(|_| model.new_world());
    let members: [El; 4] = std::array::from_fn(|_| named(&mut model, source));
    model.insert_edge(source, members[0], members[1]);
    model.insert_tail(source, members[2], members[3]);
    model.close();
    let to_target = inherit(&mut model, source, target);
    let target_members = members.map(|member| model.el_mor_app(to_target, member).unwrap());
    let to_child = inherit(&mut model, target, child);
    model.close();
    assert_eq!(model.iter_path().count(), 0);
    model.equate_el(target, target_members[1], target_members[2]);
    model.close();
    let child_members = target_members.map(|member| model.el_mor_app(to_child, member).unwrap());
    assert!(model.path(target, target_members[0], target_members[3]));
    assert!(model.path(child, child_members[0], child_members[3]));
    assert_eq!(model.iter_path().count(), 2);
    assert!(!model.are_equal_el(members[1], members[2]));
}

#[test]
fn ancestor_equality_reopens_a_previously_unmatched_cross_parent_join() {
    let mut run = FanIn::new(4);
    run.model
        .insert_edge(run.parents[0], run.at_parent(0, 0), run.at_parent(0, 1));
    run.model
        .insert_tail(run.parents[2], run.at_parent(2, 2), run.at_parent(2, 3));
    run.model.close();
    assert_eq!(run.model.iter_path().count(), 0);
    run.model
        .equate_el(run.source, run.members[1], run.members[2]);
    run.model.close();
    assert!(run
        .model
        .path(run.target, run.at_target(0), run.at_target(3)));
    assert!(run.model.path(run.child, run.at_child(0), run.at_child(3)));
    assert_eq!(run.model.iter_path().count(), 2);
}

#[test]
fn interrupted_mixed_parent_matches_keep_pending_existential_conclusions() {
    let mut run = FanIn::new(2);
    run.model.insert_p(run.parents[0], run.at_parent(0, 0));
    run.model
        .insert_request(run.parents[1], run.at_parent(1, 0));
    run.model.insert_p(run.parents[2], run.at_parent(2, 1));
    let target_first = run.at_target(0);
    let target_second = run.at_target(1);
    assert!(run.model.close_until(|model| {
        model.ready(run.target, target_first) && model.witness(run.target, target_first).is_none()
    }));
    run.model
        .insert_request(run.parents[2], run.at_parent(2, 1));
    run.model.close();
    let first_witness = run.model.witness(run.target, target_first).unwrap();
    let source_witness = run
        .model
        .witness(run.parents[2], run.at_parent(2, 1))
        .unwrap();
    let second_witness = run
        .model
        .el_mor_app(run.from_parent[2], source_witness)
        .unwrap();
    assert_eq!(
        run.model.witness(run.target, target_second),
        Some(second_witness)
    );
    assert!(!run.model.are_equal_el(first_witness, second_witness));
    for (member, witness) in [(0, first_witness), (1, second_witness)] {
        assert!(run
            .model
            .witnessed(run.target, run.at_target(member), witness));
        let child_witness = run.model.el_mor_app(run.to_child, witness).unwrap();
        assert_eq!(
            run.model.witness(run.child, run.at_child(member)),
            Some(child_witness)
        );
        assert!(run
            .model
            .witnessed(run.child, run.at_child(member), child_witness));
    }
    assert_eq!(run.model.witness(run.parents[0], run.at_parent(0, 0)), None);
    assert_eq!(run.model.witness(run.parents[1], run.at_parent(1, 0)), None);
    run.model.close();
    assert_eq!(
        run.model.witness(run.target, target_first),
        Some(first_witness)
    );
}

#[test]
fn distinct_parent_certificates_do_not_alias_across_a_machine_word() {
    let mut model = CompactMultiParent::new();
    model.enable_compact_world();
    let source = model.new_world();
    let parents: Vec<_> = (0..70).map(|_| model.new_world()).collect();
    let target = model.new_world();
    let member = named(&mut model, source);
    let to_parent: Vec<_> = parents
        .iter()
        .map(|&parent| inherit(&mut model, source, parent))
        .collect();
    let images: Vec<_> = to_parent
        .iter()
        .map(|&morphism| model.el_mor_app(morphism, member).unwrap())
        .collect();
    model.insert_p(parents[0], images[0]);
    model.insert_q(parents[64], images[64]);
    model.insert_r(parents[69], images[69]);
    let to_target: Vec<_> = parents
        .iter()
        .map(|&parent| inherit(&mut model, parent, target))
        .collect();
    model.close();
    let target_member = model.el_mor_app(to_target[0], images[0]).unwrap();
    assert!(model.pqr(target, target_member));
    assert!(model.triple(target, target_member, target_member, target_member));
    assert_eq!(model.iter_pqr().count(), 1);
    for (&morphism, &image) in to_target.iter().zip(&images) {
        assert_eq!(model.el_mor_app(morphism, image), Some(target_member));
    }
}

#[test]
fn repeated_relations_keep_their_distinct_atom_bindings() {
    let mut run = FanIn::new(3);
    run.model
        .insert_edge(run.parents[0], run.at_parent(0, 0), run.at_parent(0, 1));
    run.model
        .insert_edge(run.parents[1], run.at_parent(1, 1), run.at_parent(1, 2));
    run.model
        .insert_edge(run.parents[2], run.at_parent(2, 0), run.at_parent(2, 1));
    run.model
        .insert_edge(run.parents[2], run.at_parent(2, 1), run.at_parent(2, 0));
    run.model.close();
    assert!(run
        .model
        .two_step(run.target, run.at_target(0), run.at_target(2)));
    assert!(run
        .model
        .two_step(run.child, run.at_child(0), run.at_child(2)));
    assert_eq!(run.model.iter_two_step().count(), 8);
    run.model
        .insert_edge(run.parents[1], run.at_parent(1, 2), run.at_parent(1, 0));
    run.model.close();
    assert!(run
        .model
        .two_step(run.target, run.at_target(2), run.at_target(1)));
    assert!(run
        .model
        .two_step(run.child, run.at_child(2), run.at_child(1)));
    assert!(!run
        .model
        .two_step(run.parents[1], run.at_parent(1, 2), run.at_parent(1, 1)));
    assert_eq!(
        run.model
            .iter_two_step()
            .filter(|(owner, _, _)| *owner == run.target)
            .count(),
        5
    );
}

#[test]
fn independent_function_results_still_collide_at_the_target() {
    let mut run = FanIn::new(1);
    let key = run.model.new_key();
    let first = named(&mut run.model, run.parents[0]);
    let second = named(&mut run.model, run.parents[1]);
    run.model.insert_value(run.parents[0], key, first);
    run.model.insert_value(run.parents[1], key, second);
    run.model.insert_p(run.parents[0], first);
    run.model.insert_q(run.parents[1], second);
    run.model.close();
    let first_image = run.model.el_mor_app(run.from_parent[0], first).unwrap();
    let second_image = run.model.el_mor_app(run.from_parent[1], second).unwrap();
    assert!(run.model.are_equal_el(first_image, second_image));
    assert!(!run.model.are_equal_el(first, second));
    let value = run.model.value(run.target, key).unwrap();
    assert_eq!(run.model.root_el(first_image), value);
    assert!(run.model.pq(run.target, value));
    let child_value = run.model.el_mor_app(run.to_child, value).unwrap();
    assert_eq!(run.model.value(run.child, key), Some(child_value));
    assert!(run.model.pq(run.child, child_value));
    assert!(!run.model.pq(run.parents[0], first));
    assert!(!run.model.pq(run.parents[1], second));
}

#[test]
fn projected_private_witnesses_do_not_hide_a_new_cross_parent_pair() {
    let mut run = FanIn::new(4);
    run.model
        .insert_support(run.parents[0], run.at_parent(0, 0), run.at_parent(0, 1));
    run.model.insert_q(run.parents[0], run.at_parent(0, 2));
    run.model
        .insert_support(run.parents[1], run.at_parent(1, 0), run.at_parent(1, 3));
    run.model.insert_q(run.parents[1], run.at_parent(1, 1));
    run.model.insert_q(run.parents[2], run.at_parent(2, 3));
    run.model.close();
    for member in 1..4 {
        assert!(run
            .model
            .supported_pair(run.target, run.at_target(0), run.at_target(member)));
        assert!(run
            .model
            .supported_pair(run.child, run.at_child(0), run.at_child(member)));
    }
    assert!(!run
        .model
        .supported_pair(run.target, run.at_target(0), run.at_target(0)));
    run.model.insert_q(run.target, run.at_target(0));
    run.model.close();
    for member in 0..4 {
        assert!(run
            .model
            .supported_pair(run.target, run.at_target(0), run.at_target(member)));
        assert!(run
            .model
            .supported_pair(run.child, run.at_child(0), run.at_child(member)));
    }
    assert_eq!(run.model.iter_supported_pair().count(), 10);
}
