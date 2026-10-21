#![cfg(not(feature = "desugared"))]

use eqlog_test_eval as _;

mod generated {
    include!(concat!(
        env!("EQLOG_OUT_DIR"),
        "/eqlog-test-eval/src/compact_member_pending.eql.rs"
    ));

    pub fn pending_state(model: &CompactMemberPending) -> (usize, bool) {
        (model.__pending_delta.new_next_def.len(), model.__allocated)
    }
}

use generated::{pending_state, CompactMemberPending};

#[test]
fn materialization_keeps_queued_scoped_function_requests() {
    let mut model = CompactMemberPending::new();
    model.enable_compact_world();
    let unused = model.new_world();
    model.new_el(unused);
    let owner = model.new_world();
    let member = model.new_el(owner);
    let left = model.new_label();
    let right = model.new_label();
    model.insert_wanted(owner, member);
    model.insert_selected(owner);
    model.insert_merge_labels(left, right);
    assert!(model.close_until(|model| {
        model.ready(owner)
            && model.next(owner, member).is_none()
            && !model.are_equal_label(left, right)
    }));
    let before = pending_state(&model);
    assert_eq!(before.0, 1);
    model.equate_label(left, right);
    assert_eq!(pending_state(&model), before);
    model.close();
    let next = model.next(owner, member).unwrap();
    assert!(model.world_member_el(owner, next));
    assert!(!model.world_member_el(unused, next));
}

#[test]
fn live_scoped_requests_survive_global_equality_outputs() {
    let mut model = CompactMemberPending::new();
    model.enable_compact_world();
    let unused = model.new_world();
    model.new_el(unused);
    let owner = model.new_world();
    let member = model.new_el(owner);
    let left = model.new_label();
    let right = model.new_label();
    model.insert_wanted(owner, member);
    model.insert_selected(owner);
    model.insert_merge_labels(left, right);
    model.close();
    assert!(model.are_equal_label(left, right));
    let next = model.next(owner, member).unwrap();
    assert!(model.world_member_el(owner, next));
    assert!(!model.world_member_el(unused, next));
}
