use super::generated::{El, World};
use super::Engine;
use crate::dag::spec::{Inputs, Metrics, Oracle, SEED};
use std::collections::BTreeMap;
use std::iter::Peekable;

struct HandleSet(Vec<u64>);

impl HandleSet {
    fn insert(&mut self, element: El) -> bool {
        let word = element.0 as usize / 64;
        let bit = 1_u64 << (element.0 % 64);
        if word >= self.0.len() {
            self.0.resize(word + 1, 0);
        }
        let absent = self.0[word] & bit == 0;
        self.0[word] |= bit;
        absent
    }

    fn remove(&mut self, element: El) -> bool {
        let word = element.0 as usize / 64;
        let bit = 1_u64 << (element.0 % 64);
        if word >= self.0.len() {
            return false;
        }
        let present = self.0[word] & bit != 0;
        self.0[word] &= !bit;
        present
    }
}

fn owner_relation(
    rows: &mut Peekable<impl Iterator<Item = (World, El)>>,
    world: World,
    inverse: &BTreeMap<El, u32>,
    expected: impl Fn(u32) -> bool,
    expected_count: usize,
    key_bound: usize,
) {
    let mut seen = vec![false; key_bound];
    let mut count = 0;
    while let Some(&(row_owner, element)) = rows.peek() {
        if row_owner != world {
            break;
        }
        rows.next().unwrap();
        let key = *inverse
            .get(&element)
            .expect("predicate or carrier contains an unnamed member");
        assert!(expected(key), "unexpected predicate or carrier row");
        assert!(
            !std::mem::replace(&mut seen[key as usize], true),
            "duplicate predicate or carrier row"
        );
        count += 1;
    }
    assert_eq!(
        count, expected_count,
        "missing rows or iterator owner grouping changed"
    );
}

pub(super) fn verify(workload: &Engine, inputs: &Inputs, expected: &Oracle) -> Metrics {
    assert_eq!(workload.worlds.len(), inputs.nodes.len());
    assert_eq!(workload.keys.len(), SEED as usize + inputs.nodes.len());
    assert_eq!(workload.morphisms.len(), inputs.edges.len());
    let model = &workload.model;
    assert!(
        model.iter_world().eq(workload.worlds.iter().copied()),
        "unexpected World carrier"
    );
    assert!(
        model.iter_key().eq(workload.keys.iter().copied()),
        "unexpected Key carrier"
    );
    assert!(
        model
            .iter_world_mor()
            .eq(workload.morphisms.iter().copied()),
        "unexpected WorldMor carrier"
    );
    let key_labels: BTreeMap<_, _> = workload
        .keys
        .iter()
        .copied()
        .enumerate()
        .map(|(key, handle)| (handle, u32::try_from(key).unwrap()))
        .collect();
    assert_eq!(key_labels.len(), workload.keys.len());
    let mut carrier = HandleSet(Vec::new());
    let mut items = model.iter_item().peekable();
    let mut members = model.iter_world_member_el().peekable();
    let mut marks = model.iter_marked().peekable();
    let mut elements = 0;
    let mut member_rows = 0;
    for (owner, &world) in workload.worlds.iter().enumerate() {
        let key_bound = workload.keys.len();
        let expected_count = expected.keys(owner).count();
        let mut seen = vec![false; key_bound];
        let mut inverse = BTreeMap::new();
        while let Some(&(row_owner, key, element)) = items.peek() {
            if row_owner != world {
                break;
            }
            items.next().unwrap();
            let key_label = *key_labels
                .get(&key)
                .expect("item references an unknown global key");
            assert!(
                expected.contains_key(owner, key_label),
                "unexpected owner/key item row"
            );
            assert!(
                !std::mem::replace(&mut seen[key_label as usize], true),
                "duplicate owner/key item row"
            );
            assert_eq!(model.root_el(element), element);
            assert_eq!(model.item(world, key), Some(element));
            assert!(
                inverse.insert(element, key_label).is_none(),
                "distinct keys must have distinct members"
            );
            assert!(
                carrier.insert(element),
                "members of distinct owners must remain disjoint"
            );
        }
        assert_eq!(
            inverse.len(),
            expected_count,
            "missing items or iterator owner grouping changed"
        );
        let mark_count = expected.marked(owner).count();
        owner_relation(
            &mut members,
            world,
            &inverse,
            |_| true,
            expected_count,
            key_bound,
        );
        owner_relation(
            &mut marks,
            world,
            &inverse,
            |key| expected.contains_marked(owner, key),
            mark_count,
            key_bound,
        );
        elements += expected_count;
        member_rows += expected_count + mark_count;
    }
    assert!(
        items.next().is_none(),
        "extra item rows or iterator owner grouping changed"
    );
    assert!(
        members.next().is_none(),
        "extra carrier rows or iterator owner grouping changed"
    );
    assert!(
        marks.next().is_none(),
        "extra marked rows or iterator owner grouping changed"
    );
    let mut actual_elements = 0;
    for element in model.iter_el() {
        assert!(
            carrier.remove(element),
            "extra or duplicate canonical carrier member"
        );
        actual_elements += 1;
    }
    assert_eq!(actual_elements, elements);
    assert!(carrier.0.iter().all(|&word| word == 0));
    drop(carrier);

    let mut image_rows = model.iter_el_mor_app().peekable();
    let mut images = 0;
    let mut previous_parent = None;
    let mut source_labels = BTreeMap::new();
    for (&morphism, &(parent, owner)) in workload.morphisms.iter().zip(&inputs.edges) {
        let source_world = workload.worlds[parent];
        let target_world = workload.worlds[owner];
        assert_eq!(model.world_mor_dom(morphism), Some(source_world));
        assert_eq!(model.world_mor_cod(morphism), Some(target_world));
        if previous_parent != Some(parent) {
            source_labels.clear();
            for key in expected.keys(parent) {
                let source = model
                    .item(source_world, workload.keys[key as usize])
                    .unwrap();
                assert!(source_labels.insert(source, key).is_none());
            }
            previous_parent = Some(parent);
        }
        let mut seen = vec![false; workload.keys.len()];
        let mut count = 0;
        while let Some(&(row_morphism, source, target)) = image_rows.peek() {
            if row_morphism != morphism {
                break;
            }
            image_rows.next().unwrap();
            let key = *source_labels
                .get(&source)
                .expect("image source is outside the morphism domain");
            assert!(
                !std::mem::replace(&mut seen[key as usize], true),
                "duplicate morphism image"
            );
            let expected_target = model
                .item(target_world, workload.keys[key as usize])
                .unwrap();
            assert_eq!(
                target, expected_target,
                "image does not preserve the named member"
            );
            assert_eq!(model.el_mor_app(morphism, source), Some(expected_target));
            count += 1;
        }
        assert_eq!(
            count,
            source_labels.len(),
            "missing images or iterator morphism grouping changed"
        );
        images += count;
    }
    assert!(
        image_rows.next().is_none(),
        "extra images or iterator morphism grouping changed"
    );
    let metrics = expected.metrics();
    assert_eq!(metrics.elements, elements);
    assert_eq!(metrics.member_rows, member_rows);
    assert_eq!(metrics.images, images);
    metrics
}
