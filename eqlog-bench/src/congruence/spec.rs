use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;

use crate::Metrics;

use super::Input;

pub(super) trait View {
    type Member: Copy + Debug + Ord;

    fn item(&self, owner: usize, key: u32) -> Option<Self::Member>;
    fn next(&self, owner: usize, member: Self::Member) -> Option<Self::Member>;
    fn local_root(&self, owner: usize, key: usize, level: usize) -> Self::Member;
    fn image(&self, edge: usize, member: Self::Member) -> Option<Self::Member>;
    fn items(&self) -> impl Iterator<Item = (usize, u32, Self::Member)>;
    fn next_rows(&self) -> impl Iterator<Item = (usize, Self::Member, Self::Member)>;
    fn members(&self) -> impl Iterator<Item = (usize, Self::Member)>;
    fn globals(&self) -> impl Iterator<Item = Self::Member>;
    fn images(&self) -> impl Iterator<Item = (usize, Self::Member, Self::Member)>;
}

pub(super) fn exact<T: Ord + Debug>(rows: impl Iterator<Item = T>, expected: BTreeSet<T>) {
    let mut actual = BTreeSet::new();
    for row in rows {
        assert!(actual.insert(row), "duplicate public row");
    }
    assert_eq!(actual, expected);
}

pub(super) fn verify<V: View>(model: &V, input: &Input) -> Metrics {
    let mut expected_items = BTreeSet::new();
    let mut expected_next = BTreeSet::new();
    let mut expected_members = BTreeSet::new();
    let mut expected_globals = BTreeSet::new();
    let mut expected_images = BTreeSet::new();
    let mut previous = BTreeMap::new();
    let mut checksum = 0xcbf29ce484222325_u64;
    for owner in 0..input.vertices {
        let mut classes = BTreeMap::new();
        for key in 0..input.keys {
            let mut member = model.item(owner, u32::try_from(key).unwrap()).unwrap();
            expected_items.insert((owner, u32::try_from(key).unwrap(), member));
            for level in 0..=input.depth {
                assert_eq!(model.local_root(owner, key, level), member);
                assert!(classes.insert((key, level), member).is_none());
                assert!(
                    expected_members.insert((owner, member)),
                    "unrelated classes merged"
                );
                assert!(
                    expected_globals.insert(member),
                    "different owners share an identity"
                );
                if owner > 0 {
                    let source = previous[&(key, level)];
                    assert_eq!(model.image(owner - 1, source), Some(member));
                    expected_images.insert((owner - 1, source, member));
                }
                for part in [owner as u64, key as u64, level as u64] {
                    checksum ^= part;
                    checksum = checksum.wrapping_mul(0x100000001b3);
                }
                if level < input.depth {
                    let successor = model.next(owner, member).unwrap();
                    expected_next.insert((owner, member, successor));
                    member = successor;
                } else {
                    assert_eq!(model.next(owner, member), None);
                }
            }
        }
        previous = classes;
    }
    exact(model.items(), expected_items);
    exact(model.next_rows(), expected_next);
    exact(model.members(), expected_members);
    exact(model.globals(), expected_globals);
    exact(model.images(), expected_images);
    let owned_elements = input.vertices * input.width();
    Metrics {
        worlds: input.vertices,
        morphisms: input.vertices - 1,
        owned_elements,
        local_size: 2 * owned_elements,
        checksum,
    }
}
