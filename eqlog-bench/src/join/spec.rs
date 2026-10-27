use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::iter::Peekable;

use crate::Metrics;

#[derive(Clone, Copy)]
pub enum Role {
    Spare,
    Left,
    Right,
}

#[derive(Clone, Copy)]
pub struct Element {
    pub origin: u32,
    pub key: u32,
    pub group: u32,
    pub role: Role,
}

pub struct Node {
    pub parents: Vec<usize>,
    pub local: Vec<Element>,
}

pub struct Inputs {
    pub nodes: Vec<Node>,
    pub edges: Vec<(usize, usize)>,
    pub elements: Vec<Element>,
    pub key_origins: Vec<u32>,
    pub groups: usize,
}

pub trait Evaluator {
    type Member: Copy + Ord + Debug;

    fn close(&mut self);
    fn items(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member)> + '_>;
    fn members(&self) -> Box<dyn Iterator<Item = (usize, Self::Member)> + '_>;
    fn globals(&self) -> Box<dyn Iterator<Item = Self::Member> + '_>;
    fn left(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member)> + '_>;
    fn right(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member)> + '_>;
    fn pairs(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member, Self::Member)> + '_>;
    fn images(&self) -> Box<dyn Iterator<Item = (usize, Self::Member, Self::Member)> + '_>;
}

fn take_rows<'a, T: Copy + Ord + Debug + 'a>(
    rows: &mut Peekable<Box<dyn Iterator<Item = (usize, T)> + 'a>>,
    owner: usize,
) -> BTreeSet<T> {
    let mut result = BTreeSet::new();
    while rows.peek().is_some_and(|(next, _)| *next == owner) {
        assert!(
            result.insert(rows.next().unwrap().1),
            "duplicate public row"
        );
    }
    if let Some((next, _)) = rows.peek() {
        assert!(*next > owner, "owner enumeration is ordered");
    }
    result
}

pub fn verify<E: Evaluator>(engine: &E, input: &Inputs) -> Metrics {
    let mut domains: Vec<BTreeSet<u32>> = Vec::new();
    let mut items = (Box::new(engine.items().map(|(w, k, e)| (w, (k, e))))
        as Box<dyn Iterator<Item = _>>)
        .peekable();
    let mut members = engine.members().peekable();
    let mut left = (Box::new(engine.left().map(|(w, g, e)| (w, (g, e))))
        as Box<dyn Iterator<Item = _>>)
        .peekable();
    let mut right = (Box::new(engine.right().map(|(w, g, e)| (w, (g, e))))
        as Box<dyn Iterator<Item = _>>)
        .peekable();
    let mut pairs = (Box::new(engine.pairs().map(|(w, g, x, y)| (w, (g, x, y))))
        as Box<dyn Iterator<Item = _>>)
        .peekable();
    let mut global_map = BTreeMap::new();
    let mut total = Metrics {
        worlds: input.nodes.len(),
        morphisms: input.edges.len(),
        owned_elements: input.elements.len(),
        local_size: 0,
        checksum: 0xcbf29ce484222325,
    };
    for (owner, node) in input.nodes.iter().enumerate() {
        let mut domain: BTreeSet<u32> = node.local.iter().map(|e| e.origin).collect();
        for &parent in &node.parents {
            domain.extend(&domains[parent]);
        }
        let current = take_rows(&mut items, owner);
        assert_eq!(current.len(), domain.len());
        let mut by_origin = BTreeMap::new();
        let mut by_member = BTreeMap::new();
        for (key, member) in current {
            let origin = input.key_origins[key as usize];
            assert!(domain.contains(&origin));
            assert!(by_origin.insert(origin, member).is_none());
            assert!(by_member.insert(member, origin).is_none());
            assert!(
                global_map.insert(member, (owner, origin)).is_none(),
                "different owners retain different member identities"
            );
        }
        assert_eq!(
            take_rows(&mut members, owner),
            by_member.keys().copied().collect()
        );
        let mut expected_left = BTreeSet::new();
        let mut expected_right = BTreeSet::new();
        for &origin in &domain {
            let element = input.elements[origin as usize];
            match element.role {
                Role::Spare => {}
                Role::Left => {
                    expected_left.insert((element.group, origin));
                }
                Role::Right => {
                    expected_right.insert((element.group, origin));
                }
            }
        }
        let actual_left: BTreeSet<_> = take_rows(&mut left, owner)
            .into_iter()
            .map(|(group, member)| (group, by_member[&member]))
            .collect();
        let actual_right: BTreeSet<_> = take_rows(&mut right, owner)
            .into_iter()
            .map(|(group, member)| (group, by_member[&member]))
            .collect();
        assert_eq!(actual_left, expected_left);
        assert_eq!(actual_right, expected_right);
        let expected_pairs: BTreeSet<_> = expected_left
            .iter()
            .flat_map(|&(group, x)| {
                expected_right.iter().filter_map(move |&(other_group, y)| {
                    (group == other_group).then_some((group, x, y))
                })
            })
            .collect();
        let actual_pairs: BTreeSet<_> = take_rows(&mut pairs, owner)
            .into_iter()
            .map(|(group, x, y)| (group, by_member[&x], by_member[&y]))
            .collect();
        assert_eq!(actual_pairs, expected_pairs);
        let inherited_pairs: BTreeSet<_> = node
            .parents
            .iter()
            .flat_map(|&parent| {
                let domain = &domains[parent];
                expected_pairs
                    .iter()
                    .copied()
                    .filter(move |(_, x, y)| domain.contains(x) && domain.contains(y))
            })
            .collect();
        let local_inputs: usize = node
            .local
            .iter()
            .map(|element| match element.role {
                Role::Spare => 0,
                Role::Left | Role::Right => 1,
            })
            .sum();
        total.local_size += 2 * node.local.len()
            + local_inputs
            + expected_pairs.difference(&inherited_pairs).count();
        for &origin in &domain {
            for value in [owner as u64, origin as u64] {
                total.checksum ^= value;
                total.checksum = total.checksum.wrapping_mul(0x100000001b3);
            }
        }
        for &(group, x, y) in &expected_pairs {
            for value in [owner as u64, group as u64, x as u64, y as u64] {
                total.checksum ^= value;
                total.checksum = total.checksum.wrapping_mul(0x100000001b3);
            }
        }
        domains.push(domain);
    }
    assert!(items.next().is_none());
    assert!(members.next().is_none());
    assert!(left.next().is_none());
    assert!(right.next().is_none());
    assert!(pairs.next().is_none());
    let globals: Vec<_> = engine.globals().collect();
    assert_eq!(globals.len(), global_map.len());
    assert_eq!(
        globals.into_iter().collect::<BTreeSet<_>>(),
        global_map.keys().copied().collect()
    );
    let mut seen = BTreeSet::new();
    for (edge, source, target) in engine.images() {
        let (source_owner, target_owner) = input.edges[edge];
        let (actual_source, origin) = global_map[&source];
        let (actual_target, target_origin) = global_map[&target];
        assert_eq!(
            (actual_source, actual_target, origin),
            (source_owner, target_owner, target_origin)
        );
        assert!(domains[source_owner].contains(&origin));
        assert!(seen.insert((edge, origin)), "duplicate public image");
    }
    let expected_images: usize = input
        .edges
        .iter()
        .map(|&(parent, _)| domains[parent].len())
        .sum();
    assert_eq!(seen.len(), expected_images);
    total
}
