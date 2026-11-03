use std::collections::BTreeSet;

use eqlog_runtime::{PrefixTree1, PrefixTree2, PrefixTree3};

use super::spec::{Evaluator, Inputs, Role};

#[derive(Clone)]
struct World {
    carrier: PrefixTree1,
    items: PrefixTree2,
    left: PrefixTree2,
    right: PrefixTree2,
    pairs: PrefixTree3,
}

impl World {
    fn new() -> Self {
        Self {
            carrier: PrefixTree1::new(),
            items: PrefixTree2::new(),
            left: PrefixTree2::new(),
            right: PrefixTree2::new(),
            pairs: PrefixTree3::new(),
        }
    }

    fn product(&mut self, group: u32, left: &PrefixTree1, right: &PrefixTree1) {
        if left.is_empty() || right.is_empty() {
            return;
        }
        let mut rows = PrefixTree2::new();
        for [x] in left.iter() {
            // Suffix sharing avoids materializing every pair.
            rows.insert_restriction(x, right.clone());
        }
        if let Some(previous) = self.pairs.get(group) {
            rows = rows.union(previous);
        }
        self.pairs.insert_restriction(group, rows);
    }

    fn close_local(&mut self) {
        let groups: Vec<_> = self.left.map.iter().map(|(group, _)| group).collect();
        for group in groups {
            let left = self.left.get(group).unwrap().clone();
            if let Some(right) = self.right.get(group).cloned() {
                self.product(group, &left, &right);
            }
        }
    }

    fn merge(&mut self, other: &Self) {
        let mut groups = BTreeSet::new();
        assert!(other
            .left
            .map
            .all_difference_entries(&self.left.map, |group, _, _| {
                groups.insert(group);
                true
            }));
        assert!(other
            .right
            .map
            .all_difference_entries(&self.right.map, |group, _, _| {
                groups.insert(group);
                true
            }));
        self.pairs = self.pairs.union(&other.pairs);
        for group in groups {
            let left = self.left.get(group).unwrap_or_else(|| PrefixTree1::empty());
            let right = self
                .right
                .get(group)
                .unwrap_or_else(|| PrefixTree1::empty());
            let other_left = other
                .left
                .get(group)
                .unwrap_or_else(|| PrefixTree1::empty());
            let other_right = other
                .right
                .get(group)
                .unwrap_or_else(|| PrefixTree1::empty());
            let only_left = left.difference(other_left);
            let only_right = right.difference(other_right);
            let only_other_left = other_left.difference(left);
            let only_other_right = other_right.difference(right);
            // Each input already contains its internal products.
            self.product(group, &only_left, &only_other_right);
            self.product(group, &only_other_left, &only_right);
        }
        self.carrier = self.carrier.union(&other.carrier);
        self.items = self.items.union(&other.items);
        self.left = self.left.union(&other.left);
        self.right = self.right.union(&other.right);
    }
}

pub struct Cow {
    worlds: Vec<World>,
    parents: Vec<Vec<usize>>,
    edges: Vec<(usize, usize)>,
    closed: bool,
}

impl Cow {
    pub fn new(input: &Inputs) -> Self {
        let worlds = input
            .nodes
            .iter()
            .map(|node| {
                let mut world = World::new();
                for element in &node.local {
                    world.carrier.insert([element.origin]);
                    world.items.insert([element.key, element.origin]);
                    match element.role {
                        Role::Spare => {}
                        Role::Left => {
                            world.left.insert([element.group, element.origin]);
                        }
                        Role::Right => {
                            world.right.insert([element.group, element.origin]);
                        }
                    }
                }
                world
            })
            .collect();
        Self {
            worlds,
            parents: input
                .nodes
                .iter()
                .map(|node| node.parents.clone())
                .collect(),
            edges: input.edges.clone(),
            closed: false,
        }
    }
}

impl Evaluator for Cow {
    type Member = (usize, u32);

    fn close(&mut self) {
        if self.closed {
            return;
        }
        for owner in 0..self.worlds.len() {
            let mut world = self.worlds[owner].clone();
            world.close_local();
            for &parent in &self.parents[owner] {
                world.merge(&self.worlds[parent]);
            }
            self.worlds[owner] = world;
        }
        self.closed = true;
    }

    fn items(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member)> + '_> {
        Box::new(self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .items
                .iter()
                .map(move |[key, element]| (owner, key, (owner, element)))
        }))
    }

    fn members(&self) -> Box<dyn Iterator<Item = (usize, Self::Member)> + '_> {
        Box::new(self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .carrier
                .iter()
                .map(move |[element]| (owner, (owner, element)))
        }))
    }

    fn globals(&self) -> Box<dyn Iterator<Item = Self::Member> + '_> {
        Box::new(self.members().map(|(_, element)| element))
    }

    fn left(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member)> + '_> {
        Box::new(self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .left
                .iter()
                .map(move |[group, element]| (owner, group, (owner, element)))
        }))
    }

    fn right(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member)> + '_> {
        Box::new(self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .right
                .iter()
                .map(move |[group, element]| (owner, group, (owner, element)))
        }))
    }

    fn pairs(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member, Self::Member)> + '_> {
        Box::new(self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .pairs
                .iter()
                .map(move |[group, x, y]| (owner, group, (owner, x), (owner, y)))
        }))
    }

    fn images(&self) -> Box<dyn Iterator<Item = (usize, Self::Member, Self::Member)> + '_> {
        Box::new(
            self.edges
                .iter()
                .enumerate()
                .flat_map(move |(edge, &(source, target))| {
                    self.worlds[source]
                        .carrier
                        .iter()
                        .filter(move |_| self.closed)
                        .map(move |[element]| (edge, (source, element), (target, element)))
                }),
        )
    }
}
