use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;

use eqlog_runtime::PrefixTree1;

use super::Input;
use crate::Metrics;

pub(super) struct Members<M> {
    pub by_handle: Vec<BTreeMap<M, u32>>,
    pub origins: Vec<BTreeSet<u32>>,
    pub metrics: Metrics,
}

pub(super) fn exact<T: Ord + Debug>(actual: impl IntoIterator<Item = T>, expected: BTreeSet<T>) {
    let mut rows = BTreeSet::new();
    for row in actual {
        assert!(rows.insert(row), "duplicate public row");
    }
    assert_eq!(rows, expected);
}

pub(super) fn topology(
    input: &Input,
    worlds: impl IntoIterator<Item = u32>,
    morphisms: impl IntoIterator<Item = u32>,
    domains: impl IntoIterator<Item = (u32, u32)>,
    codomains: impl IntoIterator<Item = (u32, u32)>,
) {
    exact(
        worlds,
        (0..u32::try_from(input.graph.parents.len()).unwrap()).collect(),
    );
    exact(
        morphisms,
        (0..u32::try_from(input.graph.edges.len()).unwrap()).collect(),
    );
    exact(
        domains,
        input
            .graph
            .edges
            .iter()
            .enumerate()
            .map(|(edge, &(source, _))| {
                (u32::try_from(edge).unwrap(), u32::try_from(source).unwrap())
            })
            .collect(),
    );
    exact(
        codomains,
        input
            .graph
            .edges
            .iter()
            .enumerate()
            .map(|(edge, &(_, target))| {
                (u32::try_from(edge).unwrap(), u32::try_from(target).unwrap())
            })
            .collect(),
    );
}

pub(super) fn rows<const N: usize>(
    actual: impl IntoIterator<Item = [u32; N]>,
    expected: BTreeSet<[u32; N]>,
    metrics: &mut Metrics,
) {
    hash(metrics, [u64::MAX, N as u64]);
    for row in &expected {
        hash(metrics, row.iter().map(|&value| u64::from(value)));
    }
    exact(actual, expected);
}

pub(super) fn members<M: Copy + Debug + Ord>(
    input: &Input,
    local: &[Vec<M>],
    actual_members: impl IntoIterator<Item = (usize, M)>,
    actual_globals: impl IntoIterator<Item = M>,
    actual_images: impl IntoIterator<Item = (usize, M, M)>,
) -> Members<M> {
    let mut images = BTreeMap::new();
    for (edge, source, target) in actual_images {
        assert!(images.insert((edge, source), target).is_none());
    }
    let mut incoming = vec![Vec::new(); input.graph.parents.len()];
    for (edge, &(source, target)) in input.graph.edges.iter().enumerate() {
        incoming[target].push((edge, source));
    }
    let ancestors = input.graph.ancestors();
    let mut by_origin: Vec<BTreeMap<u32, M>> = Vec::new();
    let mut by_handle = Vec::new();
    let mut origins = Vec::new();
    let mut expected_members = BTreeSet::new();
    let mut expected_globals = BTreeSet::new();
    let mut expected_images = BTreeMap::new();
    let mut metrics = Metrics {
        worlds: input.graph.parents.len(),
        morphisms: input.graph.edges.len(),
        owned_elements: input.member_count(),
        local_size: input.member_count(),
        checksum: 0xcbf29ce484222325,
    };
    for owner in 0..input.graph.parents.len() {
        let mut current = BTreeMap::new();
        assert_eq!(local[owner].len(), input.members);
        for (origin, &member) in input.local(owner).zip(&local[owner]) {
            assert!(current.insert(origin, member).is_none());
        }
        for &(edge, parent) in &incoming[owner] {
            for (&origin, &source) in &by_origin[parent] {
                let target = images[&(edge, source)];
                assert!(current.insert(origin, target).is_none());
                assert!(expected_images.insert((edge, source), target).is_none());
            }
        }
        let expected_origins: BTreeSet<_> = ancestors[owner]
            .iter()
            .flat_map(|&ancestor| input.local(ancestor))
            .collect();
        assert_eq!(
            current.keys().copied().collect::<BTreeSet<_>>(),
            expected_origins
        );
        let mut reverse = BTreeMap::new();
        for (&origin, &member) in &current {
            assert!(
                reverse.insert(member, origin).is_none(),
                "unexpected member merge"
            );
            assert!(
                expected_globals.insert(member),
                "owners share a member identity"
            );
            expected_members.insert((owner, member));
            hash(&mut metrics, [owner as u64, u64::from(origin)]);
        }
        by_origin.push(current);
        by_handle.push(reverse);
        origins.push(expected_origins);
    }
    exact(actual_members, expected_members);
    exact(actual_globals, expected_globals);
    assert_eq!(images, expected_images);
    Members {
        by_handle,
        origins,
        metrics,
    }
}

pub(super) fn cow_members<'a>(
    input: &Input,
    carriers: impl IntoIterator<Item = &'a PrefixTree1>,
) -> Members<(usize, u32)> {
    let carriers: Vec<_> = carriers.into_iter().collect();
    let local: Vec<Vec<_>> = (0..input.graph.parents.len())
        .map(|owner| input.local(owner).map(|origin| (owner, origin)).collect())
        .collect();
    let actual_members = carriers
        .iter()
        .enumerate()
        .flat_map(|(owner, carrier)| carrier.iter().map(move |[origin]| (owner, (owner, origin))));
    let actual_globals = carriers
        .iter()
        .enumerate()
        .flat_map(|(owner, carrier)| carrier.iter().map(move |[origin]| (owner, origin)));
    let actual_images =
        input
            .graph
            .edges
            .iter()
            .enumerate()
            .flat_map(|(edge, &(source, target))| {
                carriers[source]
                    .iter()
                    .map(move |[origin]| (edge, (source, origin), (target, origin)))
            });
    members(input, &local, actual_members, actual_globals, actual_images)
}

pub(super) fn hash(metrics: &mut Metrics, values: impl IntoIterator<Item = u64>) {
    for value in values {
        metrics.checksum ^= value;
        metrics.checksum = metrics.checksum.wrapping_mul(0x100000001b3);
    }
}
