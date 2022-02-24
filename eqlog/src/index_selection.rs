use std::collections::{BTreeSet, HashSet, HashMap};
use crate::flat_ast::*;
use itertools::Itertools;
use std::cmp::Ordering;
use std::iter::{once, repeat};

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
struct RelationIndex {
    projections: BTreeSet<usize>,
    diagonals: BTreeSet<BTreeSet<usize>>,
}

impl PartialOrd<RelationIndex> for RelationIndex {
    fn partial_cmp(&self, rhs: &RelationIndex) -> Option<Ordering> {
        use Ordering::*;
        if self.diagonals != rhs.diagonals {
            None
        } else if self.projections == rhs.projections {
            Some(Equal)
        } else if self.projections.is_subset(&rhs.projections) {
            Some(Less)
        } else if self.projections.is_superset(&rhs.projections) {
            Some(Greater)
        } else {
            None
        }
    }
}

fn index_chains(indices: HashSet<RelationIndex>) -> Vec<Vec<RelationIndex>> {
    let mut indices: Vec<RelationIndex> = indices.into_iter().collect();
    indices.sort_by_key(|index| index.projections.len());

    let mut chains: Vec<Vec<RelationIndex>> = Vec::new();
    for index in indices.into_iter() {
        let compatible_chain = chains.iter_mut().find(|chain| index >= *chain.last().unwrap());
        match compatible_chain {
            Some(compatible_chain) => compatible_chain.push(index),
            None => chains.push(vec![index]),
        }
    }
    chains
}

fn index_chain_to_order(arity: usize, chain: &[RelationIndex]) -> Vec<usize> {
    let empty_projections = BTreeSet::new();
    let full_projections: BTreeSet<usize> = (0 .. arity).collect();

    // Some `impl Iterator<&BTreeSet<usize>`:
    let chain = chain.iter().map(|index| &index.projections);
    let bot_chain = once(&empty_projections).chain(chain.clone());
    let top_chain = chain.chain(once(&full_projections));
    // An `impl Iterator<BTreeSet<usize>`:
    let diffs = bot_chain.zip(top_chain).map(|(prev, next)| next - prev);

    diffs.flatten().collect()
}

struct IndexRequirements {
    relations: HashMap<String, HashSet<RelationIndex>>,
    sorts: HashMap<String, bool>,
}

impl IndexRequirements {
    fn new(
        sorts: impl IntoIterator<Item=String>,
        relations: impl IntoIterator<Item=String>,
    ) -> Self {
        IndexRequirements {
            relations: relations.into_iter().zip(repeat(HashSet::new())).collect(),
            sorts: sorts.into_iter().zip(repeat(false)).collect(),
        }
    }
}

fn diagonals(args: &[FlatTerm]) -> BTreeSet<BTreeSet<usize>> {
    let mut enumerated_args: Vec<(usize, FlatTerm)> =
        args.iter().copied().enumerate().collect();
    enumerated_args.sort_by_key(|(_, tm)| *tm);

    enumerated_args.iter()
        .group_by(|(_, tm)| tm).into_iter()
        .map(|(_, group)| -> BTreeSet<usize> { group.map(|(i, _)| *i).collect() })
        .filter(|diagonal| diagonal.len() > 1)
        .collect()
}

fn projections(fixed_terms: &HashSet<FlatTerm>, args: &[FlatTerm]) -> BTreeSet<usize> {
    args.iter().copied()
        .enumerate()
        .filter(|(_, tm)| fixed_terms.contains(tm))
        .map(|(i, _)| i)
        .collect()
}

impl IndexRequirements {
    fn add_from_premise(&mut self, premise: &[FlatAtom]) {
        let mut fixed_terms: HashSet<FlatTerm> = HashSet::new();
        for atom in premise.iter() {
            use FlatAtom::*;
            match atom {
                Equal(lhs, rhs) => {
                    fixed_terms.insert(*lhs);
                    fixed_terms.insert(*rhs);
                },
                Relation(rel, args) => {
                    let projections = projections(&fixed_terms, args);
                    let diagonals = diagonals(args);

                    if !projections.is_empty() || !diagonals.is_empty() {
                        let index = RelationIndex{projections, diagonals};
                        self.relations.get_mut(rel).unwrap().insert(index);
                    }

                    for arg in args.iter().copied() {
                        fixed_terms.insert(arg);
                    }
                },
                Unconstrained(tm, sort) => {
                    fixed_terms.insert(*tm);
                    *self.sorts.get_mut(sort).unwrap() = true;
                },
            }
        }
    }
}

#[cfg(test)]
mod tests {

use super::*;

#[test]
fn simple_reduction() {
    // comp(h, comp(g, f)) ~> comp(comp(h, g), f)";
    let mor = || "mor".to_string();
    let comp = || "comp".to_string();
    let h = FlatTerm(0);
    let g = FlatTerm(1);
    let f = FlatTerm(2);
    let gf = FlatTerm(3);
    let hg = FlatTerm(4);
    let hg_f = FlatTerm(5);

    use FlatAtom::*;
    let premise = vec![
        // comp(g, f)!
        Relation(comp(), vec![g, f, gf]),
        Relation(comp(), vec![h, g, hg]),
        // comp(comp(h, g), f)!
        Relation(comp(), vec![hg, f, hg_f]),
    ];

    let mut indices = IndexRequirements::new([mor()], [comp()]);
    indices.add_from_premise(&premise);

    let relation_indices = hashmap!{
        comp() => hashset!{
            RelationIndex {
                projections: btreeset!{1},
                diagonals: btreeset!{},
            },
            RelationIndex {
                projections: btreeset!{0, 1},
                diagonals: btreeset!{},
            },
        },
    };
    assert_eq!(indices.relations, relation_indices);

    let sort_indices = hashmap!{
        mor() => false,
    };
    assert_eq!(indices.sorts, sort_indices);
}

#[test]
fn non_surjective_implication() {
    // signature(x, f, y) & signature(y, g, z) => comp(g, f)! & signature(x, comp(g, f), z)
    let obj = || "obj".to_string();
    let mor = || "mor".to_string();
    let signature = || "signature".to_string();
    let comp = || "comp".to_string();
    let x = FlatTerm(0);
    let f = FlatTerm(1);
    let y = FlatTerm(2);
    let g = FlatTerm(3);
    let z = FlatTerm(4);

    use FlatAtom::*;
    let premise = vec![
        Relation(signature(), vec![x, f, y]),
        Relation(signature(), vec![y, g, z]),
    ];

    let mut indices = IndexRequirements::new([obj(), mor()], [signature(), comp()]);
    indices.add_from_premise(&premise);

    let relation_indices = hashmap!{
        signature() => hashset!{
            RelationIndex {
                projections: btreeset!{0},
                diagonals: btreeset!{},
            },
        },
        comp() => hashset!{},
    };
    assert_eq!(indices.relations, relation_indices);

    let sort_indices = hashmap!{
        obj() => false,
        mor() => false,
    };
    assert_eq!(indices.sorts, sort_indices);
}

#[test]
fn simultaneous_projection_and_diagonal() {
    // i = id(x) & signature(y, i, y) & signature(x, f, x) & j = id(y) => x = y & j = i
    let obj = || "obj".to_string();
    let mor = || "mor".to_string();
    let id = || "id".to_string();
    let signature = || "signature".to_string();

    let i = FlatTerm(0);
    let x = FlatTerm(1);
    let y = FlatTerm(2);
    let f = FlatTerm(3);
    let j = FlatTerm(4);

    use FlatAtom::*;
    let premise = vec![
        Relation(id(), vec![x, i]),
        Relation(signature(), vec![y, i, y]),
        Relation(signature(), vec![x, f, x]),
        Relation(id(), vec![y, j]),
    ];

    let mut indices = IndexRequirements::new([obj(), mor()], [id(), signature()]);
    indices.add_from_premise(&premise);

    let relation_indices = hashmap!{
        signature() => hashset!{
            RelationIndex {
                projections: btreeset!{1},
                diagonals: btreeset!{btreeset!{0, 2}},
            },
            RelationIndex {
                projections: btreeset!{0, 2},
                diagonals: btreeset!{btreeset!{0, 2}},
            },
        },
        id() => hashset!{
            RelationIndex {
                projections: btreeset!{0},
                diagonals: btreeset!{},
            },
        },
    };
    assert_eq!(indices.relations, relation_indices);

    let sort_indices = hashmap!{
        obj() => false,
        mor() => false,
    };
    assert_eq!(indices.sorts, sort_indices);
}

#[test]
fn unconstrained_variable() {
    // !x: obj & !y: obj => x = y
    let obj = || "obj".to_string();
    let mor = || "mor".to_string();
    let x = FlatTerm(0);
    let y = FlatTerm(1);

    use FlatAtom::*;
    let premise = vec![
        Unconstrained(x, obj()),
        Unconstrained(y, obj()),
    ];
    let mut indices = IndexRequirements::new([obj(), mor()], []);
    indices.add_from_premise(&premise);

    let relation_indices = hashmap!{};
    assert_eq!(indices.relations, relation_indices);

    let sort_indices = hashmap!{
        obj() => true,
        mor() => false,
    };
    assert_eq!(indices.sorts, sort_indices);
}

}
