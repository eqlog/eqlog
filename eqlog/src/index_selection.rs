use crate::query_action::*;
use crate::signature::Signature;
use maplit::hashset;
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::iter::{once, repeat};

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct QuerySpec {
    pub projections: BTreeSet<usize>,
    pub diagonals: BTreeSet<BTreeSet<usize>>,
}

impl QuerySpec {
    pub fn new() -> QuerySpec {
        QuerySpec {
            projections: BTreeSet::new(),
            diagonals: BTreeSet::new(),
        }
    }
}

impl PartialOrd<QuerySpec> for QuerySpec {
    fn partial_cmp(&self, rhs: &QuerySpec) -> Option<Ordering> {
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

fn query_spec_chains(indices: HashSet<QuerySpec>) -> Vec<Vec<QuerySpec>> {
    let mut specs: Vec<QuerySpec> = indices.into_iter().collect();
    specs.sort_by_key(|index| index.projections.len());

    let mut chains: Vec<Vec<QuerySpec>> = Vec::new();
    for spec in specs.into_iter() {
        let compatible_chain = chains
            .iter_mut()
            .find(|chain| spec >= *chain.last().unwrap());
        match compatible_chain {
            Some(compatible_chain) => compatible_chain.push(spec),
            None => chains.push(vec![spec]),
        }
    }
    chains
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct IndexSpec {
    pub order: Vec<usize>,
    pub diagonals: BTreeSet<BTreeSet<usize>>,
}

fn is_prefix(prefix: &BTreeSet<usize>, order: &[usize]) -> bool {
    let count = order.iter().take_while(|el| prefix.contains(el)).count();
    count == prefix.len()
}

impl IndexSpec {
    pub fn can_serve(&self, query: &QuerySpec) -> bool {
        query.diagonals == self.diagonals && is_prefix(&query.projections, &self.order)
    }
    pub fn from_query_spec_chain(arity_len: usize, chain: &[QuerySpec]) -> Self {
        let empty_projections = BTreeSet::new();
        let full_projections: BTreeSet<usize> = (0..arity_len).collect();

        // Some `impl Iterator<&BTreeSet<usize>`:
        let proj_chain = chain.iter().map(|query| &query.projections);
        let bot_chain = once(&empty_projections).chain(proj_chain.clone());
        let top_chain = proj_chain.chain(once(&full_projections));
        // An `impl Iterator<BTreeSet<usize>`:
        let diffs = bot_chain.zip(top_chain).map(|(prev, next)| next - prev);

        let order: Vec<usize> = diffs.flatten().collect();

        let diagonals = chain.last().unwrap().diagonals.clone();
        IndexSpec { order, diagonals }
    }
}

// Maps relation name and query spec to an index for the relation that can serve the query.
pub type IndexSelection = HashMap<String, HashMap<QuerySpec, IndexSpec>>;

pub fn select_indices(signature: &Signature, query_actions: &[QueryAction]) -> IndexSelection {
    // Maps relations to tuple of arity.len() and set of collected query specs.
    let mut query_specs: HashMap<String, (usize, HashSet<QuerySpec>)> = signature
        .relations()
        .map(|(rel, arity)| (rel.to_string(), (arity.len(), hashset! {QuerySpec::new()})))
        .collect();

    // Add indices for (implicit) functionality axioms.
    for func in signature.functions().values() {
        let spec = QuerySpec {
            projections: (0..func.dom.len()).collect(),
            diagonals: BTreeSet::new(),
        };
        query_specs.get_mut(&func.name).unwrap().1.insert(spec);
    }

    // Add indices for axioms.
    for query_action in query_actions.iter() {
        for query in query_action.queries.iter() {
            use Query::*;
            match query {
                Relation {
                    relation,
                    diagonals,
                    projections,
                    ..
                } => {
                    query_specs.get_mut(relation).unwrap().1.insert(QuerySpec {
                        diagonals: diagonals.clone(),
                        projections: projections.keys().copied().collect(),
                    });
                }
                Sort { .. } => (),
            }
        }
    }

    query_specs
        .into_iter()
        .map(|(rel, (arity_len, query_specs))| {
            let chains = query_spec_chains(query_specs);
            let query_index_map: HashMap<QuerySpec, IndexSpec> = chains
                .into_iter()
                .flat_map(|queries| {
                    let index = IndexSpec::from_query_spec_chain(arity_len, &queries);
                    queries.into_iter().zip(repeat(index))
                })
                .collect();
            (rel, query_index_map)
        })
        .collect()
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::flat_ast::*;
    use crate::indirect_ast::*;
    use itertools::Itertools;

    #[test]
    fn test_can_serve() {
        let query0 = QuerySpec {
            projections: btreeset! {0, 2, 3},
            diagonals: btreeset! {},
        };
        let query1 = QuerySpec {
            projections: btreeset! {0, 2, 3, 1},
            diagonals: btreeset! {},
        };
        let query2 = QuerySpec {
            projections: btreeset! {0, 2},
            diagonals: btreeset! {btreeset!{0, 3}},
        };
        let query3 = QuerySpec {
            projections: btreeset! {0, 2},
            diagonals: btreeset! {btreeset!{0, 3}, btreeset!{1, 2}},
        };

        let index0 = IndexSpec {
            order: vec![2, 0, 3, 1],
            diagonals: btreeset! {},
        };
        let index1 = IndexSpec {
            order: vec![2, 0, 1, 3],
            diagonals: btreeset! {},
        };
        let index2 = IndexSpec {
            order: vec![2, 0, 1, 3],
            diagonals: btreeset! {btreeset!{0, 3}},
        };
        let index3 = IndexSpec {
            order: vec![0, 3, 1, 2],
            diagonals: btreeset! {btreeset!{0, 3}, btreeset!{1, 2}},
        };

        assert!(index0.can_serve(&query0));
        assert!(!index1.can_serve(&query0));
        assert!(!index2.can_serve(&query0));
        assert!(!index3.can_serve(&query0));

        assert!(index0.can_serve(&query1));
        assert!(index1.can_serve(&query1));
        assert!(!index2.can_serve(&query1));
        assert!(!index3.can_serve(&query1));

        assert!(!index0.can_serve(&query2));
        assert!(!index1.can_serve(&query2));
        assert!(index2.can_serve(&query2));
        assert!(!index3.can_serve(&query2));

        assert!(!index0.can_serve(&query3));
        assert!(!index1.can_serve(&query3));
        assert!(!index2.can_serve(&query3));
        assert!(!index3.can_serve(&query3));
    }

    fn obj() -> String {
        "obj".to_string()
    }
    fn mor() -> String {
        "mor".to_string()
    }
    fn comp() -> String {
        "comp".to_string()
    }
    fn id() -> String {
        "id".to_string()
    }
    fn signature() -> String {
        "signature".to_string()
    }

    fn category_signature() -> Signature {
        let mut sig = Signature::new();
        sig.add_sort(Sort::new(obj()));
        sig.add_sort(Sort::new(mor()));
        sig.add_function(Function::new(comp(), vec![mor(), mor()], mor()));
        sig.add_function(Function::new(id(), vec![obj()], mor()));
        sig.add_predicate(Predicate::new(signature(), vec![obj(), mor(), obj()]));
        sig
    }

    fn check_well_formed_index_selection(signature: &Signature, index_selection: &IndexSelection) {
        let sig_rels: HashSet<&str> = signature.relations().map(|(name, _)| name).collect();
        let sel_rels: HashSet<&str> = index_selection.keys().map(|s| s.as_str()).collect();
        assert_eq!(sel_rels, sig_rels);

        for (rel, arity) in signature.relations() {
            for (query, index) in index_selection.get(rel).unwrap().iter() {
                // `index.order` is a permutation of [0, arity.len()).
                assert_eq!(index.order.len(), arity.len());
                for i in 0..arity.len() {
                    assert!(index.order.iter().find(|j| i == **j).is_some());
                }

                // Diagonals contain values less than `arity.len()` only.
                for diagonal in &index.diagonals {
                    assert!(diagonal.len() > 1);
                    for i in diagonal {
                        assert!(*i < arity.len());
                    }
                }

                assert!(index.can_serve(query));
            }
        }
    }

    #[test]
    fn simple_reduction() {
        // comp(h, comp(g, f)) ~> comp(comp(h, g), f)";
        let sig = category_signature();
        let h = FlatTerm(0);
        let g = FlatTerm(1);
        let f = FlatTerm(2);
        let gf = FlatTerm(3);
        let hg = FlatTerm(4);
        let hg_f = FlatTerm(5);
        let h_gf = hg_f;

        use FlatAtom::*;
        let premise = vec![
            // comp(g, f)!
            Relation(comp(), vec![g, f, gf]),
            Relation(comp(), vec![h, g, hg]),
            // comp(comp(h, g), f)!
            Relation(comp(), vec![hg, f, hg_f]),
        ];
        let conclusion = vec![
            // comp(h, comp(g, f)) = comp(comp(h, g), f)
            Relation(comp(), vec![h, gf, h_gf]),
        ];
        let axioms = vec![QueryAction::new(
            &sig,
            &FlatSequent {
                premise,
                conclusion,
            },
        )];

        let index_selection = select_indices(&sig, &axioms);

        check_well_formed_index_selection(&sig, &index_selection);

        let comp_specs = index_selection.get(&comp()).unwrap();
        let id_specs = index_selection.get(&id()).unwrap();
        let signature_specs = index_selection.get(&signature()).unwrap();

        // Second atom.
        assert!(comp_specs.contains_key(&QuerySpec {
            projections: btreeset! {1},
            diagonals: btreeset! {},
        }));
        // Third atom.
        assert!(comp_specs.contains_key(&QuerySpec {
            projections: btreeset! {0, 1},
            diagonals: btreeset! {},
        }));
        // Functionality.
        assert!(comp_specs.contains_key(&QuerySpec {
            projections: btreeset! {0, 1},
            diagonals: btreeset! {},
        }));
        // Functionality.
        assert!(id_specs.contains_key(&QuerySpec {
            projections: btreeset! {0},
            diagonals: btreeset! {},
        }));

        assert_eq!(comp_specs.values().unique().count(), 1);
        assert_eq!(id_specs.values().unique().count(), 1);
        assert_eq!(signature_specs.values().unique().count(), 1);
    }

    #[test]
    fn non_surjective_implication() {
        // signature(x, f, y) & signature(y, g, z) => comp(g, f)! & signature(x, comp(g, f), z)
        let sig = category_signature();
        let x = FlatTerm(0);
        let f = FlatTerm(1);
        let y = FlatTerm(2);
        let g = FlatTerm(3);
        let z = FlatTerm(4);
        let gf = FlatTerm(5);

        use FlatAtom::*;
        let premise = vec![
            Relation(signature(), vec![x, f, y]),
            Relation(signature(), vec![y, g, z]),
        ];
        let conclusion = vec![
            Relation(comp(), vec![g, f, gf]),
            Relation(signature(), vec![x, gf, z]),
        ];
        let axioms = vec![QueryAction::new(
            &sig,
            &FlatSequent {
                premise,
                conclusion,
            },
        )];

        let index_selection = select_indices(&sig, &axioms);

        check_well_formed_index_selection(&sig, &index_selection);

        let comp_specs = index_selection.get(&comp()).unwrap();
        let id_specs = index_selection.get(&id()).unwrap();
        let signature_specs = index_selection.get(&signature()).unwrap();

        // Second atom.
        assert!(signature_specs.contains_key(&QuerySpec {
            projections: btreeset! {0},
            diagonals: btreeset! {},
        }));

        assert_eq!(comp_specs.values().unique().count(), 1);
        assert_eq!(id_specs.values().unique().count(), 1);
        assert_eq!(signature_specs.values().unique().count(), 1);
    }

    #[test]
    fn simultaneous_projection_and_diagonal() {
        // i = id(x) & signature(y, i, y) & signature(x, f, x) & j = id(y) => x = y & j = i
        let sig = category_signature();
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
        let conclusion = vec![Equal(x, y), Equal(j, i)];
        let axioms = vec![QueryAction::new(
            &sig,
            &FlatSequent {
                premise,
                conclusion,
            },
        )];

        let index_selection = select_indices(&sig, &axioms);

        check_well_formed_index_selection(&sig, &index_selection);

        let comp_specs = index_selection.get(&comp()).unwrap();
        let id_specs = index_selection.get(&id()).unwrap();
        let signature_specs = index_selection.get(&signature()).unwrap();

        // Second atom.
        assert!(signature_specs.contains_key(&QuerySpec {
            projections: btreeset! {1},
            diagonals: btreeset! {btreeset!{0, 2}},
        }));
        // Third atom.
        assert!(signature_specs.contains_key(&QuerySpec {
            projections: btreeset! {0, 2},
            diagonals: btreeset! {btreeset!{0, 2}},
        }));
        // Fourth atom.
        assert!(id_specs.contains_key(&QuerySpec {
            projections: btreeset! {0},
            diagonals: btreeset! {},
        }));

        assert_eq!(comp_specs.values().unique().count(), 1);
        assert_eq!(id_specs.values().unique().count(), 1);
        assert_eq!(signature_specs.values().unique().count(), 3);
    }
}
