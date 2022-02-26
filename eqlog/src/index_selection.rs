use std::collections::{BTreeSet, HashSet, HashMap};
use crate::flat_ast::*;
use crate::indirect_ast::*;
use itertools::Itertools;
use std::cmp::Ordering;
use std::iter::once;
use crate::signature::Signature;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
struct QuerySpec {
    projections: BTreeSet<usize>,
    diagonals: BTreeSet<BTreeSet<usize>>,
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

fn query_spec_chains(indices: HashSet<QuerySpec>)-> Vec<Vec<QuerySpec>> {
    let mut specs: Vec<QuerySpec> = indices.into_iter().collect();
    specs.sort_by_key(|index| index.projections.len());

    let mut chains: Vec<Vec<QuerySpec>> = Vec::new();
    for spec in specs.into_iter() {
        let compatible_chain = chains.iter_mut().find(|chain| spec >= *chain.last().unwrap());
        match compatible_chain {
            Some(compatible_chain) => compatible_chain.push(spec),
            None => chains.push(vec![spec]),
        }
    }
    chains
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
struct IndexSpec {
    order: Vec<usize>,
    diagonals: BTreeSet<BTreeSet<usize>>,
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
        let full_projections: BTreeSet<usize> = (0 .. arity_len).collect();

        // Some `impl Iterator<&BTreeSet<usize>`:
        let proj_chain = chain.iter().map(|query| &query.projections);
        let bot_chain = once(&empty_projections).chain(proj_chain.clone());
        let top_chain = proj_chain.chain(once(&full_projections));
        // An `impl Iterator<BTreeSet<usize>`:
        let diffs = bot_chain.zip(top_chain).map(|(prev, next)| next - prev);

        let order: Vec<usize> = diffs.flatten().collect();

        let diagonals = chain.last().unwrap().diagonals.clone();
        IndexSpec{order, diagonals}
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

fn query_specs_for_premise<'a>(premise: &'a [FlatAtom]) -> impl 'a + Iterator<Item=(&'a str, QuerySpec)> {
    let mut fixed_terms: HashSet<FlatTerm> = HashSet::new();
    let spec_for_atom = move |atom: &'a FlatAtom| -> Option<(&'a str, QuerySpec)> {
        use FlatAtom::*;
        match atom {
            Equal(lhs, rhs) => {
                fixed_terms.insert(*lhs);
                fixed_terms.insert(*rhs);
                None
            },
            Relation(rel, args) => {
                let projections = projections(&fixed_terms, args);
                let diagonals = diagonals(args);

                for arg in args.iter().copied() {
                    fixed_terms.insert(arg);
                }

                if !projections.is_empty() || !diagonals.is_empty() {
                    Some((rel.as_str(), QuerySpec{projections, diagonals}))
                } else {
                    None
                }
            },
            Unconstrained(tm, _) => {
                fixed_terms.insert(*tm);
                None
            },
        }
    };

    premise.iter().map(spec_for_atom).flatten()
}

fn index_specs(signature: &Signature, axioms: &[FlatSequent]) -> HashMap<String, Vec<IndexSpec>> {
    let mut query_specs: HashMap<String, (usize, HashSet<QuerySpec>)> =
        signature.relations()
        .map(|(rel, arity)| (rel.to_string(), (arity.len(), HashSet::new())))
        .collect();

    // Add indices for (implicit) functionality axioms.
    for func in signature.functions().values() {
        let spec = QuerySpec {
            projections: (0 .. func.dom.len()).collect(),
            diagonals: BTreeSet::new(),
        };
        query_specs.get_mut(&func.name).unwrap().1.insert(spec);
    }

    // Add indices for axioms.
    let rel_specs = axioms.iter().flat_map(|sequent| query_specs_for_premise(&sequent.premise));
    for (rel, query_spec) in rel_specs {
        query_specs.get_mut(rel).unwrap().1.insert(query_spec);
    }

    query_specs.into_iter()
        .map(|(rel, (arity_len, query_specs))| {
            let chains = query_spec_chains(query_specs);
            let index_specs: Vec<IndexSpec> = 
                chains.iter()
                .map(|chain| IndexSpec::from_query_spec_chain(arity_len, chain))
                .collect();
            (rel, index_specs)
        })
        .collect() 
}

#[cfg(test)]
mod tests {

use super::*;

#[test]
fn test_can_serve() {
    let query0 = QuerySpec{
        projections: btreeset!{0, 2, 3},
        diagonals: btreeset!{},
    };
    let query1 = QuerySpec{
        projections: btreeset!{0, 2, 3, 1},
        diagonals: btreeset!{},
    };
    let query2 = QuerySpec{
        projections: btreeset!{0, 2},
        diagonals: btreeset!{btreeset!{0, 3}},
    };
    let query3 = QuerySpec{
        projections: btreeset!{0, 2},
        diagonals: btreeset!{btreeset!{0, 3}, btreeset!{1, 2}},
    };

    let index0 = IndexSpec{
        order: vec![2, 0, 3, 1],
        diagonals: btreeset!{},
    };
    let index1 = IndexSpec{
        order: vec![2, 0, 1, 3],
        diagonals: btreeset!{},
    };
    let index2 = IndexSpec{
        order: vec![2, 0, 1, 3],
        diagonals: btreeset!{btreeset!{0, 3}},
    };
    let index3 = IndexSpec{
        order: vec![0, 3, 1, 2],
        diagonals: btreeset!{btreeset!{0, 3}, btreeset!{1, 2}},
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

fn obj() -> String { "obj".to_string() }
fn mor() -> String { "mor".to_string() }
fn comp() -> String { "comp".to_string() }
fn id() -> String { "id".to_string() }
fn signature() -> String { "signature".to_string() }

fn category_signature() -> Signature {
    let mut sig = Signature::new();
    sig.add_sort(Sort(obj()));
    sig.add_sort(Sort(mor()));
    sig.add_function(Function{name: comp(), dom: vec![mor(), mor()], cod: mor()});
    sig.add_function(Function{name: id(), dom: vec![obj()], cod: mor()});
    sig.add_predicate(Predicate{name: signature(), arity: vec![obj(), mor(), obj()]});
    sig
}

fn category_relations() -> HashSet<String> {
    hashset!{comp(), id(), signature()}
}

fn can_serve<'a>(indices: impl IntoIterator<Item=&'a IndexSpec>, query: &QuerySpec) -> bool {
    indices.into_iter().find(|index| index.can_serve(query)).is_some()
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
        Relation(comp(), vec![h, gf, h_gf])
    ];
    let axioms = vec![FlatSequent{premise, conclusion}];

    let index_specs = index_specs(&sig, &axioms);

    let rels: HashSet<String> = index_specs.keys().map(|s| s.to_string()).collect();
    assert_eq!(rels, category_relations());

    let comp_specs = index_specs.get(&comp()).unwrap();
    let id_specs = index_specs.get(&id()).unwrap();
    let signature_specs = index_specs.get(&signature()).unwrap();

    // Second atom.
    assert!(can_serve(
            comp_specs.iter(),
            &QuerySpec{projections: btreeset!{1}, diagonals: btreeset!{}}
    ));
    // Third atom.
    assert!(can_serve(
            comp_specs.iter(),
            &QuerySpec{projections: btreeset!{0, 1}, diagonals: btreeset!{}}
    ));
    // Functionality.
    assert!(can_serve(
            comp_specs.iter(),
            &QuerySpec{projections: btreeset!{0, 1}, diagonals: btreeset!{}}
    ));
    // Functionality.
    assert!(can_serve(
            id_specs.iter(),
            &QuerySpec{projections: btreeset!{0}, diagonals: btreeset!{}}
    ));

    assert_eq!(comp_specs.len(), 1);
    assert_eq!(id_specs.len(), 1);
    assert_eq!(signature_specs.len(), 0);
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
    let axioms = vec![FlatSequent{premise, conclusion}];

    let index_specs = index_specs(&sig, &axioms);

    let rels: HashSet<String> = index_specs.keys().map(|s| s.to_string()).collect();
    assert_eq!(rels, category_relations());

    let signature_specs = index_specs.get(&signature()).unwrap();
    let id_specs = index_specs.get(&id()).unwrap();
    let comp_specs = index_specs.get(&comp()).unwrap();

    // Second atom.
    assert!(can_serve(
            signature_specs.iter(),
            &QuerySpec{projections: btreeset!{0}, diagonals: btreeset!{}}
    ));
    assert_eq!(signature_specs.len(), 1);
    // Functionality only.
    assert_eq!(id_specs.len(), 1);
    assert_eq!(comp_specs.len(), 1);
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
    let conclusion = vec![
        Equal(x, y),
        Equal(j, i),
    ];
    let axioms = vec![FlatSequent{premise, conclusion}];

    let index_specs = index_specs(&sig, &axioms);

    let rels: HashSet<String> = index_specs.keys().map(|s| s.to_string()).collect();
    assert_eq!(rels, category_relations());

    let signature_specs = index_specs.get(&signature()).unwrap();
    let id_specs = index_specs.get(&id()).unwrap();
    let comp_specs = index_specs.get(&comp()).unwrap();

    // Second atom.
    assert!(can_serve(
            signature_specs.iter(),
            &QuerySpec{projections: btreeset!{1}, diagonals: btreeset!{btreeset!{0, 2}}}
    ));
    // Third atom.
    assert!(can_serve(
            signature_specs.iter(),
            &QuerySpec{projections: btreeset!{0, 2}, diagonals: btreeset!{btreeset!{0, 2}}}
    ));
    assert_eq!(signature_specs.len(), 2);
    // Fourth atom.
    assert!(can_serve(
            id_specs.iter(),
            &QuerySpec{projections: btreeset!{0}, diagonals: btreeset!{}}
    ));
    assert_eq!(id_specs.len(), 1);
    assert_eq!(comp_specs.len(), 1);
}

}
