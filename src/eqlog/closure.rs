use super::relational_structure::*;
use super::signature::*;
use super::element::Element;
use std::cmp::max;
use std::fmt::Debug;

#[derive(Clone, PartialEq, Eq, Debug)]
struct RelationInPresentation<Sig: Signature> {
    id: Sig::Relation,
    equalities: Vec<(usize, usize)>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Presentation<Sig: Signature> {
    rips: Vec<RelationInPresentation<Sig>>,
    row_length: usize,
}

impl<Sig: Signature> Presentation<Sig> {
    pub fn new(
        signature: &Sig,
        relations: Vec<Sig::Relation>,
        mut equalities: Vec<(usize, usize)>,
    ) -> Self {
        let arities =
            relations.iter().
            map(|r| signature.arity(*r).iter());
        let row_arity: Vec<Sig::Sort> =
            arities.clone().
            flatten().
            cloned().
            collect();
        let row_length = row_arity.len();

        assert!(equalities.iter().all(|(lhs, rhs)| row_arity[*lhs] == row_arity[*rhs]));

        equalities.sort_by_key(|(lhs, rhs)| max(*lhs, *rhs));

        let mut rips: Vec<RelationInPresentation<Sig>> = Vec::with_capacity(relations.len());
        let mut remaining_equalities: &[(usize, usize)] = equalities.as_slice();
        let mut current_row_position = 0;

        for (r, current_length) in relations.iter().zip(arities.map(|a| a.len())) {
            let next_row_position = current_row_position + current_length;
            let local_equalities: Vec<(usize, usize)> =
                remaining_equalities.iter().
                take_while(|(lhs, rhs)| max(*lhs, *rhs) < next_row_position).
                cloned().
                collect();

            current_row_position = next_row_position;
            remaining_equalities = &remaining_equalities[local_equalities.len() ..];

            rips.push(RelationInPresentation {
                id: *r,
                equalities: local_equalities,
            });

        }
        Presentation {
            rips,
            row_length,
        }
    }
    pub fn relations<'a>(&'a self) -> impl 'a + Iterator<Item = Sig::Relation> {
        self.rips.iter().map(|rip| rip.id)
    }
    pub fn equalities<'a>(&'a self) -> impl 'a + Iterator<Item = (usize, usize)> {
        self.rips.iter().map(|rip| rip.equalities.iter().copied()).flatten()
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct RelationInInterpretation<'a, Sig: Signature> {
    rip: &'a RelationInPresentation<Sig>,
    use_new_rows: bool,
    use_old_rows: bool,
}

fn visit_new_interpretations_impl<'a, Sig: 'a + Signature>(
    structure: &RelationalStructure<Sig>,
    visitor: &mut impl for<'b> FnMut(&'b [Element]),
    interpretation: &mut Vec<Element>,
    mut riis: impl Iterator<Item = RelationInInterpretation<'a, Sig>> + Clone
) {
    if let Some(RelationInInterpretation{rip, use_new_rows, use_old_rows}) = riis.next() {
        let before_len = interpretation.len();
        let satisfies_equalities = |interp: &Vec<Element>| {
            rip.equalities.iter().all(|(lhs, rhs)| interp[*lhs] == interp[*rhs])
        };
        if use_old_rows {
            for row in structure.old_rows(rip.id) {
                interpretation.extend_from_slice(row);
                if satisfies_equalities(interpretation) {
                    visit_new_interpretations_impl(
                        structure,
                        visitor,
                        interpretation,
                        riis.clone(),
                    );
                }
                interpretation.truncate(before_len);
            }
        }
        if use_new_rows {
            for row in structure.new_rows(rip.id) {
                interpretation.extend_from_slice(row);
                if satisfies_equalities(interpretation) {
                    visit_new_interpretations_impl(
                        structure,
                        visitor,
                        interpretation,
                        riis.clone(),
                    );
                }
                interpretation.truncate(before_len);
            }
        }
    } else {
        visitor(&interpretation);
    }
}

pub fn visit_new_interpretations<Sig: Signature>(
    presentation: &Presentation<Sig>,
    structure: &RelationalStructure<Sig>,
    mut visitor: impl for<'b> FnMut(&'b [Element])
) {
    let mut interpretation: Vec<Element> = Vec::with_capacity(presentation.row_length);
    for i in 0 .. presentation.rips.len() {
        visit_new_interpretations_impl(
            structure,
            &mut visitor,
            &mut interpretation,
            presentation.rips.iter().enumerate().map(|(j, rip)| RelationInInterpretation {
                rip: rip,
                use_new_rows: i <= j,
                use_old_rows: i != j,
            }),
        );
    }
}

#[cfg(test)]
mod test_interpretation {
    use super::*;
    use std::collections::HashSet;

    fn compute_new_interpretation<Sig: Signature>(
        presentation: &Presentation<Sig>,
        structure: &RelationalStructure<Sig>,
    ) -> HashSet<Row> {
        let mut result: HashSet<Row> = HashSet::new();
        visit_new_interpretations(presentation, structure, |row| {
            result.insert(row.to_vec());
        });
        result
    }

    #[test]
    fn nullary_interpretation() {
        arities!{
            pub enum Sort {S0, S1},
            pub enum Relation {
                R: S0 x S1,
            },
        }
        let sig = StaticSignature::<Sort, Relation>::new();

        let structure = RelationalStructure::new(sig);
        let presentation = Presentation::new(&sig, vec![], vec![]);
        assert_eq!(compute_new_interpretation(&presentation, &structure), hashset!{});
    }

    #[test]
    fn unary_interpretation() {
        arities!{
            pub enum Sort {S0, S1},
            pub enum Relation {
                R: S0 x S1,
            },
        }
        use Sort::*;
        use Relation::*;
        let sig = StaticSignature::<Sort, Relation>::new();

        let mut structure = RelationalStructure::new(sig);
        let a0 = structure.adjoin_element(S0);
        let a1 = structure.adjoin_element(S0);
        let b0 = structure.adjoin_element(S1);
        let b1 = structure.adjoin_element(S1);

        structure.adjoin_rows(R, vec![
            vec![a0, b1],
            vec![a1, b0],
        ]);

        let presentation = Presentation::new(&sig, vec![R], vec![]);

        assert_eq!(
            compute_new_interpretation(&presentation, &structure), hashset!{
            vec![a0, b1],
            vec![a1, b0],
        });

        structure.age_rows();
        assert_eq!(compute_new_interpretation(&presentation, &structure), hashset!{});
    }

    #[test]
    fn binary_self_join() {
        arities!{
            pub enum Sort {S0, S1},
            pub enum Relation {
                R: S0 x S1,
            },
        }
        use Sort::*;
        use Relation::*;
        let sig = StaticSignature::<Sort, Relation>::new();

        let mut structure = RelationalStructure::new(sig);

        let a0 = structure.adjoin_element(S0);
        let a1 = structure.adjoin_element(S0);
        let b0 = structure.adjoin_element(S1);
        let b1 = structure.adjoin_element(S1);

        structure.adjoin_rows(R, vec![
            vec![a0, b0],
            vec![a1, b0],
            vec![a1, b1],
        ]);

        let presentation = Presentation::new(&sig, vec![R, R], vec![(1, 3)]);

        assert_eq!(compute_new_interpretation(&presentation, &structure), hashset!{
            vec![a0, b0, a0, b0],
            vec![a0, b0, a1, b0],
            vec![a1, b0, a0, b0],
            vec![a1, b0, a1, b0],
            vec![a1, b1, a1, b1],
        });

        structure.age_rows();
        assert_eq!(compute_new_interpretation(&presentation, &structure), hashset!{});
    }

    #[test]
    fn binary_join() {
        arities!{
            pub enum Sort {S0, S1},
            pub enum Relation {
                R0: S0 x S1,
                R1: S1 x S0,
            },
        }
        use Sort::*;
        use Relation::*;
        let sig = StaticSignature::<Sort, Relation>::new();

        let mut structure = RelationalStructure::new(sig);

        let a0 = structure.adjoin_element(S0);
        let a1 = structure.adjoin_element(S0);
        let b0 = structure.adjoin_element(S1);
        let b1 = structure.adjoin_element(S1);

        structure.adjoin_rows(R0, vec![
            vec![a0, b0],
            vec![a1, b0],
            vec![a1, b1],
        ]);
        structure.adjoin_rows(R1, vec![
            vec![b0, a0],
            vec![b1, a1],
        ]);

        let presentation = Presentation::new(&sig, vec![R0, R1], vec![(0, 3)]);

        assert_eq!(compute_new_interpretation(&presentation, &structure), hashset!{
            vec![a0, b0, b0, a0],
            vec![a1, b0, b1, a1],
            vec![a1, b1, b1, a1],
        });

        structure.age_rows();

        structure.adjoin_rows(R0, vec![
            vec![a0, b1],
        ]);
        structure.adjoin_rows(R1, vec![
            vec![b1, a0],
        ]);
        assert_eq!(compute_new_interpretation(&presentation, &structure), hashset!{
             vec![a0, b1, b1, a0],
             vec![a0, b1, b0, a0],
             vec![a0, b0, b1, a0],
        });

    }

    #[test]
    fn binary_diagonal() {
        arities!{
            pub enum Sort {S0, S1},
            pub enum Relation {
                R0: S0 x S1,
                R1: S1 x S1,
            },
        }
        use Sort::*;
        use Relation::*;
        let sig = StaticSignature::<Sort, Relation>::new();

        let mut structure = RelationalStructure::new(sig);

        let a0 = structure.adjoin_element(S0);
        let a1 = structure.adjoin_element(S0);
        let b0 = structure.adjoin_element(S1);
        let b1 = structure.adjoin_element(S1);

        structure.adjoin_rows(R0, vec![
            vec![a0, b0],
            vec![a1, b0],
            vec![a1, b1],
        ]);
        structure.adjoin_rows(R1, vec![
            vec![b0, b0],
            vec![b1, b0],
            vec![b0, b1],
        ]);

        let presentation = Presentation::new(&sig, vec![R0, R1], vec![(2, 3), (1, 2)]);

        assert_eq!(compute_new_interpretation(&presentation, &structure), hashset!{
            vec![a0, b0, b0, b0],
            vec![a1, b0, b0, b0],
        });
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SurjectionPresentation<Sig: Signature> {
    domain: Presentation<Sig>,
    codomain_equalities: Vec<(usize, usize)>,
    codomain_relations: Vec<(Sig::Relation, Vec<usize>)>,
}

impl<Sig: Signature> SurjectionPresentation<Sig> {
    pub fn new(
        signature: &Sig,
        domain: Presentation<Sig>,
        codomain_relations: Vec<(Sig::Relation, Vec<usize>)>,
        codomain_equalities: Vec<(usize, usize)>,
    ) -> Self {
        let row_arity: Vec<Sig::Sort> =
            domain.rips.iter().
            map(|rip| signature.arity(rip.id).iter()).
            flatten().
            cloned().
            collect();

        for (lhs, rhs) in &codomain_equalities {
            assert_eq!(row_arity[*lhs], row_arity[*rhs]);
        }
        for (r, arg_indices) in &codomain_relations {
            let arity = signature.arity(*r);
            assert_eq!(arg_indices.len(), arity.len());
            for (ai, s) in arg_indices.iter().zip(arity) {
                assert_eq!(row_arity[*ai], *s);
            }
        }

        SurjectionPresentation {
            domain,
            codomain_equalities,
            codomain_relations,
        }
    }
    pub fn functionality(signature: &Sig, relation: Sig::Relation) -> Self {
        let l = signature.arity(relation).len();
        let domain = Presentation {
            rips: vec![
                RelationInPresentation {
                    id: relation,
                    equalities: vec![],
                },
                RelationInPresentation {
                    id: relation,
                    equalities: (0 .. l - 1).map(|i| (i, i + l)).collect()
                },
            ],
            row_length: 2 * l,
        };

        SurjectionPresentation {
            domain,
            codomain_equalities: vec![(l - 1, 2 * l - 1)],
            codomain_relations: vec![],
        }
    }
    pub fn domain(&self) -> &Presentation<Sig> {
        &self.domain
    }
    pub fn codomain_relations<'a>(&'a self) -> impl 'a + Iterator<Item = (Sig::Relation, &'a [usize])> {
        self.codomain_relations.iter().map(|(r, row)| (*r, row.as_slice()))
    }
    pub fn codomain_equalities<'a>(&'a self) -> impl 'a + Iterator<Item = (usize, usize)> {
        self.codomain_equalities.iter().copied()
    }
}

pub enum Conclusion<Sig: Signature> {
    Row(Sig::Relation, Row),
    Equation(Element, Element),
}

pub fn visit_new_conclusions<Sig: Signature>(
    surjection_presentation: &SurjectionPresentation<Sig>,
    structure: &RelationalStructure<Sig>,
    mut visitor: impl FnMut(Conclusion<Sig>),
) {
    let SurjectionPresentation{
        domain,
        codomain_equalities,
        codomain_relations,
    } = surjection_presentation;

    visit_new_interpretations(&domain, structure, |row| {
        for (r, row_indices) in codomain_relations {
            visitor(Conclusion::Row(*r, row_indices.iter().map(|&i| row[i]).collect()));
        }
        for &(lhs, rhs) in codomain_equalities {
            visitor(Conclusion::Equation(row[lhs], row[rhs]));
        }
    });
}

pub fn close_structure<'a, Sig: 'a + Signature>(
    presentations: impl Clone + IntoIterator<Item = &'a SurjectionPresentation<Sig>>,
    structure: &mut RelationalStructure<Sig>
) {
    let mut conc_eqs: Vec<(Element, Element)> = vec![];
    let mut conc_rows: Vec<(Sig::Relation, Vec<Element>)> = vec![];

    loop {
        for presentation in presentations.clone() {
            visit_new_conclusions(presentation, structure, |conclusion| {
                match conclusion {
                    Conclusion::Row(r, row) => conc_rows.push((r, row)),
                    Conclusion::Equation(lhs, rhs) => conc_eqs.push((lhs, rhs)),
                }

            });
        }

        structure.age_rows();
        conc_eqs.drain(..).for_each(|(lhs, rhs)| { structure.equate(lhs, rhs); });
        structure.canonicalize_elements();
        structure.extend(conc_rows.drain(..));
        debug_assert!(conc_rows.is_empty());
        debug_assert!(conc_eqs.is_empty());

        let no_new_rows: bool =
            structure.signature().relations().iter().
            all(|&r| structure.new_rows(r).next().is_none());
        if no_new_rows {
            break;
        }
    }
}

#[cfg(test)]
mod test_close_structure {
    use super::*;

    use std::collections::HashSet;
    use std::iter::{repeat_with, once};

    fn save_rows<'a>(rows: impl IntoIterator<Item = &'a [Element]>) -> HashSet<Row> {
        rows.into_iter().map(|row| row.to_vec()).collect()
    }

    #[test]
    fn symmetry() {
        arities!{
            pub enum Sort {S},
            pub enum Relation { R: S x S },
        }
        use Sort::*;
        use Relation::*;
        let sig = StaticSignature::<Sort, Relation>::new();
        let mut structure = RelationalStructure::new(sig);
        let el0 = structure.adjoin_element(S);
        let el1 = structure.adjoin_element(S);
        let el2 = structure.adjoin_element(S);
        let el3 = structure.adjoin_element(S);
        let el4 = structure.adjoin_element(S);
        structure.adjoin_rows(R, vec![
            vec![el0, el1],
            vec![el2, el2],
            vec![el3, el4],
            vec![el4, el3],
        ]);

        let symmetry = SurjectionPresentation::new(
            &sig,
            Presentation::new(&sig, vec![R], vec![]),
            vec![(R, vec![1, 0])],
            vec![],
        );

        close_structure(&[symmetry], &mut structure);

        assert_eq!(save_rows(structure.rows(R)), hashset!{
            vec![el0, el1],
            vec![el1, el0],
            vec![el2, el2],
            vec![el3, el4],
            vec![el4, el3],
        });
        for &el in &[el0, el1, el2, el3, el4] {
            assert_eq!(structure.representative(el), el);
        }
    }

    #[test]
    fn transitivity() {
        arities!{
            pub enum Sort {S},
            pub enum Relation { R: S x S },
        }
        use Sort::*;
        use Relation::*;
        let sig = StaticSignature::<Sort, Relation>::new();
        let mut structure = RelationalStructure::new(sig);
        let el0 = structure.adjoin_element(S);
        let el1 = structure.adjoin_element(S);
        let el2 = structure.adjoin_element(S);
        let el3 = structure.adjoin_element(S);
        let el4 = structure.adjoin_element(S);
        let el5 = structure.adjoin_element(S);
        let el6 = structure.adjoin_element(S);
        let el7 = structure.adjoin_element(S);
        let el8 = structure.adjoin_element(S);
        let el9 = structure.adjoin_element(S);
        structure.adjoin_rows(R, vec![
            vec![el0, el1],

            vec![el2, el3],
            vec![el3, el4],
            vec![el4, el2],

            vec![el5, el5],

            vec![el5, el6],
            vec![el6, el7],
            vec![el7, el8],
            vec![el8, el9],
        ]);

        let transitivity = SurjectionPresentation::new(
            &sig,
            Presentation::new(&sig, vec![R, R], vec![(1, 2)]),
            vec![(R, vec![0, 3])],
            vec![],
        );

        let mut expected = save_rows(structure.rows(R));
        for a in &[el2, el3, el4] {
            for b in &[el2, el3, el4] {
                expected.insert(vec![*a, *b]);
            }
        }
        expected.insert(vec![el5, el7]);
        expected.insert(vec![el5, el8]);
        expected.insert(vec![el5, el9]);
        expected.insert(vec![el5, el9]);

        expected.insert(vec![el6, el8]);
        expected.insert(vec![el6, el9]);

        expected.insert(vec![el7, el9]);

        close_structure(&[transitivity], &mut structure);

        assert_eq!(save_rows(structure.rows(R)), expected);
        for &el in &[el0, el1, el2, el3, el4, el5, el6, el7, el8, el9] {
            assert_eq!(structure.representative(el), el);
        }
    }

    #[test]
    fn antisymmetry() {
        arities!{
            pub enum Sort {S},
            pub enum Relation { R: S x S },
        }
        use Sort::*;
        use Relation::*;
        let sig = StaticSignature::<Sort, Relation>::new();
        let mut structure = RelationalStructure::new(sig);
        let el0 = structure.adjoin_element(S);
        let el1 = structure.adjoin_element(S);
        let el2 = structure.adjoin_element(S);
        let el3 = structure.adjoin_element(S);
        let el4 = structure.adjoin_element(S);
        let el5 = structure.adjoin_element(S);
        let el6 = structure.adjoin_element(S);
        let el7 = structure.adjoin_element(S);

        structure.adjoin_rows(R, vec![
            vec![el0, el1],

            vec![el2, el3],
            vec![el3, el2],

            vec![el5, el5],

            vec![el5, el6],
            vec![el6, el7],
            vec![el7, el5],
        ]);

        let antisymmetry = SurjectionPresentation::new(
            &sig,
            Presentation::new(&sig, vec![R, R], vec![(0, 3), (1, 2)]),
            vec![],
            vec![(0, 1)],
        );

        close_structure(&[antisymmetry], &mut structure);

        let elx = structure.representative(el2);
        assert_eq!(structure.representative(el3), elx);
        assert_eq!(save_rows(structure.rows(R)), hashset!{
            vec![el0, el1],

            vec![elx, elx],

            vec![el5, el5],

            vec![el5, el6],
            vec![el6, el7],
            vec![el7, el5],
        });
        for &el in &[el0, el1, el4, el5, el6, el7] {
            assert_eq!(structure.representative(el), el);
        }
    }

    #[test]
    fn antisymmetry_transitivity() {
        arities!{
            pub enum Sort {S},
            pub enum Relation { R: S x S },
        }
        use Sort::*;
        use Relation::*;
        let sig = StaticSignature::<Sort, Relation>::new();

        let transitivity = SurjectionPresentation::new(
            &sig,
            Presentation::new(&sig, vec![R, R], vec![(1, 2)]),
            vec![(R, vec![0, 3])],
            vec![],
        );
        let antisymmetry = SurjectionPresentation::new(
            &sig,
            Presentation::new(&sig, vec![R, R], vec![(0, 3), (1, 2)]),
            vec![],
            vec![(0, 1)],
        );

        let mut structure = RelationalStructure::new(sig);
        let el0 = structure.adjoin_element(S);
        let el1 = structure.adjoin_element(S);
        let el2 = structure.adjoin_element(S);
        let el3 = structure.adjoin_element(S);
        let el4 = structure.adjoin_element(S);
        let el5 = structure.adjoin_element(S);
        let el6 = structure.adjoin_element(S);
        let el7 = structure.adjoin_element(S);

        structure.adjoin_rows(R, vec![
            vec![el0, el1],

            vec![el2, el3],
            vec![el3, el2],

            vec![el5, el5],

            vec![el5, el6],
            vec![el6, el7],
            vec![el7, el5],
        ]);

        // Add a cycle of elements, i.e. a sequence in which each element is related to the next
        let cycle_elements: Vec<Element> =
            repeat_with(|| structure.adjoin_element(S)).
            take(10).
            collect();
        structure.adjoin_rows(R,
            cycle_elements.iter().
            zip(cycle_elements.iter().skip(1).chain(once(cycle_elements.first().unwrap()))).
            map(|(a, b)| vec![*a, *b])
        );

        close_structure(&[transitivity, antisymmetry], &mut structure);

        for &el in &[el0, el1, el4] {
            assert_eq!(structure.representative(el), el);
        }

        let elx = structure.representative(el2);
        assert_eq!(structure.representative(el3), elx);

        let ely = structure.representative(el5);
        assert_eq!(structure.representative(el6), ely);
        assert_eq!(structure.representative(el7), ely);

        let elz = structure.representative(*cycle_elements.first().unwrap());
        for el in cycle_elements {
            assert_eq!(structure.representative(el), elz);
        }

        assert_eq!(save_rows(structure.rows(R)), hashset!{
            vec![el0, el1],
            vec![elx, elx],
            vec![ely, ely],
            vec![elz, elz],
        });
    }

    #[test]
    fn functionality() {
        arities!{
            pub enum Sort {S},
            pub enum Relation { O: S x S -> S },
        }
        use Sort::*;
        use Relation::*;
        let sig = StaticSignature::<Sort, Relation>::new();
        
        let functionality = SurjectionPresentation::functionality(&sig, O);

        let mut structure = RelationalStructure::new(sig);
        let el0 = structure.adjoin_element(S);
        let el1 = structure.adjoin_element(S);
        let el2 = structure.adjoin_element(S);
        let el3 = structure.adjoin_element(S);
        let el4 = structure.adjoin_element(S);
        let el5 = structure.adjoin_element(S);
        let el6 = structure.adjoin_element(S);

        structure.adjoin_rows(O, vec![
            vec![el0, el1, el1],
            vec![el0, el1, el2],

            vec![el1, el1, el3],
            vec![el1, el2, el4],


            vec![el3, el2, el5],
            vec![el4, el1, el6],
        ]);

        close_structure(&[functionality], &mut structure);

        let el12 = structure.representative(el1);
        assert_eq!(structure.representative(el2), el12);

        let el34 = structure.representative(el3);
        assert_eq!(structure.representative(el4), el34);

        let el56 = structure.representative(el5);
        assert_eq!(structure.representative(el6), el56);

        assert_eq!(hashset!{el0, el12, el34, el56}.len(), 4);
    }
}
