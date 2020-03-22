use crate::model::*;
use crate::signature::*;
use crate::element::Element;
use std::cmp::max;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Presentation {
    pub relations: Vec<RelationId>,
    pub equalities: Vec<(usize, usize)>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct RelationInPresentation {
    id: RelationId,
    equalities: Vec<(usize, usize)>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct CheckedPresentation<'a> {
    signature: &'a Signature,
    rips: Vec<RelationInPresentation>,
    row_length: usize,
}

impl Presentation {
    pub fn checked<'a>(self, signature: &'a Signature) -> CheckedPresentation<'a> {
        let Presentation { relations, mut equalities} = self;
        let arities =
            relations.iter().
            map(|r| signature.get_arity(*r).unwrap().iter());
        let row_arity: Vec<SortId> =
            arities.clone().
            flatten().
            cloned().
            collect();
        let row_length = row_arity.len();

        assert!(equalities.iter().all(|(lhs, rhs)| row_arity[*lhs] == row_arity[*rhs]));

        equalities.sort_by_key(|(lhs, rhs)| max(*lhs, *rhs));

        let mut rips: Vec<RelationInPresentation> = Vec::with_capacity(relations.len());
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
        CheckedPresentation {
            signature,
            rips,
            row_length,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct RelationInInterpretation<'a> {
    rip: &'a RelationInPresentation,
    use_new_rows: bool,
    use_old_rows: bool,
}

fn visit_new_interpretations_impl<'b>(
    model: &Model,
    visitor: &mut impl for<'c> FnMut(&'c [Element]),
    interpretation: &mut Vec<Element>,
    mut riis: impl Iterator<Item = RelationInInterpretation<'b>> + Clone
) {
    if let Some(RelationInInterpretation{rip, use_new_rows, use_old_rows}) = riis.next() {
        let before_len = interpretation.len();
        let satisfies_equalities = |interp: &Vec<Element>| {
            rip.equalities.iter().all(|(lhs, rhs)| interp[*lhs] == interp[*rhs])
        };
        if use_old_rows {
            for row in model.old_rows(rip.id) {
                interpretation.extend_from_slice(row);
                if satisfies_equalities(interpretation) {
                    visit_new_interpretations_impl(
                        model,
                        visitor,
                        interpretation,
                        riis.clone(),
                    );
                }
                interpretation.truncate(before_len);
            }
        }
        if use_new_rows {
            for row in model.new_rows(rip.id) {
                interpretation.extend_from_slice(row);
                if satisfies_equalities(interpretation) {
                    visit_new_interpretations_impl(
                        model,
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

impl<'a> CheckedPresentation<'a> {
    pub fn visit_new_interpretations(
        &self,
        model: &Model,
        mut visitor: impl for<'b> FnMut(&'b [Element])
    ) {
        assert_eq!(
            self.signature as *const Signature,
            model.signature() as *const Signature
        );

        let mut interpretation: Vec<Element> = Vec::with_capacity(self.row_length);
        for i in 0 .. self.rips.len() {
            visit_new_interpretations_impl(
                model,
                &mut visitor,
                &mut interpretation,
                self.rips.iter().enumerate().map(|(j, rip)| RelationInInterpretation {
                    rip: rip,
                    use_new_rows: i <= j,
                    use_old_rows: i != j,
                }),
            );
        }
    }
}

#[cfg(test)]
mod test_interpretation {
    use super::*;
    use std::collections::HashSet;

    fn compute_new_interpretation(
        presentation: &CheckedPresentation,
        model: &Model,
    ) -> HashSet<Row> {
        let mut result: HashSet<Row> = HashSet::new();
        presentation.visit_new_interpretations(model, |row| {
            result.insert(row.to_vec());
        });
        result
    }

    #[test]
    fn nullary_interpretation() {
        // the interpretation over the empty product is the singleton row [], but this is never new
        let sig = Signature::from_sorts_arities(
            2,
            vec![vec![SortId(0), SortId(1)]],
        );
        let model = Model::new(&sig);
        let presentation = Presentation {
            relations: vec![],
            equalities: vec![],
        }.checked(&sig);
        assert_eq!(compute_new_interpretation(&presentation, &model), hashset!{});
    }

    #[test]
    fn unary_interpretation() {
        let sig = Signature::from_sorts_arities(
            2,
            vec![vec![SortId(0), SortId(1)]],
        );

        let r = RelationId(0);

        let mut model = Model::new(&sig);

        let a0 = model.adjoin_element(SortId(0));
        let a1 = model.adjoin_element(SortId(0));
        let b0 = model.adjoin_element(SortId(1));
        let b1 = model.adjoin_element(SortId(1));

        model.adjoin_rows(RelationId(0), vec![
            vec![a0, b1],
            vec![a1, b0],
        ]);

        let presentation = Presentation {
            relations: vec![r],
            equalities: vec![],
        }.checked(&sig);

        assert_eq!(
            compute_new_interpretation(&presentation, &model), hashset!{
            vec![a0, b1],
            vec![a1, b0],
        });

        model.age_rows();
        assert_eq!(compute_new_interpretation(&presentation, &model), hashset!{});
    }

    #[test]
    fn binary_self_join() {
        let sig = Signature::from_sorts_arities(
            2,
            vec![vec![SortId(0), SortId(1)]],
        );

        let r = RelationId(0);

        let mut model = Model::new(&sig);

        let a0 = model.adjoin_element(SortId(0));
        let a1 = model.adjoin_element(SortId(0));
        let b0 = model.adjoin_element(SortId(1));
        let b1 = model.adjoin_element(SortId(1));

        model.adjoin_rows(RelationId(0), vec![
            vec![a0, b0],
            vec![a1, b0],
            vec![a1, b1],
        ]);

        let presentation = Presentation {
            relations: vec![r, r],
            equalities: vec![(1, 3)],
        }.checked(&sig);

        assert_eq!(compute_new_interpretation(&presentation, &model), hashset!{
            vec![a0, b0, a0, b0],
            vec![a0, b0, a1, b0],
            vec![a1, b0, a0, b0],
            vec![a1, b0, a1, b0],
            vec![a1, b1, a1, b1],
        });

        model.age_rows();
        assert_eq!(compute_new_interpretation(&presentation, &model), hashset!{});
    }

    #[test]
    fn binary_join() {
        let sig = Signature::from_sorts_arities(
            2,
            vec![
                vec![SortId(0), SortId(1)],
                vec![SortId(1), SortId(0)],
            ],
        );

        let r0 = RelationId(0);
        let r1 = RelationId(1);

        let mut model = Model::new(&sig);

        let a0 = model.adjoin_element(SortId(0));
        let a1 = model.adjoin_element(SortId(0));
        let b0 = model.adjoin_element(SortId(1));
        let b1 = model.adjoin_element(SortId(1));

        model.adjoin_rows(r0, vec![
            vec![a0, b0],
            vec![a1, b0],
            vec![a1, b1],
        ]);
        model.adjoin_rows(r1, vec![
            vec![b0, a0],
            vec![b1, a1],
        ]);

        let presentation = Presentation {
            relations: vec![r0, r1],
            equalities: vec![(0, 3)],
        }.checked(&sig);

        assert_eq!(compute_new_interpretation(&presentation, &model), hashset!{
            vec![a0, b0, b0, a0],
            vec![a1, b0, b1, a1],
            vec![a1, b1, b1, a1],
        });

        model.age_rows();

        model.adjoin_rows(r0, vec![
            vec![a0, b1],
        ]);
        model.adjoin_rows(r1, vec![
            vec![b1, a0],
        ]);
        assert_eq!(compute_new_interpretation(&presentation, &model), hashset!{
             vec![a0, b1, b1, a0],
             vec![a0, b1, b0, a0],
             vec![a0, b0, b1, a0],
        });

    }

    #[test]
    fn binary_diagonal() {
        let sig = Signature::from_sorts_arities(
            2,
            vec![
                vec![SortId(0), SortId(1)],
                vec![SortId(1), SortId(1)],
            ],
        );

        let r0 = RelationId(0);
        let r1 = RelationId(1);

        let mut model = Model::new(&sig);

        let a0 = model.adjoin_element(SortId(0));
        let a1 = model.adjoin_element(SortId(0));
        let b0 = model.adjoin_element(SortId(1));
        let b1 = model.adjoin_element(SortId(1));

        model.adjoin_rows(r0, vec![
            vec![a0, b0],
            vec![a1, b0],
            vec![a1, b1],
        ]);
        model.adjoin_rows(r1, vec![
            vec![b0, b0],
            vec![b1, b0],
            vec![b0, b1],
        ]);

        let presentation = Presentation {
            relations: vec![r0, r1],
            equalities: vec![(2, 3), (1, 2)],
        }.checked(&sig);

        assert_eq!(compute_new_interpretation(&presentation, &model), hashset!{
            vec![a0, b0, b0, b0],
            vec![a1, b0, b0, b0],
        });
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SurjectionPresentation {
    pub domain: Presentation,
    pub codomain_equalities: Vec<(usize, usize)>,
    pub codomain_relations: Vec<(RelationId, Vec<usize>)>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct CheckedSurjectionPresentation<'a> {
    domain: CheckedPresentation<'a>,
    codomain_equalities: Vec<(usize, usize)>,
    codomain_relations: Vec<(RelationId, Vec<usize>)>,
}

impl SurjectionPresentation {
    pub fn checked<'a>(self, signature: &'a Signature) -> CheckedSurjectionPresentation<'a> {
        let domain = self.domain.checked(signature);
        let row_arity: Vec<SortId> =
            domain.rips.iter().
            map(|rip| signature.get_arity(rip.id).unwrap().iter()).
            flatten().
            cloned().
            collect();

        for (lhs, rhs) in &self.codomain_equalities {
            assert_eq!(row_arity[*lhs], row_arity[*rhs]);
        }
        for (r, arg_indices) in &self.codomain_relations {
            let arity = signature.get_arity(*r).unwrap();
            assert_eq!(arg_indices.len(), arity.len());
            for (ai, s) in arg_indices.iter().zip(arity) {
                assert_eq!(row_arity[*ai], *s);
            }
        }

        CheckedSurjectionPresentation {
            domain,
            codomain_equalities: self.codomain_equalities,
            codomain_relations: self.codomain_relations,
        }
    }
}

pub fn close_model(presentations: &[CheckedSurjectionPresentation], model: &mut Model) {
    for presentation in presentations {
        assert_eq!(
            presentation.domain.signature as *const Signature,
            model.signature() as *const Signature,
        );
    }
    let mut conc_eqs: Vec<(Element, Element)> = vec![];
    let mut conc_rows: Vec<(RelationId, Vec<Element>)> = vec![];

    loop {
        for presentation in presentations {
            presentation.domain.visit_new_interpretations(model, |row| {
                conc_rows.extend(presentation.codomain_relations.iter().map(|(r, row_indices)| {
                    (*r, row_indices.iter().map(|i| row[*i]).collect())
                }));
                conc_eqs.extend(presentation.codomain_equalities.iter().map(|(lhs_index, rhs_index)| {
                    (row[*lhs_index], row[*rhs_index])
                }));
            });
        }

        model.age_rows();
        conc_eqs.drain(..).for_each(|(lhs, rhs)| { model.equate(lhs, rhs); });
        model.canonicalize_elements();
        model.extend(conc_rows.drain(..));
        debug_assert!(conc_rows.is_empty());
        debug_assert!(conc_eqs.is_empty());

        let no_new_rows: bool =
            (0 .. model.signature().relation_number()).
            map(RelationId).
            all(|r| model.new_rows(r).next().is_none());
        if no_new_rows {
            break;
        }
    }
}

#[cfg(test)]
mod test_close_model {
    use super::*;

    use std::collections::HashSet;
    use std::iter::{repeat_with, once};

    fn save_rows<'a>(rows: impl IntoIterator<Item = &'a [Element]>) -> HashSet<Row> {
        rows.into_iter().map(|row| row.to_vec()).collect()
    }

    #[test]
    fn symmetry() {
        let s0 = SortId(0);
        let r0 = RelationId(0);
        let sig = Signature::from_sorts_arities(1, vec![vec![s0, s0]]);
        let mut model = Model::new(&sig);
        let el0 = model.adjoin_element(s0);
        let el1 = model.adjoin_element(s0);
        let el2 = model.adjoin_element(s0);
        let el3 = model.adjoin_element(s0);
        let el4 = model.adjoin_element(s0);
        model.adjoin_rows(r0, vec![
            vec![el0, el1],
            vec![el2, el2],
            vec![el3, el4],
            vec![el4, el3],
        ]);

        let symmetry = SurjectionPresentation {
            domain: Presentation {
                relations: vec![r0],
                equalities: vec![],
            },
            codomain_equalities: vec![],
            codomain_relations: vec![(r0, vec![1, 0])],
        }.checked(&sig);

        close_model(&[symmetry], &mut model);

        assert_eq!(save_rows(model.rows(r0)), hashset!{
            vec![el0, el1],
            vec![el1, el0],
            vec![el2, el2],
            vec![el3, el4],
            vec![el4, el3],
        });
        for &el in &[el0, el1, el2, el3, el4] {
            assert_eq!(model.representative(el), el);
        }
    }

    #[test]
    fn transitivity() {
        let s0 = SortId(0);
        let r0 = RelationId(0);
        let sig = Signature::from_sorts_arities(1, vec![vec![s0, s0]]);
        let mut model = Model::new(&sig);
        let el0 = model.adjoin_element(s0);
        let el1 = model.adjoin_element(s0);
        let el2 = model.adjoin_element(s0);
        let el3 = model.adjoin_element(s0);
        let el4 = model.adjoin_element(s0);
        let el5 = model.adjoin_element(s0);
        let el6 = model.adjoin_element(s0);
        let el7 = model.adjoin_element(s0);
        let el8 = model.adjoin_element(s0);
        let el9 = model.adjoin_element(s0);
        model.adjoin_rows(r0, vec![
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

        let transitivity = SurjectionPresentation {
            domain: Presentation {
                relations: vec![r0, r0],
                equalities: vec![(1, 2)],
            },
            codomain_relations: vec![(r0, vec![0, 3])],
            codomain_equalities: vec![],
        }.checked(&sig);

        let mut expected = save_rows(model.rows(r0));
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

        close_model(&[transitivity], &mut model);

        assert_eq!(save_rows(model.rows(r0)), expected);
        for &el in &[el0, el1, el2, el3, el4, el5, el6, el7, el8, el9] {
            assert_eq!(model.representative(el), el);
        }
    }

    #[test]
    fn antisymmetry() {
        let s0 = SortId(0);
        let r0 = RelationId(0);
        let sig = Signature::from_sorts_arities(1, vec![vec![s0, s0]]);
        let mut model = Model::new(&sig);
        let el0 = model.adjoin_element(s0);
        let el1 = model.adjoin_element(s0);
        let el2 = model.adjoin_element(s0);
        let el3 = model.adjoin_element(s0);
        let el4 = model.adjoin_element(s0);
        let el5 = model.adjoin_element(s0);
        let el6 = model.adjoin_element(s0);
        let el7 = model.adjoin_element(s0);

        model.adjoin_rows(r0, vec![
            vec![el0, el1],

            vec![el2, el3],
            vec![el3, el2],

            vec![el5, el5],

            vec![el5, el6],
            vec![el6, el7],
            vec![el7, el5],
        ]);

        let antisymmetry = SurjectionPresentation {
            domain: Presentation {
                relations: vec![r0, r0],
                equalities: vec![(0, 3), (1, 2)],
            },
            codomain_relations: vec![],
            codomain_equalities: vec![(0, 1)],
        }.checked(&sig);

        close_model(&[antisymmetry], &mut model);

        let elx = model.representative(el2);
        assert_eq!(model.representative(el3), elx);
        assert_eq!(save_rows(model.rows(r0)), hashset!{
            vec![el0, el1],

            vec![elx, elx],

            vec![el5, el5],

            vec![el5, el6],
            vec![el6, el7],
            vec![el7, el5],
        });
        for &el in &[el0, el1, el4, el5, el6, el7] {
            assert_eq!(model.representative(el), el);
        }
    }

    #[test]
    fn antisymmetry_transitivity() {
        let s0 = SortId(0);
        let r0 = RelationId(0);
        let sig = Signature::from_sorts_arities(1, vec![vec![s0, s0]]);

        let transitivity = SurjectionPresentation {
            domain: Presentation {
                relations: vec![r0, r0],
                equalities: vec![(1, 2)],
            },
            codomain_relations: vec![(r0, vec![0, 3])],
            codomain_equalities: vec![],
        }.checked(&sig);
        let antisymmetry = SurjectionPresentation {
            domain: Presentation {
                relations: vec![r0, r0],
                equalities: vec![(0, 3), (1, 2)],
            },
            codomain_relations: vec![],
            codomain_equalities: vec![(0, 1)],
        }.checked(&sig);

        let mut model = Model::new(&sig);
        let el0 = model.adjoin_element(s0);
        let el1 = model.adjoin_element(s0);
        let el2 = model.adjoin_element(s0);
        let el3 = model.adjoin_element(s0);
        let el4 = model.adjoin_element(s0);
        let el5 = model.adjoin_element(s0);
        let el6 = model.adjoin_element(s0);
        let el7 = model.adjoin_element(s0);

        model.adjoin_rows(r0, vec![
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
            repeat_with(|| model.adjoin_element(s0)).
            take(10).
            collect();
        model.adjoin_rows(r0,
            cycle_elements.iter().
            zip(cycle_elements.iter().skip(1).chain(once(cycle_elements.first().unwrap()))).
            map(|(a, b)| vec![*a, *b])
        );

        close_model(&[transitivity, antisymmetry], &mut model);

        for &el in &[el0, el1, el4] {
            assert_eq!(model.representative(el), el);
        }

        let elx = model.representative(el2);
        assert_eq!(model.representative(el3), elx);

        let ely = model.representative(el5);
        assert_eq!(model.representative(el6), ely);
        assert_eq!(model.representative(el7), ely);

        let elz = model.representative(*cycle_elements.first().unwrap());
        for el in cycle_elements {
            assert_eq!(model.representative(el), elz);
        }

        assert_eq!(save_rows(model.rows(r0)), hashset!{
            vec![el0, el1],
            vec![elx, elx],
            vec![ely, ely],
            vec![elz, elz],
        });
    }
}
