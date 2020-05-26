use super::union_find::*;
use super::element::*;
use super::signature::*;
use std::vec::Vec;
use std::collections::HashSet;
use std::iter::{FromIterator, once};
use std::mem::swap;

pub type Row = Vec<Element>;

#[derive(Clone, PartialEq, Eq, Debug)]
struct DeltaRelation {
    old_rows: HashSet<Row>,
    new_rows: HashSet<Row>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Model<Sig: Signature> {
    signature: Sig,
    element_sorts: Vec<Sig::Sort>,
    representatives: UnionFind,
    relations: Vec<DeltaRelation>,
}

impl<Sig: Signature> Model<Sig> {
    pub fn self_check(&self) {
        let sig = self.signature();

        assert_eq!(self.representatives.len(), self.element_sorts.len());
        for (el0, &s) in self.element_sorts.iter().enumerate() {
            // TODO check whether el0 < u32 max
            let el = Element(el0 as u32);
            // element's sort is a valid sort in m's signature
            assert!(sig.sorts().iter().find(|s0| **s0 == s).is_some());
            // el's sort is the same as that of its representative
            let repr = self.representatives.find_const(el);
            assert_eq!(s, self.element_sorts[repr.0 as usize]);
        }

        assert_eq!(self.relations.len(), sig.relations().len());

        for &r in sig.relations() {
            let arity = sig.arity(r);
            let r0: usize = r.into();
            let DeltaRelation{old_rows, new_rows} = &self.relations[r0];

            assert!(old_rows.is_disjoint(new_rows));

            for row in old_rows.iter().chain(new_rows) {
                // this row has the right length
                assert_eq!(row.len(), arity.len());
                for (&el, &sort) in row.iter().zip(arity.iter()) {
                    assert_eq!(self.element_sort(el), sort);
                }
            }
        }
    }

    pub fn new(signature: Sig) -> Self {
        let relations = Vec::from_iter(
            signature.relations().iter().
            map(|_| DeltaRelation { old_rows: HashSet::default(), new_rows: HashSet::default() })
        );
        Model {
            signature,
            element_sorts: Vec::new(),
            representatives: UnionFind::new(),
            relations: relations,
        }
    }
    pub fn signature(&self) -> &Sig {
        &self.signature
    }
    pub fn elements<'a>(&'a self) -> impl Iterator<Item = (Element, Sig::Sort)> + 'a {
        self.element_sorts.iter().enumerate().map(|(el0, sort)|
            (Element(el0 as u32), *sort)
        )
    }
    pub fn element_sort(&self, el: Element) -> Sig::Sort {
        self.element_sorts[el.0 as usize]
    }
    pub fn sort_elements<'a>(&'a self, sort: Sig::Sort) -> impl Iterator<Item = Element> + 'a {
        self.elements()
        .filter_map(move |(el, el_sort)| {
            if el_sort == sort {
                Some(el)
            } else {
                None
            }
        })
    }
    pub fn representative_const(&self, el: Element) -> Element {
        self.representatives.find_const(el)
    }
    pub fn representative(&mut self, el: Element) -> Element {
        self.representatives.find(el)
    }
    pub fn old_rows<'a>(&'a self, relation: Sig::Relation) -> impl Iterator<Item = &'a [Element]> {
        self.relations[relation.into()].old_rows.iter().map(|row| row.as_slice())
    }
    pub fn new_rows<'a>(&'a self, relation: Sig::Relation) -> impl Iterator<Item = &'a [Element]> {
        self.relations[relation.into()].new_rows.iter().map(|row| row.as_slice())
    }
    pub fn rows<'a>(&'a self, relation: Sig::Relation) -> impl Iterator<Item = &'a [Element]> {
        self.old_rows(relation).chain(self.new_rows(relation))
    }

    pub fn age_rows(&mut self) {
        for DeltaRelation { new_rows, old_rows } in &mut self.relations {
            old_rows.extend(new_rows.drain());
        }
        #[cfg(debug_assertions)]
        self.self_check();
    }
    pub fn adjoin_element(&mut self, sort: Sig::Sort) -> Element {
        let el = self.representatives.new_element();
        debug_assert_eq!(el.0 as usize, self.element_sorts.len());
        self.element_sorts.push(sort);
        #[cfg(debug_assertions)]
        self.self_check();
        el
    }

    pub fn adjoin_rows(
        &mut self,
        relation: Sig::Relation,
        rows: impl IntoIterator<Item = Row>,
    ) -> usize {
        let arity = self.signature.arity(relation);

        let DeltaRelation { new_rows, old_rows } = &mut self.relations[relation.into()];
        let representatives = &mut self.representatives;
        let element_sorts = &self.element_sorts;

        let before_len = new_rows.len();
        new_rows.extend(
            rows.into_iter().
            filter_map(|mut row| {
                assert_eq!(arity.len(), row.len());
                for (el, &required_sort) in row.iter_mut().zip(arity) {
                    *el = representatives.find(*el);
                    let el_sort = element_sorts[el.0 as usize];
                    assert_eq!(el_sort, required_sort);
                }

                if !old_rows.contains(&row) {
                    Some(row)
                } else {
                    None
                }
            })
        );

        let new_row_num = new_rows.len() - before_len;

        #[cfg(debug_assertions)]
        self.self_check();

        new_row_num
    }
    pub fn remove_rows<'a>(
        &mut self,
        relation: Sig::Relation,
        rows: impl IntoIterator<Item = &'a Row>
    ) {
        let DeltaRelation { new_rows, old_rows } = &mut self.relations[relation.into()];
        for row in rows {
            new_rows.remove(row);
            old_rows.remove(row);
        }
        #[cfg(debug_assertions)]
        self.self_check();
    }

    pub fn equate(&mut self, mut a: Element, mut b: Element) -> Element {
        assert_eq!(self.element_sort(a), self.element_sort(b));

        a = self.representatives.find(a);
        b = self.representatives.find(b);

        if a == b {
            return a;
        }

        // make b the element with the lower id
        if b.0 > a.0 {
            swap(&mut a, &mut b);
        }

        self.representatives.merge_into(a, b);

        #[cfg(debug_assertions)]
        self.self_check();

        b
    }

    pub fn canonicalize_elements(&mut self) {
        // TODO: do not copy rels; can't iter over `self.signature.relations()` directly because
        // this would borrow `self`
        for r in self.signature.relations().to_vec() {
            let dirty_rows: Vec<Row> = Vec::new();
            debug_assert!(dirty_rows.is_empty());

            let dirty_rows: Vec<Row> =
                 // old and new rows
                self.old_rows(r).chain(self.new_rows(r))
                // containing at least one dirty element
                // TODO: use representative instead of the const version; aliasing issues
                .filter(|row| {
                    row.iter()
                        .find(|el| self.representative_const(**el) != **el)
                        .is_some()
                })
                .map(|row| row.to_vec())
                .collect();
            self.remove_rows(r, dirty_rows.iter());
            self.adjoin_rows(r, dirty_rows.into_iter());
        }

        #[cfg(debug_assertions)]
        self.self_check();
    }
}

impl<Sig: Signature> Extend<(Sig::Relation, Row)> for Model<Sig> {
    fn extend<I: IntoIterator<Item = (Sig::Relation, Row)>>(&mut self, rows: I) {
        for (r, row) in rows {
            self.adjoin_rows(r, once(row));
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    arities!{
        pub enum ExampleSort {S0, S1},
        pub enum ExampleRelation {
            R0: S0 x S1,
            R1: ,
            R2: S1 x S0 x S1,
            R3: S0 x S0,
        },
    }
    use ExampleSort::*;
    use ExampleRelation::*;
    type ExampleSignature = StaticSignature<ExampleSort, ExampleRelation>;
    type Model = super::Model<ExampleSignature>;

    fn clone_rows<'a, I: Iterator<Item = &'a [Element]>>(rows: I) -> HashSet<Row> {
        HashSet::from_iter(rows.map(|els| els.to_vec()))
    }

    #[test]
    fn adjoin_element() {
        let mut m = Model::new(ExampleSignature::new());
        let el0 = m.adjoin_element(S0);
        assert_eq!(m.representative(el0), el0);
        m.self_check();

        let el1 = m.adjoin_element(S1);
        assert_eq!(m.representative(el0), el0);
        assert_eq!(m.representative(el1), el1);
        m.self_check();

        let el2 = m.adjoin_element(S1);
        assert_eq!(m.representative(el0), el0);
        assert_eq!(m.representative(el1), el1);
        assert_eq!(m.representative(el2), el2);
        m.self_check();
    }

    #[test]
    fn adjoin_rows() {
        let mut m = Model::new(ExampleSignature::new());
        let el0 = m.adjoin_element(S0);
        let el1 = m.adjoin_element(S0);
        let el2 = m.adjoin_element(S0);
        let el3 = m.adjoin_element(S1);
        let el4 = m.adjoin_element(S1);

        m.adjoin_rows(R0, vec![
            vec![el0, el3],
            vec![el1, el3],
        ]);
        m.self_check();
        assert_eq!(
            clone_rows(m.rows(R0)),
            hashset!{vec![el0, el3], vec![el1, el3]}
        );
        assert_eq!(clone_rows(m.rows(R1)), hashset!{});
        assert_eq!(clone_rows(m.rows(R2)), hashset!{});
        assert_eq!(clone_rows(m.rows(R3)), hashset!{});

        m.adjoin_rows(R0, vec![
            vec![el1, el4],
            vec![el1, el4],
        ]);
        m.self_check();
        assert_eq!(
            clone_rows(m.rows(R0)),
            hashset!{vec![el0, el3], vec![el1, el3], vec![el1, el4]}
        );

        m.adjoin_rows(R1, vec![vec![]]);
        m.self_check();
        assert_eq!(
            clone_rows(m.rows(R0)),
            hashset!{vec![el0, el3], vec![el1, el3], vec![el1, el4]}
        );
        assert_eq!(
            clone_rows(m.rows(R1)),
            hashset!{vec![]}
        );

        m.adjoin_rows(R2, vec![
            vec![el3, el2, el4],
            vec![el4, el2, el4],
        ]);
        m.self_check();

        m.adjoin_rows(R3, vec![
            vec![el0, el0]
        ]);
        m.self_check();
    }

    #[test]
    fn extend() {
        let mut m = Model::new(ExampleSignature::new());
        let el0 = m.adjoin_element(S0);
        let el2 = m.adjoin_element(S0);
        let el3 = m.adjoin_element(S1);
        let el4 = m.adjoin_element(S1);

        m.extend(vec![
            (R0, vec![el0, el3]),
            (R2, vec![el3, el2, el4]),
        ]);
        m.self_check();
        assert_eq!(
            clone_rows(m.rows(R0)),
            hashset!{vec![el0, el3]}
        );
        assert_eq!(clone_rows(m.rows(R1)), hashset!{});
        assert_eq!(
            clone_rows(m.rows(R2)),
            hashset!{vec![el3, el2, el4]}
        );
        assert_eq!(clone_rows(m.rows(R3)), hashset!{});
    }

    #[test]
    fn old_new_rows() {
        let mut m = Model::new(ExampleSignature::new());
        let el0 = m.adjoin_element(S0);
        let el2 = m.adjoin_element(S0);
        let el3 = m.adjoin_element(S1);
        let el4 = m.adjoin_element(S1);

        m.extend(vec![
            (R0, vec![el0, el3]),
            (R2, vec![el3, el2, el4]),
        ]);
        m.self_check();
        assert_eq!(
            clone_rows(m.new_rows(R0)),
            hashset!{vec![el0, el3]}
        );
        assert_eq!(clone_rows(m.new_rows(R1)), hashset!{});
        assert_eq!(
            clone_rows(m.new_rows(R2)),
            hashset!{vec![el3, el2, el4]}
        );
        assert_eq!(clone_rows(m.new_rows(R3)), hashset!{});

        assert!(m.old_rows(R0).next().is_none());
        assert!(m.old_rows(R1).next().is_none());
        assert!(m.old_rows(R2).next().is_none());
        assert!(m.old_rows(R3).next().is_none());

        let mut n = m.clone();
        n.age_rows();
        n.self_check();

        assert_eq!(clone_rows(n.old_rows(R0)), clone_rows(m.rows(R0)));
        assert_eq!(clone_rows(n.old_rows(R1)), clone_rows(m.rows(R1)));
        assert_eq!(clone_rows(n.old_rows(R2)), clone_rows(m.rows(R2)));
        assert_eq!(clone_rows(n.old_rows(R3)), clone_rows(m.rows(R3)));

        assert!(n.new_rows(R0).next().is_none());
        assert!(n.new_rows(R1).next().is_none());
        assert!(n.new_rows(R2).next().is_none());
        assert!(n.new_rows(R3).next().is_none());

        n.extend(once((R1, vec![])));
        assert!(n.old_rows(R1).next().is_none());
        assert_eq!(clone_rows(n.rows(R1)), hashset!{vec![]});

        n.extend(once((R2, vec![el3, el2, el4]))); // already in old rows
        n.self_check();
        assert!(n.old_rows(R2).find(|row| row == &[el3, el2, el4]).is_some());
        assert!(n.new_rows(R2).next().is_none());
    }

    #[test]
    fn equate_canonicalize() {
        let mut m = Model::new(ExampleSignature::new());
        let el0 = m.adjoin_element(S0);
        let el1 = m.adjoin_element(S0);
        let el2 = m.adjoin_element(S0);
        let el3 = m.adjoin_element(S1);
        let el4 = m.adjoin_element(S1);

        m.adjoin_rows(R2, vec![
            vec![el3, el0, el4],
            vec![el3, el1, el4],
            vec![el4, el2, el3],
        ]);
        m.age_rows();
        m.adjoin_rows(R2, vec![
            vec![el3, el1, el3],
            vec![el4, el0, el3],
            vec![el4, el0, el4],
        ]);

        assert_eq!(m.equate(el0, el1), el0);
        m.self_check();
        m.canonicalize_elements();
        m.self_check();

        assert_eq!(m.representative(el0), el0);
        assert_eq!(m.representative(el1), el0);
        assert_eq!(m.representative(el2), el2);
        assert_eq!(m.representative(el3), el3);

        assert_eq!(
            clone_rows(m.rows(R2)),
            hashset!{
                vec![el3, el0, el4],
                vec![el3, el0, el4],
                vec![el4, el2, el3],
                vec![el3, el0, el3],
                vec![el4, el0, el3],
                vec![el4, el0, el4],
            }
        );
        assert!(clone_rows(m.old_rows(R2)).is_subset(&hashset!{
            vec![el3, el0, el4],
            vec![el3, el1, el4],
            vec![el4, el2, el3],
        }));
    }
}
