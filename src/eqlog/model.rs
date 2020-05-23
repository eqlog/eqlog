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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct ElementInfo<Sort> {
    row_occurences: usize,
    sort: Sort,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Model<Sig: Signature> {
    signature: Sig,
    element_infos: Vec<ElementInfo<Sig::Sort>>,
    representatives: UnionFind,
    dirty_elements: HashSet<Element>,
    relations: Vec<DeltaRelation>,
}

impl<Sig: Signature> Model<Sig> {
    pub fn new(signature: Sig) -> Self {
        let relations = Vec::from_iter(
            signature.relations().iter().
            map(|_| DeltaRelation { old_rows: hashset!{}, new_rows: hashset!{} })
        );
        Model {
            signature,
            element_infos: Vec::new(),
            representatives: UnionFind::new(),
            dirty_elements: HashSet::new(),
            relations: relations,
        }
    }
    pub fn signature(&self) -> &Sig {
        &self.signature
    }
    pub fn elements<'a>(&'a self) -> impl Iterator<Item = (Element, Sig::Sort)> + 'a {
        self.element_infos.iter().enumerate().map(|(el0, info)|
            (Element(el0 as u32), info.sort)
        )
    }
    pub fn element_sort(&self, el: Element) -> Sig::Sort {
        let Element(el0) = el;
        self.element_infos[el0 as usize].sort
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
    }
    pub fn adjoin_element(&mut self, sort: Sig::Sort) -> Element {
        let Element(el) = self.representatives.new_element();
        debug_assert_eq!(el as usize, self.element_infos.len());
        self.element_infos.push(ElementInfo { sort, row_occurences: 0 });
        Element(el)
    }

    pub fn adjoin_rows(
        &mut self,
        relation: Sig::Relation,
        rows: impl IntoIterator<Item = Row>,
    ) -> usize {
        let arity = self.signature.arity(relation);

        let element_infos = &mut self.element_infos;
        let DeltaRelation { new_rows, old_rows } = &mut self.relations[relation.into()];
        let representatives = &mut self.representatives;

        let before_len = new_rows.len();
        new_rows.extend(
            rows.into_iter().
            map(|mut row| {
                assert_eq!(arity.len(), row.len());
                for (el, sort) in row.iter_mut().zip(arity) {
                    *el = representatives.find(*el);
                    let info = &mut element_infos[el.0 as usize];
                    assert_eq!(info.sort, *sort);
                    info.row_occurences += 1;
                }
                row
            }).
            filter(|row| !old_rows.contains(row))
        );
        new_rows.len() - before_len
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
    }

    pub fn equate(&mut self, mut a: Element, mut b: Element) -> Element {
        assert_eq!(self.element_sort(a), self.element_sort(b));

        a = self.representatives.find(a);
        b = self.representatives.find(b);

        if a == b {
            return a;
        }

        let eis = &mut self.element_infos;

        // make b the element with maximal row_occurences
        if eis[a.0 as usize].row_occurences > eis[b.0 as usize].row_occurences {
            swap(&mut a, &mut b);
        }

        self.representatives.merge_into(a, b);
        eis[b.0 as usize].row_occurences += eis[a.0 as usize].row_occurences;
        self.dirty_elements.insert(a);

        b
    }

    pub fn canonicalize_elements(&mut self) {
        // Swap out self.dirty_elements for an empty list
        let mut dirty_elements = HashSet::new();
        swap(&mut dirty_elements, &mut self.dirty_elements);

        let mut dirty_rows: Vec<Row> = vec![];
        let rels = self.signature.relations().to_vec(); 
        // TODO: do not copy rels; can't iter over `self.signature.relations()` directly because
        // this would borrow `self`
        for r in rels {
            debug_assert!(dirty_rows.is_empty());

            dirty_rows.extend(
                self.old_rows(r).chain(self.new_rows(r)).
                filter(|row| row.iter().find(|el| dirty_elements.contains(*el)).is_some()).
                map(|row| row.to_vec())
            );
            // remove_rows doesn't access dirty_elements
            self.remove_rows(r, dirty_rows.iter());
            // adjoin_rows will make rows canonical when adjoining
            self.adjoin_rows(r, dirty_rows.drain(..));
        }

        // self.dirty_elements is already empty, but let's reuse the allocated capacity of
        // dirty_elements:
        dirty_elements.clear();
        swap(&mut dirty_elements, &mut self.dirty_elements);
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

    fn assert_valid_model(m: &Model) {
        let sig = m.signature();
        for (_, s) in m.elements() {
            // element's sort is a valid sort in m's signature
            assert!(sig.sorts().iter().find(|s0| **s0 == s).is_some());
        }

        for &r in sig.relations() {
            let arity = sig.arity(r);
            let old_rows = clone_rows(m.old_rows(r));
            let new_rows = clone_rows(m.new_rows(r));
            assert!(old_rows.is_disjoint(&new_rows));
            let rows = clone_rows(m.rows(r));
            assert_eq!(
                HashSet::from_iter(old_rows.union(&new_rows).cloned()),
                rows
            );

            for row in rows {
                // this row has the right length
                assert_eq!(row.len(), arity.len());
                for (el, sort) in row.iter().zip(arity.iter()) {
                    let repr = m.representative_const(*el);
                    if repr != *el {
                        assert!(m.dirty_elements.contains(el));
                    }
                    // el has the sort specified by arity
                    assert_eq!(m.element_sort(repr), *sort);
                }
            }
        }
    }

    #[test]
    fn new_model_is_valid() {
        let m = Model::new(ExampleSignature::new());
        assert_valid_model(&m);
    }

    #[test]
    fn adjoin_element() {
        let mut m = Model::new(ExampleSignature::new());
        let el0 = m.adjoin_element(S0);
        assert_eq!(m.representative(el0), el0);
        assert_valid_model(&m);

        let el1 = m.adjoin_element(S1);
        assert_eq!(m.representative(el0), el0);
        assert_eq!(m.representative(el1), el1);
        assert_valid_model(&m);

        let el2 = m.adjoin_element(S1);
        assert_eq!(m.representative(el0), el0);
        assert_eq!(m.representative(el1), el1);
        assert_eq!(m.representative(el2), el2);
        assert_valid_model(&m);
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
        assert_valid_model(&m);
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
        assert_valid_model(&m);
        assert_eq!(
            clone_rows(m.rows(R0)),
            hashset!{vec![el0, el3], vec![el1, el3], vec![el1, el4]}
        );

        m.adjoin_rows(R1, vec![vec![]]);
        assert_valid_model(&m);
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
        assert_valid_model(&m);

        m.adjoin_rows(R3, vec![
            vec![el0, el0]
        ]);
        assert_valid_model(&m);
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
        assert_valid_model(&m);
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
        assert_valid_model(&m);
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
        assert_valid_model(&n);

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
        assert_valid_model(&n);
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
        assert_valid_model(&m);
        m.canonicalize_elements();
        assert_valid_model(&m);

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
