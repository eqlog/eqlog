use std::vec::Vec;
use std::collections::{HashMap, HashSet};
use std::iter::{FromIterator, repeat, Iterator, once};
use crate::union_find::*;
use crate::element::*;
use crate::signature::*;

pub type Row = Vec<Element>;

#[derive(Clone, PartialEq, Eq, Debug)]
struct DeltaRelation {
    old_rows: HashSet<Row>,
    new_rows: HashSet<Row>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Model<'a> {
    signature: &'a Signature,
    element_sorts: HashMap<Element, SortId>,
    representatives: UnionFind,
    relations: Vec<DeltaRelation>,
}

impl<'a> Model<'a> {
    pub fn new(signature: &'a Signature) -> Self {
        let relations = Vec::from_iter(
            repeat(DeltaRelation { old_rows: hashset!{}, new_rows: hashset!{} }).
            take(signature.relation_number())
        );
        Model {
            signature,
            element_sorts: HashMap::new(),
            representatives: UnionFind::new(),
            relations: relations,
        }
    }
    pub fn signature(&self) -> &'a Signature {
        self.signature
    }
    pub fn elements<'b>(&'b self) -> impl Iterator<Item = (Element, SortId)> + 'b {
        self.element_sorts.iter().map(|(el, s)| (*el, *s))
    }
    pub fn element_sort(&self, el: Element) -> SortId {
        *self.element_sorts.get(&el).unwrap()
    }
    pub fn representative_const(&self, el: Element) -> Element {
        self.representatives.find_const(el)
    }
    pub fn representative(&mut self, el: Element) -> Element {
        self.representatives.find(el)
    }
    pub fn old_rows<'b>(&'b self, relation_id: RelationId) -> impl Iterator<Item = &'b [Element]> {
        let RelationId(r) = relation_id;
        self.relations[r].old_rows.iter().map(|row| row.as_slice())
    }
    pub fn new_rows<'b>(&'b self, relation_id: RelationId) -> impl Iterator<Item = &'b [Element]> {
        let RelationId(r) = relation_id;
        self.relations[r].new_rows.iter().map(|row| row.as_slice())
    }
    pub fn rows<'b>(&'b self, relation_id: RelationId) -> impl Iterator<Item = &'b [Element]> {
        self.old_rows(relation_id).chain(self.new_rows(relation_id))
    }

    pub fn age_rows(&mut self) {
        for DeltaRelation { new_rows, old_rows } in &mut self.relations {
            old_rows.extend(new_rows.drain());
        }
    }
    pub fn adjoin_element(&mut self, sort: SortId) -> Element {
        assert!(self.signature.has_sort(sort));

        let el = self.representatives.new_element();
        self.element_sorts.insert(el, sort);
        el
    }
    pub fn adjoin_rows<I: IntoIterator<Item = Row>>(&mut self, r: RelationId, rows: I) {
        let arity =
            self.signature.get_arity(r).
            unwrap_or_else(|| panic!("Invalid relation id"));

        // get reference to element_sorts so that the lambda passed to `inspect` doesn't need to
        // capture `self`, which is also needed to access `self.relations`
        let element_sorts = &mut self.element_sorts;
        let RelationId(r0) = r;
        let DeltaRelation { new_rows, old_rows } = &mut self.relations[r0];

        new_rows.extend(
            rows.into_iter().inspect(|row| {
                assert_eq!(arity.len(), row.len());
                for (el, sort) in row.iter().zip(arity.iter()) {
                    assert_eq!(element_sorts.get(el), Some(sort));
                }
            }).filter(|row| !old_rows.contains(row))
        );
    }
    pub fn remove_rows<'b, I: IntoIterator<Item = &'b Row>>(&mut self, r: RelationId, rows: I) {
        let RelationId(r0) = r;
        let DeltaRelation { new_rows, old_rows } = &mut self.relations[r0];
        for row in rows {
            new_rows.remove(row);
            old_rows.remove(row);
        }
    }

    pub fn equate(&mut self, mut a: Element, mut b: Element) -> Element {
        a = self.representatives.find(a);
        b = self.representatives.find(b);

        // TODO: choose which element to pick based on how many rows it appears in
        let Element(a0) = a;
        if a0 % 2 == 0 {
            self.identify_with(a, b);
            b
        } else {
            self.identify_with(b, a);
            a
        }
    }

    pub fn identify_with(&mut self, before: Element, after: Element) {
        assert_eq!(self.element_sort(before), self.element_sort(after));

        let mut matching_rows: Vec<Row> = vec![];
        for r in 0 .. self.signature.relation_number() {
            let DeltaRelation { new_rows, old_rows } = &self.relations[r];
            matching_rows.extend(
                old_rows.iter().chain(new_rows.iter()).
                filter(|row| row.iter().find(|el| **el == before).is_some()).
                cloned()
            );
            self.remove_rows(RelationId(r), matching_rows.iter());
            self.adjoin_rows(RelationId(r), matching_rows.drain(..).map(|mut row| {
                for el in row.iter_mut() {
                    if *el == before {
                        *el = after;
                    }
                }
                row
            }));
        }

        self.representatives.merge_into(before, after);
        self.element_sorts.remove(&before);
    }
}

impl<'a> Extend<(RelationId, Row)> for Model<'a> {
    fn extend<I: IntoIterator<Item = (RelationId, Row)>>(&mut self, rows: I) {
        for (r, row) in rows {
            self.adjoin_rows(r, once(row));
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn assert_valid_model(m: &Model) {
        for (el, s) in m.elements() {
            // el's sort is a valid sort in m's signature
            assert!(m.signature.has_sort(s));
            // el is a canonical representative
            assert_eq!(m.representative_const(el), el);
        }

        for (r, arity) in m.signature.iter_arities().enumerate() {
            let old_rows = clone_rows(m.old_rows(RelationId(r)));
            let new_rows = clone_rows(m.new_rows(RelationId(r)));
            assert!(old_rows.is_disjoint(&new_rows));
            let rows = clone_rows(m.rows(RelationId(r)));
            assert_eq!(
                HashSet::from_iter(old_rows.union(&new_rows).cloned()),
                rows
            );

            for row in rows {
                // this row has the right length
                assert_eq!(row.len(), arity.len());
                for (el, sort) in row.iter().zip(arity.iter()) {
                    // el is a canonical representative
                    assert!(m.representative_const(*el) == *el);
                    // el has the sort specified by arity
                    assert_eq!(m.element_sorts[el], *sort);
                }
            }
        }
    }

    static S0: SortId = SortId(0);
    static S1: SortId = SortId(1);
    static R0: RelationId = RelationId(0);
    static R1: RelationId = RelationId(1);
    static R2: RelationId = RelationId(2);
    static R3: RelationId = RelationId(3);
    fn sig() -> Signature {
        let mut sig = Signature::new();
        assert_eq!(sig.add_sort(), S0);
        assert_eq!(sig.add_sort(), S1);
        assert_eq!(sig.add_relation(vec![S0, S1]), R0);
        assert_eq!(sig.add_relation(vec![]), R1);
        assert_eq!(sig.add_relation(vec![S1, S0, S1]), R2);
        assert_eq!(sig.add_relation(vec![S0, S0]), R3);
        sig
    }

    #[test]
    fn new_model_is_valid() {
        let sig = sig();
        let m = Model::new(&sig);

        assert_valid_model(&m);
    }

    #[test]
    fn adjoin_element() {
        let sig = sig();
        let mut m = Model::new(&sig);
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

    #[test] #[should_panic]
    fn adjoin_element_invalid_sort() {
        let sig = sig();
        let mut m = Model::new(&sig);
        m.adjoin_element(SortId(65433));
    }

    fn clone_rows<'a, I: Iterator<Item = &'a [Element]>>(rows: I) -> HashSet<Row> {
        HashSet::from_iter(rows.map(|els| els.to_vec()))
        // HashSet::from_iter(rows.map(<[Element]>::to_vec))
    }

    #[test]
    fn adjoin_rows() {
        let sig = sig();
        let mut m = Model::new(&sig);
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
        let sig = sig();
        let mut m = Model::new(&sig);
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
        let sig = sig();
        let mut m = Model::new(&sig);
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
    fn equate() {
        let sig = sig();
        let mut m = Model::new(&sig);
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
        ]);

        m.identify_with(el1, el0);
        assert_valid_model(&m);

        assert_eq!(m.representative(el0), el0);
        assert_eq!(m.representative(el1), el0);
        assert_eq!(m.representative(el2), el2);
        assert_eq!(m.representative(el3), el3);

        assert_eq!(
            clone_rows(m.old_rows(R2)),
            hashset!{vec![el3, el0, el4], vec![el4, el2, el3]}
        );
        assert_eq!(
            clone_rows(m.new_rows(R2)),
            hashset!{vec![el3, el0, el3]}
        );
    }
}
