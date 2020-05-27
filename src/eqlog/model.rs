use super::theory::*;
use super::relational_structure::*;
use super::element::*;
use std::iter::once;

#[derive(Clone, PartialEq, Eq, Debug)]
struct Model<'t, Sig: Signature> {
    theory: &'t Theory<Sig>,
    structure: RelationalStructure<Sig>,
}

impl<'t, Sig: Signature + Copy> Model<'t, Sig> {
    fn new(theory: &'t Theory<Sig>) -> Self {
        Model {
            theory,
            structure: RelationalStructure::new(theory.signature),
        }
    }
    pub fn elements<'a>(&'a self) -> impl Iterator<Item = (Element, Sig::Sort)> + 'a {
        self.structure.elements()
    }
    pub fn element_sort(&self, el: Element) -> Sig::Sort {
        self.structure.element_sort(el)
    }
    pub fn sort_elements<'a>(&'a self, sort: Sig::Sort) -> impl Iterator<Item = Element> + 'a {
        self.structure.sort_elements(sort)
    }
    pub fn representative_const(&self, el: Element) -> Element {
        self.structure.representative_const(el)
    }
    pub fn representative(&mut self, el: Element) -> Element {
        self.structure.representative(el)
    }
    pub fn rows<'a>(&'a self, relation: Sig::Relation) -> impl Iterator<Item = &'a [Element]> {
        self.structure.rows(relation)
    }
    pub fn adjoin_element(&mut self, sort: Sig::Sort) -> Element {
        self.structure.adjoin_element(sort)
    }
    pub fn adjoin_operation(&mut self, op: Sig::Relation, args: Vec<Element>) -> Element {
        assert_eq!(
            self.theory.signature.relation_kind(op),
            RelationKind::Operation,
            "adjoin_operation with predicate"
        );

        let arity: &[Sig::Sort] = self.theory.signature.arity(op);
        let dom_len = arity.len() - 1;
        let op_dom = &arity[.. dom_len];
        let cod = arity[dom_len];

        assert!(
            op_dom.iter().cloned()
            .eq(args.iter().map(|&arg| self.element_sort(arg)))
        );

        let result = self.adjoin_element(cod);
        let mut row = args;
        row.push(result);
        self.adjoin_rows(op, once(row));
        result
    }
    pub fn adjoin_rows(
        &mut self,
        relation: Sig::Relation,
        rows: impl IntoIterator<Item = Row>,
    ) -> usize {
        self.structure.adjoin_rows(relation, rows)
    }
    pub fn equate(&mut self, a: Element, b: Element) -> Element {
        self.structure.equate(a, b)
    }
    pub fn close(&mut self) {
        let sp_iter = 
            self.theory.functionalities.iter().map(|(r, sp)| sp)
            .chain(self.theory.axioms.iter().map(|(seq, sp)| sp));
        close_structure(
            sp_iter,
            &mut self.structure
        );
    }
}
