use std::collections::BTreeSet;
use std::sync::Arc;

use super::data::{RelationData, SortData};
use super::{Element, Error, RelationId, RelationKind, Signature, SortId};

/// Elements, equalities, and relation tables for a runtime signature.
///
/// Equality merges leave stored rows untouched. Ownership is recorded by
/// membership relations. No operation evaluates rules or enforces functionality.
#[derive(Clone, Debug)]
pub struct DynamicModel {
    signature: Arc<Signature>,
    sorts: Vec<SortData>,
    relations: Vec<RelationData>,
}

impl DynamicModel {
    /// Creates a structure with no elements or facts.
    pub fn new(signature: Arc<Signature>) -> Self {
        Self {
            sorts: signature.sorts().map(|_| SortData::new()).collect(),
            relations: signature
                .relations()
                .map(|(_, rel)| RelationData::new(rel.arity.len()))
                .collect(),
            signature,
        }
    }

    /// Assembles stored data without renumbering elements or rewriting rows.
    ///
    /// Checks storage dimensions, allocated handles, and representative sets.
    /// Membership and other theory axioms may remain unsatisfied.
    pub(super) fn from_parts(
        signature: Arc<Signature>,
        sorts: Vec<SortData>,
        relations: Vec<RelationData>,
    ) -> Result<Self, Error> {
        if sorts.len() != signature.sorts().len() || relations.len() != signature.relations().len()
        {
            return Err(Error::InvalidModel(
                "storage does not match the signature".into(),
            ));
        }
        let model = Self {
            signature,
            sorts,
            relations,
        };
        for (sort, data) in model.sorts.iter().enumerate() {
            if data.weights.len() != data.equalities.len() {
                return Err(Error::InvalidModel(
                    "weight count differs from element count".into(),
                ));
            }
            let mut indexed = BTreeSet::new();
            for [index] in data.new.iter().chain(data.old.iter()) {
                let el = Element {
                    sort: SortId(sort),
                    index,
                };
                if model.root(el)? != el || !indexed.insert(index) {
                    return Err(Error::InvalidModel(
                        "carrier indices must partition the representatives".into(),
                    ));
                }
            }
            let roots = model.elements_from_equalities(SortId(sort));
            if indexed != roots.collect() {
                return Err(Error::InvalidModel(
                    "carrier index is missing a representative".into(),
                ));
            }
            for &index in &data.uprooted {
                let el = Element {
                    sort: SortId(sort),
                    index,
                };
                if model.root(el)? == el {
                    return Err(Error::InvalidModel(
                        "an uprooted element is still a representative".into(),
                    ));
                }
            }
        }
        for (id, descriptor) in model.signature.relations() {
            let data = &model.relations[id.0];
            data.new.check(descriptor.arity.len())?;
            data.old.check(descriptor.arity.len())?;
            for tuple in data.tuples() {
                for (&sort, index) in descriptor.arity.iter().zip(tuple) {
                    model.root(Element { sort, index })?;
                }
            }
        }
        Ok(model)
    }

    pub fn signature(&self) -> &Arc<Signature> {
        &self.signature
    }

    pub(super) fn sort_data(&self, sort: SortId) -> Result<&SortData, Error> {
        self.sorts.get(sort.0).ok_or(Error::UnknownSort(sort))
    }

    pub(super) fn relation_data(&self, relation: RelationId) -> Result<&RelationData, Error> {
        self.relations
            .get(relation.0)
            .ok_or(Error::UnknownRelation(relation))
    }

    /// Allocates an element and its membership row.
    /// `parents` lists the enclosing model instances, outermost first.
    pub fn new_element(&mut self, sort: SortId, parents: &[Element]) -> Result<Element, Error> {
        let parents = self.check_tuple(&self.signature.sort(sort)?.parents, parents)?;
        for (i, &parent) in parents.iter().enumerate() {
            self.check_membership(parent, &parents[..i])?;
        }
        let data = &mut self.sorts[sort.0];
        let len = data.equalities.len();
        if len >= (u32::MAX - 1) as usize {
            return Err(Error::ElementLimit);
        }
        let element = Element {
            sort,
            index: len as u32,
        };
        data.equalities.increase_size_to(len + 1);
        data.weights.push(0);
        data.new.insert([element.index]);
        if let Some(relation) = self.signature.membership(sort) {
            let mut tuple = parents;
            tuple.push(element);
            self.insert_row(relation, &tuple);
        }
        Ok(element)
    }

    /// Enumerates all allocated handles, including aliases, in allocation order.
    pub fn handles(&self, sort: SortId) -> Result<impl Iterator<Item = Element> + '_, Error> {
        let count = self.sort_data(sort)?.equalities.len();
        Ok((0..count).map(move |index| Element {
            sort,
            index: index as u32,
        }))
    }

    /// Enumerates current representatives.
    pub fn elements(&self, sort: SortId) -> Result<impl Iterator<Item = Element> + '_, Error> {
        let data = self.sort_data(sort)?;
        Ok(data
            .new
            .iter()
            .chain(data.old.iter())
            .map(move |[index]| Element { sort, index }))
    }

    /// Resolves a handle to its current representative.
    pub fn root(&self, element: Element) -> Result<Element, Error> {
        if element.index as usize >= self.sort_data(element.sort)?.equalities.len() {
            return Err(Error::UnknownElement(element));
        }
        Ok(self.root_unchecked(element))
    }

    /// Merges two classes without rewriting relation rows. Returns whether they differed.
    ///
    /// Both elements must belong to `parents`, listed outermost first, even when
    /// already equal. Top-level sorts take an empty slice.
    pub fn equate(
        &mut self,
        parents: &[Element],
        lhs: Element,
        rhs: Element,
    ) -> Result<bool, Error> {
        let lhs = self.root(lhs)?;
        let rhs = self.root(rhs)?;
        if lhs.sort != rhs.sort {
            return Err(Error::SortMismatch {
                expected: lhs.sort,
                actual: rhs.sort,
            });
        }
        let parents = self.check_tuple(&self.signature.sort(lhs.sort)?.parents, parents)?;
        self.check_membership(lhs, &parents)?;
        self.check_membership(rhs, &parents)?;
        if lhs == rhs {
            return Ok(false);
        }
        let data = &mut self.sorts[lhs.sort.0];
        let (root, child) = if data.weights[lhs.index as usize] >= data.weights[rhs.index as usize]
        {
            (lhs.index, rhs.index)
        } else {
            (rhs.index, lhs.index)
        };
        data.equalities.union_roots_into(child, root);
        data.new.remove([child]);
        data.old.remove([child]);
        data.uprooted.push(child);
        Ok(true)
    }

    /// Iterates stored rows in signature column order, including aliases.
    /// Rows may be repeated.
    pub fn tuples(
        &self,
        relation: RelationId,
    ) -> Result<impl Iterator<Item = Vec<Element>> + '_, Error> {
        let arity = &self.signature.relation(relation)?.arity;
        Ok(self.relations[relation.0].tuples().map(move |tuple| {
            tuple
                .into_iter()
                .zip(arity)
                .map(|(index, &sort)| Element { sort, index })
                .collect()
        }))
    }

    /// Resolves the arguments and checks the relation indices.
    ///
    /// As in compiled models, pending equality rewrites can hide ordinary facts
    /// from this lookup. Membership checks also resolve aliases in stored rows.
    pub fn contains(&self, relation: RelationId, tuple: &[Element]) -> Result<bool, Error> {
        let descriptor = self.signature.relation(relation)?;
        let tuple = self.check_tuple(&descriptor.arity, tuple)?;
        match descriptor.kind {
            RelationKind::Membership(_) => Ok(self.contains_membership(relation, &tuple)),
            RelationKind::Predicate | RelationKind::Function(_) => {
                let tuple: Vec<_> = tuple.iter().map(|el| el.index).collect();
                let data = &self.relations[relation.0];
                Ok(data.new.contains(&tuple) || data.old.contains(&tuple))
            }
        }
    }

    /// Inserts a tuple of current representatives.
    /// Returns whether a row was added. Existing rows are left untouched.
    pub fn insert(&mut self, relation: RelationId, tuple: &[Element]) -> Result<bool, Error> {
        let descriptor = self.signature.relation(relation)?;
        let tuple = self.check_tuple(&descriptor.arity, tuple)?;
        match descriptor.kind {
            RelationKind::Membership(_) => {
                let (element, parents) =
                    tuple.split_last().expect("membership has a member column");
                self.check_membership(*element, parents)?;
            }
            RelationKind::Predicate | RelationKind::Function(_) => {}
        }
        Ok(self.insert_row(relation, &tuple))
    }

    fn insert_row(&mut self, relation: RelationId, tuple: &[Element]) -> bool {
        let data = &mut self.relations[relation.0];
        let row: Vec<_> = tuple.iter().map(|el| el.index).collect();
        if data.old.contains(&row) || data.new.contains(&row) {
            return false;
        }
        data.new.insert(&row);
        for el in tuple {
            let weight = &mut self.sorts[el.sort.0].weights[el.index as usize];
            *weight = weight.saturating_add(data.weight);
        }
        true
    }

    fn check_membership(&self, element: Element, parents: &[Element]) -> Result<(), Error> {
        if let Some(relation) = self.signature.membership(element.sort) {
            let mut tuple = parents.to_vec();
            tuple.push(element);
            if !self.contains_membership(relation, &tuple) {
                return Err(Error::ParentMismatch);
            }
        }
        Ok(())
    }

    fn contains_membership(&self, relation: RelationId, tuple: &[Element]) -> bool {
        self.relations[relation.0].tuples().any(|row| {
            row.iter().zip(tuple).all(|(&index, &el)| {
                self.root_unchecked(Element {
                    sort: el.sort,
                    index,
                }) == el
            })
        })
    }

    fn elements_from_equalities(&self, sort: SortId) -> impl Iterator<Item = u32> + '_ {
        let equalities = &self.sorts[sort.0].equalities;
        (0..equalities.len() as u32).filter(|&index| equalities.root_const(index) == index)
    }

    fn root_unchecked(&self, element: Element) -> Element {
        Element {
            sort: element.sort,
            index: self.sorts[element.sort.0]
                .equalities
                .root_const(element.index),
        }
    }

    fn check_tuple(&self, sorts: &[SortId], tuple: &[Element]) -> Result<Vec<Element>, Error> {
        if tuple.len() != sorts.len() {
            return Err(Error::ArityMismatch {
                expected: sorts.len(),
                actual: tuple.len(),
            });
        }
        tuple
            .iter()
            .zip(sorts)
            .map(|(&element, &sort)| {
                if element.sort != sort {
                    return Err(Error::SortMismatch {
                        expected: sort,
                        actual: element.sort,
                    });
                }
                self.root(element)
            })
            .collect()
    }
}
