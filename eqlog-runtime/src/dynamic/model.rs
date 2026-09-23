use std::collections::BTreeSet;
use std::sync::Arc;

use super::data::{RelationData, TypeData};
use super::{Element, Error, RelationId, RelationKind, Signature, TypeId};

/// Elements, equalities, and relation tables for a runtime signature.
#[derive(Clone, Debug)]
pub struct DynamicModel {
    signature: Arc<Signature>,
    types: Vec<TypeData>,
    relations: Vec<RelationData>,
}

impl DynamicModel {
    /// Creates a structure with no elements or facts.
    pub fn new(signature: Arc<Signature>) -> Self {
        Self {
            types: signature.types().map(|_| TypeData::new()).collect(),
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
        types: Vec<TypeData>,
        relations: Vec<RelationData>,
    ) -> Result<Self, Error> {
        if types.len() != signature.types().len() || relations.len() != signature.relations().len()
        {
            return Err(Error::InvalidModel(
                "storage does not match the signature".into(),
            ));
        }
        let model = Self {
            signature,
            types,
            relations,
        };
        for (type_, data) in model.types.iter().enumerate() {
            if data.weights.len() != data.equalities.len() {
                return Err(Error::InvalidModel(
                    "weight count differs from element count".into(),
                ));
            }
            let mut indexed = BTreeSet::new();
            for [index] in data.new.iter().chain(data.old.iter()) {
                let el = Element {
                    type_: TypeId(type_),
                    index,
                };
                if model.root(el)? != el || !indexed.insert(index) {
                    return Err(Error::InvalidModel(
                        "carrier indices must partition the representatives".into(),
                    ));
                }
            }
            let roots = model.elements_from_equalities(TypeId(type_));
            if indexed != roots.collect() {
                return Err(Error::InvalidModel(
                    "carrier index is missing a representative".into(),
                ));
            }
            for &index in &data.uprooted {
                let el = Element {
                    type_: TypeId(type_),
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
                for (&type_, index) in descriptor.arity.iter().zip(tuple) {
                    model.root(Element { type_, index })?;
                }
            }
        }
        Ok(model)
    }

    pub fn signature(&self) -> &Arc<Signature> {
        &self.signature
    }

    pub(super) fn type_data(&self, type_: TypeId) -> Result<&TypeData, Error> {
        self.types.get(type_.0).ok_or(Error::UnknownType(type_))
    }

    pub(super) fn relation_data(&self, relation: RelationId) -> Result<&RelationData, Error> {
        self.relations
            .get(relation.0)
            .ok_or(Error::UnknownRelation(relation))
    }

    /// Allocates an element and its membership row.
    /// `parents` lists the enclosing model instances, outermost first.
    pub fn new_element(&mut self, type_: TypeId, parents: &[Element]) -> Result<Element, Error> {
        let parents = self.check_tuple(&self.signature.type_(type_)?.parents, parents)?;
        for (i, &parent) in parents.iter().enumerate() {
            self.check_membership(parent, &parents[..i])?;
        }
        let data = &mut self.types[type_.0];
        let len = data.equalities.len();
        if len >= (u32::MAX - 1) as usize {
            return Err(Error::ElementLimit);
        }
        let element = Element {
            type_,
            index: len as u32,
        };
        data.equalities.increase_size_to(len + 1);
        data.weights.push(0);
        data.new.insert([element.index]);
        if let Some(relation) = self.signature.membership(type_) {
            let mut tuple = parents;
            tuple.push(element);
            self.insert_row(relation, &tuple);
        }
        Ok(element)
    }

    /// Enumerates current representatives.
    pub fn elements(&self, type_: TypeId) -> Result<impl Iterator<Item = Element> + '_, Error> {
        let data = self.type_data(type_)?;
        Ok(data
            .new
            .iter()
            .chain(data.old.iter())
            .map(move |[index]| Element { type_, index }))
    }

    /// Resolves a handle to its current representative.
    pub fn root(&self, element: Element) -> Result<Element, Error> {
        if element.index as usize >= self.type_data(element.type_)?.equalities.len() {
            return Err(Error::UnknownElement(element));
        }
        Ok(self.root_unchecked(element))
    }

    /// Merges two classes without rewriting relation rows. Returns whether they differed.
    ///
    /// Both elements must belong to `parents`, listed outermost first, even when
    /// already equal. Top-level types take an empty slice.
    pub fn equate(
        &mut self,
        parents: &[Element],
        lhs: Element,
        rhs: Element,
    ) -> Result<bool, Error> {
        let lhs = self.root(lhs)?;
        let rhs = self.root(rhs)?;
        if lhs.type_ != rhs.type_ {
            return Err(Error::TypeMismatch {
                expected: lhs.type_,
                actual: rhs.type_,
            });
        }
        let parents = self.check_tuple(&self.signature.type_(lhs.type_)?.parents, parents)?;
        self.check_membership(lhs, &parents)?;
        self.check_membership(rhs, &parents)?;
        if lhs == rhs {
            return Ok(false);
        }
        let data = &mut self.types[lhs.type_.0];
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
                .map(|(index, &type_)| Element { type_, index })
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
            let weight = &mut self.types[el.type_.0].weights[el.index as usize];
            *weight = weight.saturating_add(data.weight);
        }
        true
    }

    fn check_membership(&self, element: Element, parents: &[Element]) -> Result<(), Error> {
        if let Some(relation) = self.signature.membership(element.type_) {
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
                    type_: el.type_,
                    index,
                }) == el
            })
        })
    }

    fn elements_from_equalities(&self, type_: TypeId) -> impl Iterator<Item = u32> + '_ {
        let equalities = &self.types[type_.0].equalities;
        (0..equalities.len() as u32).filter(|&index| equalities.root_const(index) == index)
    }

    fn root_unchecked(&self, element: Element) -> Element {
        Element {
            type_: element.type_,
            index: self.types[element.type_.0]
                .equalities
                .root_const(element.index),
        }
    }

    fn check_tuple(&self, types: &[TypeId], tuple: &[Element]) -> Result<Vec<Element>, Error> {
        if tuple.len() != types.len() {
            return Err(Error::ArityMismatch {
                expected: types.len(),
                actual: tuple.len(),
            });
        }
        tuple
            .iter()
            .zip(types)
            .map(|(&element, &type_)| {
                if element.type_ != type_ {
                    return Err(Error::TypeMismatch {
                        expected: type_,
                        actual: element.type_,
                    });
                }
                self.root(element)
            })
            .collect()
    }
}
