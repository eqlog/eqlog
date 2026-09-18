use std::mem;
use std::sync::Arc;

use super::table::Table;
use super::{Element, Error, RelationId, RelationKind, Signature, SortId};
use crate::Unification;

#[derive(Clone, Debug)]
struct Carrier {
    equalities: Unification<u32>,
    parents: Vec<Vec<Element>>,
}

/// A mutable, unsaturated structure with canonical relation tuples.
///
/// Equality only identifies explicitly equated elements. In particular, inserting
/// conflicting function results does not derive equality, and enum elements may
/// temporarily lack constructors. Dependent relation constraints may be pending,
/// just as they can be between iterations in a compiled evaluator.
#[derive(Clone, Debug)]
pub struct DynamicModel {
    signature: Arc<Signature>,
    carriers: Vec<Carrier>,
    relations: Vec<Table>,
}

impl DynamicModel {
    pub fn new(signature: Arc<Signature>) -> Self {
        Self {
            carriers: signature
                .sorts()
                .map(|_| Carrier {
                    equalities: Unification::new(),
                    parents: Vec::new(),
                })
                .collect(),
            relations: signature
                .relations()
                .map(|(_, relation)| Table::new(relation.arity.len()))
                .collect(),
            signature,
        }
    }

    pub fn signature(&self) -> &Arc<Signature> {
        &self.signature
    }

    /// Allocates an element and its membership tuple, without adding other facts.
    pub fn new_element(&mut self, sort: SortId, parents: &[Element]) -> Result<Element, Error> {
        let parent_sorts = &self.signature.sort(sort)?.parents;
        let parents = self.check_tuple(parent_sorts, parents)?;
        for (i, &parent) in parents.iter().enumerate() {
            if self.parents(parent)? != parents[..i] {
                return Err(Error::ParentMismatch);
            }
        }
        let carrier = &mut self.carriers[sort.0];
        let len = carrier.equalities.len();
        if len >= (u32::MAX - 1) as usize {
            return Err(Error::ElementLimit);
        }
        let element = Element {
            sort,
            index: len as u32,
        };
        carrier.equalities.increase_size_to(len + 1);
        carrier.parents.push(parents.clone());
        if let Some(relation) = self.signature.membership(sort) {
            let mut tuple = parents;
            tuple.push(element);
            self.relations[relation.0].insert(&tuple.iter().map(|el| el.index).collect::<Vec<_>>());
        }
        Ok(element)
    }

    /// Includes aliases, so callers can preserve handles across conversions.
    pub fn handles(&self, sort: SortId) -> Result<impl Iterator<Item = Element> + '_, Error> {
        self.signature.sort(sort)?;
        Ok(
            (0..self.carriers[sort.0].equalities.len()).map(move |index| Element {
                sort,
                index: index as u32,
            }),
        )
    }

    /// Enumerates one representative of each equality class.
    pub fn elements(&self, sort: SortId) -> Result<impl Iterator<Item = Element> + '_, Error> {
        Ok(self
            .handles(sort)?
            .filter(|&element| self.root_unchecked(element) == element))
    }

    pub fn root(&self, element: Element) -> Result<Element, Error> {
        self.signature.sort(element.sort)?;
        if element.index as usize >= self.carriers[element.sort.0].equalities.len() {
            return Err(Error::UnknownElement(element));
        }
        Ok(self.root_unchecked(element))
    }

    pub fn parents(&self, element: Element) -> Result<Vec<Element>, Error> {
        let element = self.root(element)?;
        Ok(
            self.carriers[element.sort.0].parents[element.index as usize]
                .iter()
                .map(|&parent| self.root_unchecked(parent))
                .collect(),
        )
    }

    /// Returns whether the two equality classes were distinct.
    pub fn equate(&mut self, lhs: Element, rhs: Element) -> Result<bool, Error> {
        let lhs = self.root(lhs)?;
        let rhs = self.root(rhs)?;
        if lhs.sort != rhs.sort {
            return Err(Error::SortMismatch {
                expected: lhs.sort,
                actual: rhs.sort,
            });
        }
        if lhs == rhs {
            return Ok(false);
        }
        if self.parents(lhs)? != self.parents(rhs)? {
            return Err(Error::ParentMismatch);
        }
        let (root, child) = if lhs.index < rhs.index {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        self.carriers[root.sort.0]
            .equalities
            .union_roots_into(child.index, root.index);
        // Eager normalization keeps readers independent of an evaluator's schedule.
        for i in 0..self.relations.len() {
            let arity = &self
                .signature
                .relation(RelationId(i))
                .expect("stored relation")
                .arity;
            let tuples = mem::replace(&mut self.relations[i], Table::new(arity.len()));
            for tuple in tuples.iter() {
                let tuple: Vec<_> = tuple
                    .into_iter()
                    .zip(arity)
                    .map(|(index, &sort)| self.root_unchecked(Element { sort, index }).index)
                    .collect();
                self.relations[i].insert(&tuple);
            }
        }
        Ok(true)
    }

    pub fn tuples(
        &self,
        relation: RelationId,
    ) -> Result<impl Iterator<Item = Vec<Element>> + '_, Error> {
        let arity = &self.signature.relation(relation)?.arity;
        Ok(self.relations[relation.0].iter().map(move |tuple| {
            tuple
                .into_iter()
                .zip(arity)
                .map(|(index, &sort)| Element { sort, index })
                .collect()
        }))
    }

    pub fn contains(&self, relation: RelationId, tuple: &[Element]) -> Result<bool, Error> {
        let tuple = self.check_tuple(&self.signature.relation(relation)?.arity, tuple)?;
        Ok(self.relations[relation.0]
            .contains(&tuple.iter().map(|el| el.index).collect::<Vec<_>>()))
    }

    /// Adds a well-sorted tuple, without checking or executing theory rules.
    /// Membership cannot assign an element to a second parent chain.
    pub fn insert(&mut self, relation: RelationId, tuple: &[Element]) -> Result<bool, Error> {
        let descriptor = self.signature.relation(relation)?;
        let tuple = self.check_tuple(&descriptor.arity, tuple)?;
        match descriptor.kind {
            RelationKind::Predicate | RelationKind::Function(_) => {}
            RelationKind::Membership(_) => {
                let (element, parents) = tuple
                    .split_last()
                    .expect("membership has an element column");
                if self.parents(*element)? != parents {
                    return Err(Error::ParentMismatch);
                }
            }
        }
        Ok(self.relations[relation.0].insert(&tuple.iter().map(|el| el.index).collect::<Vec<_>>()))
    }

    fn root_unchecked(&self, element: Element) -> Element {
        Element {
            sort: element.sort,
            index: self.carriers[element.sort.0]
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
