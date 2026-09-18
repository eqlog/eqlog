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
/// Mutations check carrier sorts, arities, and unique parent chains. Functionality,
/// dependent relation constraints, enum coverage, and morphism preservation may
/// remain unsatisfied. No operation runs rules; errors leave the structure unchanged.
/// Element handles remain valid after equality merges, but representatives may change.
#[derive(Clone, Debug)]
pub struct DynamicModel {
    signature: Arc<Signature>,
    carriers: Vec<Carrier>,
    relations: Vec<Table>,
}

impl DynamicModel {
    /// Creates empty carriers and relations over a shared, validated signature.
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

    /// Returns the immutable signature, which can be shared with other structures.
    pub fn signature(&self) -> &Arc<Signature> {
        &self.signature
    }

    /// Allocates an element and its membership tuple, without adding other facts.
    ///
    /// `parents` must instantiate the sort's complete outermost-first parent chain;
    /// aliases are accepted. Returns an error for invalid sorts or handles, wrong
    /// argument sorts or counts, inconsistent ownership, or exhausted element IDs.
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

    /// Enumerates every allocated handle, including aliases, in allocation order.
    /// Returns [`Error::UnknownSort`] for an invalid sort ID.
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
    /// Returns [`Error::UnknownSort`] for an invalid sort ID.
    pub fn elements(&self, sort: SortId) -> Result<impl Iterator<Item = Element> + '_, Error> {
        Ok(self
            .handles(sort)?
            .filter(|&element| self.root_unchecked(element) == element))
    }

    /// Resolves a handle to its current equality representative.
    /// Returns [`Error::UnknownSort`] or [`Error::UnknownElement`] for invalid handles.
    pub fn root(&self, element: Element) -> Result<Element, Error> {
        self.signature.sort(element.sort)?;
        if element.index as usize >= self.carriers[element.sort.0].equalities.len() {
            return Err(Error::UnknownElement(element));
        }
        Ok(self.root_unchecked(element))
    }

    /// Returns the owning parent chain as current representatives, outermost first.
    /// Top-level elements have no parents. Invalid handles return the same errors
    /// as [`Self::root`].
    pub fn parents(&self, element: Element) -> Result<Vec<Element>, Error> {
        let element = self.root(element)?;
        Ok(
            self.carriers[element.sort.0].parents[element.index as usize]
                .iter()
                .map(|&parent| self.root_unchecked(parent))
                .collect(),
        )
    }

    /// Merges two equality classes and canonicalizes relation tuples immediately.
    ///
    /// Returns `true` if the classes were distinct. Both elements must have the
    /// same sort and equal parent chains; otherwise returns an invalid-handle,
    /// [`Error::SortMismatch`], or [`Error::ParentMismatch`] error. Function conflicts
    /// created by the merge do not derive further equalities.
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

    /// Enumerates distinct tuples using current representatives in schema column order.
    /// A true nullary predicate has one empty tuple; a false one has none.
    /// Returns [`Error::UnknownRelation`] for an invalid relation ID.
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

    /// Tests tuple membership modulo explicit equality.
    /// Returns an error for an invalid relation, arity, carrier sort, or element handle.
    pub fn contains(&self, relation: RelationId, tuple: &[Element]) -> Result<bool, Error> {
        let tuple = self.check_tuple(&self.signature.relation(relation)?.arity, tuple)?;
        Ok(self.relations[relation.0]
            .contains(&tuple.iter().map(|el| el.index).collect::<Vec<_>>()))
    }

    /// Inserts a tuple modulo explicit equality; returns whether it was new.
    ///
    /// Returns an error for an invalid relation, arity, carrier sort, or element
    /// handle. Membership rows must agree with the element's parent chain.
    /// Function graphs may retain multiple results for the same arguments.
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
