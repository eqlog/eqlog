use std::collections::BTreeSet;

use super::Error;

/// A sort's position in a signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SortId(pub usize);

/// A relation's position in a signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RelationId(pub usize);

/// The declaration that supplies a carrier; this does not enforce its axioms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SortKind {
    Plain,
    Model,
    Enum,
    Morphism(SortId),
}

/// A named carrier with its enclosing model sorts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sort {
    /// Unique within the signature's sort namespace.
    pub name: String,
    pub kind: SortKind,
    /// Enclosing model sorts, outermost first.
    pub parents: Vec<SortId>,
}

/// Semantic roles retained when functions are represented by graph relations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FunctionKind {
    /// A user-declared function or constant.
    Ordinary,
    /// An enum constructor whose last graph column has the enum sort.
    Constructor,
    /// The argument is a morphism between instances of this model sort.
    MorphismDomain(SortId),
    /// The result is an instance of the specified model sort.
    MorphismCodomain(SortId),
    /// Transport of a member, possibly nested, along this morphism sort.
    MorphismApplication { morphism: SortId, member: SortId },
}

/// The interpretation of a relation's columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelationKind {
    Predicate,
    /// Function graphs store the result in the last column.
    Function(FunctionKind),
    /// The owning parent chain followed by an element of this sort.
    Membership(SortId),
}

/// A named relation, with enclosing model parameters as leading columns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Relation {
    /// Unique within the signature's relation namespace.
    pub name: String,
    pub kind: RelationKind,
    /// Includes enclosing model parameters and, for functions, the result.
    pub arity: Vec<SortId>,
    /// Enclosing model parameters form a prefix of `arity`.
    pub parents: Vec<SortId>,
}

/// A validated, ordered signature without rules or compiler-specific IDs.
///
/// Names identify symbols within each of the sort and relation namespaces.
/// Generated signatures qualify names with their enclosing model names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    sorts: Vec<Sort>,
    relations: Vec<Relation>,
    memberships: Vec<Option<RelationId>>,
}

impl Signature {
    /// Validates descriptors and assigns IDs by their positions in the input vectors.
    ///
    /// Names must be nonempty and unique in each namespace. Parent chains must
    /// consist of consistently nested model sorts. Every dependent sort requires
    /// exactly one membership relation with its parent chain followed by the sort
    /// itself. Function graphs need a result column; constructor and morphism
    /// roles impose additional shape constraints.
    ///
    /// A failed sort lookup returns [`Error::UnknownSort`]; invalid descriptor
    /// shapes return [`Error::InvalidSignature`]. This validates storage shape,
    /// not completeness of an Eqlog theory.
    pub fn new(sorts: Vec<Sort>, relations: Vec<Relation>) -> Result<Self, Error> {
        let mut signature = Self {
            memberships: vec![None; sorts.len()],
            sorts,
            relations,
        };
        let mut names = BTreeSet::new();
        for (id, sort) in signature.sorts() {
            let name = &sort.name;
            if name.is_empty() || !names.insert(name) {
                return Err(Error::InvalidSignature(format!(
                    "duplicate or empty sort name: {name:?}"
                )));
            }
            signature.check_parents(&sort.parents)?;
            if sort.parents.contains(&id) {
                return Err(Error::InvalidSignature(format!(
                    "sort {name:?} owns itself"
                )));
            }
            match sort.kind {
                SortKind::Plain | SortKind::Model | SortKind::Enum => {}
                SortKind::Morphism(model) => {
                    signature.check_model(model)?;
                    if signature.sort(model)?.parents != sort.parents {
                        return Err(Error::InvalidSignature(
                            "morphism and model parents differ".into(),
                        ));
                    }
                }
            }
        }
        let mut names = BTreeSet::new();
        for (index, relation) in signature.relations.iter().enumerate() {
            let name = &relation.name;
            if name.is_empty() || !names.insert(name) {
                return Err(Error::InvalidSignature(format!(
                    "duplicate or empty relation name: {name:?}"
                )));
            }
            signature.check_parents(&relation.parents)?;
            if !relation.arity.starts_with(&relation.parents) {
                return Err(Error::InvalidSignature(
                    "relation parameters are not an arity prefix".into(),
                ));
            }
            for &sort in &relation.arity {
                signature.sort(sort)?;
            }
            match relation.kind {
                RelationKind::Predicate => {}
                RelationKind::Function(kind) => signature.check_function(relation, kind)?,
                RelationKind::Membership(member) => {
                    let sort = signature.sort(member)?;
                    let mut expected = sort.parents.clone();
                    expected.push(member);
                    if sort.parents.is_empty()
                        || relation.parents != sort.parents
                        || relation.arity != expected
                    {
                        return Err(Error::InvalidSignature(
                            "invalid membership relation".into(),
                        ));
                    }
                    if signature.memberships[member.0]
                        .replace(RelationId(index))
                        .is_some()
                    {
                        return Err(Error::InvalidSignature(
                            "multiple membership relations for a sort".into(),
                        ));
                    }
                }
            }
        }
        for (id, sort) in signature.sorts() {
            if !sort.parents.is_empty() && signature.memberships[id.0].is_none() {
                let name = &sort.name;
                return Err(Error::InvalidSignature(format!(
                    "missing membership relation for {name:?}"
                )));
            }
        }
        Ok(signature)
    }

    /// Enumerates sorts in ID order.
    pub fn sorts(&self) -> impl ExactSizeIterator<Item = (SortId, &Sort)> {
        self.sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| (SortId(i), sort))
    }

    /// Enumerates relations in ID order.
    pub fn relations(&self) -> impl ExactSizeIterator<Item = (RelationId, &Relation)> {
        self.relations
            .iter()
            .enumerate()
            .map(|(i, relation)| (RelationId(i), relation))
    }

    /// Looks up a descriptor, returning [`Error::UnknownSort`] for an invalid ID.
    pub fn sort(&self, id: SortId) -> Result<&Sort, Error> {
        self.sorts.get(id.0).ok_or(Error::UnknownSort(id))
    }

    /// Looks up a descriptor, returning [`Error::UnknownRelation`] for an invalid ID.
    pub fn relation(&self, id: RelationId) -> Result<&Relation, Error> {
        self.relations.get(id.0).ok_or(Error::UnknownRelation(id))
    }

    /// Looks up the exact, case-sensitive sort name, including any model qualification.
    pub fn sort_named(&self, name: &str) -> Option<SortId> {
        self.sorts()
            .find_map(|(id, sort)| (sort.name == name).then_some(id))
    }

    /// Looks up the exact, case-sensitive relation name, including model qualification.
    pub fn relation_named(&self, name: &str) -> Option<RelationId> {
        self.relations()
            .find_map(|(id, relation)| (relation.name == name).then_some(id))
    }

    pub(super) fn membership(&self, sort: SortId) -> Option<RelationId> {
        self.memberships[sort.0]
    }

    fn check_model(&self, id: SortId) -> Result<(), Error> {
        match self.sort(id)?.kind {
            SortKind::Model => Ok(()),
            SortKind::Plain | SortKind::Enum | SortKind::Morphism(_) => Err(
                Error::InvalidSignature(format!("expected a model sort: {id:?}")),
            ),
        }
    }

    fn check_parents(&self, parents: &[SortId]) -> Result<(), Error> {
        for (i, &parent) in parents.iter().enumerate() {
            self.check_model(parent)?;
            if self.sort(parent)?.parents != parents[..i] {
                return Err(Error::InvalidSignature("inconsistent parent chain".into()));
            }
        }
        Ok(())
    }

    fn check_function(&self, relation: &Relation, kind: FunctionKind) -> Result<(), Error> {
        let args = &relation.arity[relation.parents.len()..];
        let result = args
            .last()
            .copied()
            .ok_or_else(|| Error::InvalidSignature("function graph has no result column".into()))?;
        match kind {
            FunctionKind::Ordinary => {}
            FunctionKind::Constructor => match self.sort(result)?.kind {
                SortKind::Enum => {}
                SortKind::Plain | SortKind::Model | SortKind::Morphism(_) => {
                    return Err(Error::InvalidSignature(
                        "constructor result is not an enum".into(),
                    ));
                }
            },
            FunctionKind::MorphismDomain(model) | FunctionKind::MorphismCodomain(model) => {
                self.check_model(model)?;
                if args.len() != 2
                    || result != model
                    || relation.parents != self.sort(model)?.parents
                {
                    return Err(Error::InvalidSignature(
                        "invalid morphism endpoint signature".into(),
                    ));
                }
                let argument_model = match self.sort(args[0])?.kind {
                    SortKind::Morphism(model) => model,
                    SortKind::Plain | SortKind::Model | SortKind::Enum => {
                        return Err(Error::InvalidSignature(
                            "endpoint argument is not a morphism sort".into(),
                        ));
                    }
                };
                if argument_model != model {
                    return Err(Error::InvalidSignature(
                        "endpoint argument is not the model's morphism sort".into(),
                    ));
                }
            }
            FunctionKind::MorphismApplication { morphism, member } => {
                let model = match self.sort(morphism)?.kind {
                    SortKind::Morphism(model) => model,
                    SortKind::Plain | SortKind::Model | SortKind::Enum => {
                        return Err(Error::InvalidSignature(
                            "application requires a morphism sort".into(),
                        ));
                    }
                };
                if args != [morphism, member, member]
                    || relation.parents != self.sort(morphism)?.parents
                    || !self.sort(member)?.parents.contains(&model)
                {
                    return Err(Error::InvalidSignature(
                        "invalid morphism application signature".into(),
                    ));
                }
            }
        }
        Ok(())
    }
}
