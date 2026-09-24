use std::collections::BTreeSet;

use super::Error;

/// A type's position in a signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(pub usize);

/// A relation's position in a signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RelationId(pub usize);

/// How a type was declared.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeKind {
    Plain,
    Model,
    Enum,
    Morphism(TypeId),
}

/// A named Eqlog type with its enclosing model types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Type {
    /// Unique within the signature's type namespace.
    pub name: String,
    pub kind: TypeKind,
    /// Enclosing model types, outermost first.
    pub parents: Vec<TypeId>,
}

/// The kind of function represented by a relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FunctionKind {
    /// A user-declared function or constant.
    Ordinary,
    /// A constructor that returns a value of an enum type.
    Constructor,
    /// The argument is a morphism between instances of this model type.
    MorphismDomain(TypeId),
    /// The result is an instance of the specified model type.
    MorphismCodomain(TypeId),
    /// Applies a morphism to a member, which may belong to a nested model.
    MorphismApplication { morphism: TypeId, member: TypeId },
}

/// The interpretation of a relation's columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelationKind {
    Predicate,
    /// A function, with its arguments followed by its result.
    Function(FunctionKind),
    /// The owning parent chain followed by an element of this type.
    Membership(TypeId),
}

/// A named relation, with enclosing model parameters as leading columns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Relation {
    /// Unique within the signature's relation namespace.
    pub name: String,
    pub kind: RelationKind,
    /// Includes enclosing model parameters and, for functions, the result.
    pub arity: Vec<TypeId>,
    /// Enclosing model parameters form a prefix of `arity`.
    pub parents: Vec<TypeId>,
}

/// A validated, ordered signature without rules or compiler-specific IDs.
///
/// Names identify symbols within each of the type and relation namespaces.
/// Generated signatures qualify names with their enclosing model names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    types: Vec<Type>,
    relations: Vec<Relation>,
    memberships: Vec<Option<RelationId>>,
}

impl Signature {
    /// Validates descriptors and assigns IDs by their positions in the input vectors.
    ///
    /// Names must be nonempty and unique in each namespace. Parent chains must
    /// consist of consistently nested model types. Every dependent type requires
    /// exactly one membership relation with its parent chain followed by the type
    /// itself. Function relations must include a result. Constructors must return
    /// an enum. Morphism functions must have the expected argument and result types.
    ///
    /// Enum constructors and morphism functions may be omitted. A morphism type
    /// has at most one domain function, one codomain function, and one application
    /// for each member type.
    /// Returns [`Error::UnknownType`] or [`Error::InvalidSignature`] for invalid
    /// descriptors.
    pub fn new(types: Vec<Type>, relations: Vec<Relation>) -> Result<Self, Error> {
        let mut signature = Self {
            memberships: vec![None; types.len()],
            types,
            relations,
        };
        let mut names = BTreeSet::new();
        for (id, type_) in signature.types() {
            let name = &type_.name;
            if name.is_empty() || !names.insert(name) {
                return Err(Error::InvalidSignature(format!(
                    "duplicate or empty type name: {name:?}"
                )));
            }
            signature.check_parents(&type_.parents)?;
            if type_.parents.contains(&id) {
                return Err(Error::InvalidSignature(format!(
                    "type {name:?} owns itself"
                )));
            }
            match type_.kind {
                TypeKind::Plain | TypeKind::Model | TypeKind::Enum => {}
                TypeKind::Morphism(model) => {
                    signature.check_model(model)?;
                    if signature.type_(model)?.parents != type_.parents {
                        return Err(Error::InvalidSignature(
                            "morphism and model parents differ".into(),
                        ));
                    }
                }
            }
        }
        let mut names = BTreeSet::new();
        let mut domains = BTreeSet::new();
        let mut codomains = BTreeSet::new();
        let mut applications = BTreeSet::new();
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
            for &type_ in &relation.arity {
                signature.type_(type_)?;
            }
            match relation.kind {
                RelationKind::Predicate => {}
                RelationKind::Function(kind) => {
                    signature.check_function(relation, kind)?;
                    let unique = match kind {
                        FunctionKind::Ordinary | FunctionKind::Constructor => true,
                        FunctionKind::MorphismDomain(_) => {
                            domains.insert(relation.arity[relation.parents.len()])
                        }
                        FunctionKind::MorphismCodomain(_) => {
                            codomains.insert(relation.arity[relation.parents.len()])
                        }
                        FunctionKind::MorphismApplication { morphism, member } => {
                            applications.insert((morphism, member))
                        }
                    };
                    if !unique {
                        return Err(Error::InvalidSignature(
                            "duplicate morphism function role".into(),
                        ));
                    }
                }
                RelationKind::Membership(member) => {
                    let type_ = signature.type_(member)?;
                    let mut expected = type_.parents.clone();
                    expected.push(member);
                    if type_.parents.is_empty()
                        || relation.parents != type_.parents
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
                            "multiple membership relations for a type".into(),
                        ));
                    }
                }
            }
        }
        for (id, type_) in signature.types() {
            if !type_.parents.is_empty() && signature.memberships[id.0].is_none() {
                let name = &type_.name;
                return Err(Error::InvalidSignature(format!(
                    "missing membership relation for {name:?}"
                )));
            }
        }
        Ok(signature)
    }

    /// Enumerates types in ID order.
    pub fn types(&self) -> impl ExactSizeIterator<Item = (TypeId, &Type)> {
        self.types
            .iter()
            .enumerate()
            .map(|(i, type_)| (TypeId(i), type_))
    }

    /// Enumerates relations in ID order.
    pub fn relations(&self) -> impl ExactSizeIterator<Item = (RelationId, &Relation)> {
        self.relations
            .iter()
            .enumerate()
            .map(|(i, relation)| (RelationId(i), relation))
    }

    /// Looks up a descriptor, returning [`Error::UnknownType`] for an invalid ID.
    pub fn type_(&self, id: TypeId) -> Result<&Type, Error> {
        self.types.get(id.0).ok_or(Error::UnknownType(id))
    }

    /// Looks up a descriptor, returning [`Error::UnknownRelation`] for an invalid ID.
    pub fn relation(&self, id: RelationId) -> Result<&Relation, Error> {
        self.relations.get(id.0).ok_or(Error::UnknownRelation(id))
    }

    /// Looks up the exact, case-sensitive type name, including any model qualification.
    pub fn type_named(&self, name: &str) -> Option<TypeId> {
        self.types()
            .find_map(|(id, type_)| (type_.name == name).then_some(id))
    }

    /// Looks up the exact, case-sensitive relation name, including model qualification.
    pub fn relation_named(&self, name: &str) -> Option<RelationId> {
        self.relations()
            .find_map(|(id, relation)| (relation.name == name).then_some(id))
    }

    pub(super) fn membership(&self, type_: TypeId) -> Option<RelationId> {
        self.memberships[type_.0]
    }

    pub(super) fn morphism_domain(&self, morphism: TypeId) -> Result<RelationId, Error> {
        let model = self.morphism_model(morphism)?;
        self.morphism_function(morphism, FunctionKind::MorphismDomain(model))
    }

    pub(super) fn morphism_codomain(&self, morphism: TypeId) -> Result<RelationId, Error> {
        let model = self.morphism_model(morphism)?;
        self.morphism_function(morphism, FunctionKind::MorphismCodomain(model))
    }

    pub(super) fn morphism_application(
        &self,
        morphism: TypeId,
        member: TypeId,
    ) -> Result<RelationId, Error> {
        self.morphism_model(morphism)?;
        self.type_(member)?;
        self.morphism_function(
            morphism,
            FunctionKind::MorphismApplication { morphism, member },
        )
    }

    fn morphism_model(&self, morphism: TypeId) -> Result<TypeId, Error> {
        match self.type_(morphism)?.kind {
            TypeKind::Morphism(model) => Ok(model),
            TypeKind::Plain | TypeKind::Model | TypeKind::Enum => Err(Error::InvalidSignature(
                format!("expected a morphism type: {morphism:?}"),
            )),
        }
    }

    fn morphism_function(&self, morphism: TypeId, kind: FunctionKind) -> Result<RelationId, Error> {
        self.relations()
            .find_map(|(id, relation)| match relation.kind {
                RelationKind::Predicate | RelationKind::Membership(_) => None,
                RelationKind::Function(candidate) => (candidate == kind
                    && relation.arity[relation.parents.len()] == morphism)
                    .then_some(id),
            })
            .ok_or_else(|| {
                Error::InvalidSignature(format!(
                    "missing morphism function {kind:?} for {morphism:?}"
                ))
            })
    }

    fn check_model(&self, id: TypeId) -> Result<(), Error> {
        match self.type_(id)?.kind {
            TypeKind::Model => Ok(()),
            TypeKind::Plain | TypeKind::Enum | TypeKind::Morphism(_) => Err(
                Error::InvalidSignature(format!("expected a model type: {id:?}")),
            ),
        }
    }

    fn check_parents(&self, parents: &[TypeId]) -> Result<(), Error> {
        for (i, &parent) in parents.iter().enumerate() {
            self.check_model(parent)?;
            if self.type_(parent)?.parents != parents[..i] {
                return Err(Error::InvalidSignature("inconsistent parent chain".into()));
            }
        }
        Ok(())
    }

    fn check_function(&self, relation: &Relation, kind: FunctionKind) -> Result<(), Error> {
        let args = &relation.arity[relation.parents.len()..];
        let result = args.last().copied().ok_or_else(|| {
            Error::InvalidSignature("function relation has no result column".into())
        })?;
        match kind {
            FunctionKind::Ordinary => {}
            FunctionKind::Constructor => match self.type_(result)?.kind {
                TypeKind::Enum => {}
                TypeKind::Plain | TypeKind::Model | TypeKind::Morphism(_) => {
                    return Err(Error::InvalidSignature(
                        "constructor result is not an enum".into(),
                    ));
                }
            },
            FunctionKind::MorphismDomain(model) | FunctionKind::MorphismCodomain(model) => {
                self.check_model(model)?;
                if args.len() != 2
                    || result != model
                    || relation.parents != self.type_(model)?.parents
                {
                    return Err(Error::InvalidSignature(
                        "invalid morphism endpoint signature".into(),
                    ));
                }
                let argument_model = match self.type_(args[0])?.kind {
                    TypeKind::Morphism(model) => model,
                    TypeKind::Plain | TypeKind::Model | TypeKind::Enum => {
                        return Err(Error::InvalidSignature(
                            "endpoint argument is not a morphism type".into(),
                        ));
                    }
                };
                if argument_model != model {
                    return Err(Error::InvalidSignature(
                        "endpoint argument is not the model's morphism type".into(),
                    ));
                }
            }
            FunctionKind::MorphismApplication { morphism, member } => {
                let model = match self.type_(morphism)?.kind {
                    TypeKind::Morphism(model) => model,
                    TypeKind::Plain | TypeKind::Model | TypeKind::Enum => {
                        return Err(Error::InvalidSignature(
                            "application requires a morphism type".into(),
                        ));
                    }
                };
                if args != [morphism, member, member]
                    || relation.parents != self.type_(morphism)?.parents
                    || !self.type_(member)?.parents.contains(&model)
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
