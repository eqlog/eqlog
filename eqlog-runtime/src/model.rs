use std::collections::BTreeSet;
use std::ops::Deref;
use std::sync::Arc;

use super::data::{RelationData, RelationIndex, TypeData};
use super::table::Table;
use super::{
    Element, EnumCase, Error, FunctionKind, Relation, RelationId, RelationKind, Signature, TypeId,
    TypeKind,
};

/// A model with a runtime signature.
#[derive(Clone, Debug)]
pub struct Model {
    signature: ModelSignature,
    types: Vec<TypeData>,
    relations: Vec<RelationData>,
    canonical: bool,
}

#[derive(Clone, Debug)]
enum ModelSignature {
    Static(&'static Signature),
    Shared(Arc<Signature>),
}

impl Deref for ModelSignature {
    type Target = Signature;

    fn deref(&self) -> &Signature {
        match self {
            Self::Static(signature) => signature,
            Self::Shared(signature) => signature,
        }
    }
}

impl Model {
    /// Creates an empty model.
    pub fn new(signature: &'static Signature) -> Self {
        Self::with_model_signature(ModelSignature::Static(signature))
    }

    /// Creates an empty model with a shared runtime signature.
    pub fn with_signature(signature: Arc<Signature>) -> Self {
        Self::with_model_signature(ModelSignature::Shared(signature))
    }

    fn with_model_signature(signature: ModelSignature) -> Self {
        Self {
            types: signature.types().map(|_| TypeData::new()).collect(),
            relations: signature
                .relations()
                .map(|(_, rel)| RelationData::new(rel.arity.len()))
                .collect(),
            signature,
            canonical: true,
        }
    }

    /// Assembles stored data without renumbering elements or rewriting rows.
    ///
    /// Checks storage dimensions, allocated handles, and representative sets.
    /// Membership and other theory axioms may remain unsatisfied.
    pub(super) fn from_parts(
        signature: &'static Signature,
        types: Vec<TypeData>,
        relations: Vec<RelationData>,
    ) -> Result<Self, Error> {
        if types.len() != signature.types().len() || relations.len() != signature.relations().len()
        {
            return Err(Error::InvalidModel(
                "storage does not match the signature".into(),
            ));
        }
        let mut model = Self {
            signature: ModelSignature::Static(signature),
            types,
            relations,
            canonical: true,
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
            model.canonical &= data.uprooted.is_empty();
        }
        for (id, descriptor) in model.signature.relations() {
            let data = &model.relations[id.0];
            data.new.check(descriptor.arity.len())?;
            data.old.check(descriptor.arity.len())?;
            let mut seen = BTreeSet::new();
            for tuple in data.tuples() {
                if tuple.len() != descriptor.arity.len() {
                    return Err(Error::ArityMismatch {
                        expected: descriptor.arity.len(),
                        actual: tuple.len(),
                    });
                }
                for (&type_, &index) in descriptor.arity.iter().zip(&tuple) {
                    let element = Element { type_, index };
                    model.canonical &= model.root(element)? == element;
                }
                model.canonical &= seen.insert(tuple);
            }
        }
        Ok(model)
    }

    /// Returns whether equality updates have been applied to all stored facts.
    /// Canonical models have no pending uprooted elements or duplicate tuples,
    /// and every tuple contains only representatives. Rules may still be pending.
    pub fn is_canonical(&self) -> bool {
        self.canonical
    }

    /// Rewrites and deduplicates facts using the current equality representatives.
    ///
    /// Changed old facts become new so a later evaluation can find newly enabled
    /// matches. Unchanged old facts remain old, and existing new facts remain
    /// pending unless already present in old. Repeated calls preserve this work.
    /// Element handles remain valid. This does not run rules or enforce function
    /// axioms, and does not create elements or identify additional ones.
    pub fn canonicalize(&mut self) {
        if self.canonical {
            return;
        }
        let mut relations = Vec::with_capacity(self.relations.len());
        for (relation, descriptor) in self.signature.relations() {
            let data = &self.relations[relation.0];
            let mut old = RelationIndex {
                order: data.old.order.clone(),
                table: Table::new(descriptor.arity.len()),
            };
            let mut new = RelationIndex {
                order: data.new.order.clone(),
                table: Table::new(descriptor.arity.len()),
            };
            let normalize = |row: &[u32]| -> Vec<u32> {
                descriptor
                    .arity
                    .iter()
                    .zip(row)
                    .map(|(&type_, &index)| self.root_unchecked(Element { type_, index }).index)
                    .collect()
            };
            let mut pending = Vec::new();
            for row in data.old.tuples() {
                let canonical = normalize(&row);
                if canonical == row {
                    old.insert(&row);
                } else {
                    pending.push(canonical);
                }
            }
            for row in data.new.tuples() {
                pending.push(normalize(&row));
            }
            for row in pending {
                if !old.contains(&row) {
                    new.insert(&row);
                }
            }
            relations.push(RelationData {
                new,
                old,
                weight: data.weight,
            });
        }
        for data in &mut self.types {
            data.weights.fill(0);
        }
        for ((_, descriptor), data) in self.signature.relations().zip(&relations) {
            for row in data.tuples() {
                for (&type_, index) in descriptor.arity.iter().zip(row) {
                    let weight = &mut self.types[type_.0].weights[index as usize];
                    *weight = weight.saturating_add(data.weight);
                }
            }
        }
        self.relations = relations;
        for data in &mut self.types {
            data.uprooted.clear();
        }
        self.canonical = true;
    }

    /// Returns the model's signature.
    pub fn signature(&self) -> &Signature {
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

    /// Adjoins a new element of type `type_`.
    /// `parents` lists the enclosing model instances, outermost first.
    /// For enum types, use [`Self::new_enum`] instead.
    pub fn new_element(&mut self, type_: TypeId, parents: &[Element]) -> Result<Element, Error> {
        match self.signature.type_(type_)?.kind {
            TypeKind::Enum => return Err(Error::ConstructorRequired(type_)),
            TypeKind::Plain | TypeKind::Model | TypeKind::Morphism(_) => {}
        }
        self.allocate(type_, parents)
    }

    /// Adjoins an enum element with the given constructor and arguments.
    pub fn new_enum(&mut self, value: EnumCase) -> Result<Element, Error> {
        match self.signature.relation(value.constructor)?.kind {
            RelationKind::Function(FunctionKind::Constructor) => {
                self.define(value.constructor, &value.arguments)
            }
            RelationKind::Predicate
            | RelationKind::Membership(_)
            | RelationKind::Function(
                FunctionKind::Ordinary
                | FunctionKind::MorphismDomain(_)
                | FunctionKind::MorphismCodomain(_)
                | FunctionKind::MorphismIdentity(_)
                | FunctionKind::MorphismComposition(_)
                | FunctionKind::MorphismApplication { .. },
            ) => Err(Error::ExpectedConstructor(value.constructor)),
        }
    }

    fn check_capacity(&self, type_: TypeId) -> Result<(), Error> {
        if self.types[type_.0].equalities.len() >= (u32::MAX - 1) as usize {
            return Err(Error::ElementLimit);
        }
        Ok(())
    }

    fn allocate(&mut self, type_: TypeId, parents: &[Element]) -> Result<Element, Error> {
        let parents = self.check_tuple(&self.signature.type_(type_)?.parents, parents)?;
        for (i, &parent) in parents.iter().enumerate() {
            self.check_membership(parent, &parents[..i])?;
        }
        self.check_capacity(type_)?;
        let data = &mut self.types[type_.0];
        let len = data.equalities.len();
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

    /// Returns an iterator over elements of type `type_`.
    /// The iterator yields canonical representatives only.
    pub fn elements(&self, type_: TypeId) -> Result<impl Iterator<Item = Element> + '_, Error> {
        let data = self.type_data(type_)?;
        Ok(data
            .new
            .iter()
            .chain(data.old.iter())
            .map(move |[index]| Element { type_, index }))
    }

    /// Returns the canonical representative of the equivalence class of `element`.
    /// Returns [`Error::UnknownElement`] if its index has not been allocated.
    pub fn root(&self, element: Element) -> Result<Element, Error> {
        if element.index as usize >= self.type_data(element.type_)?.equalities.len() {
            return Err(Error::UnknownElement(element));
        }
        Ok(self.root_unchecked(element))
    }

    /// Returns `true` if `lhs` and `rhs` are in the same equivalence class.
    pub fn are_equal(&self, lhs: Element, rhs: Element) -> Result<bool, Error> {
        let lhs = self.root(lhs)?;
        let rhs = self.root(rhs)?;
        if lhs.type_ != rhs.type_ {
            return Err(Error::TypeMismatch {
                expected: lhs.type_,
                actual: rhs.type_,
            });
        }
        Ok(lhs == rhs)
    }

    /// Enforces the equality `lhs = rhs`.
    ///
    /// Both elements must belong to the supplied enclosing models, outermost first.
    /// Top-level types take an empty `parents` slice.
    /// Returns `true` if the elements were not already equal.
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
        self.canonical = false;
        Ok(true)
    }

    /// Returns an iterator over tuples of elements satisfying `relation`.
    /// For a function, each tuple contains the arguments followed by the result.
    /// Tuples may contain aliases or be repeated until [`Self::canonicalize`].
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

    /// Returns `true` if `relation` holds for `tuple`.
    /// As with compiled predicates, pending equalities can make this lookup miss facts.
    pub fn contains(&self, relation: RelationId, tuple: &[Element]) -> Result<bool, Error> {
        let descriptor = self.signature.relation(relation)?;
        let tuple = self.check_tuple(&descriptor.arity, tuple)?;
        self.check_arguments(descriptor, &tuple)?;
        match descriptor.kind {
            RelationKind::Membership(_) => Ok(self.contains_membership(relation, &tuple)),
            RelationKind::Predicate | RelationKind::Function(_) => {
                let tuple: Vec<_> = tuple.iter().map(|el| el.index).collect();
                let data = &self.relations[relation.0];
                Ok(data.new.contains(&tuple) || data.old.contains(&tuple))
            }
        }
    }

    /// Makes `relation` hold for `tuple`.
    /// Returns `true` if a tuple was added.
    pub fn insert(&mut self, relation: RelationId, tuple: &[Element]) -> Result<bool, Error> {
        let descriptor = self.signature.relation(relation)?;
        let tuple = self.check_tuple(&descriptor.arity, tuple)?;
        self.check_arguments(descriptor, &tuple)?;
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

    /// Evaluates `function(arguments)`.
    /// Returns `None` if no result is stored for these arguments.
    pub fn eval(
        &self,
        function: RelationId,
        arguments: &[Element],
    ) -> Result<Option<Element>, Error> {
        let (descriptor, _) = self.function(function)?;
        let (result_type, domain) = descriptor
            .arity
            .split_last()
            .expect("function has a result");
        let arguments = self.check_tuple(domain, arguments)?;
        self.check_arguments(descriptor, &arguments)?;
        let data = &self.relations[function.0];
        for index in [&data.new, &data.old] {
            let result = index
                .tuples()
                .filter(|row| row.iter().zip(&arguments).all(|(&i, el)| i == el.index))
                .map(|row| *row.last().expect("function has a result"))
                .min()
                .map(|index| Element {
                    type_: *result_type,
                    index,
                });
            if result.is_some() {
                return Ok(result);
            }
        }
        Ok(None)
    }

    /// Enforces that `function(arguments)` is defined, adjoining a new element if necessary.
    /// Functions returning enums must be constructors.
    pub fn define(
        &mut self,
        function: RelationId,
        arguments: &[Element],
    ) -> Result<Element, Error> {
        let (descriptor, kind) = self.function(function)?;
        let (result_type, domain) = descriptor
            .arity
            .split_last()
            .expect("function has a result");
        let result_type = *result_type;
        let outer_len = descriptor.parents.len();
        let result_parents = &self.signature.type_(result_type)?.parents;
        match self.signature.type_(result_type)?.kind {
            TypeKind::Enum => match kind {
                FunctionKind::Constructor => {}
                FunctionKind::Ordinary
                | FunctionKind::MorphismDomain(_)
                | FunctionKind::MorphismCodomain(_)
                | FunctionKind::MorphismIdentity(_)
                | FunctionKind::MorphismComposition(_)
                | FunctionKind::MorphismApplication { .. } => {
                    return Err(Error::ConstructorRequired(result_type));
                }
            },
            TypeKind::Plain | TypeKind::Model | TypeKind::Morphism(_) => {}
        }
        let arguments = self.check_tuple(domain, arguments)?;
        if let Some(result) = self.eval(function, &arguments)? {
            return Ok(result);
        }
        self.check_capacity(result_type)?;
        let parents = match kind {
            FunctionKind::MorphismApplication { morphism, member } => {
                if result_parents.len() == outer_len + 1 {
                    let codomain = self.signature.morphism_codomain(morphism)?;
                    let parent = self.define(codomain, &arguments[..=outer_len])?;
                    let mut parents = arguments[..outer_len].to_vec();
                    parents.push(parent);
                    parents
                } else {
                    let sources =
                        self.morphism_source_parents(descriptor, morphism, member, &arguments)?;
                    self.morphism_image_parents(descriptor, morphism, member, &arguments, sources)?
                }
            }
            FunctionKind::Ordinary
            | FunctionKind::Constructor
            | FunctionKind::MorphismDomain(_)
            | FunctionKind::MorphismCodomain(_)
            | FunctionKind::MorphismIdentity(_)
            | FunctionKind::MorphismComposition(_) => {
                if !result_parents.is_empty() && result_parents != &descriptor.parents {
                    return Err(Error::InvalidSignature(
                        "function result has different enclosing models".into(),
                    ));
                }
                arguments[..result_parents.len()].to_vec()
            }
        };
        let result = self.allocate(result_type, &parents)?;
        let mut tuple = arguments;
        tuple.push(result);
        self.insert_row(function, &tuple);
        Ok(result)
    }

    /// Returns an iterator over ways to destructure an enum element.
    pub fn cases(&self, element: Element) -> Result<impl Iterator<Item = EnumCase> + '_, Error> {
        let element = self.root(element)?;
        match self.signature.type_(element.type_)?.kind {
            TypeKind::Enum => {}
            TypeKind::Plain | TypeKind::Model | TypeKind::Morphism(_) => {
                return Err(Error::ExpectedEnum(element.type_));
            }
        }
        Ok(self
            .signature
            .relations()
            .filter_map(move |(id, relation)| match relation.kind {
                RelationKind::Function(FunctionKind::Constructor) => {
                    (relation.arity.last() == Some(&element.type_)).then_some((id, relation))
                }
                RelationKind::Predicate
                | RelationKind::Membership(_)
                | RelationKind::Function(
                    FunctionKind::Ordinary
                    | FunctionKind::MorphismDomain(_)
                    | FunctionKind::MorphismCodomain(_)
                    | FunctionKind::MorphismIdentity(_)
                    | FunctionKind::MorphismComposition(_)
                    | FunctionKind::MorphismApplication { .. },
                ) => None,
            })
            .flat_map(move |(constructor, relation)| {
                self.relations[constructor.0]
                    .tuples()
                    .filter_map(move |mut row| {
                        if row.pop() != Some(element.index) {
                            return None;
                        }
                        let arguments = row
                            .into_iter()
                            .zip(&relation.arity)
                            .map(|(index, &type_)| Element { type_, index })
                            .collect();
                        Some(EnumCase {
                            constructor,
                            arguments,
                        })
                    })
            }))
    }

    /// Returns the first way to destructure an enum element.
    pub fn case(&self, element: Element) -> Result<EnumCase, Error> {
        self.cases(element)?
            .next()
            .ok_or(Error::NoEnumCase(element))
    }

    fn function(&self, relation: RelationId) -> Result<(&Relation, FunctionKind), Error> {
        let descriptor = self.signature.relation(relation)?;
        match descriptor.kind {
            RelationKind::Function(kind) => Ok((descriptor, kind)),
            RelationKind::Predicate | RelationKind::Membership(_) => {
                Err(Error::ExpectedFunction(relation))
            }
        }
    }

    fn check_arguments(&self, relation: &Relation, tuple: &[Element]) -> Result<(), Error> {
        let membership = match relation.kind {
            RelationKind::Function(FunctionKind::MorphismApplication { morphism, member }) => {
                let sources = self.morphism_source_parents(relation, morphism, member, tuple)?;
                if tuple.len() == relation.arity.len() {
                    self.morphism_image_parents(relation, morphism, member, tuple, sources)?;
                }
                return Ok(());
            }
            RelationKind::Membership(member) => Some(member),
            RelationKind::Predicate
            | RelationKind::Function(
                FunctionKind::Ordinary
                | FunctionKind::Constructor
                | FunctionKind::MorphismDomain(_)
                | FunctionKind::MorphismCodomain(_)
                | FunctionKind::MorphismIdentity(_)
                | FunctionKind::MorphismComposition(_),
            ) => None,
        };
        for &element in tuple {
            let parents = &self.signature.type_(element.type_)?.parents;
            if membership != Some(element.type_)
                && !parents.is_empty()
                && relation.arity.starts_with(parents)
            {
                self.check_membership(element, &tuple[..parents.len()])?;
            }
        }
        Ok(())
    }

    fn morphism_source_parents(
        &self,
        relation: &Relation,
        morphism: TypeId,
        member: TypeId,
        tuple: &[Element],
    ) -> Result<Vec<Vec<Element>>, Error> {
        let outer_len = relation.parents.len();
        let domain = self.signature.morphism_domain(morphism)?;
        let domain_value = self
            .eval(domain, &tuple[..=outer_len])?
            .ok_or(Error::UndefinedFunction(domain))?;
        let mut prefix = tuple[..outer_len].to_vec();
        prefix.push(self.root_unchecked(domain_value));
        let source = tuple[outer_len + 1];
        let membership = self
            .signature
            .membership(member)
            .expect("member has parents");
        let parent_types = &self.signature.type_(member)?.parents;
        if parent_types.len() == prefix.len() {
            let mut row = prefix.clone();
            row.push(source);
            if !self.contains(membership, &row)? {
                return Err(Error::ParentMismatch);
            }
            return Ok(vec![prefix]);
        }
        let parents: Vec<_> = self.relations[membership.0]
            .tuples()
            .filter(|row| row.last() == Some(&source.index))
            .map(|row| {
                row.into_iter()
                    .zip(parent_types)
                    .map(|(index, &type_)| self.root_unchecked(Element { type_, index }))
                    .collect::<Vec<_>>()
            })
            .filter(|parents| parents.starts_with(&prefix))
            .collect();
        if parents.is_empty() {
            return Err(Error::ParentMismatch);
        }
        Ok(parents)
    }

    fn morphism_image_parents(
        &self,
        relation: &Relation,
        morphism: TypeId,
        member: TypeId,
        tuple: &[Element],
        sources: Vec<Vec<Element>>,
    ) -> Result<Vec<Element>, Error> {
        let outer_len = relation.parents.len();
        let codomain = self.signature.morphism_codomain(morphism)?;
        let codomain_value = self
            .eval(codomain, &tuple[..=outer_len])?
            .ok_or(Error::UndefinedFunction(codomain))?;
        let mut prefix = tuple[..outer_len].to_vec();
        prefix.push(self.root_unchecked(codomain_value));
        let mut missing = None;
        for source in sources {
            let mut parents = prefix.clone();
            for &parent in &source[prefix.len()..] {
                let application = self
                    .signature
                    .morphism_application(morphism, parent.type_)?;
                let mut arguments = tuple[..=outer_len].to_vec();
                arguments.push(parent);
                let Some(image) = self.eval(application, &arguments)? else {
                    missing = Some(application);
                    break;
                };
                parents.push(self.root_unchecked(image));
                let membership = self
                    .signature
                    .membership(parent.type_)
                    .expect("nested parent has parents");
                if !self.contains(membership, &parents)? {
                    parents.pop();
                    break;
                }
            }
            if parents.len() == self.signature.type_(member)?.parents.len() {
                if let Some(&result) = tuple.get(outer_len + 2) {
                    let membership = self
                        .signature
                        .membership(member)
                        .expect("member has parents");
                    let mut row = parents.clone();
                    row.push(result);
                    if !self.contains(membership, &row)? {
                        continue;
                    }
                }
                return Ok(parents);
            }
        }
        Err(match missing {
            Some(function) => Error::UndefinedFunction(function),
            None => Error::ParentMismatch,
        })
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
