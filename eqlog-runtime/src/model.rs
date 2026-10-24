use std::collections::BTreeSet;
use std::ops::Deref;
use std::sync::Arc;

use super::data::{RelationData, RelationIndex, TypeData};
use super::table::Table;
use super::validation::{Definition, DefinitionParents, ModelView, Validator};
use super::{
    Element, EnumCase, Error, FunctionKind, RelationId, RelationKind, Signature, TypeId, TypeKind,
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
            for [index] in data.elements.iter() {
                let el = Element {
                    type_: TypeId(type_),
                    index,
                };
                if model.root(el)? != el {
                    return Err(Error::InvalidModel(
                        "carrier index must contain only representatives".into(),
                    ));
                }
                indexed.insert(index);
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
            data.rows.check(descriptor.arity.len())?;
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
            }
        }
        Ok(model)
    }

    /// Returns whether equality updates have been applied to all stored facts.
    /// Canonical models have no pending uprooted elements,
    /// and every tuple contains only representatives. Rules may still be pending.
    pub fn is_canonical(&self) -> bool {
        self.canonical
    }

    /// Rewrites and deduplicates facts using the current equality representatives.
    ///
    /// Element handles remain valid. This does not run rules or enforce function
    /// axioms, and does not create elements or identify additional ones.
    pub fn canonicalize(&mut self) {
        if self.canonical {
            return;
        }
        let mut relations = Vec::with_capacity(self.relations.len());
        for (relation, descriptor) in self.signature.relations() {
            let data = &self.relations[relation.0];
            let mut rows = RelationIndex {
                order: data.rows.order.clone(),
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
            for row in data.rows.tuples() {
                rows.insert(&normalize(&row));
            }
            relations.push(RelationData {
                rows,
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
        let parents = Validator(self).new_element(type_, parents)?;
        Ok(self.allocate(type_, parents))
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

    fn allocate(&mut self, type_: TypeId, parents: Vec<Element>) -> Element {
        let data = &mut self.types[type_.0];
        let len = data.equalities.len();
        let element = Element {
            type_,
            index: len as u32,
        };
        data.equalities.increase_size_to(len + 1);
        data.weights.push(0);
        data.elements.insert([element.index]);
        if let Some(relation) = self.signature.membership(type_) {
            let mut tuple = parents;
            tuple.push(element);
            self.insert_row(relation, &tuple);
        }
        element
    }

    /// Returns an iterator over elements of type `type_`.
    /// The iterator yields canonical representatives only.
    pub fn elements(&self, type_: TypeId) -> Result<impl Iterator<Item = Element> + '_, Error> {
        let data = self.type_data(type_)?;
        Ok(data
            .elements
            .iter()
            .map(move |[index]| Element { type_, index }))
    }

    /// Returns the canonical representative of the equivalence class of `element`.
    /// Returns [`Error::UnknownElement`] if its index has not been allocated.
    pub fn root(&self, element: Element) -> Result<Element, Error> {
        if !self
            .type_data(element.type_)?
            .equalities
            .is_allocated(element.index)
        {
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
        let (lhs, rhs) = Validator(self).equate(parents, lhs, rhs)?;
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
        data.elements.remove([child]);
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
        Validator(self).contains(relation, tuple)
    }

    /// Makes `relation` hold for `tuple`.
    /// Returns `true` if a tuple was added.
    pub fn insert(&mut self, relation: RelationId, tuple: &[Element]) -> Result<bool, Error> {
        let tuple = Validator(self).insert(relation, tuple)?;
        Ok(self.insert_row(relation, &tuple))
    }

    /// Evaluates `function(arguments)`.
    /// Returns `None` if no result is stored for these arguments.
    pub fn eval(
        &self,
        function: RelationId,
        arguments: &[Element],
    ) -> Result<Option<Element>, Error> {
        Validator(self).eval(function, arguments)
    }

    /// Enforces that `function(arguments)` is defined, adjoining a new element if necessary.
    /// Functions returning enums must be constructors.
    pub fn define(
        &mut self,
        function: RelationId,
        arguments: &[Element],
    ) -> Result<Element, Error> {
        let definition = Validator(self).definition(function, arguments)?;
        Ok(self.apply_definition(definition))
    }

    fn apply_definition(&mut self, definition: Definition) -> Element {
        match definition {
            Definition::Existing(element) => element,
            Definition::New {
                function,
                type_,
                mut arguments,
                parents,
            } => {
                let parents = match parents {
                    DefinitionParents::Existing(parents) => parents,
                    DefinitionParents::Codomain {
                        mut outer,
                        definition,
                    } => {
                        outer.push(self.apply_definition(*definition));
                        outer
                    }
                };
                let result = self.allocate(type_, parents);
                arguments.push(result);
                self.insert_row(function, &arguments);
                result
            }
        }
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

    fn insert_row(&mut self, relation: RelationId, tuple: &[Element]) -> bool {
        let data = &mut self.relations[relation.0];
        let row: Vec<_> = tuple.iter().map(|el| el.index).collect();
        if data.rows.contains(&row) {
            return false;
        }
        data.rows.insert(&row);
        for el in tuple {
            let weight = &mut self.types[el.type_.0].weights[el.index as usize];
            *weight = weight.saturating_add(data.weight);
        }
        true
    }

    fn elements_from_equalities(&self, type_: TypeId) -> impl Iterator<Item = u32> + '_ {
        let equalities = &self.types[type_.0].equalities;
        (0..equalities.len() as u32).filter(|&index| {
            equalities.is_allocated(index) && equalities.root_const(index) == index
        })
    }

    fn root_unchecked(&self, element: Element) -> Element {
        Element {
            type_: element.type_,
            index: self.types[element.type_.0]
                .equalities
                .root_const(element.index),
        }
    }
}

impl ModelView for Model {
    fn signature(&self) -> &Signature {
        self.signature()
    }

    fn root(&self, element: Element) -> Result<Element, Error> {
        self.root(element)
    }

    fn element_bound(&self, type_: TypeId) -> usize {
        self.types[type_.0].equalities.len()
    }

    fn membership_rows(&self, relation: RelationId) -> Box<dyn Iterator<Item = Vec<Element>> + '_> {
        Box::new(self.tuples(relation).expect("validated relation"))
    }

    fn contains_raw(&self, relation: RelationId, tuple: &[Element]) -> bool {
        let row: Vec<_> = tuple.iter().map(|element| element.index).collect();
        self.relations[relation.0].rows.contains(&row)
    }

    fn eval_raw(&self, function: RelationId, arguments: &[Element]) -> Option<Element> {
        let result_type = *self
            .signature
            .relation(function)
            .expect("validated function")
            .arity
            .last()
            .expect("function has a result");
        self.relations[function.0]
            .rows
            .tuples()
            .filter(|row| {
                row.iter()
                    .zip(arguments)
                    .all(|(&index, element)| index == element.index)
            })
            .map(|row| *row.last().expect("function has a result"))
            .min()
            .map(|index| Element {
                type_: result_type,
                index,
            })
    }

    fn contains_membership(&self, relation: RelationId, tuple: &[Element]) -> bool {
        self.relations[relation.0].tuples().any(|row| {
            row.iter().zip(tuple).all(|(&index, &element)| {
                self.root_unchecked(Element {
                    type_: element.type_,
                    index,
                }) == element
            })
        })
    }
}
