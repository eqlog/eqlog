use super::{
    Element, Error, FunctionKind, Relation, RelationId, RelationKind, Signature, TypeId, TypeKind,
};

/// Read-only access keeps validation independent of a model's storage layout.
/// Raw lookups retain pending aliases so edit results agree with exported data.
pub trait ModelView {
    fn signature(&self) -> &Signature;
    fn root(&self, element: Element) -> Result<Element, Error>;
    fn element_bound(&self, type_: TypeId) -> usize;
    fn membership_rows(&self, relation: RelationId) -> Box<dyn Iterator<Item = Vec<Element>> + '_>;
    fn contains_raw(&self, relation: RelationId, tuple: &[Element]) -> bool;
    fn eval_raw(&self, function: RelationId, arguments: &[Element]) -> Option<Element>;
    fn contains_membership(&self, relation: RelationId, tuple: &[Element]) -> bool;
}

pub struct Validator<'a>(pub &'a dyn ModelView);

// Implicit codomain creation must wait until every fallible check has succeeded.
pub(crate) enum Definition {
    Existing(Element),
    New {
        function: RelationId,
        type_: TypeId,
        arguments: Vec<Element>,
        parents: DefinitionParents,
    },
}

pub(crate) enum DefinitionParents {
    Existing(Vec<Element>),
    Codomain {
        outer: Vec<Element>,
        definition: Box<Definition>,
    },
}

impl Validator<'_> {
    fn root(&self, element: Element) -> Result<Element, Error> {
        self.0.root(element)
    }

    fn check_capacity(&self, type_: TypeId) -> Result<(), Error> {
        if self.0.element_bound(type_) >= (u32::MAX - 1) as usize {
            return Err(Error::ElementLimit);
        }
        Ok(())
    }

    pub fn new_element(&self, type_: TypeId, parents: &[Element]) -> Result<Vec<Element>, Error> {
        match self.0.signature().type_(type_)?.kind {
            TypeKind::Enum => return Err(Error::ConstructorRequired(type_)),
            TypeKind::Plain | TypeKind::Model | TypeKind::Morphism(_) => {}
        }
        self.allocation(type_, parents)
    }

    fn allocation(&self, type_: TypeId, parents: &[Element]) -> Result<Vec<Element>, Error> {
        let parents = self.check_tuple(&self.0.signature().type_(type_)?.parents, parents)?;
        for (i, &parent) in parents.iter().enumerate() {
            self.check_membership(parent, &parents[..i])?;
        }
        self.check_capacity(type_)?;
        Ok(parents)
    }

    pub fn equate(
        &self,
        parents: &[Element],
        lhs: Element,
        rhs: Element,
    ) -> Result<(Element, Element), Error> {
        let lhs = self.root(lhs)?;
        let rhs = self.root(rhs)?;
        if lhs.type_ != rhs.type_ {
            return Err(Error::TypeMismatch {
                expected: lhs.type_,
                actual: rhs.type_,
            });
        }
        let parents = self.check_tuple(&self.0.signature().type_(lhs.type_)?.parents, parents)?;
        self.check_membership(lhs, &parents)?;
        self.check_membership(rhs, &parents)?;
        Ok((lhs, rhs))
    }

    pub fn insert(&self, relation: RelationId, tuple: &[Element]) -> Result<Vec<Element>, Error> {
        let descriptor = self.0.signature().relation(relation)?;
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
        Ok(tuple)
    }

    pub fn contains(&self, relation: RelationId, tuple: &[Element]) -> Result<bool, Error> {
        let descriptor = self.0.signature().relation(relation)?;
        let tuple = self.check_tuple(&descriptor.arity, tuple)?;
        self.check_arguments(descriptor, &tuple)?;
        Ok(match descriptor.kind {
            RelationKind::Membership(_) => self.contains_membership(relation, &tuple),
            RelationKind::Predicate | RelationKind::Function(_) => {
                self.0.contains_raw(relation, &tuple)
            }
        })
    }

    pub fn eval(
        &self,
        function: RelationId,
        arguments: &[Element],
    ) -> Result<Option<Element>, Error> {
        let (descriptor, _) = self.function(function)?;
        let (_, domain) = descriptor
            .arity
            .split_last()
            .expect("function has a result");
        let arguments = self.check_tuple(domain, arguments)?;
        self.check_arguments(descriptor, &arguments)?;
        Ok(self.0.eval_raw(function, &arguments))
    }

    pub fn check_define(&self, function: RelationId, arguments: &[Element]) -> Result<(), Error> {
        self.definition(function, arguments).map(|_| ())
    }

    pub(crate) fn definition(
        &self,
        function: RelationId,
        arguments: &[Element],
    ) -> Result<Definition, Error> {
        let (descriptor, kind) = self.function(function)?;
        let (result_type, domain) = descriptor
            .arity
            .split_last()
            .expect("function has a result");
        let result_type = *result_type;
        let outer_len = descriptor.parents.len();
        let result_parents = &self.0.signature().type_(result_type)?.parents;
        match self.0.signature().type_(result_type)?.kind {
            TypeKind::Enum => match kind {
                FunctionKind::Constructor => {}
                FunctionKind::Ordinary
                | FunctionKind::MorphismDomain(_)
                | FunctionKind::MorphismCodomain(_)
                | FunctionKind::MorphismIdentity(_)
                | FunctionKind::MorphismComposition(_)
                | FunctionKind::MorphismApplication { .. } => {
                    return Err(Error::ConstructorRequired(result_type))
                }
            },
            TypeKind::Plain | TypeKind::Model | TypeKind::Morphism(_) => {}
        }
        let arguments = self.check_tuple(domain, arguments)?;
        if let Some(result) = self.eval(function, &arguments)? {
            return Ok(Definition::Existing(result));
        }
        self.check_capacity(result_type)?;
        let parents = match kind {
            FunctionKind::MorphismApplication { morphism, member } => {
                if result_parents.len() == outer_len + 1 {
                    let codomain = self.0.signature().morphism_codomain(morphism)?;
                    let definition = self.definition(codomain, &arguments[..=outer_len])?;
                    match definition {
                        Definition::Existing(parent) => {
                            let mut parents = arguments[..outer_len].to_vec();
                            parents.push(parent);
                            DefinitionParents::Existing(self.allocation(result_type, &parents)?)
                        }
                        Definition::New { .. } => DefinitionParents::Codomain {
                            outer: arguments[..outer_len].to_vec(),
                            definition: Box::new(definition),
                        },
                    }
                } else {
                    let sources =
                        self.morphism_source_parents(descriptor, morphism, member, &arguments)?;
                    let parents = self.morphism_image_parents(
                        descriptor, morphism, member, &arguments, sources,
                    )?;
                    DefinitionParents::Existing(self.allocation(result_type, &parents)?)
                }
            }
            FunctionKind::Ordinary
            | FunctionKind::Constructor
            | FunctionKind::MorphismDomain(_)
            | FunctionKind::MorphismCodomain(_)
            | FunctionKind::MorphismIdentity(_)
            | FunctionKind::MorphismComposition(_) => {
                let parents = if let Some(columns) = self
                    .0
                    .signature()
                    .argument_parents(&descriptor.name, domain.len())
                {
                    columns.iter().map(|&column| arguments[column]).collect()
                } else if !result_parents.is_empty() && result_parents != &descriptor.parents {
                    return Err(Error::InvalidSignature(
                        "function result has different enclosing models".into(),
                    ));
                } else {
                    arguments[..result_parents.len()].to_vec()
                };
                DefinitionParents::Existing(self.allocation(result_type, &parents)?)
            }
        };
        Ok(Definition::New {
            function,
            type_: result_type,
            arguments,
            parents,
        })
    }

    fn function(&self, relation: RelationId) -> Result<(&Relation, FunctionKind), Error> {
        let descriptor = self.0.signature().relation(relation)?;
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
        for (column, &element) in tuple.iter().enumerate() {
            let parents = &self.0.signature().type_(element.type_)?.parents;
            if let Some(columns) = self.0.signature().argument_parents(&relation.name, column) {
                let owners: Vec<_> = columns.iter().map(|&column| tuple[column]).collect();
                self.check_membership(element, &owners)?;
                continue;
            }
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
        let domain = self.0.signature().morphism_domain(morphism)?;
        let domain_value = self
            .eval(domain, &tuple[..=outer_len])?
            .ok_or(Error::UndefinedFunction(domain))?;
        let mut prefix = tuple[..outer_len].to_vec();
        prefix.push(self.root(domain_value)?);
        let source = tuple[outer_len + 1];
        let membership = self
            .0
            .signature()
            .membership(member)
            .expect("member has parents");
        let parent_types = &self.0.signature().type_(member)?.parents;
        if parent_types.len() == prefix.len() {
            let mut row = prefix.clone();
            row.push(source);
            if !self.contains(membership, &row)? {
                return Err(Error::ParentMismatch);
            }
            return Ok(vec![prefix]);
        }
        let parents: Vec<_> = self
            .0
            .membership_rows(membership)
            .filter(|row| row.last() == Some(&source))
            .map(|row| {
                row.into_iter()
                    .take(parent_types.len())
                    .map(|element| self.root(element).expect("stored handles are allocated"))
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
        let codomain = self.0.signature().morphism_codomain(morphism)?;
        let codomain_value = self
            .eval(codomain, &tuple[..=outer_len])?
            .ok_or(Error::UndefinedFunction(codomain))?;
        let mut prefix = tuple[..outer_len].to_vec();
        prefix.push(self.root(codomain_value)?);
        let mut missing = None;
        for source in sources {
            let mut parents = prefix.clone();
            for &parent in &source[prefix.len()..] {
                let application = self
                    .0
                    .signature()
                    .morphism_application(morphism, parent.type_)?;
                let mut arguments = tuple[..=outer_len].to_vec();
                arguments.push(parent);
                let Some(image) = self.eval(application, &arguments)? else {
                    missing = Some(application);
                    break;
                };
                parents.push(self.root(image)?);
                let membership = self
                    .0
                    .signature()
                    .membership(parent.type_)
                    .expect("nested parent has parents");
                if !self.contains(membership, &parents)? {
                    parents.pop();
                    break;
                }
            }
            if parents.len() == self.0.signature().type_(member)?.parents.len() {
                if let Some(&result) = tuple.get(outer_len + 2) {
                    let membership = self
                        .0
                        .signature()
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

    fn check_membership(&self, element: Element, parents: &[Element]) -> Result<(), Error> {
        if let Some(relation) = self.0.signature().membership(element.type_) {
            let mut tuple = parents.to_vec();
            tuple.push(element);
            if !self.contains_membership(relation, &tuple) {
                return Err(Error::ParentMismatch);
            }
        }
        Ok(())
    }

    fn contains_membership(&self, relation: RelationId, tuple: &[Element]) -> bool {
        self.0.contains_membership(relation, tuple)
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

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::{ModelView, Validator};
    use crate::{
        Element, Error, FunctionKind, Model, Relation, RelationId, RelationKind, Signature, Type,
        TypeId, TypeKind,
    };

    struct AtCapacity<'a> {
        model: &'a Model,
        full: TypeId,
    }

    impl ModelView for AtCapacity<'_> {
        fn signature(&self) -> &Signature {
            self.model.signature()
        }

        fn root(&self, element: Element) -> Result<Element, Error> {
            self.model.root(element)
        }

        fn element_bound(&self, type_: TypeId) -> usize {
            if type_ == self.full {
                (u32::MAX - 1) as usize
            } else {
                self.model.element_bound(type_)
            }
        }

        fn membership_rows(
            &self,
            relation: RelationId,
        ) -> Box<dyn Iterator<Item = Vec<Element>> + '_> {
            self.model.membership_rows(relation)
        }

        fn contains_raw(&self, relation: RelationId, tuple: &[Element]) -> bool {
            self.model.contains_raw(relation, tuple)
        }

        fn eval_raw(&self, function: RelationId, arguments: &[Element]) -> Option<Element> {
            self.model.eval_raw(function, arguments)
        }

        fn contains_membership(&self, relation: RelationId, tuple: &[Element]) -> bool {
            self.model.contains_membership(relation, tuple)
        }
    }

    #[test]
    fn definition_checks_both_allocations_before_creating_a_codomain() {
        let owner = TypeId(0);
        let morphism = TypeId(1);
        let member = TypeId(2);
        let domain = RelationId(1);
        let codomain = RelationId(2);
        let application = RelationId(3);
        let signature = Signature::new(
            vec![
                Type {
                    name: "M".into(),
                    kind: TypeKind::Model,
                    parents: vec![],
                },
                Type {
                    name: "Mor".into(),
                    kind: TypeKind::Morphism(owner),
                    parents: vec![],
                },
                Type {
                    name: "M::El".into(),
                    kind: TypeKind::Plain,
                    parents: vec![owner],
                },
            ],
            vec![
                Relation {
                    name: "member".into(),
                    kind: RelationKind::Membership(member),
                    arity: vec![owner, member],
                    parents: vec![owner],
                },
                Relation {
                    name: "dom".into(),
                    kind: RelationKind::Function(FunctionKind::MorphismDomain(owner)),
                    arity: vec![morphism, owner],
                    parents: vec![],
                },
                Relation {
                    name: "cod".into(),
                    kind: RelationKind::Function(FunctionKind::MorphismCodomain(owner)),
                    arity: vec![morphism, owner],
                    parents: vec![],
                },
                Relation {
                    name: "app".into(),
                    kind: RelationKind::Function(FunctionKind::MorphismApplication {
                        morphism,
                        member,
                    }),
                    arity: vec![morphism, member, member],
                    parents: vec![],
                },
            ],
        )
        .unwrap();
        let mut model = Model::with_signature(Arc::new(signature));
        let source = model.new_element(owner, &[]).unwrap();
        let x = model.new_element(member, &[source]).unwrap();
        let h = model.new_element(morphism, &[]).unwrap();
        let missing = Element {
            type_: member,
            index: 99,
        };
        assert_eq!(
            Validator(&AtCapacity {
                model: &model,
                full: member
            })
            .check_define(application, &[h, x]),
            Err(Error::UndefinedFunction(domain))
        );
        model.insert(domain, &[h, source]).unwrap();
        for full in [owner, member] {
            let view = AtCapacity {
                model: &model,
                full,
            };
            assert_eq!(
                Validator(&view).check_define(application, &[h, missing]),
                Err(Error::UnknownElement(missing))
            );
            assert_eq!(
                Validator(&view).check_define(application, &[h, x]),
                Err(Error::ElementLimit)
            );
            assert_eq!(model.eval(codomain, &[h]).unwrap(), None);
        }
        let image = model.define(application, &[h, x]).unwrap();
        for full in [owner, member] {
            let view = AtCapacity {
                model: &model,
                full,
            };
            assert_eq!(
                Validator(&view).new_element(full, &[source][..usize::from(full == member)]),
                Err(Error::ElementLimit)
            );
            assert_eq!(Validator(&view).check_define(application, &[h, x]), Ok(()));
            assert_eq!(model.eval(application, &[h, x]).unwrap(), Some(image));
        }
    }
}
