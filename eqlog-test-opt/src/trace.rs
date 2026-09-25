use eqlog_runtime::{
    Element, FunctionKind, Model, RelationId, RelationKind, Signature, TypeId, TypeKind,
};
use rand::{rngs::StdRng, RngExt, SeedableRng};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Op {
    New {
        type_: String,
        parents: Vec<usize>,
    },
    Insert {
        relation: String,
        arguments: Vec<usize>,
    },
    Define {
        function: String,
        arguments: Vec<usize>,
    },
    Equate {
        parents: Vec<usize>,
        left: usize,
        right: usize,
    },
    Canonicalize,
    Close,
}

pub struct State {
    pub model: Model,
    pub elements: Vec<Element>,
}

impl State {
    pub fn new(signature: &'static Signature) -> Self {
        Self {
            model: Model::new(signature),
            elements: Vec::new(),
        }
    }

    fn elements(&self, slots: &[usize]) -> Vec<Element> {
        slots.iter().map(|&slot| self.elements[slot]).collect()
    }

    pub fn apply(&mut self, op: &Op) {
        match op {
            Op::New { type_, parents } => {
                let type_ = self.model.signature().type_named(type_).unwrap();
                let element = self
                    .model
                    .new_element(type_, &self.elements(parents))
                    .unwrap();
                self.elements.push(element);
            }
            Op::Insert {
                relation,
                arguments,
            } => {
                let relation = self.model.signature().relation_named(relation).unwrap();
                self.model
                    .insert(relation, &self.elements(arguments))
                    .unwrap();
            }
            Op::Define {
                function,
                arguments,
            } => {
                let function = self.model.signature().relation_named(function).unwrap();
                let element = self
                    .model
                    .define(function, &self.elements(arguments))
                    .unwrap();
                self.elements.push(element);
            }
            Op::Equate {
                parents,
                left,
                right,
            } => {
                self.model
                    .equate(
                        &self.elements(parents),
                        self.elements[*left],
                        self.elements[*right],
                    )
                    .unwrap();
            }
            Op::Canonicalize | Op::Close => self.model.canonicalize(),
        }
    }
}

struct Pool {
    type_: TypeId,
    parents: Vec<usize>,
    slots: Vec<usize>,
}

struct Arrow {
    slot: usize,
    type_: TypeId,
    source: usize,
    target: usize,
}

#[derive(Clone, Copy)]
enum Action {
    Insert,
    Allocate,
    Equate,
    Canonicalize,
    Define,
    Image,
}

struct Generator {
    rng: StdRng,
    signature: &'static Signature,
    state: State,
    pools: Vec<Pool>,
    arrows: Vec<Arrow>,
    trace: Vec<Op>,
}

impl Generator {
    fn emit(&mut self, op: Op) {
        self.state.apply(&op);
        self.trace.push(op);
    }

    fn allocate(&mut self, pool: usize) {
        let slot = self.state.elements.len();
        let type_ = self
            .signature
            .type_(self.pools[pool].type_)
            .unwrap()
            .name
            .clone();
        let parents = self.pools[pool].parents.clone();
        self.emit(Op::New { type_, parents });
        self.pools[pool].slots.push(slot);
    }

    fn add_pool(&mut self, type_: TypeId, parents: Vec<usize>, count: usize) {
        let pool = self.pools.len();
        self.pools.push(Pool {
            type_,
            parents,
            slots: Vec::new(),
        });
        for _ in 0..count {
            self.allocate(pool);
        }
    }

    fn initialize(&mut self) {
        for (type_, descriptor) in self.signature.types() {
            match descriptor.kind {
                TypeKind::Model => {
                    self.add_pool(type_, Vec::new(), 3);
                }
                TypeKind::Plain | TypeKind::Morphism(_) => {}
                TypeKind::Enum => panic!("enums need a constructor-aware trace generator"),
            }
        }
        for (type_, descriptor) in self.signature.types() {
            match descriptor.kind {
                TypeKind::Plain => {
                    let contexts = self.contexts(&descriptor.parents);
                    for parents in contexts {
                        let count = self.rng.random_range(2..=4);
                        self.add_pool(type_, parents, count);
                    }
                }
                TypeKind::Model | TypeKind::Morphism(_) => {}
                TypeKind::Enum => panic!("enums need a constructor-aware trace generator"),
            }
        }
        assert!(
            !self.plain_pools().is_empty(),
            "the trace generator needs a plain type"
        );
    }

    fn contexts(&self, parents: &[TypeId]) -> Vec<Vec<usize>> {
        match parents.first() {
            None => vec![Vec::new()],
            Some(type_) => self
                .pools
                .iter()
                .find(|pool| pool.type_ == *type_)
                .unwrap()
                .slots
                .iter()
                .map(|&slot| vec![slot])
                .collect(),
        }
    }

    fn choose_slot(&mut self, type_: TypeId, parents: &[usize]) -> usize {
        let descriptor = self.signature.type_(type_).unwrap();
        let context = &parents[..descriptor.parents.len()];
        let pool = self
            .pools
            .iter()
            .find(|pool| pool.type_ == type_ && pool.parents == context)
            .unwrap();
        pool.slots[self.rng.random_range(0..pool.slots.len())]
    }

    fn arguments(&mut self, relation: RelationId, define: bool) -> Vec<usize> {
        let descriptor = self.signature.relation(relation).unwrap();
        let contexts = self.contexts(&descriptor.parents);
        let parents = &contexts[self.rng.random_range(0..contexts.len())];
        let mut arguments = parents.clone();
        let end = descriptor.arity.len() - usize::from(define);
        for &type_ in &descriptor.arity[parents.len()..end] {
            arguments.push(self.choose_slot(type_, parents));
        }
        arguments
    }

    fn plain_pools(&self) -> Vec<usize> {
        self.pools
            .iter()
            .enumerate()
            .filter_map(
                |(i, pool)| match self.signature.type_(pool.type_).unwrap().kind {
                    TypeKind::Plain => Some(i),
                    TypeKind::Model | TypeKind::Enum | TypeKind::Morphism(_) => None,
                },
            )
            .collect()
    }

    fn insert(&mut self, relations: &[RelationId]) {
        let relation = relations[self.rng.random_range(0..relations.len())];
        let arguments = self.arguments(relation, false);
        let relation = self.signature.relation(relation).unwrap().name.clone();
        let op = Op::Insert {
            relation,
            arguments,
        };
        self.emit(op.clone());
        if self.rng.random_bool(0.2) {
            self.emit(op);
        }
    }

    fn define(&mut self, functions: &[RelationId]) {
        let function = functions[self.rng.random_range(0..functions.len())];
        let arguments = self.arguments(function, true);
        let descriptor = self.signature.relation(function).unwrap();
        let result = *descriptor.arity.last().unwrap();
        let parents = arguments[..self.signature.type_(result).unwrap().parents.len()].to_vec();
        let function = descriptor.name.clone();
        let slot = self.state.elements.len();
        self.emit(Op::Define {
            function,
            arguments,
        });
        self.pools
            .iter_mut()
            .find(|pool| pool.type_ == result && pool.parents == parents)
            .unwrap()
            .slots
            .push(slot);
    }

    fn morphism(&mut self, morphisms: &[(TypeId, TypeId)]) {
        let &(type_, model) = &morphisms[self.rng.random_range(0..morphisms.len())];
        let models = &self
            .pools
            .iter()
            .find(|pool| pool.type_ == model)
            .unwrap()
            .slots;
        // Acyclic morphisms keep image creation finite.
        let source = self.rng.random_range(0..models.len() - 1);
        let target = self.rng.random_range(source + 1..models.len());
        let source = models[source];
        let target = models[target];
        let slot = self.state.elements.len();
        let name = self.signature.type_(type_).unwrap().name.clone();
        self.emit(Op::New {
            type_: name,
            parents: Vec::new(),
        });
        for (_, relation) in self.signature.relations() {
            let endpoint = match relation.kind {
                RelationKind::Function(FunctionKind::MorphismDomain(owner)) => {
                    (owner == model).then_some(source)
                }
                RelationKind::Function(FunctionKind::MorphismCodomain(owner)) => {
                    (owner == model).then_some(target)
                }
                RelationKind::Predicate
                | RelationKind::Membership(_)
                | RelationKind::Function(
                    FunctionKind::Ordinary
                    | FunctionKind::Constructor
                    | FunctionKind::MorphismApplication { .. },
                ) => None,
            };
            if let Some(endpoint) = endpoint {
                self.emit(Op::Insert {
                    relation: relation.name.clone(),
                    arguments: vec![slot, endpoint],
                });
            }
        }
        self.arrows.push(Arrow {
            slot,
            type_,
            source,
            target,
        });
    }

    fn image(&mut self) {
        let arrow = &self.arrows[self.rng.random_range(0..self.arrows.len())];
        let applications: Vec<_> = self
            .signature
            .relations()
            .filter_map(|(id, relation)| match relation.kind {
                RelationKind::Function(FunctionKind::MorphismApplication { morphism, member }) => {
                    (morphism == arrow.type_).then_some((id, member))
                }
                RelationKind::Predicate
                | RelationKind::Membership(_)
                | RelationKind::Function(
                    FunctionKind::Ordinary
                    | FunctionKind::Constructor
                    | FunctionKind::MorphismDomain(_)
                    | FunctionKind::MorphismCodomain(_),
                ) => None,
            })
            .collect();
        let &(application, member) = &applications[self.rng.random_range(0..applications.len())];
        let source = arrow.source;
        let target = arrow.target;
        let slot = arrow.slot;
        let input = self.choose_slot(member, &[source]);
        let function = self.signature.relation(application).unwrap().name.clone();
        if self.rng.random_bool(0.5) {
            let output = self.choose_slot(member, &[target]);
            self.emit(Op::Insert {
                relation: function,
                arguments: vec![slot, input, output],
            });
        } else {
            let result = self.state.elements.len();
            self.emit(Op::Define {
                function,
                arguments: vec![slot, input],
            });
            self.pools
                .iter_mut()
                .find(|pool| pool.type_ == member && pool.parents == [target])
                .unwrap()
                .slots
                .push(result);
        }
    }
}

pub fn generate(signature: &'static Signature, seed: u64, rounds: usize) -> Vec<Op> {
    validate_signature(signature);
    let mut generator = Generator {
        rng: StdRng::seed_from_u64(seed),
        signature,
        state: State::new(signature),
        pools: Vec::new(),
        arrows: Vec::new(),
        trace: Vec::new(),
    };
    let mut relations = Vec::new();
    let mut functions = Vec::new();
    for (id, relation) in signature.relations() {
        match relation.kind {
            RelationKind::Predicate => relations.push(id),
            RelationKind::Function(FunctionKind::Ordinary) => {
                relations.push(id);
                functions.push(id);
            }
            RelationKind::Membership(_)
            | RelationKind::Function(
                FunctionKind::Constructor
                | FunctionKind::MorphismDomain(_)
                | FunctionKind::MorphismCodomain(_)
                | FunctionKind::MorphismApplication { .. },
            ) => {}
        }
    }
    let morphisms: Vec<_> = signature
        .types()
        .filter_map(|(id, descriptor)| match descriptor.kind {
            TypeKind::Morphism(model) => Some((id, model)),
            TypeKind::Plain | TypeKind::Model | TypeKind::Enum => None,
        })
        .collect();
    generator.emit(Op::Close);
    generator.initialize();
    let scheduled: Vec<_> = relations
        .iter()
        .map(|&relation| (generator.rng.random_range(0..rounds), relation))
        .collect();
    for round in 0..rounds {
        if !morphisms.is_empty() && round < 3 {
            generator.morphism(&morphisms);
        }
        for &(due, relation) in &scheduled {
            if due == round {
                generator.insert(&[relation]);
            }
        }
        let mut choices = vec![Action::Allocate, Action::Equate, Action::Canonicalize];
        if !relations.is_empty() {
            choices.extend([Action::Insert, Action::Insert]);
        }
        if !functions.is_empty() {
            choices.push(Action::Define);
        }
        if !generator.arrows.is_empty() {
            choices.push(Action::Image);
        }
        let pools = generator.plain_pools();
        for _ in 0..generator.rng.random_range(8..=16) {
            let action = choices[generator.rng.random_range(0..choices.len())];
            let pool = pools[generator.rng.random_range(0..pools.len())];
            match action {
                Action::Insert => generator.insert(&relations),
                Action::Allocate => generator.allocate(pool),
                Action::Equate => {
                    let pool = &generator.pools[pool];
                    let parents = pool.parents.clone();
                    let left = pool.slots[generator.rng.random_range(0..pool.slots.len())];
                    let right = pool.slots[generator.rng.random_range(0..pool.slots.len())];
                    generator.emit(Op::Equate {
                        parents,
                        left,
                        right,
                    });
                }
                Action::Canonicalize => generator.emit(Op::Canonicalize),
                Action::Define => generator.define(&functions),
                Action::Image => generator.image(),
            }
        }
        generator.emit(Op::Close);
        generator.emit(Op::Close);
    }
    generator.trace
}

fn validate_signature(signature: &Signature) {
    for (_, descriptor) in signature.types() {
        match descriptor.kind {
            TypeKind::Plain => assert!(
                descriptor.parents.len() <= 1,
                "nested members are not supported"
            ),
            TypeKind::Model => assert!(
                descriptor.parents.is_empty(),
                "nested models are not supported"
            ),
            TypeKind::Enum => panic!("enums are not supported by the trace generator"),
            TypeKind::Morphism(model) => {
                assert!(
                    descriptor.parents.is_empty(),
                    "nested morphisms are not supported"
                );
                assert!(
                    signature
                        .types()
                        .any(|(_, member)| member.parents == [model]),
                    "morphisms without member types are not supported"
                );
            }
        }
    }
    for (_, relation) in signature.relations() {
        let function = match relation.kind {
            RelationKind::Predicate => false,
            RelationKind::Function(FunctionKind::Ordinary) => true,
            RelationKind::Membership(_)
            | RelationKind::Function(
                FunctionKind::Constructor
                | FunctionKind::MorphismDomain(_)
                | FunctionKind::MorphismCodomain(_)
                | FunctionKind::MorphismApplication { .. },
            ) => continue,
        };
        for &type_ in &relation.arity {
            let descriptor = signature.type_(type_).unwrap();
            match descriptor.kind {
                TypeKind::Plain | TypeKind::Model => {}
                TypeKind::Enum | TypeKind::Morphism(_) => {
                    panic!("input relations need plain or model arguments")
                }
            }
            assert!(
                relation.parents.starts_with(&descriptor.parents),
                "member arguments must belong to the enclosing model"
            );
        }
        if function {
            let result = signature.type_(*relation.arity.last().unwrap()).unwrap();
            match result.kind {
                TypeKind::Plain => {}
                TypeKind::Model | TypeKind::Enum | TypeKind::Morphism(_) => {
                    panic!("input functions must return plain elements")
                }
            }
        }
    }
}
