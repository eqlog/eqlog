use std::collections::{hash_map, BTreeMap, BTreeSet, HashMap};

use crate::kernel::{
    Args, Call, Constructor, Context, ContextMor, Data, Definition, Kernel, Telescope, Tm, Ty,
};
use crate::syntax::{self, Case, ConstructorDecl, Declaration, Error, Expr};

pub struct Checked {
    pub model: Kernel,
    pub declarations: Vec<String>,
}

pub fn check(source: &str) -> Result<Checked, Error> {
    let declarations = syntax::parse(source)?;
    let mut checker = Checker::new();
    for declaration in declarations {
        checker.declaration(declaration)?;
    }
    checker.model.close();
    for (name, goal) in &checker.goals {
        if !checker.model.checked_definition(*goal) {
            return Err(Error(format!(
                "{name}: type checking did not establish the declared type (beta budget: 3)"
            )));
        }
    }
    for (name, scope, a, b) in &checker.type_goals {
        if !checker.model.valid(checker.context(*scope)) || !checker.model.are_equal_ty(*a, *b) {
            return Err(Error(format!("{name}: incompatible index binder type")));
        }
    }
    Ok(Checked {
        model: checker.model,
        declarations: checker.names,
    })
}

struct Scope {
    context: Context,
    parent: Option<(usize, ContextMor)>,
    locals: BTreeMap<String, Tm>,
    types: BTreeMap<Ty, Ty>,
    terms: BTreeMap<Tm, Tm>,
    application_bases: BTreeMap<Tm, ContextMor>,
    calls: BTreeMap<Tm, Call>,
}

#[derive(Clone)]
struct Parameter {
    scope: usize,
    name: String,
    ty: Ty,
    syntax: Expr,
}

#[derive(Clone)]
enum Form {
    Term,
    Family(Data, Ty),
    Constructor(Constructor),
}

#[derive(Clone)]
struct Construction {
    base: usize,
    parameters: Vec<Parameter>,
    end: usize,
    result: Expr,
    ty: Ty,
    term: Tm,
    application_base: Option<ContextMor>,
    call: Option<Call>,
    form: Form,
}

#[derive(Clone)]
struct Inductive {
    data: Data,
    signature: Construction,
    parameter_count: usize,
    indices: Vec<(String, Expr)>,
    constructors: Vec<ConstructorInfo>,
}

#[derive(Clone)]
struct ConstructorInfo {
    name: String,
    constructor: Constructor,
    fields: Vec<(String, Expr)>,
    recursive: Vec<Option<Vec<Expr>>>,
    result_indices: Vec<Expr>,
    signature: Construction,
}

struct Checker {
    model: Kernel,
    scopes: Vec<Scope>,
    global: usize,
    data: BTreeMap<String, Inductive>,
    constructors: BTreeMap<String, ConstructorInfo>,
    definitions: BTreeMap<String, Construction>,
    goals: Vec<(String, Definition)>,
    names: Vec<String>,
    type_goals: Vec<(String, usize, Ty, Ty)>,
    weakenings: BTreeMap<(usize, usize), ContextMor>,
}

impl Checker {
    fn new() -> Self {
        let mut model = Kernel::new();
        let context = model.define_empty();
        Self {
            model,
            scopes: vec![Scope {
                context,
                parent: None,
                locals: BTreeMap::new(),
                types: BTreeMap::new(),
                terms: BTreeMap::new(),
                application_bases: BTreeMap::new(),
                calls: BTreeMap::new(),
            }],
            global: 0,
            data: BTreeMap::new(),
            constructors: BTreeMap::new(),
            definitions: BTreeMap::new(),
            goals: Vec::new(),
            names: Vec::new(),
            type_goals: Vec::new(),
            weakenings: BTreeMap::new(),
        }
    }

    fn context(&self, scope: usize) -> Context {
        self.scopes[scope].context
    }

    fn environment(&self, source: usize, target: usize) -> BTreeMap<String, Tm> {
        self.scopes[source]
            .locals
            .iter()
            .map(|(name, term)| (name.clone(), self.scopes[target].terms[term]))
            .collect()
    }

    fn remember_type(&mut self, scope: usize, ty: Ty) -> Ty {
        self.scopes[scope].types.insert(ty, ty);
        ty
    }

    fn remember_term(&mut self, scope: usize, term: Tm) -> Tm {
        self.scopes[scope].terms.insert(term, term);
        term
    }

    fn literal(&mut self, scope: usize, term: Tm) {
        let Some(call) = self.scopes[scope].calls.get(&term).copied() else {
            return;
        };
        let site = self.model.new_expansion();
        let mut next = site;
        for _ in 0..3 {
            next = self.model.define_next_expansion(next);
        }
        self.model.insert_literal(site, call);
    }

    fn child(&mut self, parent: usize, extension: Option<Ty>) -> usize {
        let context = self.model.new_context();
        let source = self.context(parent);
        let morphism = self.model.define_projection(context);
        if let Some(ty) = extension {
            self.model.insert_extension(context, source, ty);
        } else {
            self.model.insert_advance(source, context, morphism);
        }
        // Scope maps send the elements of every ancestor to the same parent
        // element, so most values repeat; each is weakened only once.
        let mut type_images = HashMap::new();
        let mut types = Vec::new();
        for (&origin, &ty) in &self.scopes[parent].types {
            let image = match type_images.entry(ty) {
                hash_map::Entry::Occupied(entry) => *entry.get(),
                hash_map::Entry::Vacant(entry) => {
                    let image = self.model.new_ty(context);
                    self.model
                        .insert_type_image(morphism, source, ty, context, image);
                    *entry.insert(image)
                }
            };
            types.push((origin, image));
        }
        let mut term_images = HashMap::new();
        let mut terms = Vec::new();
        for (&origin, &term) in &self.scopes[parent].terms {
            let image = match term_images.entry(term) {
                hash_map::Entry::Occupied(entry) => *entry.get(),
                hash_map::Entry::Vacant(entry) => {
                    let image = self.model.new_tm(context);
                    self.model
                        .insert_term_image(morphism, source, term, context, image);
                    *entry.insert(image)
                }
            };
            terms.push((origin, image));
        }
        types.extend(type_images.values().map(|&image| (image, image)));
        terms.extend(term_images.values().map(|&image| (image, image)));
        let types: BTreeMap<_, _> = types.into_iter().collect();
        let terms: BTreeMap<_, _> = terms.into_iter().collect();
        let locals = self.scopes[parent]
            .locals
            .iter()
            .map(|(name, term)| (name.clone(), term_images[term]))
            .collect();
        let mut application_bases = BTreeMap::new();
        for (term, base) in &self.scopes[parent].application_bases {
            let base = self.model.define_compose(*base, morphism);
            application_bases.insert(term_images[term], base);
        }
        let calls = self.scopes[parent]
            .calls
            .iter()
            .map(|(term, call)| {
                (
                    term_images[term],
                    self.model.define_image_call(*call, morphism),
                )
            })
            .collect();
        let id = self.scopes.len();
        self.scopes.push(Scope {
            context,
            parent: Some((parent, morphism)),
            locals,
            types,
            terms,
            application_bases,
            calls,
        });
        id
    }

    fn bind(&mut self, parent: usize, name: &str, ty: Ty) -> usize {
        let scope = self.child(parent, Some(ty));
        let variable = self.model.define_variable(self.context(scope));
        self.remember_term(scope, variable);
        self.scopes[scope].locals.insert(name.to_owned(), variable);
        scope
    }

    fn weakening(&mut self, source: usize, target: usize) -> Result<ContextMor, Error> {
        // Defining a weakening again returns the same morphism, so walking the
        // scope chain once per pair suffices.
        if let Some(&weakening) = self.weakenings.get(&(source, target)) {
            return Ok(weakening);
        }
        let weakening = if source == target {
            self.model.define_identity_sub(self.context(source))
        } else {
            let (parent, projection) = self.scopes[target]
                .parent
                .ok_or_else(|| Error("construction is outside its defining scope".to_owned()))?;
            let previous = self.weakening(source, parent)?;
            self.model.define_compose(previous, projection)
        };
        self.weakenings.insert((source, target), weakening);
        Ok(weakening)
    }

    fn stage_path(&mut self, start: usize, end: usize) {
        let mut current = end;
        while current != start {
            let (parent, _) = self.scopes[current].parent.unwrap();
            self.model.insert_stage_step(
                self.context(start),
                self.context(current),
                self.context(parent),
            );
            current = parent;
        }
    }

    fn goal(&mut self, name: String, scope: usize, term: Tm, ty: Ty) -> Tm {
        let definition = self.model.new_definition();
        let exported = self.model.new_tm(self.context(scope));
        self.model
            .insert_definition_goal(definition, self.context(scope), term, ty, exported);
        self.goals.push((name, definition));
        if let Some(base) = self.scopes[scope].application_bases.get(&term).copied() {
            self.scopes[scope].application_bases.insert(exported, base);
        }
        if let Some(call) = self.scopes[scope].calls.get(&term).copied() {
            self.scopes[scope].calls.insert(exported, call);
        }
        self.remember_term(scope, exported)
    }

    fn args(&mut self, scope: usize, values: &[Tm]) -> Args {
        let context = self.context(scope);
        let mut args = self.model.define_nil_args(context);
        for value in values.iter().rev() {
            args = self.model.define_cons_args(context, *value, args);
        }
        args
    }

    fn parameters(
        &mut self,
        base: usize,
        binders: &[(String, Expr)],
    ) -> Result<(usize, Vec<Parameter>), Error> {
        let mut scope = base;
        let mut parameters = Vec::new();
        for (name, syntax) in binders {
            if name == "Type" {
                return Err(Error("Type is reserved".to_owned()));
            }
            if parameters.iter().any(|p: &Parameter| p.name == *name) {
                return Err(Error(format!("repeated parameter {name}")));
            }
            let ty = self.ty(scope, syntax)?;
            scope = self.bind(scope, name, ty);
            parameters.push(Parameter {
                scope,
                name: name.clone(),
                ty,
                syntax: syntax.clone(),
            });
        }
        Ok((scope, parameters))
    }

    fn declaration(&mut self, declaration: Declaration) -> Result<(), Error> {
        match declaration {
            Declaration::Data {
                name,
                parameters,
                indices,
                constructors,
            } => self.inductive(name, parameters, indices, constructors),
            Declaration::Definition {
                name,
                parameters,
                result,
                body,
            } => {
                self.fresh_name(&name)?;
                let base = self.child(self.global, None);
                self.global = base;
                let (scope, parameters) = self.parameters(base, &parameters)?;
                let ty = self.ty(scope, &result)?;
                let (end, term, ty) = self.body(scope, &body, ty)?;
                let term = self.goal(name.clone(), end, term, ty);
                let application_base = self.scopes[end].application_bases.get(&term).copied();
                self.definitions.insert(
                    name.clone(),
                    Construction {
                        base,
                        parameters,
                        end,
                        result,
                        ty,
                        term,
                        application_base,
                        call: self.scopes[end].calls.get(&term).copied(),
                        form: Form::Term,
                    },
                );
                self.names.push(name);
                Ok(())
            }
        }
    }

    fn inductive(
        &mut self,
        name: String,
        parameters: Vec<(String, Expr)>,
        indices: Vec<(String, Expr)>,
        constructors: Vec<ConstructorDecl>,
    ) -> Result<(), Error> {
        self.fresh_name(&name)?;
        if parameters
            .iter()
            .chain(&indices)
            .chain(constructors.iter().flat_map(|c| c.fields.iter()))
            .any(|(binder, _)| binder == &name)
        {
            return Err(Error(format!(
                "{name}: binders cannot shadow the family being declared"
            )));
        }
        let base = self.child(self.global, None);
        self.global = base;
        let data = self.model.new_data();
        let all_binders: Vec<_> = parameters.iter().chain(&indices).cloned().collect();
        let (end, telescope) = self.parameters(base, &all_binders)?;
        let values: Vec<_> = all_binders
            .iter()
            .map(|(n, _)| self.scopes[end].locals[n])
            .collect();
        let args = self.args(end, &values);
        let family = self.model.define_data_type(self.context(end), data, args);
        self.remember_type(end, family);
        self.model.insert_family_schema(self.context(end), family);
        let ty = self.model.define_universe(self.context(end));
        self.remember_type(end, ty);
        let term = self.model.define_quote(self.context(end), family);
        let term = self.goal(name.clone(), end, term, ty);
        let signature = Construction {
            base,
            parameters: telescope,
            end,
            result: named("Type"),
            ty,
            term,
            application_base: None,
            call: None,
            form: Form::Family(data, family),
        };
        self.data.insert(
            name.clone(),
            Inductive {
                data,
                signature,
                parameter_count: parameters.len(),
                indices: indices.clone(),
                constructors: Vec::new(),
            },
        );
        let uniform: Vec<_> = parameters.iter().map(|(n, _)| named(n)).collect();
        let mut checked = Vec::new();
        for constructor in constructors {
            let full = format!("{name}.{}", constructor.name);
            self.fresh_name(&full)?;
            let result = constructor
                .result
                .unwrap_or_else(|| Expr::Name(name.clone(), uniform.clone()));
            let result_args = family_arguments(&result, &name, &uniform, indices.len())?;
            let mut recursive = Vec::new();
            for (_, field) in &constructor.fields {
                if free_names(field).contains(&name) {
                    let args = family_arguments(field, &name, &uniform, indices.len())?;
                    recursive.push(Some(args));
                } else {
                    recursive.push(None);
                }
            }
            let all_fields: Vec<_> = parameters
                .iter()
                .chain(&constructor.fields)
                .cloned()
                .collect();
            let (end, telescope) = self.parameters(base, &all_fields)?;
            for field in telescope.iter().skip(parameters.len()) {
                let parent = self.scopes[field.scope].parent.unwrap().0;
                let code = self.model.define_quote(self.context(parent), field.ty);
                let universe = self.model.define_universe(self.context(parent));
                self.remember_type(parent, universe);
                self.goal(format!("{full}.{}", field.name), parent, code, universe);
            }
            let ty = self.ty(end, &result)?;
            let c = self.model.new_constructor();
            let values: Vec<_> = all_fields
                .iter()
                .map(|(n, _)| self.scopes[end].locals[n])
                .collect();
            let args = self.args(end, &values);
            let term = self.model.define_construct(self.context(end), c, args);
            self.model
                .insert_constructor_schema(self.context(end), term, ty);
            let term = self.goal(full.clone(), end, term, ty);
            let signature = Construction {
                base,
                parameters: telescope,
                end,
                result,
                ty,
                term,
                application_base: None,
                call: None,
                form: Form::Constructor(c),
            };
            let info = ConstructorInfo {
                name: constructor.name,
                constructor: c,
                fields: constructor.fields,
                recursive,
                result_indices: result_args,
                signature,
            };
            self.constructors.insert(full, info.clone());
            checked.push(info);
        }
        let mut list = self.model.define_no_data_constructors();
        for constructor in checked.iter().rev() {
            list = self
                .model
                .define_more_data_constructors(constructor.constructor, list);
        }
        self.model.insert_data_constructors(data, list);
        self.data.get_mut(&name).unwrap().constructors = checked;
        self.names.push(name);
        Ok(())
    }

    fn fresh_name(&self, name: &str) -> Result<(), Error> {
        if name == "Type" {
            return Err(Error("Type is reserved".to_owned()));
        }
        if self.data.contains_key(name)
            || self.constructors.contains_key(name)
            || self.definitions.contains_key(name)
        {
            return Err(Error(format!("duplicate declaration {name}")));
        }
        Ok(())
    }

    fn ty(&mut self, scope: usize, expr: &Expr) -> Result<Ty, Error> {
        let context = self.context(scope);
        let ty = match expr {
            Expr::Name(name, args) => {
                if name == "Type" && args.is_empty() {
                    self.model.define_universe(context)
                } else {
                    let code = self.term(scope, expr, None)?;
                    self.model.define_decode(context, code)
                }
            }
            Expr::Equal(lhs, rhs) => {
                let lhs = self.term(scope, lhs, None)?;
                let rhs = self.term(scope, rhs, None)?;
                let ty = self.model.define_type_of(context, lhs);
                self.remember_type(scope, ty);
                self.model.define_identity(context, ty, lhs, rhs)
            }
            Expr::Refl | Expr::Rec { .. } | Expr::Let(_, _, _, _) => {
                return Err(Error("expected a type".to_owned()));
            }
        };
        Ok(self.remember_type(scope, ty))
    }

    fn term(&mut self, scope: usize, expr: &Expr, expected: Option<Ty>) -> Result<Tm, Error> {
        let context = self.context(scope);
        let term = match expr {
            Expr::Name(name, args) => {
                if let Some(&local) = self.scopes[scope].locals.get(name) {
                    if !args.is_empty() {
                        return Err(Error(format!("local variable {name} cannot be applied")));
                    }
                    local
                } else if name == "Type" && args.is_empty() {
                    let ty = self.ty(scope, expr)?;
                    self.model.define_quote(context, ty)
                } else if let Some(data) = self.data.get(name).cloned() {
                    self.apply(scope, name, &data.signature, args)?
                } else if let Some(constructor) = self.constructors.get(name).cloned() {
                    self.apply(scope, name, &constructor.signature, args)?
                } else if let Some(definition) = self.definitions.get(name).cloned() {
                    self.apply(scope, name, &definition, args)?
                } else {
                    return Err(Error(format!("unknown term {name}")));
                }
            }
            Expr::Refl => {
                let ty = expected
                    .ok_or_else(|| Error("rfl needs an expected identity type".to_owned()))?;
                self.model.define_refl(context, ty)
            }
            Expr::Rec {
                arguments,
                binders,
                motive,
                cases,
            } => self.rec(scope, arguments, binders, motive, cases)?,
            Expr::Equal(_, _) => {
                let ty = self.ty(scope, expr)?;
                self.model.define_quote(context, ty)
            }
            Expr::Let(_, _, _, _) => {
                return Err(Error(
                    "put let statements at the start of a declaration or branch body".to_owned(),
                ))
            }
        };
        self.remember_term(scope, term);
        self.literal(scope, term);
        Ok(term)
    }

    fn apply(
        &mut self,
        scope: usize,
        name: &str,
        definition: &Construction,
        args: &[Expr],
    ) -> Result<Tm, Error> {
        if args.len() != definition.parameters.len() {
            return Err(Error(format!("wrong number of arguments to {name}")));
        }
        let saved = self.scopes[scope].locals.clone();
        self.scopes[scope].locals = self.environment(definition.base, scope);
        let mut morphism = self.weakening(definition.base, scope)?;
        let mut source = definition.base;
        let mut values = Vec::new();
        for (parameter, argument) in definition.parameters.iter().zip(args) {
            let ty = self.ty(scope, &parameter.syntax)?;
            let signature = self.scopes[scope].locals.clone();
            self.scopes[scope].locals = saved.clone();
            let argument = self.term(scope, argument, Some(ty))?;
            self.scopes[scope].locals = signature;
            self.model.insert_type_image(
                morphism,
                self.context(source),
                parameter.ty,
                self.context(scope),
                ty,
            );
            morphism = self.model.define_pair(
                self.context(parameter.scope),
                self.context(scope),
                morphism,
                argument,
            );
            source = parameter.scope;
            self.scopes[scope]
                .locals
                .insert(parameter.name.clone(), argument);
            values.push(argument);
        }
        let ty = self.ty(scope, &definition.result)?;
        self.scopes[scope].locals = saved;
        self.stage_path(source, definition.end);
        morphism = self.model.define_through(
            self.context(source),
            self.context(definition.end),
            self.context(scope),
            morphism,
        );
        self.model.insert_type_image(
            morphism,
            self.context(definition.end),
            definition.ty,
            self.context(scope),
            ty,
        );
        let context = self.context(scope);
        let term = match definition.form {
            Form::Term => {
                let args = self.args(scope, &values);
                self.model.define_instance(
                    self.context(definition.end),
                    definition.term,
                    context,
                    args,
                )
            }
            Form::Family(data, source_ty) => {
                let args = self.args(scope, &values);
                let target_ty = self.model.define_data_type(context, data, args);
                self.remember_type(scope, target_ty);
                self.model.insert_type_image(
                    morphism,
                    self.context(definition.end),
                    source_ty,
                    context,
                    target_ty,
                );
                self.model.define_quote(context, target_ty)
            }
            Form::Constructor(constructor) => {
                let args = self.args(scope, &values);
                self.model.define_construct(context, constructor, args)
            }
        };
        self.model.insert_term_image(
            morphism,
            self.context(definition.end),
            definition.term,
            context,
            term,
        );
        for base in self.scopes[definition.end].application_bases.values() {
            self.model.define_compose(*base, morphism);
        }
        if let Some(base) = definition.application_base {
            let base = self.model.define_compose(base, morphism);
            self.scopes[scope].application_bases.insert(term, base);
        }
        self.remember_term(scope, term);
        if let Some(call) = definition.call {
            let call = self.model.define_image_call(call, morphism);
            self.scopes[scope].calls.insert(term, call);
        }
        Ok(term)
    }

    fn motive_instance(
        &mut self,
        scope: usize,
        motive: &Construction,
        values: &[Tm],
    ) -> Result<(ContextMor, Ty), Error> {
        let saved = self.scopes[scope].locals.clone();
        self.scopes[scope].locals = self.environment(motive.base, scope);
        let mut morphism = self.weakening(motive.base, scope)?;
        let mut source = motive.base;
        for (parameter, value) in motive.parameters.iter().zip(values) {
            let ty = self.ty(scope, &parameter.syntax)?;
            self.model.insert_type_image(
                morphism,
                self.context(source),
                parameter.ty,
                self.context(scope),
                ty,
            );
            morphism = self.model.define_pair(
                self.context(parameter.scope),
                self.context(scope),
                morphism,
                *value,
            );
            self.scopes[scope]
                .locals
                .insert(parameter.name.clone(), *value);
            source = parameter.scope;
        }
        let ty = self.ty(scope, &motive.result)?;
        self.model.insert_type_image(
            morphism,
            self.context(motive.end),
            motive.ty,
            self.context(scope),
            ty,
        );
        self.scopes[scope].locals = saved;
        Ok((morphism, ty))
    }

    fn telescope(&mut self, parameters: &[Parameter]) -> Telescope {
        let mut telescope = self.model.define_telescope_end();
        for parameter in parameters.iter().rev() {
            telescope = self
                .model
                .define_telescope_cons(self.context(parameter.scope), telescope);
        }
        telescope
    }

    fn body(&mut self, scope: usize, expr: &Expr, expected: Ty) -> Result<(usize, Tm, Ty), Error> {
        match expr {
            Expr::Let(name, annotation, value, rest) => {
                if name == "Type" {
                    return Err(Error("Type is reserved".to_owned()));
                }
                let scope = self.child(scope, None);
                let expected = self.scopes[scope].types[&expected];
                let ty = self.ty(scope, annotation)?;
                let (scope, term, ty) = self.body(scope, value, ty)?;
                let term = self.goal(format!("let {name}"), scope, term, ty);
                self.scopes[scope].locals.insert(name.clone(), term);
                let scope = self.child(scope, None);
                let expected = self.scopes[scope].types[&expected];
                self.body(scope, rest, expected)
            }
            Expr::Name(_, _) | Expr::Equal(_, _) | Expr::Refl | Expr::Rec { .. } => {
                let term = self.term(scope, expr, Some(expected))?;
                Ok((scope, term, expected))
            }
        }
    }

    fn rec(
        &mut self,
        scope: usize,
        arguments: &[Expr],
        binders: &[(String, Expr)],
        motive: &Expr,
        cases: &[Case],
    ) -> Result<Tm, Error> {
        let (_, scrutinee_type) = binders.last().unwrap();
        let (data_name, family_args) = match scrutinee_type {
            Expr::Name(name, args) => (name, args),
            Expr::Equal(_, _) | Expr::Refl | Expr::Rec { .. } | Expr::Let(_, _, _, _) => {
                return Err(Error(
                    "the last motive binder must have an inductive type".to_owned(),
                ));
            }
        };
        let inductive = self
            .data
            .get(data_name)
            .cloned()
            .ok_or_else(|| Error(format!("unknown inductive {data_name}")))?;
        if self.scopes[scope].locals.contains_key(data_name)
            || binders.iter().any(|(name, _)| name == data_name)
        {
            return Err(Error(format!(
                "rec {data_name}: inductive name is shadowed by a local binder"
            )));
        }
        if arguments.len() != binders.len()
            || binders.len() != inductive.indices.len() + 1
            || family_args.len() != inductive.parameter_count + inductive.indices.len()
        {
            return Err(Error(format!(
                "rec {data_name}: supply every index followed by the scrutinee"
            )));
        }
        let binder_names: BTreeSet<_> = binders.iter().map(|(name, _)| name.clone()).collect();
        if binder_names.contains("Type")
            || cases
                .iter()
                .any(|case| case.variables.iter().any(|name| name == "Type"))
        {
            return Err(Error("Type is reserved".to_owned()));
        }
        if binder_names.len() != binders.len() {
            return Err(Error("repeated motive binder".to_owned()));
        }
        for (index, (name, _)) in family_args[inductive.parameter_count..].iter().zip(binders) {
            if *index != named(name) {
                return Err(Error(
                    "motive indices must be its index binders in declaration order".to_owned(),
                ));
            }
        }
        let uniform_exprs = &family_args[..inductive.parameter_count];
        if uniform_exprs
            .iter()
            .any(|expr| !free_names(expr).is_disjoint(&binder_names))
        {
            return Err(Error(
                "uniform parameters cannot depend on motive indices".to_owned(),
            ));
        }
        let mut seen = BTreeSet::new();
        for case in cases {
            let short = case
                .constructor
                .strip_prefix(&format!("{data_name}."))
                .unwrap_or(&case.constructor);
            if !seen.insert(short.to_owned()) {
                return Err(Error(format!("duplicate branch {short}")));
            }
        }
        if seen
            != inductive
                .constructors
                .iter()
                .map(|c| c.name.clone())
                .collect()
        {
            return Err(Error(format!(
                "rec {data_name}: branches must cover each constructor exactly once"
            )));
        }
        let mut captures = free_names(motive);
        for (_, annotation) in binders {
            captures.extend(free_names(annotation));
        }
        for name in &binder_names {
            captures.remove(name);
        }
        for case in cases {
            let mut names = free_names(&case.body);
            for name in &case.variables {
                names.remove(name);
            }
            captures.extend(names);
        }
        let mut base_scope = scope;
        while base_scope != self.global {
            let (parent, _) = self.scopes[base_scope].parent.unwrap();
            let can_drop = captures.iter().all(|name| {
                self.scopes[base_scope]
                    .locals
                    .get(name)
                    .map(|term| {
                        self.scopes[parent]
                            .locals
                            .get(name)
                            .map(|old| self.scopes[base_scope].terms[old] == *term)
                            .unwrap_or(false)
                    })
                    .unwrap_or(true)
            });
            if !can_drop {
                break;
            }
            base_scope = parent;
        }
        let mut uniforms = Vec::new();
        for expr in uniform_exprs {
            uniforms.push(self.term(base_scope, expr, None)?);
        }
        let mut formal: BTreeMap<_, _> = inductive
            .signature
            .parameters
            .iter()
            .zip(&uniforms)
            .map(|(p, value)| (p.name.clone(), *value))
            .collect();
        let mut current = base_scope;
        let mut parameters = Vec::new();
        for (i, (name, annotation)) in binders.iter().enumerate() {
            let ty = self.ty(current, annotation)?;
            if i < inductive.indices.len() {
                let saved = self.scopes[current].locals.clone();
                self.scopes[current].locals = formal.clone();
                let canonical = self.ty(current, &inductive.indices[i].1)?;
                self.scopes[current].locals = saved;
                self.type_goals
                    .push((format!("rec {data_name}"), current, ty, canonical));
            }
            current = self.bind(current, name, ty);
            formal = self.transport_environment(&formal, current);
            if i < inductive.indices.len() {
                formal.insert(
                    inductive.indices[i].0.clone(),
                    self.scopes[current].locals[name],
                );
            }
            parameters.push(Parameter {
                scope: current,
                name: name.clone(),
                ty,
                syntax: annotation.clone(),
            });
        }
        let motive_ty = self.ty(current, motive)?;
        let result = self.model.new_tm(self.context(current));
        self.remember_term(current, result);
        let motive = Construction {
            base: base_scope,
            parameters,
            end: current,
            result: motive.clone(),
            ty: motive_ty,
            term: result,
            application_base: None,
            call: None,
            form: Form::Term,
        };
        let eliminator = self.model.new_eliminator();
        let telescope = self.telescope(&motive.parameters);
        self.model
            .insert_elimination_base(eliminator, self.context(base_scope));
        self.model
            .insert_elimination_telescope(eliminator, telescope);
        self.model.insert_elimination(
            eliminator,
            inductive.data,
            self.context(current),
            motive_ty,
            result,
        );

        for case in cases {
            let short = case
                .constructor
                .strip_prefix(&format!("{data_name}."))
                .unwrap_or(&case.constructor);
            let constructor = inductive
                .constructors
                .iter()
                .find(|c| c.name == short)
                .unwrap();
            let count = constructor.fields.len()
                + constructor.recursive.iter().filter(|r| r.is_some()).count();
            if case.variables.len() != count
                || case.variables.iter().collect::<BTreeSet<_>>().len() != count
            {
                return Err(Error(format!("branch {short}: expected {count} distinct field and induction-hypothesis binders")));
            }
            let mut start = base_scope;
            let mut field_env: BTreeMap<_, _> = constructor
                .signature
                .parameters
                .iter()
                .zip(&uniforms)
                .map(|(p, value)| (p.name.clone(), *value))
                .collect();
            let mut body_env = self.scopes[base_scope].locals.clone();
            let mut steps = Vec::new();
            for value in &uniforms {
                steps.push(Plan::Parameter(self.context(base_scope), *value));
            }
            let mut variables = case.variables.iter();
            for ((field, syntax), recursive) in
                constructor.fields.iter().zip(&constructor.recursive)
            {
                let saved = self.scopes[start].locals.clone();
                self.scopes[start].locals = field_env.clone();
                let ty = self.ty(start, syntax)?;
                self.scopes[start].locals = saved;
                let alias = variables.next().unwrap();
                start = self.bind(start, alias, ty);
                steps.push(Plan::Field(self.context(start)));
                field_env = self.transport_environment(&field_env, start);
                body_env = self.transport_environment(&body_env, start);
                let value = self.scopes[start].locals[alias];
                field_env.insert(field.clone(), value);
                body_env.insert(alias.clone(), value);
                if let Some(indices) = recursive {
                    let mut values = self.evaluate_in(start, &field_env, indices)?;
                    values.push(value);
                    let (instance, ih_ty) = self.motive_instance(start, &motive, &values)?;
                    let args = self.args(start, &values);
                    let source = self.context(start);
                    let alias = variables.next().unwrap();
                    start = self.bind(start, alias, ih_ty);
                    steps.push(Plan::Hypothesis(
                        source,
                        args,
                        self.context(start),
                        instance,
                    ));
                    field_env = self.transport_environment(&field_env, start);
                    body_env = self.transport_environment(&body_env, start);
                    body_env.insert(alias.clone(), self.scopes[start].locals[alias]);
                }
            }
            let saved = self.scopes[start].locals.clone();
            self.scopes[start].locals = field_env.clone();
            let ctor_args: Vec<_> = constructor
                .signature
                .parameters
                .iter()
                .map(|p| named(&p.name))
                .collect();
            let pattern =
                self.apply(start, &constructor.name, &constructor.signature, &ctor_args)?;
            self.remember_term(start, pattern);
            self.scopes[start].locals = saved;
            let mut indices = self.evaluate_in(start, &field_env, &constructor.result_indices)?;
            indices.push(pattern);
            let (_, expected) = self.motive_instance(start, &motive, &indices)?;
            let expected_args = self.args(start, &indices);
            let branch_scope = self.child(start, None);
            self.scopes[branch_scope].locals = self.transport_environment(&body_env, branch_scope);
            let expected = self.scopes[branch_scope].types[&expected];
            let (end, body, expected) = self.body(branch_scope, &case.body, expected)?;
            self.stage_path(start, end);
            let branch = self
                .model
                .define_case_branch(eliminator, constructor.constructor);
            self.model
                .insert_branch_goal(branch, self.context(end), body, expected);
            let mut plan = self.model.new_branch_steps();
            self.model.insert_finish_step(
                plan,
                self.context(start),
                expected_args,
                self.context(end),
                body,
            );
            if let Some(call) = self.scopes[end].calls.get(&body).copied() {
                self.model.insert_body_call(plan, call);
            }
            for base in self.scopes[end].application_bases.values() {
                self.model.insert_body_base(plan, *base);
            }
            for step in steps.into_iter().rev() {
                let next = self.model.new_branch_steps();
                match step {
                    Plan::Parameter(context, value) => {
                        self.model.insert_parameter_step(next, context, value, plan)
                    }
                    Plan::Field(context) => self.model.insert_field_step(next, context, plan),
                    Plan::Hypothesis(context, args, target, instance) => {
                        self.model
                            .insert_hypothesis_step(next, context, args, target, instance, plan);
                    }
                }
                plan = next;
            }
            self.model
                .insert_case_steps(eliminator, constructor.constructor, plan);
        }
        let saved = self.scopes[scope].locals.clone();
        let mut signature_env = self.environment(base_scope, scope);
        let mut values = Vec::new();
        for (argument, parameter) in arguments.iter().zip(&motive.parameters) {
            self.scopes[scope].locals = signature_env;
            let expected = self.ty(scope, &parameter.syntax)?;
            signature_env = self.scopes[scope].locals.clone();
            self.scopes[scope].locals = saved.clone();
            let value = self.term(scope, argument, Some(expected))?;
            signature_env.insert(parameter.name.clone(), value);
            values.push(value);
        }
        self.scopes[scope].locals = saved;
        self.motive_instance(scope, &motive, &values)?;
        let args = self.args(scope, &values);
        let base = self.weakening(base_scope, scope)?;
        let application =
            self.model
                .define_application(eliminator, base, self.context(scope), args);
        self.scopes[scope]
            .application_bases
            .insert(application, base);
        let call = self
            .model
            .define_direct_call(eliminator, base, self.context(scope), args);
        self.scopes[scope].calls.insert(application, call);
        Ok(application)
    }

    fn transport_environment(
        &self,
        environment: &BTreeMap<String, Tm>,
        scope: usize,
    ) -> BTreeMap<String, Tm> {
        environment
            .iter()
            .map(|(name, term)| (name.clone(), self.scopes[scope].terms[term]))
            .collect()
    }

    fn evaluate_in(
        &mut self,
        scope: usize,
        environment: &BTreeMap<String, Tm>,
        expressions: &[Expr],
    ) -> Result<Vec<Tm>, Error> {
        let saved = self.scopes[scope].locals.clone();
        self.scopes[scope].locals = environment.clone();
        let values = expressions
            .iter()
            .map(|e| self.term(scope, e, None))
            .collect();
        self.scopes[scope].locals = saved;
        values
    }
}

enum Plan {
    Parameter(Context, Tm),
    Field(Context),
    Hypothesis(Context, Args, Context, ContextMor),
}

fn named(name: &str) -> Expr {
    Expr::Name(name.to_owned(), Vec::new())
}

fn family_arguments(
    expr: &Expr,
    family: &str,
    uniform: &[Expr],
    indices: usize,
) -> Result<Vec<Expr>, Error> {
    match expr {
        Expr::Name(name, args) => {
            if name != family
                || args.len() != uniform.len() + indices
                || args[..uniform.len()] != *uniform
                || args.iter().any(|arg| free_names(arg).contains(family))
            {
                return Err(Error(format!("{family}: recursive fields and constructor results must apply the family directly with unchanged parameters")));
            }
            Ok(args[uniform.len()..].to_vec())
        }
        Expr::Equal(_, _) | Expr::Refl | Expr::Rec { .. } | Expr::Let(_, _, _, _) => Err(Error(
            format!("{family}: only direct strictly positive recursive fields are supported"),
        )),
    }
}

fn free_names(expr: &Expr) -> BTreeSet<String> {
    match expr {
        Expr::Name(name, args) => {
            let mut names = BTreeSet::from([name.clone()]);
            for arg in args {
                names.extend(free_names(arg));
            }
            names
        }
        Expr::Equal(lhs, rhs) => {
            let mut names = free_names(lhs);
            names.extend(free_names(rhs));
            names
        }
        Expr::Refl => BTreeSet::new(),
        Expr::Rec {
            arguments,
            binders,
            motive,
            cases,
        } => {
            let mut names = free_names(motive);
            for (name, ty) in binders.iter().rev() {
                names.remove(name);
                names.extend(free_names(ty));
            }
            for argument in arguments {
                names.extend(free_names(argument));
            }
            for case in cases {
                let mut branch = free_names(&case.body);
                for variable in &case.variables {
                    branch.remove(variable);
                }
                names.extend(branch);
            }
            names
        }
        Expr::Let(name, ty, value, body) => {
            let mut names = free_names(body);
            names.remove(name);
            names.extend(free_names(ty));
            names.extend(free_names(value));
            names
        }
    }
}
