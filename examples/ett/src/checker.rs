use std::collections::{BTreeMap, BTreeSet};

use crate::kernel::{Constructor, Context, ContextMor, Data, Definition, Kernel, Tm, Ty};
use crate::syntax::{self, Case, Declaration, Error, Expr};

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
}

#[derive(Clone)]
struct Parameter {
    scope: usize,
    name: String,
    ty: Ty,
    syntax: Expr,
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
}

#[derive(Clone)]
struct Inductive {
    data: Data,
    constructors: Vec<(String, Constructor, bool)>,
}

struct Checker {
    model: Kernel,
    scopes: Vec<Scope>,
    global: usize,
    data: BTreeMap<String, Inductive>,
    constructors: BTreeMap<String, (Data, Constructor, bool)>,
    definitions: BTreeMap<String, Construction>,
    goals: Vec<(String, Definition)>,
    names: Vec<String>,
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
            }],
            global: 0,
            data: BTreeMap::new(),
            constructors: BTreeMap::new(),
            definitions: BTreeMap::new(),
            goals: Vec::new(),
            names: Vec::new(),
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
        let site = self.model.new_expansion();
        let mut next = site;
        for _ in 0..3 {
            next = self.model.define_next_expansion(next);
        }
        self.model.insert_literal(site, self.context(scope), term);
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
        let mut types = BTreeMap::new();
        let mut terms = BTreeMap::new();
        let mut type_images = BTreeMap::new();
        let mut term_images = BTreeMap::new();
        for &ty in self.scopes[parent].types.values() {
            let image = *type_images
                .entry(ty)
                .or_insert_with(|| self.model.new_ty(context));
            self.model
                .insert_type_image(morphism, source, ty, context, image);
        }
        for &term in self.scopes[parent].terms.values() {
            let image = *term_images
                .entry(term)
                .or_insert_with(|| self.model.new_tm(context));
            self.model
                .insert_term_image(morphism, source, term, context, image);
        }
        for (&origin, ty) in &self.scopes[parent].types {
            types.insert(origin, type_images[ty]);
        }
        for &image in type_images.values() {
            types.insert(image, image);
        }
        for (&origin, term) in &self.scopes[parent].terms {
            terms.insert(origin, term_images[term]);
        }
        for &image in term_images.values() {
            terms.insert(image, image);
        }
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
        let id = self.scopes.len();
        self.scopes.push(Scope {
            context,
            parent: Some((parent, morphism)),
            locals,
            types,
            terms,
            application_bases,
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
        if source == target {
            return Ok(self.model.define_identity_sub(self.context(source)));
        }
        let (parent, projection) = self.scopes[target]
            .parent
            .ok_or_else(|| Error("construction is outside its defining scope".to_owned()))?;
        let previous = self.weakening(source, parent)?;
        Ok(self.model.define_compose(previous, projection))
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
        self.remember_term(scope, exported)
    }

    fn declaration(&mut self, declaration: Declaration) -> Result<(), Error> {
        match declaration {
            Declaration::Data(name, constructors) => {
                self.fresh_name(&name)?;
                let data = self.model.new_data();
                let mut cs = Vec::new();
                for (short, recursive) in constructors {
                    let full = format!("{name}.{short}");
                    self.fresh_name(&full)?;
                    let constructor = self.model.new_constructor();
                    if recursive {
                        self.model.insert_recursive(constructor, data);
                    } else {
                        self.model.insert_nullary(constructor, data);
                    }
                    self.constructors
                        .insert(full, (data, constructor, recursive));
                    cs.push((short, constructor, recursive));
                }
                let mut list = self.model.define_no_data_constructors();
                for (_, constructor, _) in cs.iter().rev() {
                    list = self.model.define_more_data_constructors(*constructor, list);
                }
                self.model.insert_data_constructors(data, list);
                self.data.insert(
                    name.clone(),
                    Inductive {
                        data,
                        constructors: cs,
                    },
                );
                self.names.push(name);
                self.global = self.child(self.global, None);
                Ok(())
            }
            Declaration::Definition {
                name,
                parameters,
                result,
                body,
            } => {
                self.fresh_name(&name)?;
                let base = self.child(self.global, None);
                self.global = base;
                let mut scope = base;
                let mut telescope = Vec::new();
                for (parameter, syntax) in parameters {
                    if self.scopes[scope].locals.contains_key(&parameter) {
                        return Err(Error(format!("{name}: repeated parameter {parameter}")));
                    }
                    let ty = self.ty(scope, &syntax)?;
                    scope = self.bind(scope, &parameter, ty);
                    telescope.push(Parameter {
                        scope,
                        name: parameter,
                        ty,
                        syntax,
                    });
                }
                let ty = self.ty(scope, &result)?;
                let (end, term, ty) = self.body(scope, &body, ty)?;
                let exported = self.goal(name.clone(), end, term, ty);
                let application_base = self.scopes[end].application_bases.get(&exported).copied();
                self.definitions.insert(
                    name.clone(),
                    Construction {
                        base,
                        parameters: telescope,
                        end,
                        result,
                        ty,
                        term: exported,
                        application_base,
                    },
                );
                self.names.push(name);
                Ok(())
            }
        }
    }

    fn fresh_name(&self, name: &str) -> Result<(), Error> {
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
                let data = self
                    .data
                    .get(name)
                    .ok_or_else(|| Error(format!("unknown type {name}")))?
                    .data;
                if !args.is_empty() {
                    return Err(Error(
                        "inductive types do not take parameters yet".to_owned(),
                    ));
                }
                self.model.define_data_type(context, data)
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

    fn body(&mut self, scope: usize, expr: &Expr, expected: Ty) -> Result<(usize, Tm, Ty), Error> {
        match expr {
            Expr::Let(name, annotation, value, rest) => {
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

    fn term(&mut self, scope: usize, expr: &Expr, expected: Option<Ty>) -> Result<Tm, Error> {
        let context = self.context(scope);
        let term = match expr {
            Expr::Name(name, args) => {
                if let Some(&local) = self.scopes[scope].locals.get(name) {
                    if !args.is_empty() {
                        return Err(Error(format!("local variable {name} cannot be applied")));
                    }
                    local
                } else if let Some(&(data, constructor, recursive)) = self.constructors.get(name) {
                    let ty = self.model.define_data_type(context, data);
                    self.remember_type(scope, ty);
                    if args.len() != usize::from(recursive) {
                        return Err(Error(format!("wrong number of arguments to {name}")));
                    }
                    if recursive {
                        let arg = self.term(scope, &args[0], Some(ty))?;
                        self.model.define_construct(context, constructor, arg)
                    } else {
                        self.model.define_constant(context, constructor)
                    }
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
                scrutinee,
                variable,
                data,
                motive,
                cases,
            } => self.rec(scope, scrutinee, variable, data, motive, cases)?,
            Expr::Equal(_, _) => return Err(Error("an identity type is not a term".to_owned())),
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
        let saved_locals = self.scopes[scope].locals.clone();
        self.scopes[scope].locals.clear();
        let mut morphism = self.weakening(definition.base, scope)?;
        let mut source = definition.base;
        for (parameter, argument) in definition.parameters.iter().zip(args) {
            let ty = self.ty(scope, &parameter.syntax)?;
            let signature_locals = self.scopes[scope].locals.clone();
            self.scopes[scope].locals = saved_locals.clone();
            let argument = self.term(scope, argument, Some(ty))?;
            self.scopes[scope].locals = signature_locals;
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
        }
        let ty = self.ty(scope, &definition.result)?;
        self.scopes[scope].locals = saved_locals;
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
        let term = self.model.new_tm(self.context(scope));
        self.model.insert_term_image(
            morphism,
            self.context(definition.end),
            definition.term,
            self.context(scope),
            term,
        );
        if let Some(base) = definition.application_base {
            let base = self.model.define_compose(base, morphism);
            self.scopes[scope].application_bases.insert(term, base);
        }
        Ok(term)
    }

    fn rec(
        &mut self,
        scope: usize,
        scrutinee: &Expr,
        variable: &str,
        data: &str,
        motive: &Expr,
        cases: &[Case],
    ) -> Result<Tm, Error> {
        let inductive = self
            .data
            .get(data)
            .cloned()
            .ok_or_else(|| Error(format!("unknown inductive {data}")))?;
        let mut seen = BTreeSet::new();
        for case in cases {
            let short = case
                .constructor
                .strip_prefix(&format!("{data}."))
                .unwrap_or(&case.constructor);
            if !seen.insert(short.to_owned()) {
                return Err(Error(format!("duplicate branch {short}")));
            }
        }
        if seen
            != inductive
                .constructors
                .iter()
                .map(|(name, _, _)| name.clone())
                .collect()
        {
            return Err(Error(format!(
                "rec {data}: branches must cover each constructor exactly once"
            )));
        }
        let scrutinee = self.term(scope, scrutinee, None)?;
        let mut captures = free_names(motive);
        captures.remove(variable);
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
        let ty = self
            .model
            .define_data_type(self.context(base_scope), inductive.data);
        self.remember_type(base_scope, ty);
        let motive_scope = self.bind(base_scope, variable, ty);
        let motive_ty = self.ty(motive_scope, motive)?;
        let result = self.model.new_tm(self.context(motive_scope));
        self.remember_term(motive_scope, result);
        let eliminator = self.model.new_eliminator();
        self.model
            .insert_elimination_base(eliminator, self.context(base_scope));
        self.model.insert_elimination(
            eliminator,
            inductive.data,
            self.context(motive_scope),
            motive_ty,
            result,
        );
        for case in cases {
            let short = case
                .constructor
                .strip_prefix(&format!("{data}."))
                .unwrap_or(&case.constructor);
            let (_, constructor, recursive) = inductive
                .constructors
                .iter()
                .find(|(name, _, _)| name == short)
                .unwrap();
            if case.variables.len() != if *recursive { 2 } else { 0 } {
                return Err(Error(format!("branch {short}: expected predecessor and induction hypothesis for a recursive constructor")));
            }
            let branch = self.model.define_case_branch(eliminator, *constructor);
            let (start, pattern) = if *recursive {
                if case.variables[0] == case.variables[1] {
                    return Err(Error(format!("branch {short}: repeated binder")));
                }
                let start = self.bind(motive_scope, &case.variables[1], motive_ty);
                let predecessor =
                    self.scopes[start].terms[&self.scopes[motive_scope].locals[variable]];
                let hypothesis = self.scopes[start].locals[&case.variables[1]];
                self.scopes[start].locals = self.environment(base_scope, start);
                self.scopes[start]
                    .locals
                    .insert(case.variables[0].clone(), predecessor);
                self.scopes[start]
                    .locals
                    .insert(case.variables[1].clone(), hypothesis);
                let pattern =
                    self.model
                        .define_construct(self.context(start), *constructor, predecessor);
                self.remember_term(start, pattern);
                (start, pattern)
            } else {
                let pattern = self
                    .model
                    .define_constant(self.context(base_scope), *constructor);
                self.remember_term(base_scope, pattern);
                (base_scope, pattern)
            };
            let base = self.weakening(base_scope, start)?;
            let instance = self.model.define_pair(
                self.context(motive_scope),
                self.context(start),
                base,
                pattern,
            );
            let saved_locals = self.scopes[start].locals.clone();
            self.scopes[start].locals = self.environment(base_scope, start);
            self.scopes[start]
                .locals
                .insert(variable.to_owned(), pattern);
            let expected = self.ty(start, motive)?;
            self.scopes[start].locals = saved_locals;
            self.model.insert_type_image(
                instance,
                self.context(motive_scope),
                motive_ty,
                self.context(start),
                expected,
            );
            let branch_scope = self.child(start, None);
            let expected = self.scopes[branch_scope].types[&expected];
            let (end, body, expected) = self.body(branch_scope, &case.body, expected)?;
            self.stage_path(start, end);
            self.model
                .insert_branch_goal(branch, self.context(end), body, expected);
            if *recursive {
                self.model.insert_recursive_case(
                    eliminator,
                    *constructor,
                    self.context(start),
                    self.context(end),
                    body,
                );
            } else {
                self.model.insert_nullary_case(
                    eliminator,
                    *constructor,
                    self.context(start),
                    self.context(end),
                    body,
                );
            }
        }
        let base = self.weakening(base_scope, scope)?;
        let application =
            self.model
                .define_application(eliminator, base, self.context(scope), scrutinee);
        let saved_locals = self.scopes[scope].locals.clone();
        self.scopes[scope].locals = self.environment(base_scope, scope);
        self.scopes[scope]
            .locals
            .insert(variable.to_owned(), scrutinee);
        let ty = self.ty(scope, motive)?;
        self.scopes[scope].locals = saved_locals;
        let instance = self.model.define_pair(
            self.context(motive_scope),
            self.context(scope),
            base,
            scrutinee,
        );
        self.model.insert_type_image(
            instance,
            self.context(motive_scope),
            motive_ty,
            self.context(scope),
            ty,
        );
        self.scopes[scope]
            .application_bases
            .insert(application, base);
        Ok(application)
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
            scrutinee,
            variable,
            data: _,
            motive,
            cases,
        } => {
            let mut names = free_names(motive);
            names.remove(variable);
            names.extend(free_names(scrutinee));
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
