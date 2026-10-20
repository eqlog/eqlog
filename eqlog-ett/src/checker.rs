use std::collections::{BTreeMap, BTreeSet};

use crate::kernel::{
    Args, Call, Constructor, Context, ContextMor, Data, Kernel, Obligation, Telescope, Tm, Ty,
};
use crate::syntax::{self, Case, ConstructorDecl, Declaration, Error, Expr, ExprKind, Location};

pub struct Checked {
    pub model: Kernel,
    pub declarations: Vec<String>,
}

pub fn check(source: &str) -> Result<Checked, Error> {
    let parsed = syntax::parse(source);
    let mut checker = Checker::new();
    let mut errors: Vec<Error> = parsed.error.into_iter().collect();
    for declaration in parsed.declarations {
        match checker.declaration(declaration) {
            Ok(()) => {}
            Err(error) => {
                errors.push(error.at(checker.declaration_location));
                break;
            }
        }
    }
    checker.model.close();
    let mut failed = BTreeSet::new();
    for (obligation, _, a, b) in checker.model.iter_types_should_be_equal() {
        if !checker.model.are_equal_ty(a, b) {
            failed.insert(obligation);
        }
    }
    for (obligation, _, x, y) in checker.model.iter_terms_should_be_equal() {
        if !checker.model.are_equal_tm(x, y) {
            failed.insert(obligation);
        }
    }
    for (obligation, _, ty, _) in checker.model.iter_reflexivity_goal() {
        let equality_type = checker
            .model
            .iter_equality()
            .any(|(_, _, _, a)| checker.model.are_equal_ty(a, ty));
        if !equality_type {
            failed.insert(obligation);
        }
    }
    errors.extend(checker.errors);
    errors.extend(
        failed
            .into_iter()
            .map(|obligation| checker.diagnostics[&obligation].clone()),
    );
    errors.sort_by_key(|error| error.location.unwrap_or_default());
    if let Some(error) = errors.into_iter().next() {
        return Err(error);
    }
    Ok(Checked {
        model: checker.model,
        declarations: checker.names,
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Value {
    Type(Ty),
    Term(Tm),
}

impl Value {
    fn term(self) -> Result<Tm, Error> {
        match self {
            Self::Term(term) => Ok(term),
            Self::Type(_) => Err(Error::new("types cannot be used as terms".to_owned())),
        }
    }

    fn ty(self) -> Result<Ty, Error> {
        match self {
            Self::Type(ty) => Ok(ty),
            Self::Term(_) => Err(Error::new("terms cannot be used as types".to_owned())),
        }
    }
}

#[derive(Clone, Copy)]
enum ParameterType {
    Type,
    Term(Ty),
}

#[derive(Clone, Copy)]
enum TypeForm {
    Abstract,
    Data,
    Equality,
}

struct Scope {
    context: Context,
    assumes_equality: bool,
    equations: BTreeSet<Ty>,
    parent: Option<(usize, ContextMor)>,
    locals: BTreeMap<String, Value>,
    // The images of the parent's elements and the scope's own elements.
    // Elements of older scopes are found through the parent chain.
    types: BTreeMap<Ty, Ty>,
    terms: BTreeMap<Tm, Tm>,
    application_bases: BTreeMap<Tm, ContextMor>,
    bases: BTreeSet<ContextMor>,
    calls: BTreeMap<Tm, Call>,
}

#[derive(Clone)]
struct Parameter {
    scope: usize,
    name: String,
    ty: ParameterType,
    syntax: Expr,
}

#[derive(Clone)]
enum Form {
    Term(Ty, Tm),
    Family(Data, Ty),
    Constructor(Constructor, Ty, Tm),
}

#[derive(Clone)]
struct Construction {
    base: usize,
    parameters: Vec<Parameter>,
    end: usize,
    result: Expr,
    application_base: Option<ContextMor>,
    call: Option<Call>,
    form: Form,
    assumptions: bool,
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
    diagnostics: BTreeMap<Obligation, Error>,
    errors: Vec<Error>,
    declaration_name: String,
    declaration_location: Location,
    names: Vec<String>,
    weakenings: BTreeMap<(usize, usize), ContextMor>,
    type_dependencies: BTreeMap<Ty, Vec<Value>>,
    term_dependencies: BTreeMap<Tm, Vec<Value>>,
    term_types: BTreeMap<Tm, Ty>,
    type_scopes: BTreeMap<Ty, usize>,
    term_scopes: BTreeMap<Tm, usize>,
    type_forms: BTreeMap<Ty, TypeForm>,
    assumption_count: usize,
}

impl Checker {
    fn new() -> Self {
        let mut model = Kernel::new();
        let context = model.define_empty();
        Self {
            model,
            scopes: vec![Scope {
                context,
                assumes_equality: false,
                equations: BTreeSet::new(),
                parent: None,
                locals: BTreeMap::new(),
                types: BTreeMap::new(),
                terms: BTreeMap::new(),
                application_bases: BTreeMap::new(),
                bases: BTreeSet::new(),
                calls: BTreeMap::new(),
            }],
            global: 0,
            data: BTreeMap::new(),
            constructors: BTreeMap::new(),
            definitions: BTreeMap::new(),
            diagnostics: BTreeMap::new(),
            errors: Vec::new(),
            declaration_name: String::new(),
            declaration_location: Location::default(),
            names: Vec::new(),
            weakenings: BTreeMap::new(),
            type_dependencies: BTreeMap::new(),
            term_dependencies: BTreeMap::new(),
            term_types: BTreeMap::new(),
            type_scopes: BTreeMap::new(),
            term_scopes: BTreeMap::new(),
            type_forms: BTreeMap::new(),
            assumption_count: 0,
        }
    }

    fn context(&self, scope: usize) -> Context {
        self.scopes[scope].context
    }

    fn environment(&self, source: usize) -> BTreeMap<String, Value> {
        self.scopes[source].locals.clone()
    }

    fn value_image(&mut self, scope: usize, value: Value) -> Value {
        match value {
            Value::Type(ty) => Value::Type(self.type_image(scope, ty)),
            Value::Term(term) => Value::Term(self.term_image(scope, term)),
        }
    }

    fn type_image(&mut self, scope: usize, ty: Ty) -> Ty {
        if let Some(&image) = self.scopes[scope].types.get(&ty) {
            return image;
        }
        let (parent, morphism) = self.scopes[scope]
            .parent
            .expect("types come from enclosing scopes");
        let source = self.type_image(parent, ty);
        if let Some(&image) = self.scopes[scope].types.get(&source) {
            self.scopes[scope].types.insert(ty, image);
            return image;
        }
        let context = self.context(scope);
        let image = self.model.new_ty(context);
        self.remember_type(scope, image);
        self.scopes[scope].types.insert(ty, image);
        self.scopes[scope].types.insert(source, image);
        let dependencies = self.type_dependencies[&source].clone();
        let images = dependencies
            .into_iter()
            .map(|value| self.value_image(scope, value))
            .collect();
        self.type_dependencies.insert(image, images);
        self.type_forms.insert(image, self.type_forms[&source]);
        self.model
            .insert_type_image(morphism, self.context(parent), source, context, image);
        let origin = self.type_scopes[&ty];
        let direct = self
            .weakening(origin, scope)
            .expect("type images follow context ancestry");
        self.model
            .insert_type_image(direct, self.context(origin), ty, context, image);
        image
    }

    fn term_image(&mut self, scope: usize, term: Tm) -> Tm {
        if let Some(&image) = self.scopes[scope].terms.get(&term) {
            return image;
        }
        let (parent, morphism) = self.scopes[scope]
            .parent
            .expect("terms come from enclosing scopes");
        let source = self.term_image(parent, term);
        if let Some(&image) = self.scopes[scope].terms.get(&source) {
            self.scopes[scope].terms.insert(term, image);
            return image;
        }
        let context = self.context(scope);
        let image = self.model.new_tm(context);
        self.remember_term(scope, image);
        self.scopes[scope].terms.insert(term, image);
        self.scopes[scope].terms.insert(source, image);
        let source_ty = self.term_types[&source];
        let ty = self.type_image(scope, source_ty);
        self.term_types.insert(image, ty);
        let dependencies = self.term_dependencies[&source].clone();
        let images = dependencies
            .into_iter()
            .map(|value| self.value_image(scope, value))
            .collect();
        self.term_dependencies.insert(image, images);
        self.model
            .insert_term_image(morphism, self.context(parent), source, context, image);
        let origin = self.term_scopes[&term];
        let direct = self
            .weakening(origin, scope)
            .expect("term images follow context ancestry");
        self.model
            .insert_term_image(direct, self.context(origin), term, context, image);
        if let Some(base) = self.scopes[origin].application_bases.get(&term).copied() {
            self.model.define_compose(base, direct);
        }
        if let Some(base) = self.scopes[parent].application_bases.get(&source).copied() {
            let base = self.model.define_compose(base, morphism);
            self.application_base(scope, image, base);
        }
        if let Some(call) = self.scopes[parent].calls.get(&source).copied() {
            let call = self.model.define_image_call(call, morphism);
            self.scopes[scope].calls.insert(image, call);
        }
        image
    }

    fn remember_type(&mut self, scope: usize, ty: Ty) -> Ty {
        self.scopes[scope].types.insert(ty, ty);
        self.type_scopes.entry(ty).or_insert(scope);
        self.type_forms.entry(ty).or_insert(TypeForm::Abstract);
        self.type_dependencies.entry(ty).or_default();
        ty
    }

    fn remember_term(&mut self, scope: usize, term: Tm) -> Tm {
        self.scopes[scope].terms.insert(term, term);
        self.term_scopes.entry(term).or_insert(scope);
        self.term_dependencies.entry(term).or_default();
        term
    }

    fn type_syntax(&mut self, scope: usize, ty: Ty, values: &[Value]) {
        let values = values
            .iter()
            .map(|value| self.value_image(scope, *value))
            .collect();
        self.type_dependencies.insert(ty, values);
    }

    fn term_syntax(&mut self, scope: usize, term: Tm, ty: Ty, values: &[Value]) {
        let values = values
            .iter()
            .map(|value| self.value_image(scope, *value))
            .collect();
        self.term_dependencies.insert(term, values);
        self.term_types.insert(term, ty);
    }

    fn may_reflect(&self, ty: Ty) -> bool {
        match self.type_forms[&ty] {
            TypeForm::Data => false,
            TypeForm::Abstract | TypeForm::Equality => true,
        }
    }

    fn assume_type(&mut self, scope: usize, term: Tm, ty: Ty) {
        self.model.insert_has_type(self.context(scope), term, ty);
        self.term_types.insert(term, ty);
        if self.may_reflect(ty) {
            self.scopes[scope].equations.insert(ty);
        }
    }

    fn assume(&mut self, scope: &mut usize) {
        *scope = self.child(*scope, None);
        self.scopes[*scope].assumes_equality = true;
        self.assumption_count += 1;
    }

    fn path_assumptions(&self, start: usize, end: usize) -> bool {
        let mut current = end;
        while current != start {
            if self.scopes[current].assumes_equality {
                return true;
            }
            current = self.scopes[current].parent.unwrap().0;
        }
        false
    }

    fn inferred_type(&mut self, scope: usize, term: Tm) -> Ty {
        let ty = self.term_types[&term];
        self.type_image(scope, ty)
    }

    fn application_base(&mut self, scope: usize, term: Tm, base: ContextMor) {
        self.scopes[scope].application_bases.insert(term, base);
        self.scopes[scope].bases.insert(base);
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

    fn child(&mut self, parent: usize, extension: Option<ParameterType>) -> usize {
        let context = self.model.new_context();
        let source = self.context(parent);
        let morphism = self.model.new_context_mor();
        if let Some(ty) = extension {
            match ty {
                ParameterType::Type => self.model.insert_type_extension(context, source, morphism),
                ParameterType::Term(ty) => {
                    self.model.insert_extension(context, source, ty, morphism)
                }
            }
        } else {
            self.model.insert_advance(source, context, morphism);
        }
        // Reflection can give an unused application the image of a referenced term.
        let bases = self.scopes[parent]
            .bases
            .iter()
            .map(|base| self.model.define_compose(*base, morphism))
            .collect();
        let equations = self.scopes[parent].equations.clone();
        let id = self.scopes.len();
        self.scopes.push(Scope {
            context,
            assumes_equality: false,
            equations: BTreeSet::new(),
            parent: Some((parent, morphism)),
            locals: self.scopes[parent].locals.clone(),
            types: BTreeMap::new(),
            terms: BTreeMap::new(),
            application_bases: BTreeMap::new(),
            bases,
            calls: BTreeMap::new(),
        });
        // Unused proofs still constrain later computations through their equality syntax.
        for equation in equations {
            let image = self.type_image(id, equation);
            self.scopes[id].equations.insert(image);
        }
        id
    }

    fn bind(&mut self, parent: usize, name: &str, ty: ParameterType) -> usize {
        let scope = self.child(parent, Some(ty));
        let value = match ty {
            ParameterType::Type => {
                let variable = self.model.define_type_variable(self.context(scope));
                Value::Type(self.remember_type(scope, variable))
            }
            ParameterType::Term(ty) => {
                let variable = self.model.define_variable(self.context(scope));
                let ty = self.type_image(scope, ty);
                self.term_types.insert(variable, ty);
                if self.may_reflect(ty) {
                    self.scopes[scope].assumes_equality = true;
                    self.scopes[scope].equations.insert(ty);
                    self.assumption_count += 1;
                }
                Value::Term(self.remember_term(scope, variable))
            }
        };
        self.scopes[scope].locals.insert(name.to_owned(), value);
        scope
    }

    fn weakening(&mut self, source: usize, target: usize) -> Result<ContextMor, Error> {
        // Defining a weakening again returns the same morphism, so walking the
        // scope chain once per pair suffices.
        if let Some(&weakening) = self.weakenings.get(&(source, target)) {
            return Ok(weakening);
        }
        let weakening = if source == target {
            self.model.define_context_mor_id(self.context(source))
        } else {
            let (parent, projection) = self.scopes[target].parent.ok_or_else(|| {
                Error::new("construction is outside its defining scope".to_owned())
            })?;
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

    fn diagnostic(&mut self, error: Error) -> Obligation {
        let obligation = self.model.new_obligation();
        self.diagnostics.insert(obligation, error);
        obligation
    }

    fn obligation(&mut self, location: Location, message: &str) -> Obligation {
        let name = &self.declaration_name;
        let location = if location.line == 0 {
            self.declaration_location
        } else {
            location
        };
        self.diagnostic(Error::new(format!("{name}: {message}")).at(location))
    }

    fn lift_morphism(
        &mut self,
        morphism: ContextMor,
        source: usize,
        target: usize,
    ) -> Result<ContextMor, Error> {
        if source == target {
            return Ok(morphism);
        }
        let weakening = self.weakening(source, target)?;
        Ok(self.model.define_compose(morphism, weakening))
    }

    fn goal(
        &mut self,
        name: String,
        scope: &mut usize,
        term: Tm,
        ty: Ty,
        location: Location,
    ) -> Tm {
        let actual = self.inferred_type(*scope, term);
        let obligation = self.diagnostic(
            Error::new(format!(
                "{name}: type checking did not establish the declared type (beta budget: 3)"
            ))
            .at(location),
        );
        self.model
            .insert_types_should_be_equal(obligation, self.context(*scope), actual, ty);
        if self.may_reflect(ty) {
            self.assume(scope);
        }
        let term = self.term_image(*scope, term);
        let ty = self.type_image(*scope, ty);
        self.assume_type(*scope, term, ty);
        term
    }

    fn args(&mut self, scope: usize, values: &[Value]) -> Args {
        let context = self.context(scope);
        let mut args = self.model.define_nil_args(context);
        for value in values.iter().rev() {
            let value = self.value_image(scope, *value);
            args = match value {
                Value::Type(ty) => self.model.define_cons_type_args(context, ty, args),
                Value::Term(term) => self.model.define_cons_args(context, term, args),
            };
        }
        args
    }

    fn parameter_type(&mut self, scope: &mut usize, syntax: &Expr) -> Result<ParameterType, Error> {
        if *syntax == named("Type") {
            Ok(ParameterType::Type)
        } else {
            Ok(ParameterType::Term(self.ty(scope, syntax)?))
        }
    }

    fn argument(
        &mut self,
        scope: &mut usize,
        expr: &Expr,
        ty: ParameterType,
    ) -> Result<Value, Error> {
        match ty {
            ParameterType::Type => Ok(Value::Type(self.ty(scope, expr)?)),
            ParameterType::Term(ty) => Ok(Value::Term(self.term(scope, expr, Some(ty))?)),
        }
    }

    fn parameters(
        &mut self,
        base: usize,
        binders: &[(String, Expr)],
        type_parameter_limit: usize,
        family: Option<&str>,
    ) -> Result<(usize, Vec<Parameter>), Error> {
        let mut scope = base;
        let mut parameters = Vec::new();
        for (index, (name, syntax)) in binders.iter().enumerate() {
            if name == "Type" {
                return Err(Error::new("Type is reserved".to_owned()).at(syntax.location));
            }
            if family == Some(name.as_str()) {
                return Err(Error::new(format!(
                    "{name}: binders cannot shadow the family being declared"
                ))
                .at(syntax.location));
            }
            if index >= type_parameter_limit && *syntax == named("Type") {
                return Err(Error::new("Type is only allowed for uniform type parameters, not indices or constructor fields".to_owned()).at(syntax.location));
            }
            if parameters.iter().any(|p: &Parameter| p.name == *name) {
                return Err(Error::new(format!("repeated parameter {name}")).at(syntax.location));
            }
            let ty = self.parameter_type(&mut scope, syntax)?;
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
                location,
                name,
                parameters,
                indices,
                constructors,
            } => {
                self.declaration_name = name.clone();
                self.declaration_location = location;
                self.inductive(name, parameters, indices, constructors)
                    .map_err(|error| error.at(location))
            }
            Declaration::Definition {
                location,
                name,
                parameters,
                result,
                body,
            } => {
                self.declaration_name = name.clone();
                self.declaration_location = location;
                self.fresh_name(&name)?;
                let base = self.child(self.global, None);
                self.global = base;
                let (mut scope, parameters) =
                    self.parameters(base, &parameters, parameters.len(), None)?;
                let assumptions = self.assumption_count;
                let ty = self.ty(&mut scope, &result)?;
                let (mut end, term, ty) = self.body(scope, &body, ty)?;
                let assumptions = self.assumption_count != assumptions;
                let term = self.goal(name.clone(), &mut end, term, ty, body.location);
                let ty = self.type_image(end, ty);
                let application_base = self.scopes[end].application_bases.get(&term).copied();
                self.definitions.insert(
                    name.clone(),
                    Construction {
                        base,
                        parameters,
                        end,
                        result,
                        application_base,
                        call: self.scopes[end].calls.get(&term).copied(),
                        form: Form::Term(ty, term),
                        assumptions,
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
        let base = self.child(self.global, None);
        self.global = base;
        let data = self.model.new_data();
        let all_binders: Vec<_> = parameters.iter().chain(&indices).cloned().collect();
        let (end, telescope) =
            self.parameters(base, &all_binders, parameters.len(), Some(&name))?;
        let values: Vec<_> = all_binders
            .iter()
            .map(|(n, _)| self.scopes[end].locals[n])
            .collect();
        let args = self.args(end, &values);
        let family = self.model.define_data_type(self.context(end), data, args);
        self.remember_type(end, family);
        self.type_syntax(end, family, &values);
        self.type_forms.insert(family, TypeForm::Data);
        let signature = Construction {
            base,
            parameters: telescope,
            end,
            result: named("Type"),
            application_base: None,
            call: None,
            form: Form::Family(data, family),
            assumptions: false,
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
            self.fresh_name(&full)
                .map_err(|error| error.at(constructor.location))?;
            let result = constructor.result.unwrap_or_else(|| Expr {
                kind: ExprKind::Name(name.clone(), uniform.clone()),
                location: constructor.end,
                end: constructor.end,
            });
            let result_args = match family_arguments(&result, &name, &uniform, indices.len()) {
                Ok(args) => args,
                Err(error) => {
                    self.errors.push(error.at(result.location));
                    Vec::new()
                }
            };
            let mut recursive = Vec::new();
            for (_, field) in &constructor.fields {
                if free_names(field).contains(&name) {
                    match family_arguments(field, &name, &uniform, indices.len()) {
                        Ok(args) => recursive.push(Some(args)),
                        Err(error) => {
                            self.errors.push(error.at(field.location));
                            recursive.push(None);
                        }
                    }
                } else {
                    recursive.push(None);
                }
            }
            let all_fields: Vec<_> = parameters
                .iter()
                .chain(&constructor.fields)
                .cloned()
                .collect();
            let (mut end, telescope) =
                self.parameters(base, &all_fields, parameters.len(), Some(&name))?;
            let assumptions = self.assumption_count;
            let ty = self.ty(&mut end, &result)?;
            let c = self.model.new_constructor();
            let values: Vec<_> = all_fields
                .iter()
                .map(|(n, _)| self.scopes[end].locals[n])
                .collect();
            let args = self.args(end, &values);
            let term = self.model.define_construct(self.context(end), c, args);
            self.model.insert_has_type(self.context(end), term, ty);
            self.term_syntax(end, term, ty, &values);
            let term = self.remember_term(end, term);
            let signature = Construction {
                base,
                parameters: telescope,
                end,
                result,
                application_base: None,
                call: None,
                form: Form::Constructor(c, ty, term),
                assumptions: self.assumption_count != assumptions,
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
        self.data.get_mut(&name).unwrap().constructors = checked;
        self.names.push(name);
        Ok(())
    }

    fn fresh_name(&self, name: &str) -> Result<(), Error> {
        if name == "Type" {
            return Err(Error::new("Type is reserved".to_owned()));
        }
        if self.data.contains_key(name)
            || self.constructors.contains_key(name)
            || self.definitions.contains_key(name)
        {
            return Err(Error::new(format!("duplicate declaration {name}")));
        }
        Ok(())
    }

    fn ty(&mut self, scope: &mut usize, expr: &Expr) -> Result<Ty, Error> {
        self.ty_inner(scope, expr)
            .map_err(|error| error.at(expr.location))
    }

    fn ty_inner(&mut self, scope: &mut usize, expr: &Expr) -> Result<Ty, Error> {
        let ty = match &expr.kind {
            ExprKind::Name(name, args) => {
                if let Some(&local) = self.scopes[*scope].locals.get(name) {
                    if !args.is_empty() {
                        return Err(Error::new(format!("local type {name} cannot be applied")));
                    }
                    self.value_image(*scope, local).ty()?
                } else if let Some(data) = self.data.get(name).cloned() {
                    self.apply(scope, name, &data.signature, args, expr.location)?
                        .ty()?
                } else if name == "Type" {
                    return Err(Error::new(
                        "Type is only a marker for fresh type parameters".to_owned(),
                    ));
                } else {
                    return Err(Error::new(format!("unknown type {name}")));
                }
            }
            ExprKind::Equal(lhs, rhs) => {
                let lhs = self.term(scope, lhs, None)?;
                let rhs = self.term(scope, rhs, None)?;
                let lhs = self.term_image(*scope, lhs);
                let a = self.inferred_type(*scope, lhs);
                let b = self.inferred_type(*scope, rhs);
                let obligation =
                    self.obligation(expr.location, "equality endpoints have incompatible types");
                self.model
                    .insert_types_should_be_equal(obligation, self.context(*scope), a, b);
                let ty = self.model.define_equality(self.context(*scope), lhs, rhs);
                self.type_syntax(*scope, ty, &[Value::Term(lhs), Value::Term(rhs)]);
                self.type_forms.insert(ty, TypeForm::Equality);
                ty
            }
            ExprKind::Refl | ExprKind::Rec { .. } | ExprKind::Let(_, _, _, _) => {
                return Err(Error::new("expected a type".to_owned()));
            }
        };
        Ok(self.remember_type(*scope, ty))
    }

    fn term(&mut self, scope: &mut usize, expr: &Expr, expected: Option<Ty>) -> Result<Tm, Error> {
        self.term_inner(scope, expr, expected)
            .map_err(|error| error.at(expr.location))
    }

    fn term_inner(
        &mut self,
        scope: &mut usize,
        expr: &Expr,
        expected: Option<Ty>,
    ) -> Result<Tm, Error> {
        let term = match &expr.kind {
            ExprKind::Name(name, args) => {
                if let Some(&local) = self.scopes[*scope].locals.get(name) {
                    if !args.is_empty() {
                        return Err(Error::new(format!(
                            "local variable {name} cannot be applied"
                        )));
                    }
                    self.value_image(*scope, local).term()?
                } else if name == "Type" || self.data.contains_key(name) {
                    return Err(Error::new("types cannot be used as terms".to_owned()));
                } else if let Some(constructor) = self.constructors.get(name).cloned() {
                    self.apply(scope, name, &constructor.signature, args, expr.location)?
                        .term()?
                } else if let Some(definition) = self.definitions.get(name).cloned() {
                    self.apply(scope, name, &definition, args, expr.location)?
                        .term()?
                } else {
                    return Err(Error::new(format!("unknown term {name}")));
                }
            }
            ExprKind::Refl => {
                let ty = expected
                    .ok_or_else(|| Error::new("rfl needs an expected equality type".to_owned()))?;
                let ty = self.type_image(*scope, ty);
                let context = self.context(*scope);
                let term = self.model.new_tm(context);
                self.remember_term(*scope, term);
                self.term_types.insert(term, ty);
                let obligation = self.obligation(
                    expr.location,
                    "reflexivity requires equal endpoints (beta budget: 3)",
                );
                self.model
                    .insert_reflexivity_goal(obligation, context, ty, term);
                if self.may_reflect(ty) {
                    self.assume(scope);
                }
                let term = self.term_image(*scope, term);
                let ty = self.type_image(*scope, ty);
                self.assume_type(*scope, term, ty);
                term
            }
            ExprKind::Rec {
                arguments,
                binders,
                motive,
                cases,
            } => self.rec(
                scope,
                arguments,
                binders,
                motive,
                cases,
                expr.location,
                expr.end,
            )?,
            ExprKind::Equal(_, _) => {
                return Err(Error::new("types cannot be used as terms".to_owned()));
            }
            ExprKind::Let(_, _, _, _) => {
                return Err(Error::new(
                    "put let statements at the start of a declaration or branch body".to_owned(),
                ))
            }
        };
        self.remember_term(*scope, term);
        self.literal(*scope, term);
        Ok(term)
    }

    fn apply(
        &mut self,
        scope: &mut usize,
        name: &str,
        definition: &Construction,
        args: &[Expr],
        location: Location,
    ) -> Result<Value, Error> {
        if args.len() != definition.parameters.len() {
            return Err(Error::new(format!("wrong number of arguments to {name}")));
        }
        let entry = *scope;
        let saved = self.scopes[*scope].locals.clone();
        self.scopes[*scope].locals = self.environment(definition.base);
        let mut morphism = self.weakening(definition.base, *scope)?;
        let mut source = definition.base;
        let mut values = Vec::new();
        for (parameter, argument) in definition.parameters.iter().zip(args) {
            let previous = *scope;
            let ty = self.parameter_type(scope, &parameter.syntax.relocated(location))?;
            let signature = self.scopes[*scope].locals.clone();
            self.restore_environment(entry, *scope, &saved);
            let value = self.argument(scope, argument, ty)?;
            self.scopes[*scope].locals = signature.clone();
            morphism = self.lift_morphism(morphism, previous, *scope)?;
            morphism = self.pair_parameter(
                scope,
                source,
                parameter,
                morphism,
                ty,
                value,
                if argument.location.line == 0 {
                    location
                } else {
                    argument.location
                },
            )?;
            source = parameter.scope;
            let value = self.value_image(*scope, value);
            self.scopes[*scope]
                .locals
                .insert(parameter.name.clone(), value);
            values.push(value);
        }
        let previous = *scope;
        let value = match definition.form {
            Form::Family(data, source_ty) => {
                if definition.assumptions {
                    self.assume(scope);
                    morphism = self.lift_morphism(morphism, previous, *scope)?;
                }
                let args = self.args(*scope, &values);
                let target_ty = self
                    .model
                    .define_data_type(self.context(*scope), data, args);
                self.remember_type(*scope, target_ty);
                self.type_syntax(*scope, target_ty, &values);
                self.type_forms.insert(target_ty, TypeForm::Data);
                self.stage_path(source, definition.end);
                morphism = self.model.define_through(
                    self.context(source),
                    self.context(definition.end),
                    self.context(*scope),
                    morphism,
                );
                self.model.insert_type_image(
                    morphism,
                    self.context(definition.end),
                    source_ty,
                    self.context(*scope),
                    target_ty,
                );
                Value::Type(target_ty)
            }
            Form::Term(source_ty, source_term) | Form::Constructor(_, source_ty, source_term) => {
                let ty = self.ty(scope, &definition.result.relocated(location))?;
                if definition.assumptions || self.may_reflect(ty) {
                    self.assume(scope);
                }
                let ty = self.type_image(*scope, ty);
                morphism = self.lift_morphism(morphism, previous, *scope)?;
                self.stage_path(source, definition.end);
                morphism = self.model.define_through(
                    self.context(source),
                    self.context(definition.end),
                    self.context(*scope),
                    morphism,
                );
                let context = self.context(*scope);
                self.model.insert_type_image(
                    morphism,
                    self.context(definition.end),
                    source_ty,
                    context,
                    ty,
                );
                let args = self.args(*scope, &values);
                let term = match definition.form {
                    Form::Term(_, _) => self.model.define_instance(
                        self.context(definition.end),
                        source_term,
                        context,
                        args,
                    ),
                    Form::Constructor(constructor, _, _) => {
                        self.model.define_construct(context, constructor, args)
                    }
                    Form::Family(_, _) => unreachable!(),
                };
                self.model.insert_term_image(
                    morphism,
                    self.context(definition.end),
                    source_term,
                    context,
                    term,
                );
                self.assume_type(*scope, term, ty);
                self.term_syntax(*scope, term, ty, &values);
                if let Some(base) = definition.application_base {
                    let base = self.model.define_compose(base, morphism);
                    self.application_base(*scope, term, base);
                }
                self.remember_term(*scope, term);
                if let Some(call) = definition.call {
                    let call = self.model.define_image_call(call, morphism);
                    self.scopes[*scope].calls.insert(term, call);
                }
                Value::Term(term)
            }
        };
        let bases: Vec<_> = self.scopes[definition.end].bases.iter().copied().collect();
        for base in bases {
            let base = self.model.define_compose(base, morphism);
            self.scopes[*scope].bases.insert(base);
        }
        self.restore_environment(entry, *scope, &saved);
        Ok(value)
    }

    fn pair_parameter(
        &mut self,
        scope: &mut usize,
        source: usize,
        parameter: &Parameter,
        morphism: ContextMor,
        ty: ParameterType,
        value: Value,
        location: Location,
    ) -> Result<ContextMor, Error> {
        match ty {
            ParameterType::Type => {}
            ParameterType::Term(ty) => {
                let ty = self.type_image(*scope, ty);
                let term = self.value_image(*scope, value).term()?;
                let actual = self.inferred_type(*scope, term);
                let obligation =
                    self.obligation(location, "argument does not have the parameter type");
                self.model.insert_types_should_be_equal(
                    obligation,
                    self.context(*scope),
                    actual,
                    ty,
                );
            }
        }
        let parent = self.scopes[parameter.scope].parent.unwrap().0;
        let reflect = match ty {
            ParameterType::Type => false,
            ParameterType::Term(ty) => self.may_reflect(ty),
        };
        let previous = *scope;
        if reflect || self.path_assumptions(source, parent) {
            self.assume(scope);
        }
        let morphism = self.lift_morphism(morphism, previous, *scope)?;
        self.stage_path(source, parent);
        let morphism = self.model.define_through(
            self.context(source),
            self.context(parent),
            self.context(*scope),
            morphism,
        );
        let extension = self.context(parameter.scope);
        let value = self.value_image(*scope, value);
        match parameter.ty {
            ParameterType::Type => Ok(self.model.define_pair_type(
                extension,
                self.context(*scope),
                morphism,
                value.ty()?,
            )),
            ParameterType::Term(source_ty) => {
                let ty = match ty {
                    ParameterType::Term(ty) => self.type_image(*scope, ty),
                    ParameterType::Type => unreachable!(),
                };
                self.model.insert_type_image(
                    morphism,
                    self.context(parent),
                    source_ty,
                    self.context(*scope),
                    ty,
                );
                if self.may_reflect(ty) {
                    self.scopes[*scope].equations.insert(ty);
                }
                Ok(self
                    .model
                    .define_pair(extension, self.context(*scope), morphism, value.term()?))
            }
        }
    }

    fn motive_instance(
        &mut self,
        scope: &mut usize,
        motive: &Construction,
        values: &[Value],
        location: Location,
    ) -> Result<(ContextMor, Ty), Error> {
        let entry = *scope;
        let saved = self.scopes[*scope].locals.clone();
        self.scopes[*scope].locals = self.environment(motive.base);
        let mut morphism = self.weakening(motive.base, *scope)?;
        let mut source = motive.base;
        for (parameter, value) in motive.parameters.iter().zip(values) {
            let previous = *scope;
            let ty = self.parameter_type(scope, &parameter.syntax.relocated(location))?;
            morphism = self.lift_morphism(morphism, previous, *scope)?;
            morphism =
                self.pair_parameter(scope, source, parameter, morphism, ty, *value, location)?;
            let value = self.value_image(*scope, *value);
            self.scopes[*scope]
                .locals
                .insert(parameter.name.clone(), value);
            source = parameter.scope;
        }
        let previous = *scope;
        let ty = self.ty(scope, &motive.result.relocated(location))?;
        if self.path_assumptions(source, motive.end) {
            self.assume(scope);
        }
        let ty = self.type_image(*scope, ty);
        morphism = self.lift_morphism(morphism, previous, *scope)?;
        self.stage_path(source, motive.end);
        morphism = self.model.define_through(
            self.context(source),
            self.context(motive.end),
            self.context(*scope),
            morphism,
        );
        self.model.insert_type_image(
            morphism,
            self.context(motive.end),
            match motive.form {
                Form::Term(ty, _) => ty,
                Form::Family(_, _) | Form::Constructor(_, _, _) => unreachable!(),
            },
            self.context(*scope),
            ty,
        );
        self.restore_environment(entry, *scope, &saved);
        Ok((morphism, ty))
    }

    fn telescope(&mut self, base: usize, end: usize, parameters: &[Parameter]) -> Telescope {
        let mut previous = base;
        for parameter in parameters {
            let parent = self.scopes[parameter.scope].parent.unwrap().0;
            self.stage_path(previous, parent);
            previous = parameter.scope;
        }
        self.stage_path(previous, end);
        let mut telescope = self.model.define_telescope_end(self.context(end));
        for parameter in parameters.iter().rev() {
            telescope = self
                .model
                .define_telescope_cons(self.context(parameter.scope), telescope);
        }
        telescope
    }

    fn body(
        &mut self,
        mut scope: usize,
        expr: &Expr,
        expected: Ty,
    ) -> Result<(usize, Tm, Ty), Error> {
        match &expr.kind {
            ExprKind::Let(name, annotation, value, rest) => {
                if name == "Type" {
                    return Err(Error::new("Type is reserved".to_owned()).at(expr.location));
                }
                let ty = self.ty(&mut scope, annotation)?;
                let (mut scope, term, ty) = self.body(scope, value, ty)?;
                let term = self.goal(format!("let {name}"), &mut scope, term, ty, value.location);
                self.scopes[scope]
                    .locals
                    .insert(name.clone(), Value::Term(term));
                let expected = self.type_image(scope, expected);
                self.body(scope, rest, expected)
            }
            ExprKind::Name(_, _)
            | ExprKind::Equal(_, _)
            | ExprKind::Refl
            | ExprKind::Rec { .. } => {
                let term = self.term(&mut scope, expr, Some(expected))?;
                let expected = self.type_image(scope, expected);
                Ok((scope, term, expected))
            }
        }
    }

    fn rec(
        &mut self,
        scope: &mut usize,
        arguments: &[Expr],
        binders: &[(String, Expr)],
        motive: &Expr,
        cases: &[Case],
        location: Location,
        end_location: Location,
    ) -> Result<Tm, Error> {
        let assumptions = self.assumption_count;
        let (_, scrutinee_type) = binders.last().unwrap();
        let (data_name, family_args) = match &scrutinee_type.kind {
            ExprKind::Name(name, args) => (name, args),
            ExprKind::Equal(_, _)
            | ExprKind::Refl
            | ExprKind::Rec { .. }
            | ExprKind::Let(_, _, _, _) => {
                return Err(Error::new(
                    "the last motive binder must have an inductive type".to_owned(),
                ));
            }
        };
        let inductive = self
            .data
            .get(data_name)
            .cloned()
            .ok_or_else(|| Error::new(format!("unknown inductive {data_name}")))?;
        if self.scopes[*scope].locals.contains_key(data_name)
            || binders.iter().any(|(name, _)| name == data_name)
        {
            return Err(Error::new(format!(
                "rec {data_name}: inductive name is shadowed by a local binder"
            )));
        }
        if arguments.len() != binders.len()
            || binders.len() != inductive.indices.len() + 1
            || family_args.len() != inductive.parameter_count + inductive.indices.len()
        {
            return Err(Error::new(format!(
                "rec {data_name}: supply every index followed by the scrutinee"
            )));
        }
        let binder_names: BTreeSet<_> = binders.iter().map(|(name, _)| name.clone()).collect();
        if binder_names.contains("Type") {
            return Err(Error::new("Type is reserved".to_owned()));
        }
        if binder_names.len() != binders.len() {
            return Err(Error::new("repeated motive binder".to_owned()));
        }
        for (index, (name, _)) in family_args[inductive.parameter_count..].iter().zip(binders) {
            if *index != named(name) {
                return Err(Error::new(
                    "motive indices must be its index binders in declaration order".to_owned(),
                ));
            }
        }
        let uniform_exprs = &family_args[..inductive.parameter_count];
        if uniform_exprs
            .iter()
            .any(|expr| !free_names(expr).is_disjoint(&binder_names))
        {
            return Err(Error::new(
                "uniform parameters cannot depend on motive indices".to_owned(),
            ));
        }
        let mut seen = BTreeSet::new();
        let mut case_error = None;
        for case in cases {
            let short = case
                .constructor
                .strip_prefix(&format!("{data_name}."))
                .unwrap_or(&case.constructor);
            if !inductive
                .constructors
                .iter()
                .any(|constructor| constructor.name == short)
            {
                case_error.get_or_insert_with(|| {
                    Error::new(format!("unknown branch {short}")).at(case.location)
                });
            }
            if !seen.insert(short.to_owned()) {
                case_error.get_or_insert_with(|| {
                    Error::new(format!("duplicate branch {short}")).at(case.location)
                });
            }
        }
        if seen
            != inductive
                .constructors
                .iter()
                .map(|c| c.name.clone())
                .collect()
        {
            let end = end_location;
            case_error.get_or_insert_with(|| {
                Error::new(format!(
                    "rec {data_name}: branches must cover each constructor exactly once"
                ))
                .at(end)
            });
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
        let mut base_scope = *scope;
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
                            .map(|&old| old == *term)
                            .unwrap_or(false)
                    })
                    .unwrap_or(true)
            });
            if !can_drop {
                break;
            }
            base_scope = parent;
        }
        let capture = base_scope;
        let mut uniforms = Vec::new();
        let saved = self.scopes[base_scope].locals.clone();
        let mut formal = self.environment(inductive.signature.base);
        for (expr, parameter) in uniform_exprs.iter().zip(&inductive.signature.parameters) {
            self.scopes[base_scope].locals = formal.clone();
            let ty =
                self.parameter_type(&mut base_scope, &parameter.syntax.relocated(expr.location))?;
            self.restore_environment(capture, base_scope, &saved);
            let value = self.argument(&mut base_scope, expr, ty)?;
            formal.insert(parameter.name.clone(), value);
            uniforms.push(value);
        }
        let mut current = base_scope;
        let mut parameters = Vec::new();
        for (i, (name, annotation)) in binders.iter().enumerate() {
            let ty = self.ty(&mut current, annotation)?;
            if i < inductive.indices.len() {
                let previous = current;
                let saved = self.scopes[current].locals.clone();
                self.scopes[current].locals = formal.clone();
                let canonical = self.ty(&mut current, &inductive.indices[i].1)?;
                self.restore_environment(previous, current, &saved);
                let ty = self.type_image(current, ty);
                let obligation =
                    self.obligation(annotation.location, "incompatible index binder type");
                self.model.insert_types_should_be_equal(
                    obligation,
                    self.context(current),
                    ty,
                    canonical,
                );
            }
            let ty = self.type_image(current, ty);
            current = self.bind(current, name, ParameterType::Term(ty));
            if i < inductive.indices.len() {
                formal.insert(
                    inductive.indices[i].0.clone(),
                    self.scopes[current].locals[name],
                );
            }
            parameters.push(Parameter {
                scope: current,
                name: name.clone(),
                ty: ParameterType::Term(ty),
                syntax: annotation.clone(),
            });
        }
        let motive_ty = self.ty(&mut current, motive)?;
        let result = self.model.new_tm(self.context(current));
        self.remember_term(current, result);
        self.term_types.insert(result, motive_ty);
        let motive = Construction {
            base: capture,
            parameters,
            end: current,
            result: motive.clone(),
            application_base: None,
            call: None,
            form: Form::Term(motive_ty, result),
            assumptions: false,
        };
        let eliminator = self.model.new_eliminator();
        let telescope = self.telescope(capture, current, &motive.parameters);
        self.model
            .insert_elimination_base(eliminator, self.context(capture));
        self.model
            .insert_elimination_telescope(eliminator, telescope);
        self.model
            .insert_elimination_template(eliminator, self.context(current));

        let entry = *scope;
        let saved = self.scopes[*scope].locals.clone();
        let mut signature_env = self.environment(capture);
        let mut values = Vec::new();
        for (argument, parameter) in arguments.iter().zip(&motive.parameters) {
            self.scopes[*scope].locals = signature_env.clone();
            let expected = self.ty(scope, &parameter.syntax.relocated(argument.location))?;
            signature_env = self.scopes[*scope].locals.clone();
            self.restore_environment(entry, *scope, &saved);
            let value = Value::Term(self.term(scope, argument, Some(expected))?);
            signature_env.insert(parameter.name.clone(), value);
            values.push(value);
        }
        self.restore_environment(entry, *scope, &saved);
        let (_, result_ty) = self.motive_instance(scope, &motive, &values, location)?;
        if let Some(error) = case_error {
            self.errors.push(error);
        }

        let mut visited = BTreeSet::new();
        for case in cases {
            let short = case
                .constructor
                .strip_prefix(&format!("{data_name}."))
                .unwrap_or(&case.constructor);
            let Some(constructor) = inductive.constructors.iter().find(|c| c.name == short) else {
                continue;
            };
            if !visited.insert(short) {
                continue;
            }
            if case.variables.iter().any(|name| name == "Type") {
                return Err(Error::new("Type is reserved".to_owned()).at(case.location));
            }
            let count = constructor.fields.len()
                + constructor.recursive.iter().filter(|r| r.is_some()).count();
            if case.variables.len() != count
                || case.variables.iter().collect::<BTreeSet<_>>().len() != count
            {
                return Err(Error::new(format!("branch {short}: expected {count} distinct field and induction-hypothesis binders")).at(case.location));
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
            self.plan_advance(&mut steps, capture, base_scope);
            for value in &uniforms {
                steps.push(Plan::Parameter(
                    self.context(base_scope),
                    self.value_image(base_scope, *value),
                ));
            }
            let mut variables = case.variables.iter();
            for ((field, syntax), recursive) in
                constructor.fields.iter().zip(&constructor.recursive)
            {
                let previous = start;
                let saved = self.scopes[start].locals.clone();
                self.scopes[start].locals = field_env.clone();
                let ty = self.ty(&mut start, &syntax.relocated(case.location))?;
                self.plan_advance(&mut steps, previous, start);
                self.restore_environment(previous, start, &saved);
                let alias = variables.next().unwrap();
                start = self.bind(start, alias, ParameterType::Term(ty));
                steps.push(Plan::Field(self.context(start)));
                let value = self.scopes[start].locals[alias];
                field_env.insert(field.clone(), value);
                body_env.insert(alias.clone(), value);
                if let Some(indices) = recursive {
                    let previous = start;
                    let mut values = self.evaluate_in(&mut start, &field_env, indices)?;
                    values.push(value);
                    let (instance, ih_ty) =
                        self.motive_instance(&mut start, &motive, &values, case.location)?;
                    self.plan_advance(&mut steps, previous, start);
                    let args = self.args(start, &values);
                    let source = self.context(start);
                    let alias = variables.next().unwrap();
                    start = self.bind(start, alias, ParameterType::Term(ih_ty));
                    steps.push(Plan::Hypothesis(
                        source,
                        args,
                        self.context(start),
                        instance,
                    ));
                    body_env.insert(alias.clone(), self.scopes[start].locals[alias]);
                }
            }
            let previous = start;
            let saved = self.scopes[start].locals.clone();
            self.scopes[start].locals = field_env.clone();
            let ctor_args: Vec<_> = constructor
                .signature
                .parameters
                .iter()
                .map(|p| named(&p.name))
                .collect();
            let pattern = self
                .apply(
                    &mut start,
                    &constructor.name,
                    &constructor.signature,
                    &ctor_args,
                    case.location,
                )?
                .term()?;
            self.remember_term(start, pattern);
            self.restore_environment(previous, start, &saved);
            let mut indices =
                self.evaluate_in(&mut start, &field_env, &constructor.result_indices)?;
            indices.push(Value::Term(pattern));
            let (_, expected) =
                self.motive_instance(&mut start, &motive, &indices, case.location)?;
            self.plan_advance(&mut steps, previous, start);
            let expected_args = self.args(start, &indices);
            let branch_scope = self.child(start, None);
            self.scopes[branch_scope].locals = body_env.clone();
            let expected = self.type_image(branch_scope, expected);
            let (mut end, body, expected) = self.body(branch_scope, &case.body, expected)?;
            let body = self.goal(
                format!("{} branch {short}", self.declaration_name),
                &mut end,
                body,
                expected,
                case.body.location,
            );
            self.stage_path(start, end);
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
            for base in &self.scopes[end].bases {
                self.model.insert_body_base(plan, *base);
            }
            for step in steps.into_iter().rev() {
                let next = self.model.new_branch_steps();
                match step {
                    Plan::Parameter(context, value) => match value {
                        Value::Type(ty) => self
                            .model
                            .insert_type_parameter_step(next, context, ty, plan),
                        Value::Term(term) => {
                            self.model.insert_parameter_step(next, context, term, plan)
                        }
                    },
                    Plan::Advance(start, end) => {
                        self.model.insert_scope_step(next, start, end, plan)
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
        let result_scope = self.child(current, None);
        let result = self.term_image(result_scope, result);
        let motive_ty = self.type_image(result_scope, motive_ty);
        self.model.insert_elimination(
            eliminator,
            inductive.data,
            self.context(result_scope),
            motive_ty,
            result,
        );

        if self.assumption_count != assumptions || self.may_reflect(result_ty) {
            self.assume(scope);
        }
        let result_ty = self.type_image(*scope, result_ty);
        let args = self.args(*scope, &values);
        let base = self.weakening(capture, *scope)?;
        let application =
            self.model
                .define_application(eliminator, base, self.context(*scope), args);
        self.assume_type(*scope, application, result_ty);
        self.remember_term(*scope, application);
        self.term_syntax(*scope, application, result_ty, &values);
        self.application_base(*scope, application, base);
        let call = self
            .model
            .define_direct_call(eliminator, base, self.context(*scope), args);
        self.scopes[*scope].calls.insert(application, call);
        Ok(application)
    }

    fn plan_advance(&mut self, steps: &mut Vec<Plan>, start: usize, end: usize) {
        if start != end {
            self.stage_path(start, end);
            steps.push(Plan::Advance(self.context(start), self.context(end)));
        }
    }

    fn restore_environment(
        &mut self,
        start: usize,
        end: usize,
        environment: &BTreeMap<String, Value>,
    ) {
        let mut current = end;
        loop {
            self.scopes[current].locals = environment.clone();
            if current == start {
                break;
            }
            current = self.scopes[current].parent.unwrap().0;
        }
    }

    fn evaluate_in(
        &mut self,
        scope: &mut usize,
        environment: &BTreeMap<String, Value>,
        expressions: &[Expr],
    ) -> Result<Vec<Value>, Error> {
        let entry = *scope;
        let saved = self.scopes[*scope].locals.clone();
        self.scopes[*scope].locals = environment.clone();
        let values = expressions
            .iter()
            .map(|e| self.term(scope, e, None).map(Value::Term))
            .collect();
        self.restore_environment(entry, *scope, &saved);
        values
    }
}

enum Plan {
    Advance(Context, Context),
    Parameter(Context, Value),
    Field(Context),
    Hypothesis(Context, Args, Context, ContextMor),
}

fn named(name: &str) -> Expr {
    Expr {
        kind: ExprKind::Name(name.to_owned(), Vec::new()),
        location: Location::default(),
        end: Location::default(),
    }
}

fn family_arguments(
    expr: &Expr,
    family: &str,
    uniform: &[Expr],
    indices: usize,
) -> Result<Vec<Expr>, Error> {
    match &expr.kind {
        ExprKind::Name(name, args) => {
            if name != family
                || args.len() != uniform.len() + indices
                || args[..uniform.len()] != *uniform
                || args.iter().any(|arg| free_names(arg).contains(family))
            {
                return Err(Error::new(format!("{family}: recursive fields and constructor results must apply the family directly with unchanged parameters")));
            }
            Ok(args[uniform.len()..].to_vec())
        }
        ExprKind::Equal(_, _)
        | ExprKind::Refl
        | ExprKind::Rec { .. }
        | ExprKind::Let(_, _, _, _) => Err(Error::new(format!(
            "{family}: only direct strictly positive recursive fields are supported"
        ))),
    }
}

fn free_names(expr: &Expr) -> BTreeSet<String> {
    match &expr.kind {
        ExprKind::Name(name, args) => {
            let mut names = BTreeSet::from([name.clone()]);
            for arg in args {
                names.extend(free_names(arg));
            }
            names
        }
        ExprKind::Equal(lhs, rhs) => {
            let mut names = free_names(lhs);
            names.extend(free_names(rhs));
            names
        }
        ExprKind::Refl => BTreeSet::new(),
        ExprKind::Rec {
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
        ExprKind::Let(name, ty, value, body) => {
            let mut names = free_names(body);
            names.remove(name);
            names.extend(free_names(ty));
            names.extend(free_names(value));
            names
        }
    }
}
