use crate::ast::*;
use crate::error::*;
use crate::unification::*;
use convert_case::{Case, Casing};
use std::collections::{HashMap, HashSet};
use std::iter::once;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Symbol {
    Sort(Sort),
    Predicate(Predicate),
    Function(Function),
    Query {
        ast: UserQuery,
        term_sorts: TermMap<String>,
    },
}

impl Symbol {
    pub fn kind(&self) -> SymbolKind {
        match self {
            Symbol::Sort(_) => SymbolKind::Sort,
            Symbol::Predicate(_) => SymbolKind::Predicate,
            Symbol::Function(_) => SymbolKind::Function,
            Symbol::Query { .. } => SymbolKind::Query,
        }
    }
    pub fn name(&self) -> &str {
        use Symbol::*;
        match self {
            Sort(s) => &s.name,
            Predicate(p) => &p.name,
            Function(f) => &f.name,
            Query { ast, .. } => &ast.name,
        }
    }
    pub fn location(&self) -> Option<Location> {
        match self {
            Symbol::Sort(Sort { location, .. }) => *location,
            Symbol::Predicate(Predicate { location, .. }) => *location,
            Symbol::Function(Function { location, .. }) => *location,
            Symbol::Query { ast, .. } => ast.location,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Module {
    symbols: HashMap<String, Symbol>,
    axioms: Vec<(Axiom, TermMap<String>)>,
}

impl Module {
    pub fn new() -> Self {
        Module {
            symbols: HashMap::new(),
            axioms: Vec::new(),
        }
    }

    pub fn get_symbol_at(
        &self,
        name: &str,
        location: Option<Location>,
    ) -> Result<&Symbol, CompileError> {
        self.symbols
            .get(name)
            .ok_or_else(|| CompileError::UndeclaredSymbol {
                name: name.into(),
                location,
            })
    }
    fn bad_symbol_kind(
        symbol: &Symbol,
        expected: SymbolKind,
        used_location: Option<Location>,
    ) -> CompileError {
        CompileError::BadSymbolKind {
            name: symbol.name().into(),
            expected,
            found: symbol.kind(),
            used_location: used_location,
            declared_location: symbol.location(),
        }
    }
    pub fn get_sort_at(
        &self,
        name: &str,
        location: Option<Location>,
    ) -> Result<&Sort, CompileError> {
        let symbol = self.get_symbol_at(name, location)?;
        if let Symbol::Sort(s) = symbol {
            Ok(s)
        } else {
            Err(Self::bad_symbol_kind(symbol, SymbolKind::Sort, location))
        }
    }
    pub fn get_predicate_at(
        &self,
        name: &str,
        location: Option<Location>,
    ) -> Result<&Predicate, CompileError> {
        let symbol = self.get_symbol_at(name, location)?;
        if let Symbol::Predicate(p) = symbol {
            Ok(p)
        } else {
            Err(Self::bad_symbol_kind(
                symbol,
                SymbolKind::Predicate,
                location,
            ))
        }
    }
    pub fn get_function_at(
        &self,
        name: &str,
        location: Option<Location>,
    ) -> Result<&Function, CompileError> {
        let symbol = self.get_symbol_at(name, location)?;
        if let Symbol::Function(f) = symbol {
            Ok(f)
        } else {
            Err(Self::bad_symbol_kind(
                symbol,
                SymbolKind::Function,
                location,
            ))
        }
    }

    pub fn iter_sorts(&self) -> impl Iterator<Item = &Sort> {
        self.symbols.values().filter_map(|symbol| match symbol {
            Symbol::Sort(s) => Some(s),
            _ => None,
        })
    }
    pub fn iter_predicates(&self) -> impl Iterator<Item = &Predicate> {
        self.symbols.values().filter_map(|symbol| match symbol {
            Symbol::Predicate(p) => Some(p),
            _ => None,
        })
    }
    pub fn iter_functions(&self) -> impl Iterator<Item = &Function> {
        self.symbols.values().filter_map(|symbol| match symbol {
            Symbol::Function(f) => Some(f),
            _ => None,
        })
    }

    pub fn iter_axioms(&self) -> impl Iterator<Item = &(Axiom, TermMap<String>)> {
        self.axioms.iter()
    }

    pub fn relations(&self) -> impl Iterator<Item = (&str, Vec<&str>)> {
        let pred_rels = self.iter_predicates().map(|pred| {
            let name = pred.name.as_str();
            let arity: Vec<&str> = pred.arity.iter().map(|s| s.as_str()).collect();
            (name, arity)
        });
        let func_rels = self.iter_functions().map(|func| {
            let name = func.name.as_str();
            let arity: Vec<&str> = func
                .dom
                .iter()
                .chain(once(&func.cod))
                .map(|s| s.as_str())
                .collect();
            (name, arity)
        });
        pred_rels.chain(func_rels)
    }

    pub fn arity(&self, relation: &str) -> Option<Vec<&str>> {
        match self.symbols.get(relation)? {
            Symbol::Sort(_) => None,
            Symbol::Predicate(Predicate { arity, .. }) => {
                Some(arity.iter().map(|s| s.as_str()).collect())
            }
            Symbol::Function(Function { dom, cod, .. }) => {
                Some(dom.iter().chain(once(cod)).map(|s| s.as_str()).collect())
            }
            Symbol::Query { .. } => None,
        }
    }

    fn insert_symbol(&mut self, symbol: Symbol) -> Result<(), CompileError> {
        if symbol.name().to_case(Case::UpperCamel) != *symbol.name() {
            return Err(CompileError::SymbolNotCamelCase {
                name: symbol.name().into(),
                location: symbol.location(),
            });
        }

        let second_location = symbol.location();
        if let Some(prev_symbol) = self.symbols.insert(symbol.name().into(), symbol) {
            return Err(CompileError::SymbolDeclaredTwice {
                name: prev_symbol.name().into(),
                first_declaration: prev_symbol.location(),
                second_declaration: second_location,
            });
        }

        Ok(())
    }

    pub fn add_sort(&mut self, sort: Sort) -> Result<(), CompileError> {
        self.insert_symbol(Symbol::Sort(sort))
    }
    pub fn add_predicate(&mut self, pred: Predicate) -> Result<(), CompileError> {
        for s in pred.arity.iter() {
            self.get_sort_at(s, pred.location)?;
        }
        self.insert_symbol(Symbol::Predicate(pred))
    }
    pub fn add_function(&mut self, func: Function) -> Result<(), CompileError> {
        for s in func.dom.iter().chain(once(&func.cod)) {
            self.get_sort_at(s, func.location)?;
        }
        self.insert_symbol(Symbol::Function(func))
    }

    // Functions to implement sort inference/checking.
    fn collect_function_application_requirements<SortMap>(
        &self,
        universe: &TermUniverse,
        sorts: &mut SortMap,
    ) -> Result<(), CompileError>
    where
        SortMap: AbstractTermUnification<HashSet<String>>,
    {
        for tm in universe.iter_terms() {
            match universe.data(tm) {
                TermData::Application(f, args) => {
                    let loc = universe.location(tm);
                    let Function { dom, cod, .. } = self.get_function_at(f, loc)?;
                    if args.len() != dom.len() {
                        return Err(CompileError::FunctionArgumentNumber {
                            function: f.clone(),
                            expected: dom.len(),
                            got: args.len(),
                            location: universe.location(tm),
                        });
                    }
                    for (arg, sort) in args.iter().copied().zip(dom) {
                        sorts[arg].insert(sort.clone());
                    }
                    sorts[tm].insert(cod.clone());
                }
                TermData::Wildcard | TermData::Variable(_) => (),
            }
        }
        Ok(())
    }
    fn collect_atom_requirements<'a, AtomIterator, SortMap>(
        &self,
        atoms: AtomIterator,
        sorts: &mut SortMap,
    ) -> Result<(), CompileError>
    where
        SortMap: AbstractTermUnification<HashSet<String>>,
        AtomIterator: IntoIterator<Item = &'a Atom>,
    {
        for atom in atoms.into_iter() {
            match &atom.data {
                AtomData::Equal(lhs, rhs) => {
                    sorts.union(*lhs, *rhs);
                }
                AtomData::Defined(tm, Some(sort)) => {
                    let _ = self.get_sort_at(sort, atom.location)?;
                    sorts[*tm].insert(sort.clone());
                }
                AtomData::Defined(_, None) => (),
                AtomData::Predicate(p, args) => {
                    let Predicate { arity, .. } = self.get_predicate_at(p, atom.location)?;
                    if args.len() != arity.len() {
                        return Err(CompileError::PredicateArgumentNumber {
                            predicate: p.clone(),
                            expected: arity.len(),
                            got: args.len(),
                            location: atom.location,
                        });
                    }
                    for (arg, sort) in args.iter().copied().zip(arity) {
                        sorts[arg].insert(sort.clone());
                    }
                }
            }
        }
        Ok(())
    }
    // Check that all terms have precisely one assigned sort, and return a map assigning to each
    // term its unique sort.
    fn into_unique_sorts<SortMap>(
        universe: &TermUniverse,
        mut sorts: SortMap,
    ) -> Result<TermMap<String>, CompileError>
    where
        SortMap: AbstractTermUnification<HashSet<String>>,
    {
        // Merge all syntactically equal terms (i.e. variables with the same name and all terms
        // implied by functionality/right-uniqueness of functions.
        sorts.congruence_closure();

        for tm in universe.iter_terms() {
            match sorts[tm].len() {
                0 => {
                    return Err(CompileError::NoSort {
                        location: universe.location(tm),
                    })
                }
                1 => (),
                _ => {
                    return Err(CompileError::ConflictingSorts {
                        location: universe.location(tm),
                        sorts: sorts[tm].iter().cloned().collect(),
                    })
                }
            }
        }
        let sorts = sorts
            .freeze()
            .map(|sorts| sorts.into_iter().next().unwrap());
        Ok(sorts)
    }

    fn infer_sequent_sorts(&self, sequent: &Sequent) -> Result<TermMap<String>, CompileError> {
        let unify_sorts = |mut lhs: HashSet<String>, rhs: HashSet<String>| {
            lhs.extend(rhs);
            lhs
        };

        let mut sorts = TermUnification::new(
            &sequent.universe,
            vec![HashSet::new(); sequent.universe.len()],
            unify_sorts,
        );

        self.collect_function_application_requirements(&sequent.universe, &mut sorts)?;
        self.collect_atom_requirements(
            sequent.premise.iter().chain(sequent.conclusion.iter()),
            &mut sorts,
        )?;

        Self::into_unique_sorts(&sequent.universe, sorts)
    }

    fn collect_query_argument_requirements<'a, SortMap>(
        &self,
        arguments: &[QueryArgument],
        sorts: &mut SortMap,
    ) -> Result<(), CompileError>
    where
        SortMap: AbstractTermUnification<HashSet<String>>,
    {
        for arg in arguments.iter() {
            if let Some(sort) = &arg.sort {
                let _ = self.get_sort_at(sort, arg.location)?;
                sorts[arg.variable].insert(sort.clone());
            }
        }
        Ok(())
    }

    fn infer_query_sorts(&self, query: &UserQuery) -> Result<TermMap<String>, CompileError> {
        let unify_sorts = |mut lhs: HashSet<String>, rhs: HashSet<String>| {
            lhs.extend(rhs);
            lhs
        };

        let mut sorts = TermUnification::new(
            &query.universe,
            vec![HashSet::new(); query.universe.len()],
            unify_sorts,
        );

        self.collect_query_argument_requirements(&query.arguments, &mut sorts)?;
        self.collect_function_application_requirements(&query.universe, &mut sorts)?;
        if let Some(where_formula) = &query.where_formula {
            self.collect_atom_requirements(where_formula, &mut sorts)?;
        }
        Self::into_unique_sorts(&query.universe, sorts)
    }

    fn check_epimorphism(sequent: &Sequent) -> Result<(), CompileError> {
        let universe = &sequent.universe;
        let mut has_occurred = TermUnification::new(
            universe,
            vec![false; universe.len()],
            |lhs_occured, rhs_occured| lhs_occured || rhs_occured,
        );

        // Set all premise terms to have occurred.
        for tm in sequent
            .premise
            .iter()
            .map(|atom| atom.iter_subterms(universe))
            .flatten()
        {
            has_occurred[tm] = true;
        }

        // Unify terms occuring in equalities in premise.
        for atom in &sequent.premise {
            use AtomData::*;
            match &atom.data {
                Equal(lhs, rhs) => {
                    has_occurred.union(*lhs, *rhs);
                }
                Defined(_, _) | Predicate(_, _) => (),
            }
        }

        has_occurred.congruence_closure();

        // Check that conclusion doesn't contain wildcards or variables that haven't occurred in
        // premise.
        for tm in sequent
            .conclusion
            .iter()
            .map(|atom| atom.iter_subterms(universe))
            .flatten()
        {
            match universe.data(tm) {
                TermData::Variable(_) | TermData::Wildcard if has_occurred[tm] => (),
                TermData::Application(_, _) => (),
                TermData::Variable(var) => {
                    return Err(CompileError::VariableNotInPremise {
                        var: var.clone(),
                        location: universe.location(tm),
                    })
                }
                TermData::Wildcard => {
                    return Err(CompileError::WildcardInConclusion {
                        location: universe.location(tm),
                    })
                }
            }
        }

        for atom in &sequent.conclusion {
            use AtomData::*;
            match &atom.data {
                Equal(lhs, rhs) => {
                    let lhs = *lhs;
                    let rhs = *rhs;
                    if !has_occurred[lhs] && !has_occurred[rhs] {
                        return Err(CompileError::ConclusionEqualityOfNewTerms {
                            location: atom.location,
                        });
                    }

                    if !has_occurred[lhs] || !has_occurred[rhs] {
                        let new = if has_occurred[lhs] { rhs } else { lhs };
                        use TermData::*;
                        match universe.data(new) {
                            Variable(_) | Wildcard => {
                                // Variables or Wildcards should've been checked earlier.
                                debug_assert!(has_occurred[new]);
                            }
                            Application(_, args) => {
                                if let Some(arg) = args.iter().find(|arg| !has_occurred[**arg]) {
                                    return Err(CompileError::ConclusionEqualityArgNew {
                                        location: universe.location(*arg),
                                    });
                                }
                            }
                        }
                    }

                    has_occurred.union(lhs, rhs);
                    has_occurred.congruence_closure();
                }
                Defined(_, _) => (),
                Predicate(_, args) => {
                    if let Some(arg) = args.iter().copied().find(|arg| !has_occurred[*arg]) {
                        return Err(CompileError::ConclusionPredicateArgNew {
                            location: universe.location(arg),
                        });
                    }
                }
            }
            for tm in atom.iter_subterms(universe) {
                has_occurred[tm] = true;
            }
        }

        Ok(())
    }

    fn check_variable_case(universe: &TermUniverse) -> Result<(), CompileError> {
        for tm in universe.iter_terms() {
            if let TermData::Variable(v) = universe.data(tm) {
                if *v != v.to_case(Case::Snake) {
                    return Err(CompileError::VariableNotSnakeCase {
                        name: v.into(),
                        location: universe.location(tm),
                    });
                }
            }
        }
        Ok(())
    }

    fn check_variable_occurence(universe: &TermUniverse) -> Result<(), CompileError> {
        let mut occ_nums: HashMap<&str, (usize, Option<Location>)> = HashMap::new();
        for tm in universe.iter_terms() {
            if let TermData::Variable(v) = universe.data(tm) {
                if let Some((n, _)) = occ_nums.get_mut(v.as_str()) {
                    *n += 1;
                } else {
                    let loc = universe.location(tm);
                    occ_nums.insert(v, (1, loc));
                }
            }
        }
        for (name, (n, location)) in occ_nums.into_iter() {
            if n == 1 {
                return Err(CompileError::VariableOccursOnlyOnce {
                    name: name.into(),
                    location,
                });
            }
        }
        Ok(())
    }

    pub fn add_axiom(&mut self, axiom: Axiom) -> Result<(), CompileError> {
        let sorts = self.infer_sequent_sorts(&axiom.sequent)?;
        Self::check_epimorphism(&axiom.sequent)?;
        Self::check_variable_case(&axiom.sequent.universe)?;
        Self::check_variable_occurence(&axiom.sequent.universe)?;
        self.axioms.push((axiom, sorts));
        Ok(())
    }

    pub fn add_query(&mut self, query: UserQuery) -> Result<(), CompileError> {
        let term_sorts = self.infer_query_sorts(&query)?;
        Self::check_variable_case(&query.universe)?;
        Self::check_variable_occurence(&query.universe)?;
        self.insert_symbol(Symbol::Query {
            ast: query,
            term_sorts,
        })?;
        Ok(())
    }
}
