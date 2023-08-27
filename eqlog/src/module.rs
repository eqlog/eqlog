use crate::ast::{
    Decl, FuncDecl, IfAtom, IfAtomData, Module, PredDecl, RuleDecl, StmtData, TermContext,
    ThenAtom, ThenAtomData,
};
use crate::ast_v1::*;
use crate::error::*;
use crate::source_display::Location;
use crate::source_display::*;
use crate::symbol_table::SymbolTable;
use crate::unification::*;
use convert_case::{Case, Casing};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display};
use std::iter::{once, repeat};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ModuleWrapper<'a> {
    pub symbols: SymbolTable<'a>,
    axioms: Vec<(Axiom, TermMap<String>)>,
}

fn if_atom_to_v1_atom(if_atom: IfAtomData) -> AtomData {
    match if_atom {
        IfAtomData::Equal(lhs, rhs) => AtomData::Equal(lhs, rhs),
        IfAtomData::Defined(tm) => AtomData::Defined(tm, None),
        IfAtomData::Pred { pred, args } => AtomData::Predicate(pred, args),
        IfAtomData::Var { term, typ } => AtomData::Defined(term, Some(typ)),
    }
}

fn then_atom_to_v1_atom(then_atom: ThenAtomData) -> AtomData {
    match then_atom {
        ThenAtomData::Equal(lhs, rhs) => AtomData::Equal(lhs, rhs),
        ThenAtomData::Defined { var, term } => {
            assert!(
                var.is_none(),
                "Variables for then defined atoms not supported yet"
            );
            AtomData::Defined(term, None)
        }
        ThenAtomData::Pred { pred, args } => AtomData::Predicate(pred, args),
    }
}

fn rule_to_axiom(rule: RuleDecl) -> Axiom {
    let RuleDecl {
        term_context,
        body,
        loc,
        ..
    } = rule;

    let mut premise: Vec<Atom> = Vec::new();
    let mut conclusion: Vec<Atom> = Vec::new();

    for stmt in body {
        match stmt.data {
            StmtData::If(IfAtom { loc, data }) => {
                assert!(
                    conclusion.is_empty(),
                    "Mixing if and then statements not supported yet"
                );
                let v1_atom = Atom {
                    data: if_atom_to_v1_atom(data),
                    location: Some(loc),
                };
                premise.push(v1_atom);
            }
            StmtData::Then(ThenAtom { loc, data }) => {
                let v1_atom = Atom {
                    data: then_atom_to_v1_atom(data),
                    location: Some(loc),
                };
                conclusion.push(v1_atom);
            }
        }
    }

    let sequent = Sequent {
        data: SequentData::Implication {
            premise,
            conclusion,
        },
        universe: term_context,
    };

    Axiom {
        sequent,
        location: Some(loc),
    }
}

impl<'a> ModuleWrapper<'a> {
    pub fn new(module: &'a Module) -> Result<Self, CompileError> {
        let symbols = SymbolTable::from_module(module)?;
        let mut module_wrapper = ModuleWrapper {
            symbols,
            axioms: Vec::new(),
        };
        for decl in module.0.iter() {
            if let Decl::Rule(rule) = decl {
                module_wrapper.add_rule(rule.clone())?;
            }
        }
        Ok(module_wrapper)
    }

    pub fn iter_axioms(&'a self) -> impl 'a + Iterator<Item = (&'a Axiom, &'a TermMap<String>)> {
        self.axioms.iter().map(|(axiom, types)| (axiom, types))
    }

    //fn check_symbol_case(symbol: &Symbol) -> Result<(), CompileError> {
    //    let name = symbol.name();
    //    let kind = symbol.kind();
    //    use SymbolKind::*;
    //    match kind {
    //        Sort | Predicate | Function => {
    //            if name.to_case(Case::UpperCamel) != *name {
    //                return Err(CompileError::SymbolNotCamelCase {
    //                    name: name.to_string(),
    //                    location: symbol.location(),
    //                    symbol_kind: kind,
    //                });
    //            }
    //        }
    //        Query => {
    //            if name.to_case(Case::Snake) != *name {
    //                return Err(CompileError::SymbolNotSnakeCase {
    //                    name: name.to_string(),
    //                    location: symbol.location(),
    //                    symbol_kind: kind,
    //                });
    //            }
    //        }
    //    }
    //    Ok(())
    //}
}

// The term unification used for sort inference and checking. For each term, we infer a set of
// sorts that the term must have, and in the end check that the set has precisely one element.
struct SortMerge {}
impl MergeFn<BTreeSet<String>> for SortMerge {
    fn merge(&mut self, mut lhs: BTreeSet<String>, rhs: BTreeSet<String>) -> BTreeSet<String> {
        lhs.extend(rhs);
        lhs
    }
}
type SortMap<'a> = TermUnification<'a, BTreeSet<String>, SortMerge>;

impl<'a> ModuleWrapper<'a> {
    fn collect_function_application_requirements(
        &self,
        universe: &TermContext,
        sorts: &mut SortMap,
    ) -> Result<(), CompileError> {
        for tm in universe.iter_terms() {
            match universe.data(tm) {
                TermData::Application { func, args } => {
                    let loc = universe.loc(tm);
                    let FuncDecl {
                        arg_decls, result, ..
                    } = self.symbols.get_func(func, loc)?;
                    if args.len() != arg_decls.len() {
                        return Err(CompileError::FunctionArgumentNumber {
                            function: func.clone(),
                            expected: arg_decls.len(),
                            got: args.len(),
                            location: universe.loc(tm),
                        });
                    }
                    for (arg, arg_decl) in args.iter().copied().zip(arg_decls) {
                        sorts[arg].insert(arg_decl.typ.clone());
                    }
                    sorts[tm].insert(result.clone());
                }
                TermData::Wildcard | TermData::Variable(_) => (),
            }
        }
        Ok(())
    }
    fn collect_atom_requirements(
        &self,
        atom: &Atom,
        sorts: &mut SortMap,
    ) -> Result<(), CompileError> {
        match &atom.data {
            AtomData::Equal(lhs, rhs) => {
                sorts.union(*lhs, *rhs);
            }
            AtomData::Defined(tm, Some(sort)) => {
                let _ = self.symbols.get_type(sort, atom.location.unwrap())?;
                sorts[*tm].insert(sort.clone());
            }
            AtomData::Defined(_, None) => (),
            AtomData::Predicate(p, args) => {
                let PredDecl { arg_decls, .. } =
                    self.symbols.get_pred(p, atom.location.unwrap())?;
                if args.len() != arg_decls.len() {
                    return Err(CompileError::PredicateArgumentNumber {
                        predicate: p.clone(),
                        expected: arg_decls.len(),
                        got: args.len(),
                        location: atom.location,
                    });
                }
                for (arg, arg_decl) in args.iter().copied().zip(arg_decls) {
                    sorts[arg].insert(arg_decl.typ.clone());
                }
            }
        }
        Ok(())
    }
    // Check that all terms have precisely one assigned sort, and return a map assigning to each
    // term its unique sort.
    fn into_unique_sorts(
        universe: &TermContext,
        mut sorts: SortMap,
    ) -> Result<TermMap<String>, CompileError> {
        // Merge all syntactically equal terms (i.e. variables with the same name and all terms
        // implied by functionality/right-uniqueness of functions.
        sorts.congruence_closure();

        for tm in universe.iter_terms() {
            match sorts[tm].len() {
                0 => {
                    return Err(CompileError::NoSort {
                        location: Some(universe.loc(tm)),
                    })
                }
                1 => (),
                _ => {
                    return Err(CompileError::ConflictingSorts {
                        location: Some(universe.loc(tm)),
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
        let mut sorts = TermUnification::new(
            &sequent.universe,
            vec![BTreeSet::new(); sequent.universe.len()],
            SortMerge {},
        );

        self.collect_function_application_requirements(&sequent.universe, &mut sorts)?;
        for atom in sequent.data.iter_atoms() {
            self.collect_atom_requirements(&atom, &mut sorts)?;
        }
        match &sequent.data {
            SequentData::Implication { .. } => (),
            SequentData::Reduction { from, to, .. } => {
                sorts.union(*from, *to);
            }
            SequentData::Bireduction { lhs, rhs, .. } => {
                sorts.union(*lhs, *rhs);
            }
        }

        Self::into_unique_sorts(&sequent.universe, sorts)
    }

    // Check that the `from` term of a reduction is composite, i.e. not a reduction or wildcard.
    fn check_reduction_variables(sequent: &Sequent) -> Result<(), CompileError> {
        use SequentData::*;
        let err = |tm| -> CompileError {
            CompileError::ReductionFromVariableOrWildcard {
                location: Some(sequent.universe.loc(tm)),
            }
        };

        match &sequent.data {
            Implication { .. } => Ok(()),
            Reduction { from, .. } => {
                use TermData::*;
                match sequent.universe.data(*from) {
                    Application { .. } => Ok(()),
                    Wildcard | Variable(_) => Err(err(*from)),
                }
            }
            Bireduction { lhs, rhs, .. } => {
                use TermData::*;
                match sequent.universe.data(*lhs) {
                    Application { .. } => (),
                    Wildcard | Variable(_) => {
                        return Err(err(*lhs));
                    }
                }
                match sequent.universe.data(*rhs) {
                    Application { .. } => (),
                    Wildcard | Variable(_) => {
                        return Err(err(*rhs));
                    }
                }
                Ok(())
            }
        }
    }
    // Check the following:
    // - Every variable in the conclusion also appears in the premise.
    // - Every term in the conclusion is equal to some term that occurred earlier or inside an
    //   Atom::Defined.
    fn check_epimorphism(sequent: &Sequent) -> Result<(), CompileError> {
        let (premise, conclusion) = match &sequent.data {
            SequentData::Implication {
                premise,
                conclusion,
                ..
            } => (premise, conclusion),
            SequentData::Reduction { .. } | SequentData::Bireduction { .. } => {
                // Reductions are epimorphisms by construction.
                return Ok(());
            }
        };
        let universe = &sequent.universe;
        let mut has_occurred = TermUnification::new(
            universe,
            vec![false; universe.len()],
            |lhs_occured, rhs_occured| lhs_occured || rhs_occured,
        );

        // Set all premise terms to have occurred.
        for atom in premise {
            for tm in atom.iter_subterms(universe) {
                has_occurred[tm] = true;
            }
        }

        // Unify terms occuring in equalities in premise.
        for atom in premise {
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
        for atom in conclusion {
            for tm in atom.iter_subterms(universe) {
                match universe.data(tm) {
                    TermData::Variable(_) | TermData::Wildcard if has_occurred[tm] => (),
                    TermData::Application { .. } => (),
                    TermData::Variable(var) => {
                        return Err(CompileError::VariableNotInPremise {
                            var: var.clone(),
                            location: Some(universe.loc(tm)),
                        })
                    }
                    TermData::Wildcard => {
                        return Err(CompileError::WildcardInConclusion {
                            location: Some(universe.loc(tm)),
                        })
                    }
                }
            }
        }

        for atom in conclusion {
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
                            Application { args, .. } => {
                                if let Some(arg) = args.iter().find(|arg| !has_occurred[**arg]) {
                                    return Err(CompileError::ConclusionEqualityArgNew {
                                        location: Some(universe.loc(*arg)),
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
                            location: Some(universe.loc(arg)),
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

    // Check that all variables are snake_case.
    fn check_variable_case(universe: &TermContext) -> Result<(), CompileError> {
        for tm in universe.iter_terms() {
            if let TermData::Variable(v) = universe.data(tm) {
                if *v != v.to_case(Case::Snake) {
                    return Err(CompileError::VariableNotSnakeCase {
                        name: v.into(),
                        location: universe.loc(tm),
                    });
                }
            }
        }
        Ok(())
    }

    // Check that every variable occurs at least twice.
    fn check_variable_occurence(universe: &TermContext) -> Result<(), CompileError> {
        let mut occ_nums: BTreeMap<&str, (usize, Option<Location>)> = BTreeMap::new();
        for tm in universe.iter_terms() {
            if let TermData::Variable(v) = universe.data(tm) {
                if let Some((n, _)) = occ_nums.get_mut(v.as_str()) {
                    *n += 1;
                } else {
                    let loc = universe.loc(tm);
                    occ_nums.insert(v, (1, Some(loc)));
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

    fn add_rule(&mut self, rule: RuleDecl) -> Result<(), CompileError> {
        let axiom = rule_to_axiom(rule);
        let sorts = self.infer_sequent_sorts(&axiom.sequent)?;
        Self::check_reduction_variables(&axiom.sequent)?;
        Self::check_epimorphism(&axiom.sequent)?;
        Self::check_variable_case(&axiom.sequent.universe)?;
        Self::check_variable_occurence(&axiom.sequent.universe)?;
        self.axioms.push((axiom, sorts));
        Ok(())
    }
}

#[derive(Clone)]
struct DumpAxiomsDisplay<'a> {
    source: &'a str,
    module: &'a ModuleWrapper<'a>,
}

impl<'a> Display for DumpAxiomsDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Self { source, module } = self;
        let separator: String = repeat('-').take(80).chain(once('\n')).collect();
        write!(f, "{separator}")?;
        for (axiom, sorts) in module.iter_axioms() {
            if let Some(location) = axiom.location {
                write!(f, "{}", SourceDisplay::new(source, location))?;
            } else {
                write!(f, "<unmapped axiom>\n")?;
            }

            write!(f, "\n")?;

            write!(f, "Inferred sorts:\n")?;
            for tm in axiom.sequent.universe.iter_terms() {
                let sort = &sorts[tm];
                let tm = tm.debug(&axiom.sequent.universe);
                write!(f, "  {tm:?}: {sort}\n")?;
            }
            write!(f, "{separator}")?;
        }
        Ok(())
    }
}

impl<'a> ModuleWrapper<'a> {
    #[allow(dead_code)]
    pub fn dump_axioms<'b>(&'b self, source: &'b str) -> impl 'b + Clone + Display {
        DumpAxiomsDisplay {
            module: self,
            source,
        }
    }
}
