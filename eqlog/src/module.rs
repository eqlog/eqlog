use crate::ast::*;
use crate::ast_v1::*;
use crate::error::*;
use crate::semantics::*;
use crate::source_display::Location;
use crate::source_display::*;
use crate::unification::*;
use convert_case::{Case, Casing};
use std::collections::BTreeMap;
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

impl<'a> ModuleWrapper<'a> {
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
        let sorts = check_rule(&self.symbols, &rule)?.map(|typ| typ.to_string());
        let axiom = rule_to_axiom(rule);
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
