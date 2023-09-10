use crate::ast::*;
use crate::ast_v1::*;
use crate::error::*;
use crate::semantics::*;
use crate::unification::*;

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

fn rule_to_axiom(rule: RuleDecl) -> Result<Axiom, CompileError> {
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
                if !conclusion.is_empty() {
                    return Err(CompileError::IfAfterThen { location: loc });
                }
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

    Ok(Axiom {
        sequent,
        location: Some(loc),
    })
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
}

impl<'a> ModuleWrapper<'a> {
    fn add_rule(&mut self, rule: RuleDecl) -> Result<(), CompileError> {
        let types = check_rule(&self.symbols, &rule)?
            .types
            .map(|typ| typ.to_string());
        let axiom = rule_to_axiom(rule)?;
        self.axioms.push((axiom, types.map(|typ| typ.to_string())));
        Ok(())
    }
}
