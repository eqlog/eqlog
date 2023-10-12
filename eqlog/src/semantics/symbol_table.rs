use convert_case::Case;
use convert_case::Casing;

use crate::ast::*;
use crate::error::*;
use crate::grammar_util::*;
use std::collections::BTreeMap;
use std::iter::once;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SymbolRef<'a> {
    Type(&'a TypeDecl),
    Pred {
        pred: &'a PredDecl,
        arity: Vec<&'a str>,
    },
    Func {
        func: &'a FuncDecl,
        arity: Vec<&'a str>,
    },
    Rule(&'a RuleDecl),
}

impl<'a> SymbolRef<'a> {
    fn try_from_decl(decl: &'a Decl) -> Option<Self> {
        match decl {
            Decl::Type(typ) => Some(SymbolRef::Type(typ)),
            Decl::Func(func) => {
                let arity: Vec<&'a str> = func
                    .arg_decls
                    .iter()
                    .map(|arg_decl| arg_decl.typ.as_str())
                    .chain(once(func.result.as_str()))
                    .collect();
                Some(SymbolRef::Func { func, arity })
            }
            Decl::Pred(pred) => {
                let arity: Vec<&'a str> = pred
                    .arg_decls
                    .iter()
                    .map(|arg_decl| arg_decl.typ.as_str())
                    .collect();

                Some(SymbolRef::Pred { pred, arity })
            }
            Decl::Rule(rule) => match rule.name.as_ref() {
                Some(_) => Some(SymbolRef::Rule(rule)),
                None => None,
            },
        }
    }

    fn name(&self) -> &'a str {
        use SymbolRef::*;
        match self {
            Type(typ) => &typ.name,
            Pred { pred, .. } => pred.name.as_str(),
            Func { func, .. } => func.name.as_str(),
            Rule(rule) => rule.name.as_ref().unwrap().as_str(),
        }
    }

    fn loc(&self) -> Location {
        use SymbolRef::*;
        match self {
            Type(typ) => typ.loc,
            Pred { pred, .. } => pred.loc,
            Func { func, .. } => func.loc,
            Rule(rule) => rule.loc,
        }
    }

    fn kind(&self) -> SymbolKind {
        use SymbolRef::*;
        match self {
            Type(_) => SymbolKind::Type,
            Pred { .. } => SymbolKind::Pred,
            Func { .. } => SymbolKind::Func,
            Rule(_) => SymbolKind::Rule,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SymbolTable<'a>(BTreeMap<&'a str, SymbolRef<'a>>);

impl<'a> SymbolTable<'a> {
    pub fn from_module(module: &'a Module) -> Result<Self, CompileError> {
        let mut syms: BTreeMap<&'a str, SymbolRef<'a>> = BTreeMap::new();
        for sym in module.0.iter().filter_map(SymbolRef::try_from_decl) {
            let name = sym.name();
            let sym_loc = sym.loc();
            let prev_sym = syms.insert(name, sym);
            if let Some(prev_sym) = prev_sym {
                return Err(CompileError::SymbolDeclaredTwice {
                    name: name.into(),
                    first_declaration: prev_sym.loc(),
                    second_declaration: sym_loc,
                });
            }
        }
        let table = SymbolTable(syms);
        table.check_resolve()?;
        table.check_casing()?;
        Ok(table)
    }

    /// Checks that all used type names used in func and pred declarations have been declared.
    /// This function does not check type names appearing in rules.
    fn check_resolve(&self) -> Result<(), CompileError> {
        for sym in self.0.values() {
            match sym {
                SymbolRef::Type(_) => {}
                SymbolRef::Pred { pred, arity } => {
                    // TODO: AST should have more precise location for typ.
                    for typ in arity {
                        self.get_type(typ, pred.loc)?;
                    }
                }
                SymbolRef::Func { func, arity } => {
                    // TODO: AST should have more precise location for typ.
                    for typ in arity {
                        self.get_type(typ, func.loc)?;
                    }
                }
                SymbolRef::Rule(_) => {}
            }
        }

        Ok(())
    }

    fn check_casing(&self) -> Result<(), CompileError> {
        for sym in self.0.values() {
            let name = sym.name();
            let loc = sym.loc();
            let symbol_kind = sym.kind();
            match symbol_kind {
                SymbolKind::Type => {
                    if name != name.to_case(Case::UpperCamel) {
                        return Err(CompileError::SymbolNotCamelCase {
                            name: name.to_string(),
                            location: Some(loc),
                            symbol_kind,
                        });
                    }
                }
                SymbolKind::Pred | SymbolKind::Func | SymbolKind::Rule => {
                    if name != name.to_case(Case::Snake) {
                        return Err(CompileError::SymbolNotSnakeCase {
                            name: name.to_string(),
                            location: Some(loc),
                            symbol_kind,
                        });
                    }
                }
            }
        }

        Ok(())
    }

    pub fn get_symbol(
        &'a self,
        name: &str,
        used_at: Location,
    ) -> Result<&'a SymbolRef<'a>, CompileError> {
        self.0
            .get(name)
            .ok_or_else(|| CompileError::UndeclaredSymbol {
                name: name.into(),
                used_at,
            })
    }

    pub fn get_type(&'a self, name: &str, used_at: Location) -> Result<&'a TypeDecl, CompileError> {
        let sym = self.get_symbol(name, used_at)?;
        if let SymbolRef::Type(typ) = sym {
            Ok(typ)
        } else {
            Err(CompileError::BadSymbolKind {
                name: name.into(),
                expected: SymbolKind::Type,
                found: sym.kind(),
                used_at,
                declared_at: sym.loc(),
            })
        }
    }

    pub fn get_pred(&'a self, name: &str, used_at: Location) -> Result<&'a PredDecl, CompileError> {
        let sym = self.get_symbol(name, used_at)?;
        if let SymbolRef::Pred { pred, .. } = sym {
            Ok(pred)
        } else {
            Err(CompileError::BadSymbolKind {
                name: name.into(),
                expected: SymbolKind::Pred,
                found: sym.kind(),
                used_at,
                declared_at: sym.loc(),
            })
        }
    }

    pub fn get_func(&'a self, name: &str, used_at: Location) -> Result<&'a FuncDecl, CompileError> {
        let sym = self.get_symbol(name, used_at)?;
        if let SymbolRef::Func { func, .. } = sym {
            Ok(func)
        } else {
            Err(CompileError::BadSymbolKind {
                name: name.into(),
                expected: SymbolKind::Func,
                found: sym.kind(),
                used_at,
                declared_at: sym.loc(),
            })
        }
    }

    pub fn iter_types<'b>(&'b self) -> impl 'b + Iterator<Item = &'a TypeDecl> {
        self.0.values().filter_map(|sym| match sym {
            SymbolRef::Type(typ) => Some(*typ),
            _ => None,
        })
    }

    pub fn iter_preds<'b>(&'b self) -> impl 'b + Iterator<Item = &'a PredDecl> {
        self.0.values().filter_map(|sym| match sym {
            SymbolRef::Pred { pred, .. } => Some(*pred),
            _ => None,
        })
    }

    pub fn iter_funcs<'b>(&'b self) -> impl 'b + Iterator<Item = &'a FuncDecl> {
        self.0.values().filter_map(|sym| match sym {
            SymbolRef::Func { func, .. } => Some(*func),
            _ => None,
        })
    }

    pub fn get_arity(&'a self, relation: &str) -> Option<&'a [&'a str]> {
        match self.0.get(relation)? {
            SymbolRef::Type(_) => None,
            SymbolRef::Pred { arity, .. } => Some(arity),
            SymbolRef::Func { arity, .. } => Some(arity),
            SymbolRef::Rule(_) => None,
        }
    }

    pub fn iter_rels(&'a self) -> impl Iterator<Item = (&str, &[&'a str])> {
        self.0.values().filter_map(|sym| {
            let name = sym.name();
            if let Some(arity) = self.get_arity(name) {
                Some((name, arity))
            } else {
                None
            }
        })
    }
}
