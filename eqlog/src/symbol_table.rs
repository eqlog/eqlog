use crate::ast::*;
use crate::error::*;
use crate::source_display::Location;
use std::collections::BTreeMap;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SymbolRef<'a> {
    Type(&'a TypeDecl),
    Pred(&'a PredDecl),
    Func(&'a FuncDecl),
}

impl<'a> SymbolRef<'a> {
    fn try_from_decl(decl: &'a Decl) -> Option<Self> {
        match decl {
            Decl::Type(typ) => Some(SymbolRef::Type(typ)),
            Decl::Func(func) => Some(SymbolRef::Func(func)),
            Decl::Pred(pred) => Some(SymbolRef::Pred(pred)),
            Decl::Rule(_) => None,
        }
    }

    fn name(self) -> &'a str {
        use SymbolRef::*;
        match self {
            Type(typ) => &typ.name,
            Pred(pred) => &pred.name,
            Func(func) => &func.name,
        }
    }

    fn loc(self) -> Location {
        use SymbolRef::*;
        match self {
            Type(typ) => typ.loc,
            Pred(pred) => pred.loc,
            Func(func) => func.loc,
        }
    }

    fn kind(self) -> SymbolKind {
        use SymbolRef::*;
        match self {
            Type(_) => SymbolKind::Type,
            Pred(_) => SymbolKind::Pred,
            Func(_) => SymbolKind::Func,
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
            let prev_sym = syms.insert(name, sym);
            if let Some(prev_sym) = prev_sym {
                return Err(CompileError::SymbolDeclaredTwice {
                    name: name.into(),
                    first_declaration: prev_sym.loc(),
                    second_declaration: sym.loc(),
                });
            }
        }
        Ok(SymbolTable(syms))
    }

    pub fn get_symbol(&self, name: &str, used_at: Location) -> Result<SymbolRef<'a>, CompileError> {
        self.0
            .get(name)
            .copied()
            .ok_or_else(|| CompileError::UndeclaredSymbol {
                name: name.into(),
                used_at,
            })
    }

    pub fn get_type(&self, name: &str, used_at: Location) -> Result<&'a TypeDecl, CompileError> {
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

    pub fn get_pred(&self, name: &str, used_at: Location) -> Result<&'a PredDecl, CompileError> {
        let sym = self.get_symbol(name, used_at)?;
        if let SymbolRef::Pred(pred) = sym {
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

    pub fn get_func(&self, name: &str, used_at: Location) -> Result<&'a FuncDecl, CompileError> {
        let sym = self.get_symbol(name, used_at)?;
        if let SymbolRef::Func(func) = sym {
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
            SymbolRef::Pred(pred) => Some(*pred),
            _ => None,
        })
    }

    pub fn iter_funcs<'b>(&'b self) -> impl 'b + Iterator<Item = &'a FuncDecl> {
        self.0.values().filter_map(|sym| match sym {
            SymbolRef::Func(func) => Some(*func),
            _ => None,
        })
    }

    pub fn arity(&self, relation: &str) -> Option<Vec<&str>> {
        match self.0.get(relation)? {
            SymbolRef::Type(_) => None,
            SymbolRef::Pred(pred) => Some(
                pred.arg_decls
                    .iter()
                    .map(|arg_decl| arg_decl.typ.as_str())
                    .collect(),
            ),
            SymbolRef::Func(func) => {
                let mut arity: Vec<_> = func
                    .arg_decls
                    .iter()
                    .map(|arg_decl| arg_decl.typ.as_str())
                    .collect();
                arity.push(func.result.as_str());
                Some(arity)
            }
        }
    }

    pub fn relations(&self) -> impl Iterator<Item = (&str, Vec<&str>)> {
        self.0.values().filter_map(|sym| {
            let name = sym.name();
            if let Some(arity) = self.arity(name) {
                Some((name, arity))
            } else {
                None
            }
        })
    }
}
