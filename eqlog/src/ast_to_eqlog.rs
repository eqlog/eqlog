use std::collections::BTreeMap;

use eqlog_eqlog::*;

use crate::ast::*;
use crate::grammar_util::Location;

#[derive(Clone, Debug, Default)]
pub struct EqlogAstMaps {
    pub type_decl_nodes: BTreeMap<TypeDeclId, TypeDeclNode>,
    pub pred_decl_nodes: BTreeMap<PredDeclId, PredDeclNode>,
    pub func_decl_nodes: BTreeMap<FuncDeclId, FuncDeclNode>,
    pub enum_decl_nodes: BTreeMap<EnumDeclId, EnumDeclNode>,
    pub model_decl_nodes: BTreeMap<ModelDeclId, ModelDeclNode>,
    pub ctor_decl_nodes: BTreeMap<CtorDeclId, CtorDeclNode>,
}

pub fn populate_eqlog(
    ast: &Ast,
    module: ModuleId,
) -> (
    Eqlog,
    BTreeMap<Ident, String>,
    BTreeMap<Loc, Location>,
    EqlogAstMaps,
    ModuleNode,
) {
    let mut eqlog = Eqlog::new();
    let mut ctx = Ctx {
        ast,
        eqlog: &mut eqlog,
        identifiers: BTreeMap::new(),
        locations: BTreeMap::new(),
        maps: EqlogAstMaps::default(),
    };

    let module_node = ctx.build_module(module);

    let Ctx {
        identifiers,
        locations,
        maps,
        ..
    } = ctx;

    let identifiers = identifiers.into_iter().map(|(s, i)| (i, s)).collect();
    let locations = locations
        .into_iter()
        .map(|(location, loc)| (loc, location))
        .collect();

    (eqlog, identifiers, locations, maps, module_node)
}

struct Ctx<'a> {
    ast: &'a Ast,
    eqlog: &'a mut Eqlog,
    identifiers: BTreeMap<String, Ident>,
    locations: BTreeMap<Location, Loc>,
    maps: EqlogAstMaps,
}

impl<'a> Ctx<'a> {
    fn intern_ident(&mut self, name: &str) -> Ident {
        let eqlog = &mut *self.eqlog;
        *self
            .identifiers
            .entry(name.to_string())
            .or_insert_with(|| eqlog.new_ident())
    }

    fn intern_loc(&mut self, location: Location) -> Loc {
        let eqlog = &mut *self.eqlog;
        *self
            .locations
            .entry(location)
            .or_insert_with(|| eqlog.new_loc())
    }

    fn build_type_expr(&mut self, type_expr: TypeExprId) -> TypeExprNode {
        let node = self.eqlog.new_type_expr_node();
        match *self.ast.type_expr(type_expr) {
            TypeExpr::Ambient(id) => {
                let name = self.ast.ambient_type_expr(id).name.clone();
                let ident = self.intern_ident(&name);
                self.eqlog.insert_ambient_type_expr(node, ident);
            }
            TypeExpr::Mor(id) => {
                let name = self.ast.mor_type_expr(id).name.clone();
                let ident = self.intern_ident(&name);
                self.eqlog.insert_mor_type_expr(node, ident);
            }
            TypeExpr::Member(_) => {}
        }

        let loc = self.intern_loc(self.ast.loc(type_expr));
        self.eqlog.insert_type_expr_node_loc(node, loc);

        node
    }

    fn build_arg_decl(&mut self, arg: ArgDeclId) -> ArgDeclNode {
        let node = self.eqlog.new_arg_decl_node();
        let ArgDecl { name, typ } = self.ast.arg_decl(arg);
        let name = name.clone();
        let typ = *typ;
        if let Some(name) = name {
            let ident = self.intern_ident(&name);
            self.eqlog.insert_arg_decl_node_name(node, ident);
        }
        let type_node = self.build_type_expr(typ);
        self.eqlog.insert_arg_decl_node_type(node, type_node);

        let loc = self.intern_loc(self.ast.loc(arg));
        self.eqlog.insert_arg_decl_node_loc(node, loc);

        node
    }

    fn build_arg_decl_list(&mut self, list: ArgDeclListId) -> ArgDeclListNode {
        let args: Vec<ArgDeclId> = self.ast.arg_decl_list(list).args.clone();
        let arg_nodes: Vec<ArgDeclNode> =
            args.into_iter().map(|a| self.build_arg_decl(a)).collect();
        let mut node = self.eqlog.new_arg_decl_list_node();
        self.eqlog.insert_nil_arg_decl_list_node(node);
        for arg in arg_nodes.iter().rev() {
            let cons = self.eqlog.new_arg_decl_list_node();
            self.eqlog.insert_cons_arg_decl_list_node(cons, *arg, node);
            node = cons;
        }

        let loc = self.intern_loc(self.ast.loc(list));
        self.eqlog.insert_arg_decl_list_node_loc(node, loc);

        node
    }

    fn build_type_decl(&mut self, decl: TypeDeclId) -> TypeDeclNode {
        let node = self.eqlog.new_type_decl_node();
        self.maps.type_decl_nodes.insert(decl, node);
        let TypeDecl { name } = self.ast.type_decl(decl);
        let ident = self.intern_ident(&name.clone());
        self.eqlog.insert_type_decl(node, ident);

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_type_decl_node_loc(node, loc);

        node
    }

    fn build_pred_decl(&mut self, decl: PredDeclId) -> PredDeclNode {
        let node = self.eqlog.new_pred_decl_node();
        self.maps.pred_decl_nodes.insert(decl, node);
        let PredDecl { name, args } = self.ast.pred_decl(decl);
        let name = name.clone();
        let args = *args;
        let ident = self.intern_ident(&name);
        let args = self.build_arg_decl_list(args);
        self.eqlog.insert_pred_decl(node, ident, args);

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_pred_decl_node_loc(node, loc);

        node
    }

    fn build_func_decl(&mut self, decl: FuncDeclId) -> FuncDeclNode {
        let node = self.eqlog.new_func_decl_node();
        self.maps.func_decl_nodes.insert(decl, node);
        let FuncDecl { name, args, result } = self.ast.func_decl(decl);
        let name = name.clone();
        let args = *args;
        let result = *result;
        let ident = self.intern_ident(&name);
        let args = self.build_arg_decl_list(args);
        let result = self.build_type_expr(result);
        self.eqlog.insert_func_decl(node, ident, args, result);

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_func_decl_node_loc(node, loc);

        node
    }

    fn build_ctor_decl(&mut self, decl: CtorDeclId) -> CtorDeclNode {
        let node = self.eqlog.new_ctor_decl_node();
        self.maps.ctor_decl_nodes.insert(decl, node);
        let CtorDecl { name, args } = self.ast.ctor_decl(decl);
        let name = name.clone();
        let args = *args;
        let ident = self.intern_ident(&name);
        let args = self.build_arg_decl_list(args);
        self.eqlog.insert_ctor_decl(node, ident, args);

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_ctor_decl_node_loc(node, loc);

        node
    }

    fn build_ctor_decl_list(&mut self, ctors: &[CtorDeclId]) -> CtorDeclListNode {
        let ctor_nodes: Vec<CtorDeclNode> =
            ctors.iter().map(|c| self.build_ctor_decl(*c)).collect();
        let mut node = self.eqlog.new_ctor_decl_list_node();
        self.eqlog.insert_nil_ctor_decl_list_node(node);
        for ctor in ctor_nodes.iter().rev() {
            let cons = self.eqlog.new_ctor_decl_list_node();
            self.eqlog
                .insert_cons_ctor_decl_list_node(cons, *ctor, node);
            node = cons;
        }
        node
    }

    fn build_enum_decl(&mut self, decl: EnumDeclId) -> EnumDeclNode {
        let node = self.eqlog.new_enum_decl_node();
        self.maps.enum_decl_nodes.insert(decl, node);
        let EnumDecl { name, ctors } = self.ast.enum_decl(decl);
        let name = name.clone();
        let ctors = ctors.clone();
        let ident = self.intern_ident(&name);
        let ctors = self.build_ctor_decl_list(&ctors);
        self.eqlog.insert_enum_decl(node, ident, ctors);

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_enum_decl_node_loc(node, loc);

        node
    }

    fn build_model_decl(&mut self, decl: ModelDeclId) -> ModelDeclNode {
        let node = self.eqlog.new_model_decl_node();
        self.maps.model_decl_nodes.insert(decl, node);
        let ModelDecl { name, body } = self.ast.model_decl(decl);
        let name = name.clone();
        let body = body.clone();
        let ident = self.intern_ident(&name);
        let body = self.build_decl_list(&body);
        self.eqlog.insert_model_decl(node, ident, body);

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_model_decl_node_loc(node, loc);

        node
    }

    fn build_decl(&mut self, decl: DeclId) -> Option<DeclNode> {
        let node = self.eqlog.new_decl_node();
        match *self.ast.decl(decl) {
            Decl::Type(d) => {
                let inner = self.build_type_decl(d);
                self.eqlog.insert_decl_node_type(node, inner);
            }
            Decl::Pred(d) => {
                let inner = self.build_pred_decl(d);
                self.eqlog.insert_decl_node_pred(node, inner);
            }
            Decl::Func(d) => {
                let inner = self.build_func_decl(d);
                self.eqlog.insert_decl_node_func(node, inner);
            }
            Decl::Enum(d) => {
                let inner = self.build_enum_decl(d);
                self.eqlog.insert_decl_node_enum(node, inner);
            }
            Decl::Model(d) => {
                let inner = self.build_model_decl(d);
                self.eqlog.insert_decl_node_model(node, inner);
            }
            Decl::Rule(_) => return None,
        }
        Some(node)
    }

    fn build_decl_list(&mut self, decls: &[DeclId]) -> DeclListNode {
        let decl_nodes: Vec<DeclNode> = decls.iter().filter_map(|d| self.build_decl(*d)).collect();
        let mut node = self.eqlog.new_decl_list_node();
        self.eqlog.insert_nil_decl_list_node(node);
        for decl in decl_nodes.iter().rev() {
            let cons = self.eqlog.new_decl_list_node();
            self.eqlog.insert_cons_decl_list_node(cons, *decl, node);
            node = cons;
        }
        node
    }

    fn build_module(&mut self, module: ModuleId) -> ModuleNode {
        let node = self.eqlog.new_module_node();
        let decls = self.ast.module(module).decls.clone();
        let decls_node = self.build_decl_list(&decls);
        self.eqlog.insert_decls_module_node(node, decls_node);

        let loc = self.intern_loc(self.ast.loc(module));
        self.eqlog.insert_decl_list_node_loc(decls_node, loc);
        self.eqlog.insert_module_node_loc(node, loc);

        node
    }
}
