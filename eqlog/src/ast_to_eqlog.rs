use std::collections::BTreeMap;

use eqlog_eqlog::*;

use crate::ast;
use crate::grammar_util::Location;

pub fn populate_eqlog(
    module: &ast::Module,
) -> (
    Eqlog,
    BTreeMap<Ident, String>,
    BTreeMap<Loc, Location>,
    ModuleNode,
) {
    let mut eqlog = Eqlog::new();
    let mut ctx = Ctx {
        eqlog: &mut eqlog,
        identifiers: BTreeMap::new(),
        locations: BTreeMap::new(),
    };

    let module_node = ctx.build_module(module);

    let Ctx {
        identifiers,
        locations,
        ..
    } = ctx;

    let identifiers = identifiers.into_iter().map(|(s, i)| (i, s)).collect();
    let locations = locations
        .into_iter()
        .map(|(location, loc)| (loc, location))
        .collect();

    (eqlog, identifiers, locations, module_node)
}

struct Ctx<'a> {
    eqlog: &'a mut Eqlog,
    identifiers: BTreeMap<String, Ident>,
    locations: BTreeMap<Location, Loc>,
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

    fn build_term(&mut self, term: &ast::Term) -> TermNode {
        let node = self.eqlog.new_term_node();
        match &term.data {
            ast::TermData::Var(name) => {
                let ident = self.intern_ident(name);
                let virt_ident = self.eqlog.define_real_virt_ident(ident);
                self.eqlog.insert_var_term_node(node, virt_ident);
            }
            ast::TermData::Wildcard => {
                self.eqlog.insert_wildcard_term_node(node);
            }
            ast::TermData::App { func, args } => {
                let func_expr = self.build_func_expr(func);
                let arg_list = self.build_term_list(args);
                self.eqlog.insert_app_term_node(node, func_expr, arg_list);
            }
            ast::TermData::Dom(arg) => {
                let arg_node = self.build_term(arg);
                self.eqlog.insert_dom_term_node(node, arg_node);
            }
            ast::TermData::Cod(arg) => {
                let arg_node = self.build_term(arg);
                self.eqlog.insert_cod_term_node(node, arg_node);
            }
            ast::TermData::MorApp { mor, arg } => {
                let mor_node = self.build_term(mor);
                let arg_node = self.build_term(arg);
                self.eqlog
                    .insert_mor_app_term_node(node, mor_node, arg_node);
            }
        }

        let loc = self.intern_loc(term.loc);
        self.eqlog.insert_term_node_loc(node, loc);

        node
    }

    fn build_term_list(&mut self, list: &ast::TermList) -> TermListNode {
        let term_nodes: Vec<TermNode> = list.terms.iter().map(|t| self.build_term(t)).collect();

        let mut node = self.eqlog.new_term_list_node();
        self.eqlog.insert_nil_term_list_node(node);
        for tm in term_nodes.iter().rev() {
            let cons = self.eqlog.new_term_list_node();
            self.eqlog.insert_cons_term_list_node(cons, *tm, node);
            node = cons;
        }

        let loc = self.intern_loc(list.loc);
        self.eqlog.insert_term_list_node_loc(node, loc);

        node
    }

    fn build_type_expr(&mut self, type_expr: &ast::TypeExpr) -> TypeExprNode {
        let node = self.eqlog.new_type_expr_node();
        match &type_expr.data {
            ast::TypeExprData::Ambient(name) => {
                let ident = self.intern_ident(name);
                self.eqlog.insert_ambient_type_expr(node, ident);
            }
            ast::TypeExprData::Member { term, name } => {
                let term_node = self.build_term(term);
                let ident = self.intern_ident(name);
                self.eqlog.insert_member_type_expr(node, term_node, ident);
            }
            ast::TypeExprData::Mor(name) => {
                let ident = self.intern_ident(name);
                self.eqlog.insert_mor_type_expr(node, ident);
            }
        }

        let loc = self.intern_loc(type_expr.loc);
        self.eqlog.insert_type_expr_node_loc(node, loc);

        node
    }

    fn build_pred_expr(&mut self, pred_expr: &ast::PredExpr) -> PredExprNode {
        let node = self.eqlog.new_pred_expr_node();
        match &pred_expr.data {
            ast::PredExprData::Ambient(name) => {
                let ident = self.intern_ident(name);
                self.eqlog.insert_ambient_pred_expr(node, ident);
            }
            ast::PredExprData::Member { term, name } => {
                let term_node = self.build_term(term);
                let ident = self.intern_ident(name);
                self.eqlog.insert_member_pred_expr(node, term_node, ident);
            }
        }

        let loc = self.intern_loc(pred_expr.loc);
        self.eqlog.insert_pred_expr_node_loc(node, loc);

        node
    }

    fn build_func_expr(&mut self, func_expr: &ast::FuncExpr) -> FuncExprNode {
        let node = self.eqlog.new_func_expr_node();
        match &func_expr.data {
            ast::FuncExprData::Ambient(name) => {
                let ident = self.intern_ident(name);
                self.eqlog.insert_ambient_func_expr(node, ident);
            }
            ast::FuncExprData::Member { term, name } => {
                let term_node = self.build_term(term);
                let ident = self.intern_ident(name);
                self.eqlog.insert_member_func_expr(node, term_node, ident);
            }
        }

        let loc = self.intern_loc(func_expr.loc);
        self.eqlog.insert_func_expr_node_loc(node, loc);

        node
    }

    fn build_if_atom(&mut self, atom: &ast::IfAtom) -> IfAtomNode {
        let node = self.eqlog.new_if_atom_node();
        match &atom.data {
            ast::IfAtomData::Equal(lhs, rhs) => {
                let lhs = self.build_term(lhs);
                let rhs = self.build_term(rhs);
                self.eqlog.insert_equal_if_atom_node(node, lhs, rhs);
            }
            ast::IfAtomData::Defined(term) => {
                let term_node = self.build_term(term);
                self.eqlog.insert_defined_if_atom_node(node, term_node);
            }
            ast::IfAtomData::Pred { pred, args } => {
                let pred_node = self.build_pred_expr(pred);
                let args_node = self.build_term_list(args);
                self.eqlog
                    .insert_pred_if_atom_node(node, pred_node, args_node);
            }
            ast::IfAtomData::Var { term, typ } => {
                let term_node = self.build_term(term);
                let typ_node = self.build_type_expr(typ);
                self.eqlog
                    .insert_var_if_atom_node(node, term_node, typ_node);
            }
        }

        let loc = self.intern_loc(atom.loc);
        self.eqlog.insert_if_atom_node_loc(node, loc);

        node
    }

    fn build_then_atom(&mut self, atom: &ast::ThenAtom) -> ThenAtomNode {
        let node = self.eqlog.new_then_atom_node();
        match &atom.data {
            ast::ThenAtomData::Equal(lhs, rhs) => {
                let lhs = self.build_term(lhs);
                let rhs = self.build_term(rhs);
                self.eqlog.insert_equal_then_atom_node(node, lhs, rhs);
            }
            ast::ThenAtomData::Defined { var, term } => {
                let term_node = self.build_term(term);
                let var_node = self.build_opt_term(var.as_ref());
                self.eqlog
                    .insert_defined_then_atom_node(node, var_node, term_node);
            }
            ast::ThenAtomData::Pred { pred, args } => {
                let pred_node = self.build_pred_expr(pred);
                let args_node = self.build_term_list(args);
                self.eqlog
                    .insert_pred_then_atom_node(node, pred_node, args_node);
            }
        }

        let loc = self.intern_loc(atom.loc);
        self.eqlog.insert_then_atom_node_loc(node, loc);

        node
    }

    fn build_opt_term(&mut self, term: Option<&ast::Term>) -> OptTermNode {
        let node = self.eqlog.new_opt_term_node();
        match term {
            Some(term) => {
                let term_node = self.build_term(term);
                self.eqlog.insert_some_term_node(node, term_node);
            }
            None => {
                self.eqlog.insert_none_term_node(node);
            }
        }
        node
    }

    fn build_stmt_block(&mut self, stmts: &[ast::Stmt]) -> StmtListNode {
        let stmt_nodes: Vec<StmtNode> = stmts.iter().map(|s| self.build_stmt(s)).collect();
        let mut node = self.eqlog.new_stmt_list_node();
        self.eqlog.insert_nil_stmt_list_node(node);
        for stmt in stmt_nodes.iter().rev() {
            let cons = self.eqlog.new_stmt_list_node();
            self.eqlog.insert_cons_stmt_list_node(cons, *stmt, node);
            node = cons;
        }
        node
    }

    fn build_stmt_block_list(&mut self, blocks: &[Vec<ast::Stmt>]) -> StmtBlockListNode {
        let block_nodes: Vec<StmtListNode> =
            blocks.iter().map(|b| self.build_stmt_block(b)).collect();
        let mut node = self.eqlog.new_stmt_block_list_node();
        self.eqlog.insert_nil_stmt_block_list_node(node);
        for block in block_nodes.iter().rev() {
            let cons = self.eqlog.new_stmt_block_list_node();
            self.eqlog
                .insert_cons_stmt_block_list_node(cons, *block, node);
            node = cons;
        }
        node
    }

    fn build_match_case(&mut self, case: &ast::MatchCase) -> MatchCaseNode {
        let node = self.eqlog.new_match_case_node();
        let pattern = self.build_term(&case.pattern);
        let body = self.build_stmt_block(&case.body);
        self.eqlog.insert_match_case(node, pattern, body);

        let loc = self.intern_loc(case.loc);
        self.eqlog.insert_match_case_node_loc(node, loc);

        node
    }

    fn build_match_case_list(&mut self, cases: &[ast::MatchCase]) -> MatchCaseListNode {
        let case_nodes: Vec<MatchCaseNode> =
            cases.iter().map(|c| self.build_match_case(c)).collect();
        let mut node = self.eqlog.new_match_case_list_node();
        self.eqlog.insert_nil_match_case_list_node(node);
        for case in case_nodes.iter().rev() {
            let cons = self.eqlog.new_match_case_list_node();
            self.eqlog
                .insert_cons_match_case_list_node(cons, *case, node);
            node = cons;
        }
        node
    }

    fn build_stmt(&mut self, stmt: &ast::Stmt) -> StmtNode {
        let node = self.eqlog.new_stmt_node();
        let insert_loc;
        match &stmt.data {
            ast::StmtData::If(atom) => {
                let atom_node = self.build_if_atom(atom);
                self.eqlog.insert_if_stmt_node(node, atom_node);
                insert_loc = true;
            }
            ast::StmtData::Then(atom) => {
                let atom_node = self.build_then_atom(atom);
                self.eqlog.insert_then_stmt_node(node, atom_node);
                insert_loc = true;
            }
            ast::StmtData::Branch(blocks) => {
                let blocks_node = self.build_stmt_block_list(blocks);
                self.eqlog.insert_branch_stmt_node(node, blocks_node);
                insert_loc = false;
            }
            ast::StmtData::Match { term, cases } => {
                let term_node = self.build_term(term);
                let cases_node = self.build_match_case_list(cases);
                self.eqlog
                    .insert_match_stmt_node(node, term_node, cases_node);
                insert_loc = true;
            }
        }

        if insert_loc {
            let loc = self.intern_loc(stmt.loc);
            self.eqlog.insert_stmt_node_loc(node, loc);
        }

        node
    }

    fn build_arg_decl(&mut self, arg: &ast::ArgDecl) -> ArgDeclNode {
        let node = self.eqlog.new_arg_decl_node();
        if let Some(name) = &arg.name {
            let ident = self.intern_ident(name);
            self.eqlog.insert_arg_decl_node_name(node, ident);
        }
        let type_node = self.build_type_expr(&arg.typ);
        self.eqlog.insert_arg_decl_node_type(node, type_node);

        let loc = self.intern_loc(arg.loc);
        self.eqlog.insert_arg_decl_node_loc(node, loc);

        node
    }

    fn build_arg_decl_list(&mut self, list: &ast::ArgDeclList) -> ArgDeclListNode {
        let arg_nodes: Vec<ArgDeclNode> =
            list.args.iter().map(|a| self.build_arg_decl(a)).collect();
        let mut node = self.eqlog.new_arg_decl_list_node();
        self.eqlog.insert_nil_arg_decl_list_node(node);
        for arg in arg_nodes.iter().rev() {
            let cons = self.eqlog.new_arg_decl_list_node();
            self.eqlog.insert_cons_arg_decl_list_node(cons, *arg, node);
            node = cons;
        }

        let loc = self.intern_loc(list.loc);
        self.eqlog.insert_arg_decl_list_node_loc(node, loc);

        node
    }

    fn build_type_decl(&mut self, decl: &ast::TypeDecl) -> TypeDeclNode {
        let node = self.eqlog.new_type_decl_node();
        let ident = self.intern_ident(&decl.name);
        self.eqlog.insert_type_decl(node, ident);

        let loc = self.intern_loc(decl.loc);
        self.eqlog.insert_type_decl_node_loc(node, loc);

        node
    }

    fn build_pred_decl(&mut self, decl: &ast::PredDecl) -> PredDeclNode {
        let node = self.eqlog.new_pred_decl_node();
        let ident = self.intern_ident(&decl.name);
        let args = self.build_arg_decl_list(&decl.args);
        self.eqlog.insert_pred_decl(node, ident, args);

        let loc = self.intern_loc(decl.loc);
        self.eqlog.insert_pred_decl_node_loc(node, loc);

        node
    }

    fn build_func_decl(&mut self, decl: &ast::FuncDecl) -> FuncDeclNode {
        let node = self.eqlog.new_func_decl_node();
        let ident = self.intern_ident(&decl.name);
        let args = self.build_arg_decl_list(&decl.args);
        let result = self.build_type_expr(&decl.result);
        self.eqlog.insert_func_decl(node, ident, args, result);

        let loc = self.intern_loc(decl.loc);
        self.eqlog.insert_func_decl_node_loc(node, loc);

        node
    }

    fn build_ctor_decl(&mut self, decl: &ast::CtorDecl) -> CtorDeclNode {
        let node = self.eqlog.new_ctor_decl_node();
        let ident = self.intern_ident(&decl.name);
        let args = self.build_arg_decl_list(&decl.args);
        self.eqlog.insert_ctor_decl(node, ident, args);

        let loc = self.intern_loc(decl.loc);
        self.eqlog.insert_ctor_decl_node_loc(node, loc);

        node
    }

    fn build_ctor_decl_list(&mut self, ctors: &[ast::CtorDecl]) -> CtorDeclListNode {
        let ctor_nodes: Vec<CtorDeclNode> =
            ctors.iter().map(|c| self.build_ctor_decl(c)).collect();
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

    fn build_enum_decl(&mut self, decl: &ast::EnumDecl) -> EnumDeclNode {
        let node = self.eqlog.new_enum_decl_node();
        let ident = self.intern_ident(&decl.name);
        let ctors = self.build_ctor_decl_list(&decl.ctors);
        self.eqlog.insert_enum_decl(node, ident, ctors);

        let loc = self.intern_loc(decl.loc);
        self.eqlog.insert_enum_decl_node_loc(node, loc);

        node
    }

    fn build_rule_decl(&mut self, decl: &ast::RuleDecl) -> RuleDeclNode {
        let node = self.eqlog.new_rule_decl_node();
        let body = self.build_stmt_block(&decl.body);
        self.eqlog.insert_rule_decl(node, body);

        if let Some(name) = &decl.name {
            let ident = self.intern_ident(name);
            self.eqlog.insert_rule_name(node, ident);
        }

        let loc = self.intern_loc(decl.loc);
        self.eqlog.insert_rule_decl_node_loc(node, loc);

        node
    }

    fn build_model_decl(&mut self, decl: &ast::ModelDecl) -> ModelDeclNode {
        let node = self.eqlog.new_model_decl_node();
        let ident = self.intern_ident(&decl.name);
        let body = self.build_decl_list(&decl.body);
        self.eqlog.insert_model_decl(node, ident, body);

        let loc = self.intern_loc(decl.loc);
        self.eqlog.insert_model_decl_node_loc(node, loc);

        node
    }

    fn build_decl(&mut self, decl: &ast::Decl) -> DeclNode {
        let node = self.eqlog.new_decl_node();
        match decl {
            ast::Decl::Type(d) => {
                let inner = self.build_type_decl(d);
                self.eqlog.insert_decl_node_type(node, inner);
            }
            ast::Decl::Pred(d) => {
                let inner = self.build_pred_decl(d);
                self.eqlog.insert_decl_node_pred(node, inner);
            }
            ast::Decl::Func(d) => {
                let inner = self.build_func_decl(d);
                self.eqlog.insert_decl_node_func(node, inner);
            }
            ast::Decl::Rule(d) => {
                let inner = self.build_rule_decl(d);
                self.eqlog.insert_decl_node_rule(node, inner);
            }
            ast::Decl::Enum(d) => {
                let inner = self.build_enum_decl(d);
                self.eqlog.insert_decl_node_enum(node, inner);
            }
            ast::Decl::Model(d) => {
                let inner = self.build_model_decl(d);
                self.eqlog.insert_decl_node_model(node, inner);
            }
        }
        node
    }

    fn build_decl_list(&mut self, decls: &[ast::Decl]) -> DeclListNode {
        let decl_nodes: Vec<DeclNode> = decls.iter().map(|d| self.build_decl(d)).collect();
        let mut node = self.eqlog.new_decl_list_node();
        self.eqlog.insert_nil_decl_list_node(node);
        for decl in decl_nodes.iter().rev() {
            let cons = self.eqlog.new_decl_list_node();
            self.eqlog.insert_cons_decl_list_node(cons, *decl, node);
            node = cons;
        }
        node
    }

    fn build_module(&mut self, module: &ast::Module) -> ModuleNode {
        let node = self.eqlog.new_module_node();
        let decls = self.build_decl_list(&module.decls);
        self.eqlog.insert_decls_module_node(node, decls);

        let loc = self.intern_loc(module.loc);
        self.eqlog.insert_decl_list_node_loc(decls, loc);
        self.eqlog.insert_module_node_loc(node, loc);

        node
    }
}
