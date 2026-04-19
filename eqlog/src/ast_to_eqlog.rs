use std::collections::BTreeMap;

use eqlog_eqlog::*;

use crate::ast::*;
use crate::grammar_util::Location;

pub fn populate_eqlog(
    ast: &Ast,
    module: ModuleId,
) -> (
    Eqlog,
    BTreeMap<Ident, String>,
    BTreeMap<Loc, Location>,
    ModuleNode,
) {
    let mut eqlog = Eqlog::new();
    let mut ctx = Ctx {
        ast,
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
    ast: &'a Ast,
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

    fn build_term(&mut self, term: TermId) -> TermNode {
        let node = self.eqlog.new_term_node();
        match self.ast.term(term) {
            TermData::Var(name) => {
                let ident = self.intern_ident(name);
                let virt_ident = self.eqlog.define_real_virt_ident(ident);
                self.eqlog.insert_var_term_node(node, virt_ident);
            }
            TermData::Wildcard => {
                self.eqlog.insert_wildcard_term_node(node);
            }
            TermData::App { func, args } => {
                let func = *func;
                let args = *args;
                let func_expr = self.build_func_expr(func);
                let arg_list = self.build_term_list(args);
                self.eqlog.insert_app_term_node(node, func_expr, arg_list);
            }
            TermData::Dom(arg) => {
                let arg = *arg;
                let arg_node = self.build_term(arg);
                self.eqlog.insert_dom_term_node(node, arg_node);
            }
            TermData::Cod(arg) => {
                let arg = *arg;
                let arg_node = self.build_term(arg);
                self.eqlog.insert_cod_term_node(node, arg_node);
            }
            TermData::MorApp { mor, arg } => {
                let mor = *mor;
                let arg = *arg;
                let mor_node = self.build_term(mor);
                let arg_node = self.build_term(arg);
                self.eqlog
                    .insert_mor_app_term_node(node, mor_node, arg_node);
            }
        }

        let loc = self.intern_loc(self.ast.loc(term));
        self.eqlog.insert_term_node_loc(node, loc);

        node
    }

    fn build_term_list(&mut self, list: TermListId) -> TermListNode {
        let terms: Vec<TermId> = self.ast.term_list(list).terms.clone();
        let term_nodes: Vec<TermNode> = terms.into_iter().map(|t| self.build_term(t)).collect();

        let mut node = self.eqlog.new_term_list_node();
        self.eqlog.insert_nil_term_list_node(node);
        for tm in term_nodes.iter().rev() {
            let cons = self.eqlog.new_term_list_node();
            self.eqlog.insert_cons_term_list_node(cons, *tm, node);
            node = cons;
        }

        let loc = self.intern_loc(self.ast.loc(list));
        self.eqlog.insert_term_list_node_loc(node, loc);

        node
    }

    fn build_type_expr(&mut self, type_expr: TypeExprId) -> TypeExprNode {
        let node = self.eqlog.new_type_expr_node();
        match self.ast.type_expr(type_expr) {
            TypeExprData::Ambient(name) => {
                let ident = self.intern_ident(name);
                self.eqlog.insert_ambient_type_expr(node, ident);
            }
            TypeExprData::Member { term, name } => {
                let term = *term;
                let name = name.clone();
                let term_node = self.build_term(term);
                let ident = self.intern_ident(&name);
                self.eqlog.insert_member_type_expr(node, term_node, ident);
            }
            TypeExprData::Mor(name) => {
                let ident = self.intern_ident(name);
                self.eqlog.insert_mor_type_expr(node, ident);
            }
        }

        let loc = self.intern_loc(self.ast.loc(type_expr));
        self.eqlog.insert_type_expr_node_loc(node, loc);

        node
    }

    fn build_pred_expr(&mut self, pred_expr: PredExprId) -> PredExprNode {
        let node = self.eqlog.new_pred_expr_node();
        match self.ast.pred_expr(pred_expr) {
            PredExprData::Ambient(name) => {
                let ident = self.intern_ident(name);
                self.eqlog.insert_ambient_pred_expr(node, ident);
            }
            PredExprData::Member { term, name } => {
                let term = *term;
                let name = name.clone();
                let term_node = self.build_term(term);
                let ident = self.intern_ident(&name);
                self.eqlog.insert_member_pred_expr(node, term_node, ident);
            }
        }

        let loc = self.intern_loc(self.ast.loc(pred_expr));
        self.eqlog.insert_pred_expr_node_loc(node, loc);

        node
    }

    fn build_func_expr(&mut self, func_expr: FuncExprId) -> FuncExprNode {
        let node = self.eqlog.new_func_expr_node();
        match self.ast.func_expr(func_expr) {
            FuncExprData::Ambient(name) => {
                let ident = self.intern_ident(name);
                self.eqlog.insert_ambient_func_expr(node, ident);
            }
            FuncExprData::Member { term, name } => {
                let term = *term;
                let name = name.clone();
                let term_node = self.build_term(term);
                let ident = self.intern_ident(&name);
                self.eqlog.insert_member_func_expr(node, term_node, ident);
            }
        }

        let loc = self.intern_loc(self.ast.loc(func_expr));
        self.eqlog.insert_func_expr_node_loc(node, loc);

        node
    }

    fn build_if_atom(&mut self, atom: IfAtomId) -> IfAtomNode {
        let node = self.eqlog.new_if_atom_node();
        match self.ast.if_atom(atom) {
            IfAtomData::Equal(lhs, rhs) => {
                let lhs = *lhs;
                let rhs = *rhs;
                let lhs = self.build_term(lhs);
                let rhs = self.build_term(rhs);
                self.eqlog.insert_equal_if_atom_node(node, lhs, rhs);
            }
            IfAtomData::Defined(term) => {
                let term = *term;
                let term_node = self.build_term(term);
                self.eqlog.insert_defined_if_atom_node(node, term_node);
            }
            IfAtomData::Pred { pred, args } => {
                let pred = *pred;
                let args = *args;
                let pred_node = self.build_pred_expr(pred);
                let args_node = self.build_term_list(args);
                self.eqlog
                    .insert_pred_if_atom_node(node, pred_node, args_node);
            }
            IfAtomData::Var { term, typ } => {
                let term = *term;
                let typ = *typ;
                let term_node = self.build_term(term);
                let typ_node = self.build_type_expr(typ);
                self.eqlog
                    .insert_var_if_atom_node(node, term_node, typ_node);
            }
        }

        let loc = self.intern_loc(self.ast.loc(atom));
        self.eqlog.insert_if_atom_node_loc(node, loc);

        node
    }

    fn build_then_atom(&mut self, atom: ThenAtomId) -> ThenAtomNode {
        let node = self.eqlog.new_then_atom_node();
        match self.ast.then_atom(atom) {
            ThenAtomData::Equal(lhs, rhs) => {
                let lhs = *lhs;
                let rhs = *rhs;
                let lhs = self.build_term(lhs);
                let rhs = self.build_term(rhs);
                self.eqlog.insert_equal_then_atom_node(node, lhs, rhs);
            }
            ThenAtomData::Defined { var, term } => {
                let var = *var;
                let term = *term;
                let term_node = self.build_term(term);
                let var_node = self.build_opt_term(var);
                self.eqlog
                    .insert_defined_then_atom_node(node, var_node, term_node);
            }
            ThenAtomData::Pred { pred, args } => {
                let pred = *pred;
                let args = *args;
                let pred_node = self.build_pred_expr(pred);
                let args_node = self.build_term_list(args);
                self.eqlog
                    .insert_pred_then_atom_node(node, pred_node, args_node);
            }
        }

        let loc = self.intern_loc(self.ast.loc(atom));
        self.eqlog.insert_then_atom_node_loc(node, loc);

        node
    }

    fn build_opt_term(&mut self, term: Option<TermId>) -> OptTermNode {
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

    fn build_stmt_block(&mut self, stmts: &[StmtId]) -> StmtListNode {
        let stmt_nodes: Vec<StmtNode> = stmts.iter().map(|s| self.build_stmt(*s)).collect();
        let mut node = self.eqlog.new_stmt_list_node();
        self.eqlog.insert_nil_stmt_list_node(node);
        for stmt in stmt_nodes.iter().rev() {
            let cons = self.eqlog.new_stmt_list_node();
            self.eqlog.insert_cons_stmt_list_node(cons, *stmt, node);
            node = cons;
        }
        node
    }

    fn build_stmt_block_list(&mut self, blocks: &[Vec<StmtId>]) -> StmtBlockListNode {
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

    fn build_match_case(&mut self, case: MatchCaseId) -> MatchCaseNode {
        let node = self.eqlog.new_match_case_node();
        let MatchCaseData { pattern, body } = self.ast.match_case(case);
        let pattern = *pattern;
        let body = body.clone();
        let pattern_node = self.build_term(pattern);
        let body_node = self.build_stmt_block(&body);
        self.eqlog.insert_match_case(node, pattern_node, body_node);

        let loc = self.intern_loc(self.ast.loc(case));
        self.eqlog.insert_match_case_node_loc(node, loc);

        node
    }

    fn build_match_case_list(&mut self, cases: &[MatchCaseId]) -> MatchCaseListNode {
        let case_nodes: Vec<MatchCaseNode> =
            cases.iter().map(|c| self.build_match_case(*c)).collect();
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

    fn build_stmt(&mut self, stmt: StmtId) -> StmtNode {
        let node = self.eqlog.new_stmt_node();
        let insert_loc;
        match self.ast.stmt(stmt) {
            StmtData::If(atom) => {
                let atom = *atom;
                let atom_node = self.build_if_atom(atom);
                self.eqlog.insert_if_stmt_node(node, atom_node);
                insert_loc = true;
            }
            StmtData::Then(atom) => {
                let atom = *atom;
                let atom_node = self.build_then_atom(atom);
                self.eqlog.insert_then_stmt_node(node, atom_node);
                insert_loc = true;
            }
            StmtData::Branch(blocks) => {
                let blocks = blocks.clone();
                let blocks_node = self.build_stmt_block_list(&blocks);
                self.eqlog.insert_branch_stmt_node(node, blocks_node);
                insert_loc = false;
            }
            StmtData::Match { term, cases } => {
                let term = *term;
                let cases = cases.clone();
                let term_node = self.build_term(term);
                let cases_node = self.build_match_case_list(&cases);
                self.eqlog
                    .insert_match_stmt_node(node, term_node, cases_node);
                insert_loc = true;
            }
        }

        if insert_loc {
            let loc = self.intern_loc(self.ast.loc(stmt));
            self.eqlog.insert_stmt_node_loc(node, loc);
        }

        node
    }

    fn build_arg_decl(&mut self, arg: ArgDeclId) -> ArgDeclNode {
        let node = self.eqlog.new_arg_decl_node();
        let ArgDeclData { name, typ } = self.ast.arg_decl(arg);
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
        let TypeDeclData { name } = self.ast.type_decl(decl);
        let ident = self.intern_ident(&name.clone());
        self.eqlog.insert_type_decl(node, ident);

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_type_decl_node_loc(node, loc);

        node
    }

    fn build_pred_decl(&mut self, decl: PredDeclId) -> PredDeclNode {
        let node = self.eqlog.new_pred_decl_node();
        let PredDeclData { name, args } = self.ast.pred_decl(decl);
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
        let FuncDeclData { name, args, result } = self.ast.func_decl(decl);
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
        let CtorDeclData { name, args } = self.ast.ctor_decl(decl);
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
        let EnumDeclData { name, ctors } = self.ast.enum_decl(decl);
        let name = name.clone();
        let ctors = ctors.clone();
        let ident = self.intern_ident(&name);
        let ctors = self.build_ctor_decl_list(&ctors);
        self.eqlog.insert_enum_decl(node, ident, ctors);

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_enum_decl_node_loc(node, loc);

        node
    }

    fn build_rule_decl(&mut self, decl: RuleDeclId) -> RuleDeclNode {
        let node = self.eqlog.new_rule_decl_node();
        let RuleDeclData { name, body } = self.ast.rule_decl(decl);
        let name = name.clone();
        let body = body.clone();
        let body_node = self.build_stmt_block(&body);
        self.eqlog.insert_rule_decl(node, body_node);

        if let Some(name) = name {
            let ident = self.intern_ident(&name);
            self.eqlog.insert_rule_name(node, ident);
        }

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_rule_decl_node_loc(node, loc);

        node
    }

    fn build_model_decl(&mut self, decl: ModelDeclId) -> ModelDeclNode {
        let node = self.eqlog.new_model_decl_node();
        let ModelDeclData { name, body } = self.ast.model_decl(decl);
        let name = name.clone();
        let body = body.clone();
        let ident = self.intern_ident(&name);
        let body = self.build_decl_list(&body);
        self.eqlog.insert_model_decl(node, ident, body);

        let loc = self.intern_loc(self.ast.loc(decl));
        self.eqlog.insert_model_decl_node_loc(node, loc);

        node
    }

    fn build_decl(&mut self, decl: &DeclData) -> DeclNode {
        let node = self.eqlog.new_decl_node();
        match decl {
            DeclData::Type(d) => {
                let inner = self.build_type_decl(*d);
                self.eqlog.insert_decl_node_type(node, inner);
            }
            DeclData::Pred(d) => {
                let inner = self.build_pred_decl(*d);
                self.eqlog.insert_decl_node_pred(node, inner);
            }
            DeclData::Func(d) => {
                let inner = self.build_func_decl(*d);
                self.eqlog.insert_decl_node_func(node, inner);
            }
            DeclData::Rule(d) => {
                let inner = self.build_rule_decl(*d);
                self.eqlog.insert_decl_node_rule(node, inner);
            }
            DeclData::Enum(d) => {
                let inner = self.build_enum_decl(*d);
                self.eqlog.insert_decl_node_enum(node, inner);
            }
            DeclData::Model(d) => {
                let inner = self.build_model_decl(*d);
                self.eqlog.insert_decl_node_model(node, inner);
            }
        }
        node
    }

    fn build_decl_list(&mut self, decls: &[DeclData]) -> DeclListNode {
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
