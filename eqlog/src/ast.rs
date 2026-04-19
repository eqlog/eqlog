use crate::grammar_util::Location;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct NodeId(usize);

macro_rules! typed_id {
    ($name:ident) => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub struct $name(NodeId);

        impl From<$name> for NodeId {
            fn from(id: $name) -> NodeId {
                id.0
            }
        }
    };
}

typed_id!(ModuleId);
typed_id!(TypeDeclId);
typed_id!(PredDeclId);
typed_id!(FuncDeclId);
typed_id!(RuleDeclId);
typed_id!(EnumDeclId);
typed_id!(ModelDeclId);
typed_id!(CtorDeclId);
typed_id!(ArgDeclId);
typed_id!(ArgDeclListId);
typed_id!(TermId);
typed_id!(TermListId);
typed_id!(TypeExprId);
typed_id!(PredExprId);
typed_id!(FuncExprId);
typed_id!(IfAtomId);
typed_id!(ThenAtomId);
typed_id!(MatchCaseId);
typed_id!(StmtId);

#[derive(Clone, Debug)]
pub struct ModuleData {
    pub decls: Vec<DeclData>,
}

#[derive(Clone, Debug)]
pub enum DeclData {
    Type(TypeDeclId),
    Pred(PredDeclId),
    Func(FuncDeclId),
    Rule(RuleDeclId),
    Enum(EnumDeclId),
    Model(ModelDeclId),
}

#[derive(Clone, Debug)]
pub struct TypeDeclData {
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct PredDeclData {
    pub name: String,
    pub args: ArgDeclListId,
}

#[derive(Clone, Debug)]
pub struct FuncDeclData {
    pub name: String,
    pub args: ArgDeclListId,
    pub result: TypeExprId,
}

#[derive(Clone, Debug)]
pub struct RuleDeclData {
    pub name: Option<String>,
    pub body: Vec<StmtId>,
}

#[derive(Clone, Debug)]
pub struct EnumDeclData {
    pub name: String,
    pub ctors: Vec<CtorDeclId>,
}

#[derive(Clone, Debug)]
pub struct ModelDeclData {
    pub name: String,
    pub body: Vec<DeclData>,
}

#[derive(Clone, Debug)]
pub struct CtorDeclData {
    pub name: String,
    pub args: ArgDeclListId,
}

#[derive(Clone, Debug)]
pub struct ArgDeclData {
    pub name: Option<String>,
    pub typ: TypeExprId,
}

#[derive(Clone, Debug)]
pub struct ArgDeclListData {
    pub args: Vec<ArgDeclId>,
}

#[derive(Clone, Debug)]
pub enum TermData {
    Var(String),
    Wildcard,
    App { func: FuncExprId, args: TermListId },
    Dom(TermId),
    Cod(TermId),
    MorApp { mor: TermId, arg: TermId },
}

#[derive(Clone, Debug)]
pub struct TermListData {
    pub terms: Vec<TermId>,
}

#[derive(Clone, Debug)]
pub enum TypeExprData {
    Ambient(String),
    Member { term: TermId, name: String },
    Mor(String),
}

#[derive(Clone, Debug)]
pub enum PredExprData {
    Ambient(String),
    Member { term: TermId, name: String },
}

#[derive(Clone, Debug)]
pub enum FuncExprData {
    Ambient(String),
    Member { term: TermId, name: String },
}

#[derive(Clone, Debug)]
pub enum IfAtomData {
    Equal(TermId, TermId),
    Defined(TermId),
    Pred { pred: PredExprId, args: TermListId },
    Var { term: TermId, typ: TypeExprId },
}

#[derive(Clone, Debug)]
pub enum ThenAtomData {
    Equal(TermId, TermId),
    Defined { var: Option<TermId>, term: TermId },
    Pred { pred: PredExprId, args: TermListId },
}

#[derive(Clone, Debug)]
pub struct MatchCaseData {
    pub pattern: TermId,
    pub body: Vec<StmtId>,
}

#[derive(Clone, Debug)]
pub enum StmtData {
    If(IfAtomId),
    Then(ThenAtomId),
    Branch(Vec<Vec<StmtId>>),
    Match {
        term: TermId,
        cases: Vec<MatchCaseId>,
    },
}

#[derive(Clone, Debug)]
pub enum NodeData {
    Module(ModuleData),
    TypeDecl(TypeDeclData),
    PredDecl(PredDeclData),
    FuncDecl(FuncDeclData),
    RuleDecl(RuleDeclData),
    EnumDecl(EnumDeclData),
    ModelDecl(ModelDeclData),
    CtorDecl(CtorDeclData),
    ArgDecl(ArgDeclData),
    ArgDeclList(ArgDeclListData),
    Term(TermData),
    TermList(TermListData),
    TypeExpr(TypeExprData),
    PredExpr(PredExprData),
    FuncExpr(FuncExprData),
    IfAtom(IfAtomData),
    ThenAtom(ThenAtomData),
    MatchCase(MatchCaseData),
    Stmt(StmtData),
}

#[derive(Clone, Debug, Default)]
pub struct Ast {
    nodes: Vec<(Location, NodeData)>,
}

impl Ast {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn loc(&self, id: impl Into<NodeId>) -> Location {
        self.nodes[id.into().0].0
    }
}

macro_rules! accessor {
    ($getter:ident, $pusher:ident, $id:ident, $data:ident, $variant:ident) => {
        impl Ast {
            pub fn $getter(&self, id: $id) -> &$data {
                match &self.nodes[(id.0).0].1 {
                    NodeData::$variant(d) => d,
                    other => panic!(
                        "expected {} at {:?}, got {:?}",
                        stringify!($variant),
                        id,
                        other
                    ),
                }
            }

            pub fn $pusher(&mut self, loc: Location, data: $data) -> $id {
                let id = NodeId(self.nodes.len());
                self.nodes.push((loc, NodeData::$variant(data)));
                $id(id)
            }
        }
    };
}

accessor!(module, push_module, ModuleId, ModuleData, Module);
accessor!(
    type_decl,
    push_type_decl,
    TypeDeclId,
    TypeDeclData,
    TypeDecl
);
accessor!(
    pred_decl,
    push_pred_decl,
    PredDeclId,
    PredDeclData,
    PredDecl
);
accessor!(
    func_decl,
    push_func_decl,
    FuncDeclId,
    FuncDeclData,
    FuncDecl
);
accessor!(
    rule_decl,
    push_rule_decl,
    RuleDeclId,
    RuleDeclData,
    RuleDecl
);
accessor!(
    enum_decl,
    push_enum_decl,
    EnumDeclId,
    EnumDeclData,
    EnumDecl
);
accessor!(
    model_decl,
    push_model_decl,
    ModelDeclId,
    ModelDeclData,
    ModelDecl
);
accessor!(
    ctor_decl,
    push_ctor_decl,
    CtorDeclId,
    CtorDeclData,
    CtorDecl
);
accessor!(arg_decl, push_arg_decl, ArgDeclId, ArgDeclData, ArgDecl);
accessor!(
    arg_decl_list,
    push_arg_decl_list,
    ArgDeclListId,
    ArgDeclListData,
    ArgDeclList
);
accessor!(term, push_term, TermId, TermData, Term);
accessor!(
    term_list,
    push_term_list,
    TermListId,
    TermListData,
    TermList
);
accessor!(
    type_expr,
    push_type_expr,
    TypeExprId,
    TypeExprData,
    TypeExpr
);
accessor!(
    pred_expr,
    push_pred_expr,
    PredExprId,
    PredExprData,
    PredExpr
);
accessor!(
    func_expr,
    push_func_expr,
    FuncExprId,
    FuncExprData,
    FuncExpr
);
accessor!(if_atom, push_if_atom, IfAtomId, IfAtomData, IfAtom);
accessor!(
    then_atom,
    push_then_atom,
    ThenAtomId,
    ThenAtomData,
    ThenAtom
);
accessor!(
    match_case,
    push_match_case,
    MatchCaseId,
    MatchCaseData,
    MatchCase
);
accessor!(stmt, push_stmt, StmtId, StmtData, Stmt);
