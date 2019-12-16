grammar Qt;
// Parser rules
unit : defs+=def*;
def : 'def' name=ID exts+=ctxExt* ':' retTy=expr ':=' body=expr '.';
ctxExt : '(' names+=ID+ ':' ty=expr ')';
expr : '(' parenthesized=expr ')'
     | fun=ID args+=argExpr+
     | let=letExpr
     | elim=elimExpr
     | left=expr op=('+'|'=') right=expr
     | num=NUM
     | id=idExpr;
argExpr : '(' parenthesized=expr ')'
        | num=NUM
        | id=idExpr;
letExpr : 'let' varName=ID ':' ty=expr ':=' val=expr 'in' body=expr;
idExpr : id=ID;
elimExpr : 'elim' discriminee=expr 'into' exts+=ctxExt* ':' intoTy=expr cases+=elimCase*;
elimCase : '|' exts+=ctxExt* ':' caseTy=expr '=>' body=expr;

// Lexer rules
ID : [a-zA-Z_][a-zA-Z0-9_']*;
NUM : [0-9]+;
WS : [ \t\r\n]+ -> skip;
