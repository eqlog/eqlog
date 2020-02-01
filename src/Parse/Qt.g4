grammar Qt;
// Parser rules
unit : defs+=def*;
def : 'def' name=defId exts+=ctxExt* ':' retTy=expr ':=' body=expr '.';
ctxExt : '(' names+=defId+ ':' ty=expr ')';
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
letExpr : 'let' varName=defId ':' ty=expr ':=' val=expr 'in' body=expr;
idExpr : id=ID;
defId : id=ID | DISCARD;
elimExpr : 'elim' discriminee=expr 'into' exts+=ctxExt* ':' intoTy=expr cases+=elimCase*;
elimCase : '|' exts+=ctxExt* '=>' body=expr;

// Lexer rules
DISCARD : '_';
COMMENT : '(*' (COMMENT|.)*? '*)' -> skip;
ID : [a-zA-Z_][a-zA-Z0-9_']*;
NUM : [0-9]+;
WS : [ \t\r\n]+ -> skip;
