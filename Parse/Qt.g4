grammar Qt;
// Parser rules
unit : def*;
def : 'def' name=ID ctxExt* ':' retTy=expr ':=' body=expr;
ctxExt : '(' names=ID+ ':' ty=expr ')';
expr : '(' parenthesized=expr ')' | let=letExpr | id=idExpr | elim=elimExpr | fun=expr arg=expr;
letExpr : 'let' varName=ID ':' ty=expr ':=' val=expr 'in' body=expr;
idExpr : ID;
elimExpr : 'elim' discriminee=expr 'as' varName=ID 'into' ctxExt* ':' intoTy=expr elimCase*;
elimCase : '|' ctxExt* ':' caseTy=expr '=>' body=expr;

// Lexer rules
ID : [a-zA-Z_][a-zA-Z0-9_']* ;
WS : [ \t\r\n]+ -> skip ; // skip spaces, tabs, newlines
