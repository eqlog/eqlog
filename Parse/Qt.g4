grammar Qt;
// Parser rules
unit : def*;
def : 'def' name=ID param* ':' retTy=ty ':=' body=expr;
param : '(' names=ID+ ':' ty ')';
ty : ID;
expr : letExpr | idExpr;
letExpr : 'let' varName=ID ':' ty ':=' val=expr 'in' body=expr;
idExpr : ID;

// Lexer rules
ID : [a-zA-Z_][a-zA-Z0-9_']* ;
WS : [ \t\r\n]+ -> skip ; // skip spaces, tabs, newlines