using System;
using System.Collections.Generic;
using System.Linq;

namespace QT
{
    internal abstract class SyntaxNode
    {
    }

    internal class Unit : SyntaxNode
    {
        private readonly List<Def> _defs;

        public Unit(List<Def> defs)
        {
            _defs = defs;
        }

        public IReadOnlyList<Def> Definitions => _defs;

        public override string ToString()
            => string.Join(Environment.NewLine + Environment.NewLine, _defs);
    }

    internal class Def : SyntaxNode
    {
        private readonly List<Param> _params;

        public Def(string name, List<Param> @params, Ty retTy, Expr body)
        {
            Name = name;
            _params = @params;
            RetTy = retTy;
            Body = body;
        }

        public string Name { get; }
        public IReadOnlyList<Param> Params => _params;
        public Ty RetTy { get; }
        public Expr Body { get; }

        public override string ToString()
        {
            string paramsStr = string.Join(" ", Params.Select(p => $"({p})"));
            return $"def {Name} {paramsStr} : {RetTy} :={Environment.NewLine}  {Body}";
        }
    }

    internal class Param : SyntaxNode
    {
        public Param(string name, Ty type)
        {
            Name = name;
            Type = type;
        }

        public string Name { get; }
        public Ty Type { get; }

        public override string ToString()
            => $"{Name} : {Type}";
    }

    internal class Ty : SyntaxNode
    {
        public Ty(string id)
        {
            Id = id;
        }

        public string Id { get; }

        public override string ToString()
            => Id;
    }

    internal abstract class Expr : SyntaxNode
    {
    }

    internal class LetExpr : Expr
    {
        public LetExpr(string id, Ty type, Expr val, Expr body)
        {
            Id = id;
            Type = type;
            Val = val;
            Body = body;
        }

        public string Id { get; }
        public Ty Type { get; }
        public Expr Val { get; }
        public Expr Body { get; }

        public override string ToString()
            => $"let {Id} : {Type} := {Val} in {Body}";
    }

    internal class IdExpr : Expr
    {
        public IdExpr(string id)
        {
            Id = id;
        }

        public string Id { get; }

        public override string ToString()
            => Id;
    }
}
