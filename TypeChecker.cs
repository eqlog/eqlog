using Microsoft.Z3;
using System;

namespace QT
{
    internal class TypeChecker : IDisposable
    {
        private readonly Context _ctx;
        private readonly Fixedpoint _fix;
        const string Z3Setup =
            @"
(declare-sort Ty)
(declare-sort Tm)
(declare-rel IsTy (Ty))
(declare-rel TmTy (Tm Ty))
(declare-rel 
(declare-rel Tm-Eq (Tm Tm))
(
";

        public TypeChecker()
        {
            _ctx = new Context();
            _fix = _ctx.MkFixedpoint();
            BoolExpr[] rels = _fix.ParseString(Z3Setup);
        }

        public bool Check(Unit unit, out string error)
        {
            error = "";

            return false;
        }

        public void Dispose()
        {
            _ctx.Dispose();
        }
    }
}
