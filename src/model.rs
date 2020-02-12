use super::cwf::*;

pub trait Model {
    fn ctx_eq(&mut self, l: &Ctx, r: &Ctx) -> bool;
    fn morph_eq(&mut self, l: &Morph, r: &Morph) -> bool;
    fn ty_eq(&mut self, l: &Ty, r: &Ty) -> bool;
    fn tm_eq(&mut self, l: &Tm, r: &Tm) -> bool;

    fn empty_ctx(&mut self) -> Ctx;
    fn comprehension(&mut self, base: &Ctx, ty: &Ty) -> Ctx;
    fn weakening(&mut self, ty: &Ty) -> Morph;
    fn var(&mut self, ty: &Ty) -> Tm;

    fn id_morph(&mut self, ctx: &Ctx) -> Morph;
    fn compose(&mut self, g: &Morph, f: &Morph) -> Morph;
    fn extension(&mut self, morph: &Morph, ty: &Ty, tm: &Tm) -> Morph;

    fn subst_ty(&mut self, f: &Morph, ty: &Ty) -> Ty;
    fn subst_tm(&mut self, f: &Morph, tm: &Tm) -> Tm;

    fn eq(&mut self, l: &Tm, r: &Tm) -> Ty;
    fn refl(&mut self, tm: &Tm) -> Tm;

    fn bool_ty(&mut self, ctx: &Ctx) -> Ty;
    fn true_tm(&mut self, ctx: &Ctx) -> Tm;
    fn false_tm(&mut self, ctx: &Ctx) -> Tm;
    fn elim_bool(&mut self, into: &Ty, true_case: &Tm, false_case: &Tm) -> Tm;
}