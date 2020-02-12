use libc::{size_t, c_char};
use std::clone::Clone;
use std::collections::HashMap;
use std::ffi::CString;
use std::hash::Hash;
use super::model::Model;
use super::cwf::*;

mod phl {
    use libc::{size_t, c_char};
    extern {
        pub fn create_cwf() -> size_t;
        pub fn destroy_cwf(cwf: size_t);
        pub fn get_sort(name: *const c_char) -> size_t;
        pub fn get_operation(name: *const c_char) -> size_t;
        pub fn get_operation_arity(op: size_t) -> size_t;
        pub fn get_predicate(name: *const c_char) -> size_t;
        pub fn are_equal(pstruct: size_t, l: size_t, r: size_t) -> bool;
        pub fn define_operation(pstruct: size_t, op: size_t, args: *const size_t) -> size_t;
        pub fn define_predicate(pstruct: size_t, pred: size_t, args: *const size_t) -> size_t;
        pub fn compute_fixpoint(pstruct: size_t);
    }
}

fn get_op(name: &str) -> size_t {
    let cstr = CString::new(name).unwrap();
    unsafe { phl::get_operation(cstr.as_ptr()) }
}

lazy_static! {
    static ref DOM: size_t = get_op("dom");
    static ref COD: size_t = get_op("cod");
    static ref ID_MORPH: size_t = get_op("id");
    static ref COMP: size_t = get_op("comp");
    static ref TY_CTX: size_t = get_op("ty_ctx");
    static ref TM_TY: size_t = get_op("tm_ty");
    static ref SUBST_TY: size_t = get_op("subst_ty");
    static ref SUBST_TM: size_t = get_op("subst_tm");
    static ref EMPTY_CTX: size_t = get_op("empty_ctx");
    static ref CTX_EXT: size_t = get_op("ctx_ext");
    static ref WKN: size_t = get_op("wkn");
    static ref VAR: size_t = get_op("var");
    static ref MOR_EXT: size_t = get_op("mor_ext");
    static ref EQ_TY: size_t = get_op("Eq");
    static ref REFL: size_t = get_op("refl");
    static ref BOOL: size_t = get_op("bool");
    static ref TRUE: size_t = get_op("true");
    static ref FALSE: size_t = get_op("false");
    static ref BOOL_ELIM: size_t = get_op("bool_elim");
}

pub struct Cwf {
    pstruct: size_t,
    ctxs: HashMap<Ctx, size_t>,
    morphs: HashMap<Morph, size_t>,
    tys: HashMap<Ty, size_t>,
    tms: HashMap<Tm, size_t>
}

impl Cwf {
    pub fn new() -> Self {
        Cwf {
            pstruct: unsafe { phl::create_cwf() },
            ctxs: HashMap::new(),
            morphs: HashMap::new(),
            tys: HashMap::new(),
            tms: HashMap::new(),
        }
    }
}

impl Drop for Cwf {
    fn drop(&mut self) {
        unsafe { phl::destroy_cwf(self.pstruct) }
    }
}

impl Cwf {
    fn check_eq<T: Eq + Hash>(&self, map: &HashMap<T, size_t>, l: &T, r: &T) -> bool {
        let lid = map.get(l).unwrap();
        let rid = map.get(r).unwrap();
        unsafe { phl::are_equal(self.pstruct, *lid, *rid) }
    }

    fn def_op<T: Eq + Hash + Clone>(pstruct: size_t, map: &mut HashMap<T, size_t>, node: &T, op: size_t, args: &[size_t]) -> T {
        let id = unsafe {
            assert_eq!(args.len(), phl::get_operation_arity(op));
            phl::define_operation(pstruct, op, args.as_ptr())
        };
        map.insert((*node).clone(), id);
        (*node).clone()
    }
    fn def_ctx(&mut self, node: &Ctx, op: size_t, args: &[size_t]) -> Ctx {
        Cwf::def_op(self.pstruct, &mut self.ctxs, node, op, args)
    }
    fn def_morph(&mut self, node: &Morph, op: size_t, args: &[size_t]) -> Morph {
        Cwf::def_op(self.pstruct, &mut self.morphs, node, op, args)
    }
    fn def_ty(&mut self, node: &Ty, op: size_t, args: &[size_t]) -> Ty {
        Cwf::def_op(self.pstruct, &mut self.tys, node, op, args)
    }
    fn def_tm(&mut self, node: &Tm, op: size_t, args: &[size_t]) -> Tm {
        Cwf::def_op(self.pstruct, &mut self.tms, node, op, args)
    }

    fn get_ctx(&self, ctx: &Ctx) -> size_t {
        *self.ctxs.get(ctx).unwrap()
    }
    fn get_morph(&self, morph: &Morph) -> size_t {
        *self.morphs.get(morph).unwrap()
    }
    fn get_ty(&self, ty: &Ty) -> size_t {
        *self.tys.get(ty).unwrap()
    }
    fn get_tm(&self, tm: &Tm) -> size_t {
        *self.tms.get(tm).unwrap()
    }
}

impl Model for Cwf {
    fn ctx_eq(&self, l: &Ctx, r: &Ctx) -> bool {
        self.check_eq(&self.ctxs, l, r)
    }
    fn morph_eq(&self, l: &Morph, r: &Morph) -> bool {
        self.check_eq(&self.morphs, l, r)
    }
    fn ty_eq(&self, l: &Ty, r: &Ty) -> bool {
        self.check_eq(&self.tys, l, r)
    }
    fn tm_eq(&self, l: &Tm, r: &Tm) -> bool {
        self.check_eq(&self.tms, l, r)
    }

    fn empty_ctx(&mut self) -> Ctx {
        self.def_ctx(&Ctx::Empty, *EMPTY_CTX, &[])
    }
    fn comprehension(&mut self, base: &Ctx, ty: &Ty) -> Ctx {
        self.def_ctx(
            &Ctx::Comprehension(Box::new((*base).clone()), Box::new((*ty).clone())),
            *CTX_EXT,
            &[self.get_ctx(base), self.get_ty(ty)]
        )
    }
    fn weakening(&mut self, ty: &Ty) -> Morph {
        self.def_morph(
            &Morph::Weakening(Box::new((*ty).clone())),
            *WKN,
            &[self.get_ty(ty)]
        )
    }
    fn var(&mut self, ty: &Ty) -> Tm {
        self.def_tm(
            &Tm::Var(Box::new((*ty).clone())),
            *VAR,
            &[self.get_ty(ty)]
        )
    }

    fn id_morph(&mut self, ctx: &Ctx) -> Morph {
        self.def_morph(
            &Morph::Identity(Box::new((*ctx).clone())),
            *ID_MORPH,
            &[self.get_ctx(ctx)]
        )
    }
    fn compose(&mut self, g: &Morph, f: &Morph) -> Morph {
        self.def_morph(
            &Morph::Composition(Box::new((*g).clone()), Box::new((*f).clone())),
            *COMP,
            &[self.get_morph(g), self.get_morph(f)]
        )
    }
    fn extension(&mut self, f: &Morph, ty: &Ty, tm: &Tm) -> Morph {
        self.def_morph(
            &Morph::Extension(Box::new((*f).clone()), Box::new((*ty).clone()), Box::new((*tm).clone())),
            *MOR_EXT,
            &[self.get_morph(f), self.get_ty(ty), self.get_tm(tm)]
        )
    }

    fn subst_ty(&mut self, f: &Morph, ty: &Ty) -> Ty {
        self.def_ty(
            &Ty::Subst(Box::new((*f).clone()), Box::new((*ty).clone())),
            *SUBST_TY,
            &[self.get_morph(f), self.get_ty(ty)]
        )
    }
    fn subst_tm(&mut self, f: &Morph, tm: &Tm) -> Tm {
        self.def_tm(
            &Tm::Subst(Box::new((*f).clone()), Box::new((*tm).clone())),
            *SUBST_TM,
            &[self.get_morph(f), self.get_tm(tm)]
        )
    }

    fn eq(&mut self, l: &Tm, r: &Tm) -> Ty {
        self.def_ty(
            &Ty::Eq(Box::new((*l).clone()), Box::new((*r).clone())),
            *EQ_TY,
            &[self.get_tm(l), self.get_tm(r)]
        )
    }
    fn refl(&mut self, tm: &Tm) -> Tm {
        self.def_tm(
            &Tm::Refl(Box::new((*tm).clone())),
            *REFL,
            &[self.get_tm(tm)]
        )
    }

    fn bool_ty(&mut self, ctx: &Ctx) -> Ty {
        self.def_ty(
            &Ty::Bool(Box::new((*ctx).clone())),
            *BOOL,
            &[self.get_ctx(ctx)]
        )
    }
    fn true_tm(&mut self, ctx: &Ctx) -> Tm {
        self.def_tm(
            &Tm::True(Box::new((*ctx).clone())),
            *TRUE,
            &[self.get_ctx(ctx)]
        )
    }
    fn false_tm(&mut self, ctx: &Ctx) -> Tm {
        self.def_tm(
            &Tm::True(Box::new((*ctx).clone())),
            *TRUE,
            &[self.get_ctx(ctx)]
        )
    }
    fn elim_bool(&mut self, into: &Ty, true_case: &Tm, false_case: &Tm) -> Tm {
        self.def_tm(
            &Tm::ElimBool(Box::new((*into).clone()), Box::new((*true_case).clone()), Box::new((*false_case).clone())),
            *BOOL_ELIM,
            &[self.get_ty(into), self.get_tm(true_case), self.get_tm(false_case)]
        )
    }
}
