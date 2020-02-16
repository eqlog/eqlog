use libc::{size_t};
use std::clone::Clone;
use std::collections::HashMap;
use std::ffi::CString;
use std::hash::Hash;
use super::model::Model;
use super::cwf::*;

mod phl {
    use libc::{size_t, c_char};
    #[allow(dead_code)]
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
    tms: HashMap<Tm, size_t>,
    dirty: bool
}

impl Cwf {
    pub fn new() -> Self {
        Cwf {
            pstruct: unsafe { phl::create_cwf() },
            ctxs: HashMap::new(),
            morphs: HashMap::new(),
            tys: HashMap::new(),
            tms: HashMap::new(),
            dirty: false
        }
    }
}

impl Drop for Cwf {
    fn drop(&mut self) {
        unsafe { phl::destroy_cwf(self.pstruct) }
    }
}

impl Cwf {
    pub fn check_id_eq(&mut self, lid: size_t, rid: size_t) -> bool {
        if self.dirty {
            unsafe { phl::compute_fixpoint(self.pstruct) };
            self.dirty = false
        }
        unsafe { phl::are_equal(self.pstruct, lid, rid) }
    }

    fn check_eq<T: Eq + Hash, F>(&mut self, map: F, l: &T, r: &T) -> bool
        where F: FnOnce(&Self) -> &HashMap<T, size_t>
    {
        let map = map(self);
        let lid = *map.get(l).unwrap();
        let rid = *map.get(r).unwrap();
        self.check_id_eq(lid, rid)
    }

    pub fn def_op(&mut self, op: size_t, args: &[size_t]) -> size_t {
        self.dirty = true;
        unsafe {
            assert_eq!(args.len(), phl::get_operation_arity(op));
            phl::define_operation(self.pstruct, op, args.as_ptr())
        }
    }

    fn def_op_syn<T: Eq + Hash + Clone, F>(&mut self, map: F, node: &T, op: size_t, args: &[size_t]) -> size_t
        where F: FnOnce(&mut Self) -> &mut HashMap<T, size_t>
    {
        let id = self.def_op(op, args);
        map(self).insert(node.clone(), id);
        id
    }
    fn def_ctx(&mut self, node: Ctx, op: size_t, args: &[size_t]) -> Ctx {
        self.def_op_syn(|s| &mut s.ctxs, &node, op, args);
        node
    }
    fn def_morph(&mut self, node: Morph, op: size_t, args: &[size_t]) -> Morph {
        let id = self.def_op_syn(|s| &mut s.morphs, &node, op, args);
        self.def_op(*DOM, &[id]);
        self.def_op(*COD, &[id]);
        node
    }
    fn def_ty(&mut self, node: Ty, op: size_t, args: &[size_t]) -> Ty {
        let id = self.def_op_syn(|s| &mut s.tys, &node, op, args);
        self.def_op(*TY_CTX, &[id]);
        node
    }
    fn def_tm(&mut self, node: Tm, op: size_t, args: &[size_t]) -> Tm {
        let id = self.def_op_syn(|s| &mut s.tms, &node, op, args);
        self.def_op(*TM_TY, &[id]);
        node
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
    fn ctx_eq(&mut self, l: &Ctx, r: &Ctx) -> bool {
        self.check_eq(|s| &s.ctxs, l, r)
    }
    fn morph_eq(&mut self, l: &Morph, r: &Morph) -> bool {
        self.check_eq(|s| &s.morphs, l, r)
    }
    fn ty_eq(&mut self, l: &Ty, r: &Ty) -> bool {
        self.check_eq(|s| &s.tys, l, r)
    }
    fn tm_eq(&mut self, l: &Tm, r: &Tm) -> bool {
        self.check_eq(|s| &s.tms, l, r)
    }

    fn empty_ctx(&mut self) -> Ctx {
        self.def_ctx(Ctx::Empty, *EMPTY_CTX, &[])
    }
    fn comprehension(&mut self, ty: &Ty) -> Ctx {
        self.def_ctx(
            Ctx::Comprehension(Box::new(ty.clone())),
            *CTX_EXT,
            &[self.get_ty(ty)]
        )
    }
    fn weakening(&mut self, ty: &Ty) -> Morph {
        self.def_morph(
            Morph::Weakening(Box::new(ty.clone())),
            *WKN,
            &[self.get_ty(ty)]
        )
    }
    fn var(&mut self, ty: &Ty) -> Tm {
        self.def_tm(
            Tm::Var(Box::new(ty.clone())),
            *VAR,
            &[self.get_ty(ty)]
        )
    }

    fn id_morph(&mut self, ctx: &Ctx) -> Morph {
        self.def_morph(
            Morph::Identity(Box::new(ctx.clone())),
            *ID_MORPH,
            &[self.get_ctx(ctx)]
        )
    }
    fn compose(&mut self, g: &Morph, f: &Morph) -> Morph {
        self.def_morph(
            Morph::Composition(Box::new(g.clone()), Box::new(f.clone())),
            *COMP,
            &[self.get_morph(g), self.get_morph(f)]
        )
    }
    fn extension(&mut self, f: &Morph, ty: &Ty, tm: &Tm) -> Morph {
        self.def_morph(
            Morph::Extension(Box::new(f.clone()), Box::new(ty.clone()), Box::new(tm.clone())),
            *MOR_EXT,
            &[self.get_morph(f), self.get_ty(ty), self.get_tm(tm)]
        )
    }

    fn subst_ty(&mut self, f: &Morph, ty: &Ty) -> Ty {
        self.def_ty(
            Ty::Subst(Box::new(f.clone()), Box::new(ty.clone())),
            *SUBST_TY,
            &[self.get_morph(f), self.get_ty(ty)]
        )
    }
    fn subst_tm(&mut self, f: &Morph, tm: &Tm) -> Tm {
        self.def_tm(
            Tm::Subst(Box::new(f.clone()), Box::new(tm.clone())),
            *SUBST_TM,
            &[self.get_morph(f), self.get_tm(tm)]
        )
    }

    fn eq_ty(&mut self, l: &Tm, r: &Tm) -> Ty {
        self.def_ty(
            Ty::Eq(Box::new(l.clone()), Box::new(r.clone())),
            *EQ_TY,
            &[self.get_tm(l), self.get_tm(r)]
        )
    }
    fn refl(&mut self, tm: &Tm) -> Tm {
        self.def_tm(
            Tm::Refl(Box::new(tm.clone())),
            *REFL,
            &[self.get_tm(tm)]
        )
    }

    fn bool_ty(&mut self, ctx: &Ctx) -> Ty {
        self.def_ty(
            Ty::Bool(Box::new(ctx.clone())),
            *BOOL,
            &[self.get_ctx(ctx)]
        )
    }
    fn true_tm(&mut self, ctx: &Ctx) -> Tm {
        self.def_tm(
            Tm::True(Box::new(ctx.clone())),
            *TRUE,
            &[self.get_ctx(ctx)]
        )
    }
    fn false_tm(&mut self, ctx: &Ctx) -> Tm {
        self.def_tm(
            Tm::False(Box::new(ctx.clone())),
            *FALSE,
            &[self.get_ctx(ctx)]
        )
    }
    fn elim_bool(&mut self, base_ctx: &Ctx, into: &Ty, true_case: &Tm, false_case: &Tm) -> Tm {
        self.def_tm(
            Tm::ElimBool(
                Box::new(base_ctx.clone()),
                Box::new(into.clone()),
                Box::new(true_case.clone()),
                Box::new(false_case.clone())),
            *BOOL_ELIM,
            &[self.get_ctx(base_ctx), self.get_ty(into),
              self.get_tm(true_case), self.get_tm(false_case)]
        )
    }
}

#[test]
fn functionality1() {
    let mut cwf = Cwf::new();
    let empty = cwf.def_op(*EMPTY_CTX, &[]);
    let bool1 = cwf.def_op(*BOOL, &[empty]);
    let bool2 = cwf.def_op(*BOOL, &[empty]);
    let id_morph = cwf.def_op(*ID_MORPH, &[empty]);
    let subst_bool1 = cwf.def_op(*SUBST_TY, &[id_morph, bool1]);
    unsafe { phl::compute_fixpoint(cwf.pstruct) }
    let subst_bool2 = cwf.def_op(*SUBST_TY, &[id_morph, bool2]);
    assert!(cwf.check_id_eq(subst_bool1, subst_bool2));
}

#[test]
fn eq_subst() {
    // f(a == a) = fa == fa
    let mut cwf = Cwf::new();
    let empty = cwf.empty_ctx();
    let empty_bool = cwf.bool_ty(&empty);
    let bool_ctx = cwf.comprehension(&empty_bool);
    let a = cwf.var(&empty_bool);
    let aeq = cwf.eq_ty(&a, &a);
    let bool_ctx_bool = cwf.bool_ty(&bool_ctx);
    // f injects to context with another variable
    let f = cwf.weakening(&bool_ctx_bool);
    let faa = cwf.subst_ty(&f, &aeq);
    let fa = cwf.subst_tm(&f, &a);
    let fafa = cwf.eq_ty(&fa, &fa);
    assert!(cwf.ty_eq(&fafa, &faa));
}

#[test]
fn subst_id() {
    let mut cwf = Cwf::new();
    let empty = cwf.empty_ctx();
    let id = cwf.id_morph(&empty);
    let true_tm = cwf.true_tm(&empty);
    let eq_true_true = cwf.eq_ty(&true_tm, &true_tm);
    let refl_eq_true_true = cwf.refl(&true_tm);
    let subst_eq_true_true = cwf.subst_ty(&id, &eq_true_true);
    assert!(cwf.ty_eq(&eq_true_true, &subst_eq_true_true));
    let subst_refl_eq_true_true = cwf.subst_tm(&id, &refl_eq_true_true);
    assert!(cwf.tm_eq(&refl_eq_true_true, &subst_refl_eq_true_true));
}