#pragma once

#include <phl.hpp>

namespace cwf
{

using namespace symbolic_term_equality;

const sort
    ctx = "Ctx",
    mor = "Mor",
    ty = "Ty",
    tm = "Tm";

const operation
    dom = {"dom", {mor}, ctx},
    cod = {"cod", {mor}, ctx},
    id = {"id", {ctx}, mor},
    comp = {"comp", {mor, mor}, mor},
    ty_ctx = {"ty_ctx", {ty}, ctx},
    tm_ty = {"tm_ty", {tm}, ty},
    subst_ty = {"subst_ty", {mor, ty}, ty},
    subst_tm = {"subst_tm", {mor, ty}, ty},
    empty_ctx = {"empty_ctx", {}, ctx},
    ctx_ext = {"ctx_ext", {ty}, ctx},
    wkn = {"wkn", {ty}, mor},
    var = {"var", {ty}, tm},
    mor_ext = {"mor_ext", {mor, ty, tm}, mor},
    Eq = {"Eq", {tm, tm}, ty},
    refl = {"refl", {tm}, tm},
    bool_ = {"bool", {ctx}, ty},
    true_ = {"true", {ctx}, tm},
    false_ = {"false", {ctx}, tm},
    bool_elim = {"bool_elim", {ctx, ty, tm, tm}, tm};

const phl_signature cwf_signature = {
    {ctx, mor, ty, tm},
    {},
    {
        dom, cod,
        id, comp,
        subst_ty, subst_tm,
        empty_ctx, ctx_ext,
        ctx_ext, wkn, var, mor_ext,
        bool_, true_, false_, bool_elim
    }
};

const term
    G = "G",
    G0 = "G0",
    D = "D",
    D0 = "D0";

const term
    f = "f",
    f0 = "f0",
    ft = "ft",
    ff = "ff",
    g = "g",
    g0 = "g0",
    h = "h",
    i0 = "i0",
    i1 = "i1",
    w = "w",
    fb = "fb",
    idfb = "idfb";

const term
    A = "A",
    A0 = "A0",
    At = "At",
    Af = "Af",
    B = "B",
    B0 = "B0",
    C = "C";

const term
    a = "a",
    a0 = "a0",
    a1 = "a1",
    at = "at",
    atf = "atf",
    atf0 = "atf0",
    af = "af",
    aff = "aff",
    aff0 = "aff0",
    b = "b",
    b0 = "b0",
    c = "c",
    r = "r",
    r0 = "r0",
    afb = "afb",
    afb0 = "afb0";

const phl_theory cwf = {
    cwf_signature,
    // injective axioms:
    {
        truth |= !dom(f),
        truth |= !cod(f),
        truth |= !id(G),
        cod(f) == dom(g) |= !comp(g, f),
        truth |= !ty_ctx(A),
        truth |= !tm_ty(a),
        ty_ctx(A) == dom(f) |= !subst_ty(f, A),
        ty_ctx(a) == dom(f) |= !subst_tm(f, A),
        truth |= !empty_ctx(),
        truth |= !ctx_ext(A),
        truth |= !wkn(A),
        truth |= !var(A),
        subst_ty(f, A) == tm_ty(b) |= !mor_ext(f, A, b),
        tm_ty(a0) == tm_ty(a1) |= !Eq(a0, a1),
        truth |= !refl(a),
        truth |= !bool_(G),
        truth |= !true_(G),
        truth |= !false_(G),
        ft == mor_ext(id(G), bool_(G), true_(G)) &&
            ff == mor_ext(id(G), bool_(G), false_(G)) &&
            At == subst_ty(ft, A) &&
            Af == subst_ty(ff, A) &&
            tm_ty(at) == At &&
            tm_ty(af) == Af |=
            !bool_elim(G, A, at, af)
    },
    // surjective axioms:
    {
        truth |= G == dom(id(G)),
        G0 == dom(id(G)) |= G == G0,
        G0 == cod(id(G)) |= G == G0,
        f0 == comp(id(G), f) |= f == f0,
        f0 == comp(f, id(G)) |= f == f0,
        i0 == comp(comp(f, g), h) && i1 == comp(f, comp(g, h)) |= i0 == i1,
        G == dom(f) && D == cod(f) && subst_ty(f, A) == B && D0 == ty_ctx(B) |= D == D0,
        A == tm_ty(a) && b == subst_tm(f, a) && B == subst_ty(f, A) && B0 == tm_ty(b) |= B == B0,
        w == wkn(A) && G0 == dom(w) |= G == G0,
        w == wkn(A) && D == ctx_ext(A) && D0 == cod(w) |= D == D0,
        w == wkn(A) && B == subst_ty(w, A) && B0 == tm_ty(var(A)) |= B == B0,
        g == mor_ext(f, A, b) && w == wkn(A) && f0 == comp(g, w) |= f == f0,
        g == mor_ext(f, A, b) && b0 == subst_tm(g, var(A)) |= b == b0,
        w == wkn(A) && g == mor_ext(f, A, b) && f == comp(g0, w) && b == subst_tm(g0, var(A)) |= g == g0,
        G == ty_ctx(tm_ty(a)) && G0 == ty_ctx(Eq(a, b)) |= G == G0,
        tm_ty(c) == Eq(a, b) |= a == b,
        B0 == tm_ty(refl(a)) && B == Eq(a, a) |= B0 == B,
        tm_ty(c) == tm_ty(refl(a)) |= c == refl(a),
        B == Eq(subst_tm(f, a), subst_tm(f, b)) && B0 == subst_ty(f, Eq(a, b)) |= B == B0,
        r == refl(subst_tm(f, a)) && r0 == subst_tm(f, refl(a)) |= r == r0,
        B == bool_(G) && G0 == ty_ctx(B) |= G == G0,
        b == true_(G) && B == bool_(G) && B0 == tm_ty(b) |= B == B0,
        b == false_(G) && B == bool_(G) && B0 == tm_ty(b) |= B == B0,
        b == true_(G) && G0 == ty_ctx(tm_ty(b)) |= G == G0,
        b == false_(G) && G0 == ty_ctx(tm_ty(b)) |= G == G0,
        a == bool_elim(G, A, at, af) && A0 == tm_ty(a) |= A == A0,
        a == bool_elim(G, A, at, af) &&
            ft == mor_ext(f, A, true_(D)) &&
            atf == subst_tm(f, at) &&
            atf0 == subst_tm(ft, a) |=
            atf == atf0,
        a == bool_elim(G, A, at, af) &&
            ff == mor_ext(f, A, false_(D)) &&
            aff == subst_tm(f, af) &&
            aff0 == subst_tm(ff, a) |=
            aff == aff0,
        a == bool_elim(G, A, at, af) &&
            ft == mor_ext(id(G), A, true_(G)) &&
            ff == mor_ext(id(G), A, false_(G)) &&
            subst_tm(ft, a0) == at &&
            subst_tm(ff, a0) == af |=
            a == a0,
        cod(f) == D && B == bool_(D) && B0 == subst_ty(f, bool_(G)) |= B == B0,
        cod(f) == D && b == true_(D) && b0 == subst_tm(f, true_(G)) |= b == b0,
        cod(f) == D && b == false_(D) && b0 == subst_tm(f, false_(G)) |= b == b0,
        fb == mor_ext(f, A, b) &&
            afb == subst_tm(fb, bool_elim(G, A, at, af)) &&
            idfb == mor_ext(id(D), subst_tm(f, b)) &&
            afb0 == subst_tm(idfb, bool_elim(D, subst_ty(fb, A), subst_tm(f, at), subst_tm(f, af))) |=
            afb  == afb0
    }
};

}
