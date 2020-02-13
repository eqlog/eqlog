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
        dom(id(G)) -= G,
        cod(id(G)) -= G,
        comp(id(G), f) -= f,
        comp(f, id(G)) -= f,
        ty_ctx(subst_ty(f, A)) -= cod(f),
        tm_ty(subst_tm(f, a)) -= subst_ty(f, tm_ty(a)),
        dom(wkn(A)) -= ty_ctx(A),
        cod(wkn(A)) -= ctx_ext(A),
        tm_ty(var(A)) -= subst_ty(w, A),
        dom(mor_ext(f, A, b)) -= ctx_ext(A),
        cod(mor_ext(f, A, b)) -= cod(f),
        comp(mor_ext(f, A, b), w) -= f,
        subst_tm(mor_ext(f, A, b), var(A)) -= b,
        w == wkn(A) && g == mor_ext(f, A, b) && f == comp(g0, w) && b == subst_tm(g0, var(A)) |= g == g0,
        !Eq(a, b) && A == tm_ty(a) && A0 == tm_ty(b) |= A == A0,
        ty_ctx(Eq(a, b)) -= ty_ctx(tm_ty(a)),
        tm_ty(c) == Eq(a, b) |= a == b,
        tm_ty(c) == Eq(a, b) && r == refl(a) |= c == r,
        tm_ty(refl(a)) -= Eq(a, a),
        subst_ty(f, Eq(a, b)) -= Eq(subst_tm(f, a), subst_tm(f, b)),
        subst_tm(f, refl(a)) -= refl(subst_tm(f, a)),
        ty_ctx(bool_(G)) -= G,
        tm_ty(true_(G)) -= bool_(G),
        tm_ty(false_(G)) -= bool_(G),
        tm_ty(bool_elim(G, A, at, af)) -= A,
        subst_tm(mor_ext(f, bool_(G), true_(D)), bool_elim(G, A, at, af)) -= subst_tm(f, at),
        subst_tm(mor_ext(f, bool_(G), false_(D)), bool_elim(G, A, at, af)) -= subst_tm(f, af),
        a == bool_elim(G, A, at, af) &&
            subst_tm(mor_ext(id(G), A, true_(G)), a0) == at &&
            subst_tm(mor_ext(id(G), A, false_(G)), a0) == af |=
            a == a0,
        subst_ty(f, bool_(G)) -= bool_(cod(f)),
        subst_tm(f, true_(G)) -= true_(cod(f)),
        subst_tm(f, false_(G)) -= false_(cod(f)),
        subst_tm(mor_ext(f, A, b), bool_elim(G, A, at, af)) -=
            subst_tm(mor_ext(id(cod(f)), b), bool_elim(cod(f), subst_ty(f, A), subst_tm(at), subst_tm(af)))
    }
};

}
