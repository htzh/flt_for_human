"""Modular q-expansions — illustrative demo.

CONCEPT
    In the ring of formal q-expansions with integer coefficients:

        E_4 = 1 + 240 sum sigma_3(n) q^n,
        E_6 = 1 - 504 sum sigma_5(n) q^n,
        Delta = (E_4^3 - E_6^2)/1728 = q prod_{n>=1} (1 - q^n)^24 = sum tau(n) q^n,
        j = E_4^3 / Delta = q^-1 + 744 + 196884 q + 21493760 q^2 + ... .

    A normalized eigenform f = sum a_n q^n has a_1 = 1, is multiplicative on
    coprime indices, and satisfies the Hecke recursion

        a_{p^(r+2)} = a_p a_{p^(r+1)} - p^(k-1) a_{p^r}

    at primes p not dividing the level, k being the weight (so p^11 for Delta).
    If p divides the level the correction term is dropped.

FLT ANCHOR
    ModularCurve.eisenstein4         (Def_ModularCurve_X0.lean, line 111)
    ModularCurve.eisenstein6         (Def_ModularCurve_TateFormal.lean, line 35)
    ModularCurve.etaProd             (Def_ModularCurve_X0.lean, line 119)
    ModularCurve.dedekindEtaUnit     (line 128)   etaProd^24 = Delta/q
    ModularCurve.dedekindEtaUnitInv  (line 132)
    ModularCurve.jNum                (line 142)   eisenstein4^3 * dedekindEtaUnitInv
    ModularCurve.jq                  (line 155)   q^-1 * jNum
    CuspForm.IsNormalizedEigenform   (Def_FLTPrelim_Modularity.lean, line 28)

WHY IT MATTERS FOR FLT
    The proof's modular side is carried by q-expansions: a Frey curve is shown
    to be modular by attaching its Galois representation to a normalized
    eigenform, whose coefficients a_l are matched against traces of Frobenius
    (frobenius_charpoly), and the level-lowering steps keep track of which
    coefficients survive.  The Eisenstein series and Delta are the explicit
    members of that ring -- Delta generating the cusp forms of level one, E_4
    and E_6 the ring of level-one modular forms -- and j is the Hauptmodul the
    function-field notes use (base/004, math/010).

RUN
    python3 modular_qexp.py
    python3 modular_qexp.py > modular_qexp.expected.txt
"""

import math

from ffcurve.qexp import (add, delta, delta_from_eisenstein, delta_over_q,
                          eisenstein4, eisenstein6, eta_prod, j_coeffs, j_num,
                          mul, pow_series, scale, sub, tau)
from report import Report

N = 64  # precision: coefficients of q^0 .. q^(N-1)


def coeffs_line(c, hi=6):
    return ", ".join(str(c[k]) for k in range(min(hi, len(c))))


def main():
    R = Report("Modular q-expansions")

    R.note("""
        This demo works in the ring Z[[q]] of formal q-expansions with integer
        coefficients, truncated to q^63.  Its arithmetic is exact integer
        arithmetic, so the classical identities below are checked coefficient
        by coefficient rather than numerically.
    """)

    # ---- 1 -------------------------------------------------------------
    R.section("1. The Eisenstein series E_4 and E_6")
    R.note("""
        E_4 and E_6 are the level-one Eisenstein series: their q-coefficients
        are divisor sums, 240 sigma_3(n) and -504 sigma_5(n), and both have
        constant term 1.  They generate the ring of level-one modular forms.
    """)
    e4, e6 = eisenstein4(N), eisenstein6(N)
    R.data(f"E_4 = 1 + 240 sum sigma_3(n) q^n = {coeffs_line(e4)} + ...")
    R.data(f"E_6 = 1 - 504 sum sigma_5(n) q^n = {coeffs_line(e6)} + ...")
    R.check("E_4 has constant term 1 and integer coefficients",
            e4[0] == 1 and all(isinstance(c, int) for c in e4))
    R.check("E_6 has constant term 1 and integer coefficients",
            e6[0] == 1 and all(isinstance(c, int) for c in e6))
    R.check("the coefficients are the divisor sums 240 sigma_3(n), -504 sigma_5(n)",
            all(e4[n] == 240 * sum(d ** 3 for d in range(1, n + 1) if n % d == 0)
                for n in range(1, 12))
            and all(e6[n] == -504 * sum(d ** 5 for d in range(1, n + 1) if n % d == 0)
                    for n in range(1, 12)))

    # ---- 2 -------------------------------------------------------------
    R.section("2. Delta two ways, and the Ramanujan tau function")
    R.note("""
        Delta is a cusp form of weight 12 and level 1.  It can be written as
        the eta product q prod (1 - q^n)^24 or as (E_4^3 - E_6^2)/1728; the
        two definitions agree to every computed coefficient.  Its
        coefficients are Ramanujan's tau function.
    """)
    d_eta, d_eis = delta(N), delta_from_eisenstein(N)
    t = tau(N)
    R.data(f"Delta = q prod (1 - q^n)^24  = {coeffs_line(d_eta)} + ...")
    R.data(f"Delta = (E_4^3 - E_6^2)/1728 = {coeffs_line(d_eis)} + ...")
    R.data(f"tau(n) for n = 1..11: {', '.join(str(t[n]) for n in range(1, 12))}")
    R.check("the eta product and the Eisenstein expression define the same series",
            d_eta == d_eis)
    R.check("E_4^3 - E_6^2 = 1728 Delta",
            sub(pow_series(e4, 3, N), pow_series(e6, 2, N), N)
            == scale(d_eta, 1728, N))
    R.check("Delta/q has constant term 1, integer coefficients and is a unit",
            delta_over_q(N)[0] == 1
            and all(isinstance(c, int) for c in delta_over_q(N)))
    R.check("tau(1) = 1 and Delta starts q - 24q^2 + 252q^3 - 1472q^4 + 4830q^5",
            [t[n] for n in range(1, 6)] == [1, -24, 252, -1472, 4830])

    # ---- 3 -------------------------------------------------------------
    R.section("3. The Hecke recursions for an eigenform")
    R.note("""
        A normalized eigenform is multiplicative on coprime indices and its
        prime-power coefficients satisfy
        a_{p^(r+2)} = a_p a_{p^(r+1)} - p^(k-1) a_{p^r} for p not dividing the
        level.  Delta is the level-one weight-12 case, so the correction is
        p^11; the formalization states the weight-2 version with -p (plus a
        variant with no correction term when p does divide the level).
    """)
    coprime_ok = all(
        t[m * n] == t[m] * t[n]
        for m in range(1, N) for n in range(1, N)
        if m * n < N and math.gcd(m, n) == 1)
    rec_ok, rows = True, []
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        r = 0
        while p ** (r + 2) < N:
            lhs = t[p ** (r + 2)]
            rhs = t[p] * t[p ** (r + 1)] - p ** 11 * t[p ** r]
            rows.append((p, r, lhs, rhs))
            rec_ok = rec_ok and lhs == rhs
            r += 1
    R.data("prime-power check  tau(p^(r+2)) = tau(p) tau(p^(r+1)) - p^11 tau(p^r)")
    for (p, r, lhs, rhs) in rows[:6]:
        R.data(f"  p = {p}, r = {r}:  {lhs} = tau({p}) tau({p ** (r + 1)})"
               f" - {p}^11 tau({p ** r}) = {rhs}")
    R.check("tau(m n) = tau(m) tau(n) for all coprime m, n", coprime_ok)
    R.check("the weight-12 prime-power recursion holds for every computed prime",
            rec_ok)

    # ---- 4 -------------------------------------------------------------
    R.section("4. The Hauptmodul j")
    R.note("""
        j = E_4^3 / Delta has a simple pole at the cusp and integer
        coefficients.  The formalization stores it as jq = q^-1 * jNum with
        jNum = E_4^3 * (Delta/q)^-1, which is the same series with the pole
        divided out: jNum = 1 + 744 q + 196884 q^2 + ... .
    """)
    jn = j_num(N)
    j = j_coeffs(N)
    R.data(f"jNum = E_4^3 * (Delta/q)^-1 = {coeffs_line(jn)} + ...")
    def jterm(e):
        if e == 0:
            return str(j[0])
        if e == -1:
            return "q^-1"
        if e == 1:
            return "q" if j[1] == 1 else f"{j[1]} q"
        return f"{j[e]} q^{e}"

    R.data("j = " + " + ".join(jterm(e) for e in (-1, 0, 1, 2)) + " + ...")
    R.check("jNum has constant term 1 and integer coefficients",
            jn[0] == 1 and all(isinstance(c, int) for c in jn))
    R.check("j = q^-1 + 744 + 196884 q + 21493760 q^2 + ...",
            [j[-1], j[0], j[1], j[2]] == [1, 744, 196884, 21493760])
    R.check("j has a simple pole at the cusp (the lowest exponent is -1)",
            min(j) == -1)
    R.check("jNum * (Delta/q) = E_4^3",
            mul(jn, delta_over_q(N), N) == pow_series(e4, 3, N))

    # ---- 5 -------------------------------------------------------------
    R.section("5. The formalization")
    R.note("""
        All of the above are power series over Z in the formalization:
        eisenstein4 and eisenstein6 by divisor sums, etaProd as the product
        prod (1 - q^(n+1)), dedekindEtaUnit = etaProd^24 (that is Delta/q, not
        Delta), dedekindEtaUnitInv its inverse, jNum = eisenstein4^3 *
        dedekindEtaUnitInv, and jq = q^-1 * jNum.  Keeping Delta/q rather than
        Delta is why jNum is a unit in Z[[q]] with constant term 1.
    """)
    R.note("""
        CuspForm.IsNormalizedEigenform records the eigenform axioms as four
        clauses on qCoeff: a_1 = 1; a_{mn} = a_m a_n for coprime m, n; the
        weight-2 recursion a_{p^(r+2)} = a_p a_{p^(r+1)} - p a_{p^r} for
        p not dividing the level; and a_{p^(r+2)} = a_p a_{p^(r+1)} for p
        dividing it.  The demo checks the weight-12 case of the same shape,
        which is what Delta satisfies.
    """)

    R.finish()


if __name__ == "__main__":
    main()
