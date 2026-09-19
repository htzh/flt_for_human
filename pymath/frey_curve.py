"""The Frey curve — illustrative demo.

CONCEPT
    A Frey package is a solution of a^p + b^p = c^p with p >= 5 prime,
    gcd(a,b) = 1, a = 3 mod 4 and 2 | b.  Its curve is

        y^2 = x (x - a^p) (x + b^p),

    with the integral model
    y^2 + xy = x^3 + ((b^p - 1 - a^p)/4) x^2 - (a^p b^p / 16) x.
    Writing X = a^p, Y = b^p, Z = X + Y = c^p,

        Delta = X^2 Y^2 Z^2 / 2^8 = (a b c)^(2p) / 2^8,
        c_4   = X^2 + X Y + Y^2 = Z^2 - X Y = c^(2p) - (a b)^p,
        j     = 2^8 (X^2 + X Y + Y^2)^3 / (X Y Z)^2.

    Delta * 2^8 is a p-th power, and the curve is semistable: at every prime
    q | a b c the value c_4 is a unit, so the reduction is multiplicative.
    Hence the conductor is the squarefree number rad(a b c).

FLT ANCHOR
    FreyPackage, freyCurveInt, freyCurve  (Def_FLTPrelim_FreyPackage.lean, lines 83, 90)
    FreyCurve.Delta                       (Def_FreyCurve_Basic.lean, line 9)
    FreyCurve.c4, FreyCurve.c4'           (Def_FreyCurve_Basic.lean, lines 32, 36)
    IsSemistableModel                     (Def_FLTPrelim_Modularity.lean, line 85)
    IsConductorLevel, sq_not_dvd          (Def_FreyPackage_IsConductorLevel.lean)

WHY IT MATTERS FOR FLT
    The Frey curve turns a counterexample into a semistable elliptic curve whose
    mod-p representation is unramified outside 2p.  Semistability makes the
    conductor squarefree, which is what lets the level-lowering steps remove
    primes one at a time, and the shape of Delta -- a p-th power up to 2^8 --
    is what makes the residual representation so rigid.  This demo verifies the
    invariants and the semistability criterion symbolically; no counterexample
    exists, so the numeric run uses a package-shaped triple.

RUN
    python3 frey_curve.py
    python3 frey_curve.py > frey_curve.expected.txt
"""

import sympy as sp

from ffcurve.frey import (c4, discriminant, frey_c4, frey_c4_via_c,
                          frey_discriminant, frey_discriminant_naive, frey_int,
                          frey_j, frey_naive, is_semistable, is_squarefree,
                          prime_factors, radical)
from report import Report


def main():
    R = Report("The Frey curve")

    X, Y = sp.symbols("X Y")  # X = a^p, Y = b^p,  Z = X + Y = c^p

    R.note("""
        The Frey curve is attached to a putative counterexample to Fermat:
        a^p + b^p = c^p with p >= 5 prime and a, b, c pairwise coprime, arranged
        so that a = 3 mod 4 and b is even.  This demo verifies its invariants
        and the semistability that the rest of the proof exploits.
    """)

    # ---- 1 -------------------------------------------------------------
    R.section("1. The two models")
    R.note("""
        The naive model y^2 = x(x - a^p)(x + b^p) has rational coefficients but
        is not integral.  Completing the square and scaling gives the integral
        model below, whose coefficients are integers because a = 3 mod 4 makes
        b^p - 1 - a^p divisible by 4 and 2 | b makes a^p b^p divisible by 16.
    """)
    R.data("naive:    y^2 = x (x - X) (x + Y)")
    R.data("integral: y^2 + x y = x^3 + ((Y - 1 - X)/4) x^2 - (X Y / 16) x")
    R.data("with X = a^p, Y = b^p, Z = X + Y = c^p")

    # ---- 2 -------------------------------------------------------------
    R.section("2. Discriminant, c_4 and j, symbolically")
    R.note("""
        Expanding the Weierstrass invariants gives Delta and c_4 as polynomials
        in X and Y.  The integral model's discriminant is smaller by 2^12, the
        twelfth power of the scaling, and c_4 is smaller by 2^4, as it must be
        for a change of variables with u = 2.
    """)
    ci = frey_int(X, Y)
    cn = frey_naive(X, Y)
    R.data(f"integral: Delta = {sp.factor(discriminant(*ci))}")
    R.data(f"integral: c_4   = {sp.factor(c4(*ci))}")
    R.data(f"naive:    Delta = {sp.factor(discriminant(*cn))}")
    R.data(f"naive:    c_4   = {sp.factor(c4(*cn))}")
    R.data(f"j = c_4^3 / Delta = {sp.factor(frey_j(X, Y))}")
    R.check("integral Delta = X^2 Y^2 (X + Y)^2 / 2^8",
            sp.simplify(discriminant(*ci) - frey_discriminant(X, Y)) == 0)
    R.check("integral c_4 = X^2 + X Y + Y^2",
            sp.simplify(c4(*ci) - frey_c4(X, Y)) == 0)
    R.check("naive Delta = 16 X^2 Y^2 (X + Y)^2",
            sp.simplify(discriminant(*cn) - frey_discriminant_naive(X, Y)) == 0)
    R.check("naive c_4 = 16 (X^2 + X Y + Y^2)",
            sp.simplify(c4(*cn) - 16 * frey_c4(X, Y)) == 0)
    R.check("j = 2^8 (X^2 + X Y + Y^2)^3 / (X Y Z)^2",
            sp.simplify(frey_j(X, Y)
                        - 256 * frey_c4(X, Y) ** 3 / (X ** 2 * Y ** 2 * (X + Y) ** 2)) == 0)
    R.check("using a^p + b^p = c^p, c_4 = Z^2 - X Y = c^(2p) - (a b)^p",
            sp.simplify(frey_c4_via_c(X, Y, X + Y) - frey_c4(X, Y)) == 0)

    # ---- 3 -------------------------------------------------------------
    R.section("3. Delta is a p-th power up to 2^8")
    R.note("""
        In a genuine Frey package Z = c^p, so X Y Z = (a b c)^p and
        Delta * 2^8 = ((a b c)^2)^p is a perfect p-th power.  That is the
        arithmetic rigidity the level-lowering argument uses: the discriminant
        has no room for p-adic variation away from 2.
    """)
    a, b, c_, p = sp.symbols("a b c p", positive=True)
    R.data("Delta * 2^8 = (a b c)^(2p) = ((a b c)^2)^p")
    R.check("Delta * 2^8 is the p-th power ((a b c)^2)^p",
            all(sp.expand((a ** q * b ** q * c_ ** q) ** 2
                          - (a ** 2 * b ** 2 * c_ ** 2) ** q) == 0
                for q in (5, 7, 11, 13)))

    # ---- 4 -------------------------------------------------------------
    R.section("4. Semistability, and the conductor")
    R.note("""
        For a minimal model the reduction at q is multiplicative exactly when
        q | Delta and q does not divide c_4; the formalization's
        IsSemistableModel is literally that criterion.  Here c_4 =
        X^2 + X Y + Y^2 is a unit at every q | a b c:
        if q | a it reduces to Y^2, if q | b to X^2, and if q | c then
        b^p = -a^p mod q makes it reduce to X^2 again.  So the curve is
        semistable and its conductor is the squarefree number rad(a b c).
    """)
    R.check("q | a: c_4 reduces to Y^2 = b^(2p), a unit",
            sp.expand(frey_c4(0, Y)) == Y ** 2)
    R.check("q | b: c_4 reduces to X^2 = a^(2p), a unit",
            sp.expand(frey_c4(X, 0)) == X ** 2)
    R.check("q | c: b^p = -a^p makes c_4 reduce to X^2 = a^(2p), a unit",
            sp.expand(frey_c4(X, -X)) == X ** 2)
    a0, b0, p0, q0 = 3, 2, 5, 11
    A0, B0 = a0 ** p0, b0 ** p0
    R.check("example: for a prime q | a^p + b^p one gets c_4 = a^(2p) mod q",
            (a0 ** p0 + b0 ** p0) % q0 == 0
            and (A0 ** 2 + A0 * B0 + B0 ** 2 - a0 ** (2 * p0)) % q0 == 0)

    R.note("""
        No counterexample exists, so for a numeric run we take a triple with
        the package's normalisation but without the Fermat relation: a = 3,
        b = 2, p = 5, so X = 243, Y = 32 and Z = X + Y = 275 (not a fifth
        power).  The invariants and the semistability criterion still apply.
    """)
    C0 = A0 + B0
    D0 = frey_discriminant(A0, B0)
    c40 = frey_c4(A0, B0)
    N0 = radical(A0 * B0 * C0)
    R.data(f"a = {a0}, b = {b0}, p = {p0};  X = {A0}, Y = {B0}, Z = {C0}")
    R.data(f"Delta = (X Y Z)^2 / 2^8 = {D0}")
    R.data(f"c_4 = X^2 + X Y + Y^2 = {c40}")
    R.data(f"bad primes of Delta: {prime_factors(D0)}")
    R.data(f"conductor N = rad(X Y Z) = {N0} = "
           + " * ".join(str(q) for q in prime_factors(N0)))
    R.check("every bad prime is multiplicative: gcd(c_4, N) = 1",
            sp.gcd(int(c40), N0) == 1 and is_semistable(D0, c40))
    R.check("the conductor rad(X Y Z) is squarefree with the same primes as Delta",
            is_squarefree(N0) and prime_factors(N0) == prime_factors(D0))

    # ---- 5 -------------------------------------------------------------
    R.section("5. The formalization")
    R.note("""
        FreyPackage carries a, b, c, p with a^p + b^p = c^p, p prime and >= 5,
        gcd(a, b) = 1, a = 3 mod 4 and 2 | b; freyCurveInt and freyCurve are
        the two models above.  FreyCurve.Delta and FreyCurve.c4 prove the
        identities checked in section 2, and c4' records the form
        c^(2p) - (a b)^p used in section 3.
    """)
    R.note("""
        IsSemistableModel is the criterion of section 4, and IsConductorLevel
        records the level properties the lowering steps need -- in particular
        that the conductor is squarefree (sq_not_dvd) and not divisible by 4.
        Semistability and the squarefree conductor are what let Ribet's theorem
        strip primes from the level one at a time; the p-th-power shape of
        Delta is what makes the residual representation rigid enough for that
        theorem to apply.
    """)

    R.finish()


if __name__ == "__main__":
    main()
