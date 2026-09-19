"""Residues and the residue theorem — illustrative demo.

CONCEPT
    On a smooth projective curve C, a nonzero meromorphic differential omega has
    finitely many poles and the sum of its residues is zero:

        sum_P res_P(omega) = 0.

    On the projective line, for omega = f(x) dx, the residue at a finite point a
    is the coefficient of 1/(x - a) in f, and the residue at infinity comes from
    x = 1/t, which turns omega into -f(1/t)/t^2 dt.  For a principal
    differential omega = d log F the residue at P is the order of F at P, so the
    theorem says a function has as many zeros as poles.

FLT ANCHOR
    AlgebraicCurve.ResidueTheorem       (Def_AlgebraicCurve_WeilOfKaehler.lean, line 107)
    AlgebraicCurve.weilOfKaehler        (same file, line 78)
    AlgebraicCurve.LocalResidueData,
        res_of_mem, res_simplePole      (Def_AlgebraicCurve_LocalResidue.lean, line 20)
    AlgebraicCurve.WeilKaehlerAgree, ResiduePairingSurjective (WeilOfKaehler.lean)
    residueTheorem_of_isAlgClosed       (Thm_AlgebraicCurve_residueTheorem_of_isAlgClosed.lean)
    residueTheorem_functionField_of_smoothOfRelativeDimension_one
        (Thm_AlgebraicCurve_residueTheorem_functionField_of_smoothOfRelativeDimension_one.lean)

WHY IT MATTERS FOR FLT
    The residue theorem is what makes the Serre pairing on a function field
    nondegenerate, and so underlies the duality theory of the Jacobian used in
    the Hecke and Eisenstein arguments (math/009).  In the formalization it is
    stated adelically: the Weil pairing of a nonzero differential with the
    principal adele of a function vanishes, i.e. sum over places of
    res_v(f omega) = 0.

RUN
    python3 residue_theorem.py
    python3 residue_theorem.py > residue_theorem.expected.txt
"""

import sympy as sp

from ffcurve import EllipticCurve, FiniteField
from ffcurve.divisors import (chord_tangent_divisor, divisor_x, divisor_y,
                              ordered_points)
from ffcurve.residue import (log_derivative_residues, log_derivative_sum,
                             residue_infinity, residue_sum, residue_table)
from report import Report

x = sp.symbols("x")

EXAMPLES = ("1/x", "1/(x+1)", "1/(x*(x-1))", "1/(x**3 - x)",
            "x/(x**2 + 1)**2", "1/x**2")


def main():
    R = Report("Residues and the residue theorem")

    R.note("""
        A meromorphic differential on a curve has finitely many poles, each
        carrying a residue, and the residues always cancel.  This demo computes
        both sides of that statement on the projective line, where residues are
        coefficient extractions, and checks the logarithmic-derivative form on
        an elliptic curve, where the residues are the multiplicities in the
        divisor of a function.
    """)

    # ---- 1 -------------------------------------------------------------
    R.section("1. The statement")
    R.data("sum_P res_P(omega) = 0    for a nonzero meromorphic differential omega")
    R.data("for omega = f(x) dx on P^1:  res_a = coeff of 1/(x-a) in f;")
    R.data("res_infinity from x = 1/t:  omega = -f(1/t)/t^2 dt, residue at t = 0")
    R.note("""
        For a principal differential omega = d log F = F'/F dx the residue at P
        is the order of F at P -- positive at a zero, negative at a pole -- so
        the theorem reduces to the fact that a rational function has as many
        zeros as poles.  The formalization states the adelic version, where the
        sum runs over the places of the function field.
    """)

    # ---- 2 -------------------------------------------------------------
    R.section("2. Residues on the projective line")
    R.data("f                    | finite poles and residues        | res_inf | total")
    tables = {}
    for expr in EXAMPLES:
        f = sp.sympify(expr)
        tbl = residue_table(f)
        tables[expr] = (f, tbl)
        cells = ", ".join(f"{a}: {r}" for a, _, r in tbl)
        R.data(f"{expr:20s} | {cells:32s} | {str(residue_infinity(f)):7s} "
               f"| {residue_sum(f)}")
    R.check("the residues sum to zero for every example",
            all(residue_sum(f) == 0 for f, _ in tables.values()))
    R.check("dx/(x^3 - x) has residues -1 at 0 and 1/2 at each of +-1",
            sorted((str(a), sp.nsimplify(r)) for a, _, r in tables["1/(x**3 - x)"][1])
            == [("-1", sp.Rational(1, 2)), ("0", -1), ("1", sp.Rational(1, 2))])
    R.check("the residues of dx/x are +1 at 0 and -1 at infinity",
            tables["1/x"][1][0][2] == 1 and residue_infinity(tables["1/x"][0]) == -1)
    R.check("a double pole has residue zero (1/x^2 and x/(x^2+1)^2)",
            all(r == 0 for _, _, r in tables["1/x**2"][1])
            and all(r == 0 for _, _, r in tables["x/(x**2 + 1)**2"][1]))

    # ---- 3 -------------------------------------------------------------
    R.section("3. The residue at infinity")
    R.note("""
        Whether the point at infinity contributes depends on the degrees: for
        f = P/Q the residue at infinity vanishes once deg Q >= deg P + 2, and
        the two examples 1/x and 1/(x+1) sit exactly at deg Q = deg P + 1, where
        it is -1.  That single residue is what cancels the finite one.
    """)
    R.data("f          | deg Q - deg P | res_infinity")
    for expr in ("1/x", "1/(x+1)", "1/x**2", "1/(x**3 - x)"):
        f = tables.get(expr, (sp.sympify(expr), None))[0]
        num, den = sp.fraction(sp.together(f))
        diff = sp.Poly(den, x).degree() - sp.Poly(num, x).degree()
        R.data(f"{expr:12s} | {diff:13d} | {residue_infinity(f)}")
    R.check("res_infinity = -1 exactly when deg Q = deg P + 1, and 0 for deg Q >= deg P + 2",
            residue_infinity(sp.sympify("1/x")) == -1
            and residue_infinity(sp.sympify("1/(x+1)")) == -1
            and residue_infinity(sp.sympify("1/x**2")) == 0
            and residue_infinity(sp.sympify("1/(x**3 - x)")) == 0)

    # ---- 4 -------------------------------------------------------------
    R.section("4. Logarithmic derivatives, and an elliptic curve")
    R.note("""
        For omega = d log F = F'/F dx the residues are the orders of F.  On P^1
        they are read off from the factorisation of F, plus the order at
        infinity deg(denominator) - deg(numerator); the sum is zero again.  On a
        curve the same statement is deg(div F) = 0, and there the residues are
        the coefficients of the divisor -- which the divisors demo computed for
        x, y and the chord-tangent function.
    """)
    for expr in ("x*(x-1)/(x+2)**2", "1/(x**2 - 1)", "(x-1)**2/(x+1)"):
        f = sp.sympify(expr)
        orders = log_derivative_residues(f)
        R.data(f"F = {expr:20s} orders: "
               + ", ".join(f"{k}: {v}" for k, v in orders.items())
               + f"   sum = {log_derivative_sum(f)}")
    R.check("sum of the orders of F is zero, including the order at infinity",
            all(log_derivative_sum(sp.sympify(e)) == 0
                for e in ("x*(x-1)/(x+2)**2", "1/(x**2 - 1)", "(x-1)**2/(x+1)")))
    R.check("the infinity order is what cancels the finite ones for 1/(x^2 - 1)",
            log_derivative_residues(sp.sympify("1/(x**2 - 1)")).get(sp.oo) == 2)

    F = FiniteField(7)
    E = EllipticCurve(F, -1, 0)
    A = (F.from_int(4), F.from_int(2))
    B = (F.from_int(5), F.from_int(1))
    divisors = (("div(x)", divisor_x(E)),
                ("div(y)", divisor_y(E)),
                ("chord-tangent", chord_tangent_divisor(E, A, B)))
    R.data("E: y^2 = x^3 - x over GF(7); residues of d log F are the coefficients")
    for name, D in divisors:
        residues = ", ".join(f"{D.coeff(P)} at "
                             + ("O" if P is None else f"({F.format(P[0])}, {F.format(P[1])})")
                             for P in D.support())
        R.data(f"  F with {name:14s}: {residues}   sum = {sum(D.terms.values())}")
    R.check("the residues of d log F sum to zero for x, y and the chord-tangent function",
            all(sum(D.terms.values()) == 0 for _, D in divisors))
    R.check("equivalently deg(div F) = 0 for each of them",
            all(D.degree() == 0 for _, D in divisors))
    R.check("the chord-tangent function has only simple zeros and poles, "
            "so its residues are +-1 as in res_simplePole",
            all(abs(D.coeff(P)) == 1
                for P in chord_tangent_divisor(E, A, B).support()))

    # ---- 5 -------------------------------------------------------------
    R.section("5. The formalization")
    R.note("""
        LocalResidueData records what a residue at a place is: a K-linear map to
        the residue field that vanishes on the valuation ring (res_of_mem) and,
        at a simple pole, is the residue of uniformizer * f (res_simplePole).
        weilOfKaehler assembles these into a dual of the adele space, and
        ResidueTheorem is the statement that its value on the principal adele of
        any f vanishes -- the adelic sum of residues.
    """)
    R.note("""
        The theorem is proved for the fields the FLT argument uses:
        residueTheorem_of_isAlgClosed, residueTheorem_of_perfectField, and
        residueTheorem_functionField_of_smoothOfRelativeDimension_one.  It is
        what makes the Serre pairing nondegenerate
        (ResiduePairingSurjective, WeilKaehlerAgree) and so underlies the
        duality theory of the Jacobian that math/009 uses for the Hecke action.
        The logarithmic case checked above is the shadow of it visible on a
        single elliptic curve.
    """)

    R.finish()


if __name__ == "__main__":
    main()
