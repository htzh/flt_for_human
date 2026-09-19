"""Divisors and Pic^0 — illustrative demo.

CONCEPT
    A divisor on a smooth curve is a formal finite integer combination of
    points.  Its degree is the sum of the coefficients; it is principal when it
    is div(f) for some nonzero rational function f.  The degree-zero divisors
    modulo principal divisors form Pic^0, the Jacobian of the curve.  For an
    elliptic curve the map P |-> [P] - [O] is a group isomorphism E -> Pic^0:
    the group law of the curve is the group law of divisor classes.

FLT ANCHOR
    AlgebraicCurve.Divisor               (Def_AlgebraicCurve_DivisorClassGroup.lean)
        Divisor K F := Place K F →₀ ℤ
    AlgebraicCurve.Divisor.degree, Divisor.IsPrincipal, Divisor.principal
    AlgebraicCurve.HasPrincipalDivisors
    AlgebraicCurve.Pic, AlgebraicCurve.Pic0

WHY IT MATTERS FOR FLT
    The Jacobian J = Pic^0 of the modular curve X_0(N) is the object that
    carries the Hecke action and the Galois representation used throughout the
    proof (math/009).  For an elliptic curve the Jacobian is the curve itself,
    which is the case computed here; the same identities hold for J_0(N) with
    "rational point" replaced by "place of the function field".

RUN
    python3 divisors_and_pic0.py
    python3 divisors_and_pic0.py > divisors_and_pic0.expected.txt
"""

from ffcurve import EllipticCurve, FiniteField
from ffcurve.divisors import (Divisor, abel_jacobi_sum, chord_tangent_divisor,
                              divisor_x, divisor_y, is_principal, line_divisor,
                              ordered_points, vertical_divisor)
from report import Report

FAILURES = []


def lbl(F, P):
    if P is None:
        return "O"
    return f"({F.format(P[0])}, {F.format(P[1])})"


def pair_divisor(E, pairs):
    return Divisor(E, list(pairs))


def main():
    R = Report("Divisors and Pic^0")

    R.note("""
        A divisor on a smooth curve C is a formal finite sum of points with
        integer coefficients.  Its degree is the sum of the coefficients, and it
        is principal when it is div(f) for some nonzero rational function f.
        The degree-zero divisors modulo principal divisors form the group
        Pic^0(C), the Jacobian of C.
    """)
    R.note("""
        For an elliptic curve E (genus 1) the Jacobian is E itself, through
        P |-> [P] - [O].  This demo exhibits that isomorphism by writing down
        the principal divisors that realise the group law, on the curve
        y^2 = x^3 - x over GF(7), whose full 2-torsion is rational.
    """)

    F = FiniteField(7)
    E = EllipticCurve(F, -1, 0)
    pts = ordered_points(E)

    # ---- 1 -------------------------------------------------------------
    R.section("1. The curve and its points")
    R.data(f"E: {E!r}")
    R.data(f"#E = {E.cardinality()},  infinity written O")
    R.data("points, infinity last: " + ", ".join(lbl(F, P) for P in pts))
    orders = ", ".join(f"{lbl(F, P)} order {E.order(P)}" for P in pts)
    R.data(orders)
    R.note("""
        The orders are 1, 2, 2, 2, 4, 4, 4, 4, so E is isomorphic to
        Z/2 x Z/4.  In particular the full 2-torsion is rational: the three
        points with y = 0, namely (0,0), (1,0), (6,0).
    """)

    # ---- 2 -------------------------------------------------------------
    R.section("2. Divisors, degree, and the divisors of x and y")
    R.note("""
        A divisor is written as a formal sum, e.g. [P] + [Q] - [R] - [O].  The
        functions x and y of the Weierstrass model have divisors read off from
        the geometry: x has a double zero at (0,0) and a double pole at O,
        while y vanishes simply at the three 2-torsion points and has a triple
        pole at O.
    """)
    dx, dy = divisor_x(E), divisor_y(E)
    R.data(f"div(x) = {dx.format()}")
    R.data(f"div(y) = {dy.format()}")
    R.data(f"degree of each = {dx.degree()}, {dy.degree()}")
    R.check("deg(div x) = 0", dx.degree() == 0)
    R.check("deg(div y) = 0", dy.degree() == 0)
    R.check("Abel-Jacobi sum of div(x) is O", abel_jacobi_sum(E, dx) is None)
    R.check("Abel-Jacobi sum of div(y) is O", abel_jacobi_sum(E, dy) is None)
    R.note("""
        Degree zero is forced: a nonzero rational function on a curve has as
        many zeros as poles.  The vanishing of the group sum is the genus-1
        form of the Abel-Jacobi theorem, and here it is sharp: for an elliptic
        curve a degree-zero divisor is principal exactly when the points,
        summed in the group law, give O.
    """)

    # ---- 3 -------------------------------------------------------------
    R.section("3. The chord-tangent divisor")
    R.note("""
        A line meets E in three points counted with multiplicity, so
        div(line through P and Q) = [P] + [Q] + [-(P+Q)] - 3[O], and the
        vertical through P+Q has divisor [P+Q] + [-(P+Q)] - 2[O].  The quotient
        of the two functions therefore has divisor [P] + [Q] - [P+Q] - [O],
        which is principal.
    """)
    A = (F.from_int(4), F.from_int(2))
    B = (F.from_int(5), F.from_int(1))
    D = chord_tangent_divisor(E, A, B)
    R.data(f"P = {lbl(F, A)},  Q = {lbl(F, B)},  P+Q = {lbl(F, E.add(A, B))}")
    R.data(f"D(P,Q) = div(line) - div(vertical) = {D.format()}")
    R.check("D(P,Q) has degree 0", D.degree() == 0)
    R.check("D(P,Q) is principal, i.e. its points sum to O",
            abel_jacobi_sum(E, D) is None)
    R.check("D(P,Q) = div(line) - div(vertical)",
            D == line_divisor(E, A, B) - vertical_divisor(E, E.add(A, B)))
    R.check("D(P,Q) is principal for every pair P, Q",
            all(is_principal(E, chord_tangent_divisor(E, P, Q))
                for P in pts for Q in pts))
    R.note("""
        So [P] + [Q] and [P+Q] differ by a principal divisor: they are the same
        class in Pic^0.  The group law on E is the group law on divisor
        classes, not merely a formal analogue of it.
    """)

    # ---- 4 -------------------------------------------------------------
    R.section("4. Pic^0 is E")
    R.note("""
        Define phi(P) = class of [P] - [O].  Section 3 says
        phi(P) + phi(Q) = phi(P+Q), so phi is a group homomorphism.  It is
        injective because [P] - [Q] is principal only when P = Q: its points
        must sum to O, i.e. P - Q = O.
    """)
    R.check("phi(P) + phi(Q) = phi(P+Q) for all P, Q",
            all(is_principal(E, chord_tangent_divisor(E, P, Q))
                for P in pts for Q in pts))
    R.check("[P] - [Q] is principal if and only if P = Q",
            all(is_principal(E, pair_divisor(E, [(P, 1), (Q, -1)])) == (P == Q)
                for P in pts for Q in pts))
    R.note("""
        Both E and Pic^0 have 8 elements, so an injective homomorphism is also
        onto.  Concretely, a degree-zero divisor sum n_P [P] is principal
        exactly when the group sum of its points is O, so its class is
        [S] - [O] for the single point S = sum n_P P.
    """)
    R.check("phi is injective: the 8 classes are distinct",
            all(not is_principal(E, pair_divisor(E, [(P, 1), (Q, -1)]))
                for P in pts for Q in pts if P != Q))
    R.check("[P] + [Q] - [R] - [T] principal iff P + Q = R + T",
            all(is_principal(E, pair_divisor(E, [(P, 1), (Q, 1), (R, -1), (T, -1)]))
                == (E.add(P, Q) == E.add(R, T))
                for P in pts for Q in pts for R in pts for T in pts))
    R.check("degree is additive: deg(D + E) = deg D + deg E",
            all((chord_tangent_divisor(E, P, Q) + D).degree()
                == chord_tangent_divisor(E, P, Q).degree() + D.degree()
                for P in pts for Q in pts))
    R.data(f"#E = {E.cardinality()},  #Pic^0 = {len(pts)},  phi is a bijection")

    # ---- 5 -------------------------------------------------------------
    R.section("5. What the formalization does with this")
    R.note("""
        The formalization runs the same dictionary for an arbitrary function
        field: a Place is a valuation ring of the field (the algebraic
        substitute for a point), Divisor K F := Place K F →₀ ℤ, degree
        multiplies each coefficient by the residue degree of the place, and
        IsPrincipal asks for a function with the prescribed order at every
        place.  HasPrincipalDivisors asserts that those functions exist, and
        Pic K F := Divisor ⧸ principal, with Pic0 its degree-zero part.
    """)
    R.note("""
        For the modular curve, Pic^0 of X_0(N) is the Jacobian carrying the
        Hecke action (math/009) and the Galois representation on its torsion
        (base/007).  The elliptic-curve computation above is the case where the
        Jacobian is the curve itself, and its two ingredients -- principal
        divisors exist, and degree-zero classes are classified by the group sum
        -- are the genus-1 shadow of the general theory.
    """)

    R.finish()


if __name__ == "__main__":
    main()
