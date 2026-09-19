"""Frobenius and its characteristic polynomial — illustrative demo.

CONCEPT
    For an elliptic curve E over F_q the q-power Frobenius pi satisfies

        pi^2 - a_q pi + q = 0,        a_q = q + 1 - #E(F_q),

    so its characteristic polynomial is T^2 - a_q T + q: trace a_q, determinant
    q.  Hasse's bound is |a_q| <= 2 sqrt(q), equivalently a_q^2 <= 4q, and
    equivalently the two roots alpha, beta have |alpha| = |beta| = sqrt(q).
    The polynomial determines the counts over every extension,
    #E(F_{q^k}) = q^k + 1 - a_{q^k}, by the recurrence
    a_{q^k} = a_q a_{q^{k-1}} - q a_{q^{k-2}}.

FLT ANCHOR
    ResidualGaloisRep.IsAttachedTo          (Def_GaloisRep_Residual.lean)
        the Frobenius polynomial X^2 - a X + l
    AlgebraicCurve.Pic0.finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero
        (Thm_AlgebraicCurve_Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero.lean)
        T_l Pic^0 is free of rank 2g; for an elliptic curve that is rank 2

WHY IT MATTERS FOR FLT
    The Frobenius polynomial is the local data of a Galois representation: for
    the Frey curve the residue representation is attached to a modular form by
    matching a_l, and a_l is the trace of Frobenius, bounded by Hasse.  The
    determinant being q -- forced by the Weil pairing (base/007) -- is the
    constant term.  The rank statement is the genus-1 case of rank 2g for
    J_0(N) used in the Hecke and Eisenstein arguments (math/009).

RUN
    python3 frobenius_charpoly.py
    python3 frobenius_charpoly.py > frobenius_charpoly.expected.txt
"""

import sympy as sp

from ffcurve import EllipticCurve, FiniteField
from ffcurve.frobenius import (cardinality_over_extension, charpoly_expr,
                               charpoly_roots, hasse_ok, root_modulus_squared,
                               trace_power)
from report import Report

FAILURES = []


def point_key(F, P):
    if P is None:
        return (1, 0, 0)
    return (0, F.key(P[0]), F.key(P[1]))


def torsion_points(F, E, n):
    return sorted([P for P in E.points() if E.mul(n, P) is None],
                  key=lambda P: point_key(F, P))


def torsion_basis(F, E, n):
    pts = torsion_points(F, E, n)
    P = next(T for T in pts if T is not None and E.order(T) == n)
    sub = {E.mul(k, P) for k in range(n)}
    Q = next(T for T in pts if T not in sub)
    return P, Q


def coords(F, E, n, P, Q, R):
    for a in range(n):
        for b in range(n):
            if E.add(E.mul(a, P), E.mul(b, Q)) == R:
                return a, b
    raise ValueError("point is not in the span")


def frob_q(F, q, R):
    if R is None:
        return None
    return (F.pow(R[0], q), F.pow(R[1], q))


def main():
    R = Report("Frobenius and its characteristic polynomial")

    R.note("""
        For E over F_q the q-power Frobenius pi is an endomorphism, and it is
        algebraic of degree 2: pi satisfies pi^2 - a_q pi + q = 0 with
        a_q = q + 1 - #E(F_q).  So the characteristic polynomial of Frobenius
        is T^2 - a_q T + q, whose trace is a_q and whose determinant is q.
    """)

    # ---- 1 -------------------------------------------------------------
    R.section("1. The characteristic polynomial and Hasse's bound")
    R.data("pi^2 - a_q pi + q = 0,    a_q = q + 1 - #E(F_q)")
    R.data("char poly: T^2 - a_q T + q   (trace a_q, determinant q)")
    R.data("Hasse:  |a_q| <= 2 sqrt(q)   <=>   a_q^2 <= 4 q")
    R.note("""
        The determinant q is not an extra hypothesis: it is exactly the
        statement that the Weil pairing is multiplied by q under Frobenius
        (base/007).  Hasse's bound says the two roots have modulus sqrt(q).
    """)

    # ---- 2 -------------------------------------------------------------
    R.section("2. Point counts and Hasse for several curves")
    R.data(f"{'p':>3} | {'curve':<24}| {'#E':>3} | {'a_p':>4} | {'a_p^2':>5} "
           f"| {'4p':>3} | Hasse")
    curves = [(7, 0, 2), (7, -1, 0), (7, 1, 1), (5, 0, 1), (5, 1, 1),
              (11, 1, 6), (41, 15, 0)]
    data = []
    for (p, a, b) in curves:
        F = FiniteField(p)
        E = EllipticCurve(F, a, b)
        N = E.cardinality()
        aq = p + 1 - N
        data.append((p, a, b, N, aq))
        curve = f"y^2 = x^3 + ({a})x + ({b})"
        R.data(f"{p:>3} | {curve:<24}| {N:>3} | {aq:>4} | {aq * aq:>5} "
               f"| {4 * p:>3} | " + ("ok" if hasse_ok(aq, p) else "VIOLATED"))
    R.check("Hasse's bound a_q^2 <= 4q holds for every curve above",
            all(hasse_ok(aq, p) for (p, _, _, _, aq) in data))
    R.check("the constant term of the characteristic polynomial is q",
            all(charpoly_expr(aq, p).subs(sp.symbols("T"), 0) == p
                for (p, _, _, _, aq) in data))
    R.check("the trace is a_q",
            all(sp.Poly(charpoly_expr(aq, p), sp.symbols("T")).all_coeffs()[1] == -aq
                for (p, _, _, _, aq) in data))

    # ---- 3 -------------------------------------------------------------
    R.section("3. The polynomial determines the counts over extensions")
    R.note("""
        If alpha, beta are the roots then a_{q^k} = alpha^k + beta^k obeys
        a_{q^k} = a_q a_{q^{k-1}} - q a_{q^{k-2}}.  Hence
        #E(F_{q^k}) = q^k + 1 - a_{q^k}, which we verify against brute-force
        point counts over the extension fields.
    """)
    ext = []
    for (p, a, b, kmax) in [(3, 2, 1, 3), (5, 1, 1, 2), (7, 1, 1, 2)]:
        F = FiniteField(p)
        E = EllipticCurve(F, a, b)
        aq = p + 1 - E.cardinality()
        R.data(f"curve y^2 = x^3 + ({a})x + ({b}) over GF({p}):  a_{p} = {aq}")
        R.data(f"    k | a_(p^k) | q^k + 1 - a_(p^k) | brute force | match")
        for k in range(2, kmax + 1):
            Fk = FiniteField(p, k)
            Ek = EllipticCurve(Fk, a, b)
            N = Ek.cardinality()
            tr = trace_power(aq, p, k)
            pred = cardinality_over_extension(aq, p, k)
            ext.append((N == pred))
            R.data(f"    {k} | {tr:7d} | {pred:17d} | {N:11d} | "
                   + ("ok" if N == pred else "MISMATCH"))
    R.check("the recurrence reproduces every brute-force count above",
            all(ext))
    R.check("the recurrence is linear with coefficients a_q and q",
            all(trace_power(aq, p, k) == aq * trace_power(aq, p, k - 1)
                - p * trace_power(aq, p, k - 2)
                for (p, _, _, _, aq) in data for k in range(2, 5)))

    # ---- 4 -------------------------------------------------------------
    R.section("4. The roots are conjugate and have modulus sqrt(q)")
    R.note("""
        Over the complex numbers T^2 - a_q T + q factors as
        (T - alpha)(T - beta), so alpha + beta = a_q, alpha beta = q and
        |alpha|^2 = |beta|^2 = q.  The last identity is Hasse's bound in
        modulus form -- and it is why the Frobenius eigenvalues are the
        "Weil numbers" of weight 1.
    """)
    T = sp.symbols("T")
    roots_ok = []
    for (p, a, b, N, aq) in data[:4]:
        r = charpoly_roots(aq, p)
        s = sp.simplify(sum(r))
        prod = sp.simplify(sp.prod(r))
        mod2 = root_modulus_squared(aq, p)
        roots_ok.append((s == aq, prod == p, mod2 == p))
        R.data(f"a_{p} = {aq}:  roots {r[0]}, {r[1]}")
        R.data(f"        sum = {s} (a_q), product = {prod} (q), |root|^2 = {mod2}")
    R.check("alpha + beta = a_q, alpha beta = q, |alpha|^2 = q",
            all(all(t) for t in roots_ok))

    # ---- 5 -------------------------------------------------------------
    R.section("5. Frobenius on E[n]: rank 2, and the matrix")
    R.note("""
        E[n] is a free Z/n-module of rank 2, the elliptic-curve case of the
        Tate module T_l E being free of rank 2 = 2g.  Frobenius acts on it by
        a 2x2 matrix whose trace is a_q mod n and whose determinant is q mod n.
    """)
    F = FiniteField(7)
    for (a, b, n) in [(-1, 0, 2), (0, 2, 3)]:
        E = EllipticCurve(F, a, b)
        cnt = len(torsion_points(F, E, n))
        R.data(f"E: y^2 = x^3 + ({a})x + ({b}) over GF(7):  "
               f"#E[{n}] = {cnt} = {n}^2")
    R.check("E[2] and E[3] are free of rank 2 (n^2 points)",
            len(torsion_points(F, EllipticCurve(F, -1, 0), 2)) == 4
            and len(torsion_points(F, EllipticCurve(F, 0, 2), 3)) == 9)

    R.note("""
        To see a nontrivial action we move to a field where the torsion is
        rational: for E: y^2 = x^3 + 1 over GF(5) the 3-torsion appears over
        GF(25), and there the 5-power Frobenius acts with trace a_5 = 0 and
        determinant 5 mod 3.
    """)
    p, n = 5, 3
    F5 = FiniteField(p)
    a5 = p + 1 - EllipticCurve(F5, 0, 1).cardinality()
    K = FiniteField(p, 2)
    EK = EllipticCurve(K, 0, 1)
    P, Q = torsion_basis(K, EK, n)
    mP, mQ = frob_q(K, p, P), frob_q(K, p, Q)
    a, b_ = coords(K, EK, n, P, Q, mP)
    c, d = coords(K, EK, n, P, Q, mQ)
    tr, det = (a + d) % n, (a * d - b_ * c) % n
    R.data(f"matrix of Frobenius in the basis (P,Q): [[{a}, {b_}], [{c}, {d}]]"
           f"  mod {n}")
    R.data(f"trace = {tr} = a_{p} mod {n} = {a5 % n};  "
           f"determinant = {det} = {p} mod {n} = {p % n}")
    R.check("Frobenius on E[n] has trace a_q and determinant q",
            tr == a5 % n and det == p % n)
    # the matrix satisfies its own characteristic polynomial
    m00 = (a * a + b_ * c) % n
    m01 = (a * b_ + b_ * d) % n
    m10 = (c * a + d * c) % n
    m11 = (c * b_ + d * d) % n
    sat = ((m00 - a5 * a + p) % n == 0 and (m01 - a5 * b_) % n == 0
           and (m10 - a5 * c) % n == 0 and (m11 - a5 * d + p) % n == 0)
    R.check("the Frobenius matrix satisfies M^2 - a_q M + q = 0 on E[n]", sat)

    # ---- 6 -------------------------------------------------------------
    R.section("6. The formalization")
    R.note("""
        ResidualGaloisRep.IsAttachedTo records exactly this polynomial as the
        link between a Galois representation and a modular form: at a good
        prime l the characteristic polynomial of rho(Frob_l) is
        X^2 - a_l X + l.  The constant term l is the determinant, i.e. the
        cyclotomic character value (base/007); a_l is the trace, bounded by
        Hasse and matched against the Hecke eigenvalue of a cusp form.
    """)
    R.note("""
        The rank statement is Pic0.finrank_rationalTateModule_eq_two_mul_genusFF:
        the rational Tate module of Pic^0 is free of rank 2g.  For an elliptic
        curve g = 1 and that is the rank-2 module computed above; for J_0(N) it
        is the symplectic Galois module carrying the Hecke action (math/009).
    """)

    R.finish()


if __name__ == "__main__":
    main()
