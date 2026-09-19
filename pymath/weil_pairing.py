"""Weil pairing — illustrative demo.

CONCEPT
    For an elliptic curve E over a field F and an integer n coprime to the
    characteristic, the Weil pairing is a canonical perfect alternating pairing
    e_n : E[n] x E[n] -> mu_n between the n-torsion subgroup and the n-th roots
    of unity.  Concretely it is Miller's function: if f_P has divisor
    n[P] - n[O], then e_n(P,Q) = (-1)^n f_P(Q) / f_Q(P).

FLT ANCHOR
    AlgebraicCurve.WeilDatum               (Def_AlgebraicCurve_WeilDatum.lean)
        pairing := evalFun f1 D2 / evalFun f2 D1, with ord f_i = n * D_i
    AlgebraicCurve.WeilPairingData         (Def_AlgebraicCurve_JacobianH1Autoduality.lean)
    AlgebraicCurve.Pic0.exists_weilPairing

WHY IT MATTERS FOR FLT
    For E/Q the mod-l Galois representation rho_{E,l} : G_Q -> GL_2(F_l) has
    determinant equal to the cyclotomic character.  That is the Galois
    equivariance of e_l, and it is what makes rho_{E,l} odd -- an input to
    Serre's conjecture and to modularity lifting and level lowering.

RUN
    python3 weil_pairing.py
    python3 weil_pairing.py > weil_pairing.expected.txt
"""

from ffcurve import EllipticCurve, FiniteField
from report import Report


def curve_str(F, E):
    return f"y^2 = x^3 + ({F.format(E.a)})*x + ({F.format(E.b)}) over {F!r}"


def pt_str(F, P):
    if P is None:
        return "O"
    return f"({F.format(P[0])}, {F.format(P[1])})"


def mult_order(F, z):
    w, k = F.one(), 0
    while True:
        if k > 0 and F.eq(w, F.one()):
            return k
        w = F.mul(w, z)
        k += 1
        if k > 100000:
            return None


def point_key(F, P):
    """Canonical sort key for a point, via the field's element key."""
    if P is None:
        return (1, 0, 0)
    return (0, F.key(P[0]), F.key(P[1]))


def canonical_basis(F, E, n):
    """P, Q: the lexicographically first basis of E[n].

    Fixing this rule keeps the demo deterministic: the same basis is chosen on
    every run, so the output is reproducible.
    """
    pts = sorted([P for P in E.points() if E.mul(n, P) is None],
                 key=lambda P: point_key(F, P))
    P = next(T for T in pts if T is not None and E.order(T) == n)
    sub = {E.mul(k, P) for k in range(n)}
    Q = next(T for T in pts if T not in sub)
    return P, Q


def coords(F, E, n, P, Q, R):
    """Write R = a*P + b*Q with a, b in Z/n."""
    for a in range(n):
        for b in range(n):
            if E.add(E.mul(a, P), E.mul(b, Q)) == R:
                return a, b
    raise ValueError("point is not in the span")


def frob(F, E, p, R):
    """The p-power Frobenius on a point (identity at infinity)."""
    if R is None:
        return None
    return (F.frob(R[0]), F.frob(R[1]))


def show_pairing(R, F, E, n):
    """Print the data of one pairing instance and check its laws."""
    P, Q = canonical_basis(F, E, n)
    z = E.weil_pairing(P, Q, n)
    R.data(f"E: {curve_str(F, E)}")
    R.data(f"#E = {E.cardinality()},  n = {n},  #E[n] = {n * n}")
    R.data(f"basis  P = {pt_str(F, P)},  Q = {pt_str(F, Q)}")
    R.data(f"zeta = e_n(P,Q) = {F.format(z)}")
    print()
    R.check("e_n(P,Q)^n = 1", F.eq(F.pow(z, n), F.one()))
    R.check("order(e_n(P,Q)) = n  (nondegenerate, primitive)", mult_order(F, z) == n)
    R.check("e_n(P,P) = 1  (alternating)", F.eq(E.weil_pairing(P, P, n), F.one()))
    R.check("e_n(Q,Q) = 1  (alternating)", F.eq(E.weil_pairing(Q, Q, n), F.one()))
    R.check("e_n(Q,P) = e_n(P,Q)^-1", F.eq(E.weil_pairing(Q, P, n), F.inv(z)))
    R.check("bilinear: e_n(aP, bQ) = zeta^(ab) for all a,b",
            all(F.eq(E.weil_pairing(E.mul(a, P), E.mul(b, Q), n), F.pow(z, a * b))
                for a in range(n) for b in range(n)))
    R.check("alternating on all of E[n]",
            all(F.eq(E.weil_pairing(E.add(E.mul(a, P), E.mul(b, Q)),
                                    E.add(E.mul(a, P), E.mul(b, Q)), n), F.one())
                for a in range(n) for b in range(n)))
    R.data(f"Gram matrix in the basis (P,Q): "
           f"[[1, {F.format(z)}], [{F.format(F.inv(z))}, 1]]")
    return P, Q, z


def main():
    R = Report("Weil pairing  e_n : E[n] x E[n] -> mu_n")

    R.note("""
        This demo computes the Weil pairing on three small curves and checks the
        laws that make it useful.  The first two are over prime fields and show
        the pairing itself; the third shows how Frobenius acts on a pairing value
        and why its determinant is the cyclotomic character; the last recovers
        the pairing from Miller's function, which is the definition the FLT
        formalization uses.
    """)

    # ---- 1 -------------------------------------------------------------
    R.section("1. A perfect alternating pairing: GF(7), n = 3")
    R.note("""
        Take E: y^2 = x^3 + 2 over GF(7).  It has 9 points, and 3 is coprime to
        7, so the 3-torsion E[3] = {T : 3T = O} is a subgroup of order 9 = 3^2,
        hence is isomorphic to (Z/3)^2.  We pick a basis and pair it:
    """)
    F = FiniteField(7)
    E = EllipticCurve(F, 0, 2)
    P, Q, z = show_pairing(R, F, E, 3)
    R.note(f"""
        The value zeta = {F.format(z)} is the whole pairing on this basis: it has
        exact order 3 in GF(7)^*, so the pairing is nondegenerate, and bilinearity
        says every other value is a power of it, e_n(aP, bQ) = zeta^(ab).  Being
        alternating, e_n(T,T) = 1, is the extra symmetry that makes the pairing
        symplectic.  In the basis (P,Q) the Gram matrix is
        [[1, zeta], [zeta^-1, 1]]: zero diagonal, and zeta primitive.
    """)

    # ---- 2 -------------------------------------------------------------
    R.section("2. The same for another prime: GF(41), n = 5")
    R.note("""
        Nothing above is special to 3.  Here E: y^2 = x^3 + 15x over GF(41) has
        50 points, so E[5] = (Z/5)^2 again, and the pairing takes the basis to a
        primitive fifth root of unity.
    """)
    F = FiniteField(41)
    show_pairing(R, F, EllipticCurve(F, 15, 0), 5)

    # ---- 3 -------------------------------------------------------------
    R.section("3. Galois equivariance, and det = the cyclotomic character")
    p, k, n = 5, 2, 3
    base = FiniteField(p)
    E0 = EllipticCurve(base, 0, 1)
    a_p = p + 1 - E0.cardinality()
    R.note(f"""
        Let E: y^2 = x^3 + 1 over GF({p}).  It has {E0.cardinality()} points, so
        a_{p} = {p} + 1 - {E0.cardinality()} = {a_p}.  The 3-torsion of this
        curve is not rational over GF({p}); it first appears over
        GF(25) = GF(5)[t]/(t^2 + t + 1), where #E = 36 and E[3] is rational.
        So we move to that field and pair a basis there:
    """)
    K = FiniteField(p, k)
    EK = EllipticCurve(K, 0, 1)
    R.data(f"base curve over GF({p}): #E = {E0.cardinality()},  a_{p} = {a_p}")
    P, Q, z = show_pairing(R, K, EK, n)

    mP, mQ = frob(K, EK, p, P), frob(K, EK, p, Q)
    a, b = coords(K, EK, n, P, Q, mP)
    c, d = coords(K, EK, n, P, Q, mQ)
    det, trace = (a * d - b * c) % n, (a + d) % n
    R.note("""
        Let pi be the 5-power Frobenius, (x, y) -> (x^5, y^5).  It permutes the
        points of E[3], so in the basis (P,Q) it is a 2x2 matrix with entries
        in Z/3:
    """)
    R.data(f"pi(P) = {pt_str(K, mP)},  pi(Q) = {pt_str(K, mQ)}")
    R.data(f"matrix of pi = [[{a}, {b}], [{c}, {d}]]  in Z/{n};  "
           f"trace = {trace},  det = {det}")
    print()
    R.check("pi(P), pi(Q) lie in E[n]", EK.mul(n, mP) is None and EK.mul(n, mQ) is None)
    R.note("""
        Galois equivariance says e_n(pi P, pi Q) = e_n(P,Q)^p: Frobenius raises a
        pairing value to the p-th power.  Equivalently the determinant of the
        matrix is p mod n.  That determinant is exactly the cyclotomic character
        chi_p, so the pairing forces the Galois action on E[n] to be symplectic
        with determinant chi_p.
    """)
    lhs, rhs = EK.weil_pairing(mP, mQ, n), K.pow(z, p)
    R.data(f"e_n(pi P, pi Q) = {K.format(lhs)},   e_n(P,Q)^p = {K.format(rhs)}")
    R.check("Galois equivariance  e_n(pi P, pi Q) = e_n(P,Q)^p", K.eq(lhs, rhs))
    R.check(f"det(pi) = {det} equals p mod n = {p % n}  (cyclotomic character)",
            det == p % n)
    R.check(f"trace(pi) = {trace} equals a_{p} mod n = {a_p % n}", trace == a_p % n)
    mP2, mQ2 = frob(K, EK, p, mP), frob(K, EK, p, mQ)
    R.check("pi^2 fixes E[n] (E[n] is rational over GF(25))", mP2 == P and mQ2 == Q)
    R.note(f"""
        The trace is a_{p} mod n, matching the characteristic polynomial
        T^2 - a_{p} T + {p} = T^2 + {p} of Frobenius, whose constant term is the
        determinant.  Because E[3] is rational over GF(25), pi^2 = pi_25 acts as
        the identity on E[3]; its characteristic polynomial is T^2 + 10 T + 25
        (a_25 = {K.order + 1 - EK.cardinality()}).

        Over Q the same statement reads det rho_{{E,l}} = chi_l for the mod-l
        Galois representation rho_{{E,l}}.  Complex conjugation then has
        determinant -1, so rho_{{E,l}} is odd -- one of the hypotheses in Serre's
        conjecture, and an input to the modularity lifting and level lowering
        steps of the FLT proof.
    """)

    # ---- 4 -------------------------------------------------------------
    R.section("4. The divisorial definition (Miller's function)")
    R.note("""
        Abstractly the pairing is defined by functions, not by an algorithm.
        The divisor n[P] - n[O] is principal, so there is a function f_P with
        that divisor, and one sets

            e_n(P, Q) = (-1)^n f_P(Q) / f_Q(P).

        Miller's algorithm evaluates f_P(Q) without ever writing f_P down.  On
        the GF(7) curve from section 1, with n = 3:
    """)
    F = FiniteField(7)
    E = EllipticCurve(F, 0, 2)
    P, Q = canonical_basis(F, E, 3)
    fP, fQ = E.miller(P, Q, 3), E.miller(Q, P, 3)
    z = E.weil_pairing(P, Q, 3)
    R.data(f"{curve_str(F, E)}")
    R.data(f"P = {pt_str(F, P)},  Q = {pt_str(F, Q)}")
    R.data(f"f_P(Q) = {F.format(fP)},  f_Q(P) = {F.format(fQ)}")
    R.data(f"(-1)^3 * f_P(Q)/f_Q(P) = {F.format(z)} = e_3(P,Q)")
    print()
    R.check("Miller's formula reproduces the pairing", F.eq(F.neg(F.div(fP, fQ)), z))
    R.note("""
        That formula is exactly WeilDatum.pairing in the FLT formalization:
        evalFun f1 D2 / evalFun f2 D1 with ord f1 = n*D1 and ord f2 = n*D2
        (Def_AlgebraicCurve_WeilDatum.lean).  The formalization carries the
        pairing for the Jacobian of a general function field; this demo is the
        elliptic-curve case, where divisors are points and the same formula
        computes the classical Weil pairing.
    """)

    R.finish()


if __name__ == "__main__":
    main()
