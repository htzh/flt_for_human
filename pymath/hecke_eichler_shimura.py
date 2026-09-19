"""Hecke operators and Eichler-Shimura — illustrative demo.

CONCEPT
    For a modular form f = sum a_n q^n of weight k and level N, and a prime
    p not dividing N, the Hecke operator is defined analytically by

        heckeT k p f = heckeU k p f + p^(k-1) f(p tau),
        heckeU k p f = sum_{b=0}^{p-1} f((tau+b)/p),

    and on q-expansions simply by

        (T_p f)_n = a_{n p} + p^(k-1) a_{n/p}   (a_{n/p} = 0 unless p | n).

    A normalized eigenform satisfies T_p f = a_p f, which at n = p^r gives the
    recursion a_{p^(r+2)} = a_p a_{p^(r+1)} - p^(k-1) a_{p^r}.  The T_p commute.
    Eichler-Shimura is the matching of this action with the Galois action on
    the Tate module: a_p is the trace of Frobenius and p^(k-1) the determinant
    (for weight 2, p).

FLT ANCHOR
    ModularForm.heckeU, heckeT        (Def_ModularForm_HeckeOperator.lean, lines 93, 96)
    ModularCurve.heckeOperatorBar     (Def_ModularCurve_HeckeModule.lean, line 16)
    ModularCurve.HeckeOperatorsCommuteBar (line 25)
    HeckeAlg, heckeGen                (Def_HeckeGalois_EichlerShimura.lean, lines 14, 16)
    ModularCurve.TateModule           (Def_ModularCurve_EichlerShimuraData.lean)
    ResidualGaloisRep.IsAttachedTo    (Def_GaloisRep_Residual.lean, line 48)

WHY IT MATTERS FOR FLT
    The Eisenstein quotient and the Hecke action on J_0(N) are what Mazur's
    argument for p >= 17 runs on (math/009), and the Eichler-Shimura match is
    how a Galois representation is attached to an eigenform: the same a_p is
    the Hecke eigenvalue and the Frobenius trace.  This demo computes the
    q-expansion side -- the "roof" of the Hecke correspondence -- exactly.

RUN
    python3 hecke_eichler_shimura.py
    python3 hecke_eichler_shimura.py > hecke_eichler_shimura.expected.txt
"""

from ffcurve.hecke import (act_Tp, commutes, eigenform_ratio,
                          exact_range, operator_matrix)
from ffcurve.qexp import (delta, eisenstein4, eisenstein6, mul, pow_series,
                          scale, tau)
from report import Report

N = 128  # precision
PRIMES = (2, 3, 5, 7, 11, 13)


def main():
    R = Report("Hecke operators and Eichler-Shimura")

    R.note("""
        This demo computes the Hecke operators on q-expansions, exactly, in
        Z[[q]] truncated to q^127.  It verifies that the Eisenstein series and
        Delta are eigenforms, reads the eigenform recursion off the operator
        equation, and checks that the operators commute on the two-dimensional
        space of level-one cusp forms of weight 24.
    """)

    e4, e6, d, t = eisenstein4(N), eisenstein6(N), delta(N), tau(N)

    # ---- 1 -------------------------------------------------------------
    R.section("1. The Hecke operator on q-expansions")
    R.data("heckeT k p f = heckeU k p f + p^(k-1) f(p tau)")
    R.data("(T_p f)_n = a_(n p) + p^(k-1) a_(n/p)")
    R.note("""
        The two terms are the p-isogeny and the diagonal part: T_p is the
        operator whose q-coefficient at n combines the coefficient at np with
        the rescaled coefficient at n/p.  Additivity and Z-linearity are
        immediate from the formula.
    """)
    lhs = act_Tp([a + b for a, b in zip(e4, d)], 3, 12, N)
    rhs = [a + b for a, b in zip(act_Tp(e4, 3, 12, N), act_Tp(d, 3, 12, N))]
    R.check("T_p is additive", lhs == rhs)
    R.check("T_p is Z-linear", act_Tp(scale(d, 5, N), 3, 12, N)
            == scale(act_Tp(d, 3, 12, N), 5, N))

    # ---- 2 -------------------------------------------------------------
    R.section("2. The Eisenstein series are eigenforms")
    R.note("""
        E_4 and E_6 are eigenforms for every T_p, with eigenvalues
        sigma_3(p) = 1 + p^3 and sigma_5(p) = 1 + p^5.  The operator formula
        reproduces this coefficient by coefficient.
    """)
    R.data("p  | T_p E_4 / E_4 | 1 + p^3 | T_p E_6 / E_6 | 1 + p^5")
    ok_eis = True
    for p in PRIMES:
        lim = exact_range(p, N)
        r4 = eigenform_ratio(act_Tp(e4, p, 4, N), e4, N, lim)
        r6 = eigenform_ratio(act_Tp(e6, p, 6, N), e6, N, lim)
        R.data(f"{p:2d} | {int(r4):13d} | {1 + p ** 3:7d} | {int(r6):13d} | {1 + p ** 5}")
        ok_eis = ok_eis and r4 == 1 + p ** 3 and r6 == 1 + p ** 5
    R.check("T_p E_4 = (1 + p^3) E_4 for every prime above", ok_eis)

    # ---- 3 -------------------------------------------------------------
    R.section("3. Delta is a cusp-form eigenform")
    R.note("""
        Delta is the level-one cusp form of weight 12, and it is an eigenform
        for every T_p.  Its eigenvalue is the q^p coefficient tau(p) -- the
        same number that appears as the trace of Frobenius in
        frobenius_charpoly, which is Eichler-Shimura.
    """)
    R.data("p  | tau(p)   | T_p Delta / Delta")
    ok_delta = True
    for p in PRIMES:
        lim = exact_range(p, N)
        rd = eigenform_ratio(act_Tp(d, p, 12, N), d, N, lim)
        R.data(f"{p:2d} | {t[p]:8d} | {int(rd)}")
        ok_delta = ok_delta and rd == t[p] and rd == d[p]
    R.check("T_p Delta = tau(p) Delta for every prime above", ok_delta)
    R.check("the eigenvalue is the q^p coefficient (f is normalized)",
            all(t[p] == d[p] for p in PRIMES))

    # ---- 4 -------------------------------------------------------------
    R.section("4. The eigenform recursion comes from the operator")
    R.note("""
        Substituting n = p^r into T_p f = a_p f gives
        a_{p^(r+1)} + p^(k-1) a_{p^(r-1)} = a_p a_{p^r}, i.e.
        a_{p^(r+2)} = a_p a_{p^(r+1)} - p^(k-1) a_{p^r}.  For Delta the
        correction is p^11, the weight-12 case of the weight-2 recursion
        recorded by CuspForm.IsNormalizedEigenform.
    """)
    rec_ok, rows = True, []
    for p in PRIMES:
        r = 0
        while p ** (r + 2) < N:
            lhs = t[p ** (r + 2)]
            rhs = t[p] * t[p ** (r + 1)] - p ** 11 * t[p ** r]
            rows.append((p, r, lhs == rhs))
            rec_ok = rec_ok and lhs == rhs
            r += 1
    R.data("p, r checked: " + ", ".join(f"({p},{r})" for p, r, _ in rows))
    R.check("the recursion a_{p^(r+2)} = a_p a_{p^(r+1)} - p^11 a_{p^r} holds",
            rec_ok)

    # ---- 5 -------------------------------------------------------------
    R.section("5. The operators commute on S_24")
    R.note("""
        Commutativity is not visible on a one-dimensional space, so we use the
        two-dimensional space S_24 of level-one cusp forms, with basis
        Delta * E_4^3 and Delta * E_6^2.  Applying T_p coefficientwise and
        rewriting in that basis gives an explicit 2x2 matrix; the matrices for
        different primes must commute.  This is the numerical shadow of
        ModularCurve.heckeOperatorsCommuteBar.
    """)
    B1 = mul(d, pow_series(e4, 3, N), N)
    B2 = mul(d, pow_series(e6, 2, N), N)
    R.data(f"S_24 basis: Delta*E_4^3 and Delta*E_6^2, both starting q^1")
    pairs = [(2, 3), (2, 5), (3, 5), (3, 7), (5, 7), (2, 11)]
    used = sorted({x for pair in pairs for x in pair})
    for p in used:
        R.data(f"A_{p} = {operator_matrix([B1, B2], p, 24, N).tolist()}")
    ok_comm, integral = True, True
    for (p, q) in pairs:
        good, Ap, Aq = commutes([B1, B2], p, q, 24, N)
        ok_comm = ok_comm and good
        integral = integral and all(
            entry == int(entry) for entry in list(Ap) + list(Aq))
        R.data(f"  A_{p} A_{q} = A_{q} A_{p}: {good}")
    R.check("the Hecke matrices on S_24 have integer entries", integral)
    R.check("T_p T_q = T_q T_p on S_24 for every pair above", ok_comm)

    # ---- 6 -------------------------------------------------------------
    R.section("6. Eichler-Shimura and the formalization")
    R.note("""
        Eichler-Shimura identifies the two actions: the Hecke eigenvalue a_p of
        a normalized eigenform of weight k is the trace of Frobenius on the
        associated l-adic representation, whose determinant is p^(k-1) -- for
        weight 2, exactly the constant term l of the polynomial X^2 - a_l X + l
        in ResidualGaloisRep.IsAttachedTo.  The demo checks the eigenvalue side
        (sections 2-4); frobenius_charpoly checks the trace side.
    """)
    R.note("""
        In the formalization the analytic operator is heckeU/heckeT, the
        action on J_0(N) is heckeOperatorBar, the algebra generated by the
        operators is HeckeAlg = MvPolynomial Nat.Primes Z with generators
        heckeGen, and the Galois module on which the two actions are compared
        is ModularCurve.TateModule.  Commutativity of the operators, checked
        above on the q-expansion side, is the hypothesis
        HeckeOperatorsCommuteBar that makes J_0(N) a module over HeckeAlg.
    """)

    R.finish()


if __name__ == "__main__":
    main()
