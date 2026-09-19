"""Level lowering — illustrative demo.

CONCEPT
    Ribet's level-lowering theorem, in the form the FLT proof uses: if a
    representation is modular of a conductor level N, irreducible, and
    unramified at a prime q with q != 2, q != p and q | N, then it is modular of
    some level M | N with q not dividing M.  A companion step removes p itself
    from the level.  Iterating strips every odd prime from the Frey curve's
    conductor level rad(a b c), leaving level 2 -- and the space of weight-2
    cusp forms of level 2 is zero, which is the contradiction.

FLT ANCHOR
    FreyPackage.IsConductorLevel, squarefree, support
        (Def_FreyPackage_IsConductorLevel.lean, line 8)
    IsConductorLevel.of_dvd, sq_not_dvd, not_four_dvd, p_dvd_abc, not_p_dvd
    FreyPackage.level_lowering_odd_prime_of_conductorLevel
        (Thm_FreyPackage_level_lowering_odd_prime_of_conductorLevel.lean)
    FreyPackage.level_lowering_at_p_of_conductorLevel
        (Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean)
    FreyPackage.level_lowering_to_two  (Thm_FreyPackage_level_lowering_to_two.lean)
    FreyPackage.ModularRepOfLevel      (Def_FLTPrelim_ModularRep.lean, line 62)
    IsPeuRamifieeAt                    (Def_WeierstrassCurve_PeuRamifiee.lean, line 10)
    ModularForm.S2_Gamma0_2_eq_zero    (Thm_ModularForm_S2_Gamma0_2_eq_zero.lean, line 13)

WHY IT MATTERS FOR FLT
    The Frey curve is semistable, so its conductor is the squarefree number
    rad(a b c) (frey_curve).  Level lowering is what turns that into the
    statement that a nonzero weight-2 cusp form of level 2 must exist, which
    S2_Gamma0_2_eq_zero contradicts.  The hypotheses are where the other demos
    enter: irreducibility is galois_rep (Mazur's argument), unramifiedness at q
    comes from the multiplicative reduction verified in frey_curve, and the
    p-step needs the residual representation to be finite at p.

RUN
    python3 level_lowering.py
    python3 level_lowering.py > level_lowering.expected.txt
"""

from ffcurve.level import (conductor_level, descent_chain, divides_exactly,
                           is_squarefree, lower, prime_factors,
                           removable_odd_primes, two_part)
from report import Report


def dedekind_psi(n):
    """psi(n) = n prod_{p | n} (1 + 1/p), the index of Gamma0(n)."""
    r = n
    for q in prime_factors(n):
        r = r // q * (q + 1)
    return r


def main():
    R = Report("Level lowering")

    R.note("""
        A Galois representation attached to a modular form has a level, and
        Ribet's theorem lets odd primes be removed from that level one at a
        time, provided the representation is irreducible and unramified there.
        This demo does the level bookkeeping exactly: the Frey curve's
        conductor level descends to level 2, where there are no nonzero
        weight-2 cusp forms.
    """)

    # ---- 1 -------------------------------------------------------------
    R.section("1. The conductor level")
    R.note("""
        FreyPackage.IsConductorLevel records what the argument needs of the
        level N: it is positive, it is squarefree, and it is supported on the
        primes dividing a b c.  For the Frey curve N = rad(a b c).
    """)
    a, b, p = 3, 2, 5
    A, B = a ** p, b ** p
    C = A + B
    N = conductor_level(a, b, C)
    R.data(f"package-shaped example: a = {a}, b = {b}, p = {p};  "
           f"a b C = {a} * {b} * {C}")
    R.data(f"conductor level N = rad(a b C) = {N} = "
           + " * ".join(str(q) for q in prime_factors(N)))
    R.check("N is squarefree", is_squarefree(N))
    R.check("every prime of N divides a b C (the support condition)",
            all((a * b * C) % q == 0 for q in prime_factors(N)))
    R.check("no prime square, and not 4, divides N (sq_not_dvd, not_four_dvd)",
            all(N % (q * q) != 0 for q in prime_factors(N)) and N % 4 != 0)

    # ---- 2 -------------------------------------------------------------
    R.section("2. The lowering step")
    R.data("if  q prime, q != 2, q != p, q | N,")
    R.data("    ModularRepOfLevel N, irreducible, unramified at q,")
    R.data("then  exists M with M | N, q not dividing M, ModularRepOfLevel M")
    R.note("""
        The conclusion is the existence of a smaller level M dividing N and not
        divisible by q -- not literally N/q, which is enough for the descent.
        The hypothesis q | N is used through exact division: a conductor level
        is squarefree, but the check below shows what a repeated prime would
        do, namely block the step.
    """)
    R.data(f"removable odd primes for N = {N}, p = {p}: "
           f"{removable_odd_primes(N, p)}")
    R.check("each step removes a prime dividing the level exactly once",
            all(divides_exactly(q, N) for q in removable_odd_primes(N, p)))
    R.check("removable primes are odd and different from p",
            all(q != 2 and q != p for q in removable_odd_primes(N, p)))
    R.check("a squared factor blocks lowering: q = 3 is not removable from 18",
            not divides_exactly(3, 18) and lower(18, 3) is None
            and not divides_exactly(3, 9))

    # ---- 3 -------------------------------------------------------------
    R.section("3. The descent to level 2")
    R.note("""
        Removing the odd primes different from p, then p, leaves the 2-part of
        the conductor level, which is 2 because b is even.  Each intermediate
        level is again a conductor level (of_dvd), so the theorem applies again.
    """)
    chain = descent_chain(N, p)
    R.data("descent: " + "  ->  ".join(
        f"{lvl}" + (f" (remove {q})" if q else "") for lvl, q in chain))
    R.check("the chain for N = 330, p = 5 is 330 -> 110 -> 10 -> 2",
            [lvl for lvl, _ in chain] == [330, 110, 10, 2])
    step_ok = True
    for i in range(1, len(chain)):
        prev, q = chain[i - 1][0], chain[i][1]
        step_ok = step_ok and q in prime_factors(prev) and divides_exactly(q, prev)
    R.check("every step divides the previous level exactly once", step_ok)
    R.check("every intermediate level is a conductor level (squarefree, "
            "supported on a b C)",
            all(is_squarefree(lvl) and all((a * b * C) % q == 0
                                           for q in prime_factors(lvl))
                for lvl, _ in chain))
    R.check("the descent ends at the 2-part of N", chain[-1][0] == two_part(N) == 2)

    # ---- 4 -------------------------------------------------------------
    R.section("4. The step at p")
    R.note("""
        The step at p needs no unramifiedness hypothesis: it uses instead that
        the residual representation is finite at p (peu ramifiee), which for the
        Frey curve follows from its integral model.  The level condition is
        p | N exactly when p | a b c, by IsConductorLevel.support and
        not_p_dvd.
    """)
    R.check("p | N and p | a b C in the example",
            N % p == 0 and (a * b * C) % p == 0)
    a2, b2, p2 = 3, 2, 7
    C2 = a2 ** p2 + b2 ** p2
    N2 = conductor_level(a2, b2, C2)
    R.data(f"another example: a = {a2}, b = {b2}, p = {p2} gives "
           f"N = {N2}; p | N is {N2 % p2 == 0}, p | a b C is "
           f"{(a2 * b2 * C2) % p2 == 0}")
    R.check("p | N if and only if p | a b c",
            (N % p == 0) == ((a * b * C) % p == 0)
            and (N2 % p2 == 0) == ((a2 * b2 * C2) % p2 == 0))
    R.check("the p-step is the last step and removes p from the level",
            chain[-1][1] == p and p not in prime_factors(chain[-1][0]))

    # ---- 5 -------------------------------------------------------------
    R.section("5. The contradiction at level 2")
    R.note("""
        What remains is a nonzero weight-2 cusp form of level 2.  But
        Gamma0(2) has index psi(2) = 3 in SL_2(Z) and S_2(Gamma0(2)) = 0:
        every such form vanishes.  That is the contradiction closing the FLT
        argument, and it is proved from mathlib alone in base/003.
    """)
    R.data(f"index [SL_2(Z) : Gamma0(2)] = psi(2) = {dedekind_psi(2)}")
    R.data("ModularForm.S2_Gamma0_2_eq_zero : every level-2 weight-2 cusp form is 0")
    R.check("the final level is 2, whose weight-2 cusp forms all vanish",
            chain[-1][0] == 2 and dedekind_psi(2) == 3)
    R.check("no odd prime survives in the final level",
            all(q == 2 for q in prime_factors(chain[-1][0])))

    # ---- 6 -------------------------------------------------------------
    R.section("6. The formalization")
    R.note("""
        ModularRepOfLevel is the input notion: it says a cusp form f of level N
        has q-coefficients congruent to the traces of Frobenius of an integral
        model of the Frey curve modulo a prime above p -- a congruence of
        traces, not an isomorphism of representations.  The two lowering
        theorems then produce ModularRepOfLevel M for M | N with the chosen
        prime removed, and level_lowering_to_two packages the iteration as
        the existence of a nonzero f in CuspForm (Gamma0 2) 2.
    """)
    R.note("""
        The hypotheses of the odd-prime step are exactly the facts gathered in
        the other demos: irreducibility (galois_rep, Mazur's argument),
        unramifiedness at q (the multiplicative reduction of frey_curve), and
        the conductor-level properties above.  The p-step uses the integral
        model of the Frey curve instead, through IsPeuRamifieeAt.
    """)

    R.finish()


if __name__ == "__main__":
    main()
