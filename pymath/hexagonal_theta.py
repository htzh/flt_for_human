"""The hexagonal theta series and the chi_{-3} weight-one Eisenstein series.

CONCEPT
    The hexagonal form Q(x, y) = x^2 + x y + y^2 is the norm form of the ring
    of Eisenstein integers Z[zeta_6] = Z[zeta_3].  Its theta series

        theta(tau) = sum_{x, y in Z} q^(x^2 + x y + y^2),   q = exp(2 pi i tau),

    has coefficients r(n) = #{ (x, y) : Q(x, y) = n }, the number of elements
    of Z[zeta_6] of norm n.  A classical identity identifies it with the
    weight-one Eisenstein series attached to the nontrivial character mod 3:

        theta(tau) = 1 + 6 sum_{n >= 1} sigma_chi(n) q^n
                   = 1 + 6 q + 6 q^3 + 6 q^4 + 12 q^7 + 6 q^9 + ... ,
        sigma_chi(n) = sum_{d | n} chi_{-3}(d),   chi_{-3}(n) = (n | 3).

    The factor 6 is the number of units of Z[zeta_6]; the arithmetic content
    is the splitting law of primes in Z[zeta_6]: 3 ramifies, p = 1 mod 3
    splits, p = 2 mod 3 is inert.  Poisson summation supplies the analytic
    half: theta satisfies the Fricke functional equation
    theta(-1/(3 tau)) = -i sqrt(3) tau theta(tau) and is invariant under
    tau -> tau + 1, so it is a modular form of weight 1 on Gamma_1(3).  The
    two halves meet at the identity above: the coefficients are at once a
    representation count (arithmetic) and a divisor sum (modularity).

FLT ANCHOR
    EisensteinWeightOne.chiNegThree   (Definitions/Def_ModularForm_EisensteinChiNegThree.lean, line 7)
    EisensteinWeightOne.sigmaChi      (line 10)
    EisensteinWeightOne.e1Chi3        (line 13)
    EisensteinWeightOne.E1Chi3IsModular (line 20)
    EisensteinWeightOne.coeff_e1Chi3  (Theorems/Thm_EisensteinWeightOne_coeff_e1Chi3.lean, line 7)
    EisensteinWeightOne.tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal
                                      (Theorems/Thm_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal.lean, line 8)
    EisensteinWeightOne.three_dvd_coeff_mul_e1Chi3_sub
                                      (Theorems/Thm_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.lean, line 7)
    HexagonalLattice.summable_thetaTerm_and_tsum_neg_inv_three_mul
                                      (Theorems/Thm_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.lean, line 6)
    EisensteinWeightOne.e1Chi3IsModular
                                      (P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean, lines 3763 and 1256, 1554, 1671)
    pin: anthropics/fermats-last-theorem@aa2d8b3

WHY IT MATTERS FOR FLT
    The weight-one chi_{-3} series is the low-weight generator of the
    Gamma_1(N) spaces used by the integral-structure route (the trace route,
    math/013).  Its coefficients are integral, divisible by 6 in positive
    degree, and congruent to 1 modulo 3; that congruence is what makes the
    weight-two mod-3 congruence lift work (three_dvd_coeff_mul_e1Chi3_sub).
    The series also drives FLT's weight-one (Langlands-Tunnell) branch: it is
    the form whose Hecke eigenvalues are the character chi_{-3}, and its
    Poisson-summation functional equation is the analytic input that produces
    weight-one modularity at level 3.

RUN
    python3 hexagonal_theta.py
    python3 hexagonal_theta.py > hexagonal_theta.expected.txt
"""

import cmath
import math

import sympy as sp

from ffcurve.hexagonal import (chi_minus_3, conj, divmod_z6, e1chi3_series,
                               gcd_z6, hexform, mul, norm, repr_count,
                               repr_solutions, rot, sigma_chi, theta_series,
                               unit_orbits, units)
from report import Report

N = 64        # q-expansion precision: coefficients of q^0 .. q^(N-1)
BOX = 24      # grid half-width for the ring identities
SIGMA = 2j    # base point (in the upper half plane) for the functional equations
TRUNC = 12    # lattice truncation for the numerical theta values


def theta_value(sigma, M=TRUNC):
    """Truncated numerical value of sum_{x,y} exp(2 pi i sigma Q(x, y))."""
    total = 0j
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            total += cmath.exp(2j * math.pi * sigma * hexform(x, y))
    return total


def poly_line(coeffs, hi=6):
    """A short display of a power series, dropping zero terms."""
    terms = []
    for n in range(hi):
        c = coeffs[n]
        if c == 0:
            continue
        if n == 0:
            terms.append(str(c))
        elif n == 1:
            terms.append("q" if c == 1 else f"{c} q")
        else:
            terms.append(f"q^{n}" if c == 1 else f"{c} q^{n}")
    return " + ".join(terms)


def main():
    R = Report("The hexagonal theta series and the chi_{-3} Eisenstein series")

    # ---- 1 -------------------------------------------------------------
    R.section("1. The hexagonal form and the ring Z[zeta_6]")
    R.note("""
        Q(x, y) = x^2 + x y + y^2 is the norm form of the Eisenstein integers
        Z[zeta_6], where zeta = exp(i pi / 3) satisfies zeta^2 = zeta - 1 and
        zeta^6 = 1.  Writing z = a + b zeta as the pair (a, b), the norm is
        N(z) = z * conj(z) = a^2 + a b + b^2.  The form is positive definite
        and its discriminant is -3: the identity 4 Q = (2x + y)^2 + 3 y^2
        exhibits it as (a square) + 3 (a square).
    """)
    R.data("Q(x, y) = x^2 + x y + y^2  is the norm of x + y zeta,  zeta^6 = 1")
    R.data("Q(1,0) = 1, Q(1,1) = 3, Q(2,1) = 7, Q(1,2) = 7, Q(2,3) = 19")
    R.check("4 Q(x, y) = (2x + y)^2 + 3 y^2 for a grid of (x, y)",
            all(4 * hexform(x, y) == (2 * x + y) ** 2 + 3 * y ** 2
                for x in range(-12, 13) for y in range(-12, 13)))
    R.check("N is multiplicative: N(z w) = N(z) N(w) on a box",
            all(norm(mul(z, w)) == norm(z) * norm(w)
                for z in [(a, b) for a in range(-3, 4) for b in range(-3, 4)]
                for w in [(c, d) for c in range(-3, 4) for d in range(-3, 4)]))
    R.check("z * conj(z) = N(z) and conj(z w) = conj(z) conj(w) on a box",
            all(mul(z, conj(z)) == (norm(z), 0)
                and conj(mul(z, w)) == mul(conj(z), conj(w))
                for z in [(a, b) for a in range(-3, 4) for b in range(-3, 4)]
                for w in [(c, d) for c in range(-3, 4) for d in range(-3, 4)]))
    box = [(a, b) for a in range(-3, 4) for b in range(-3, 4)]
    R.check("Euclidean division: z = y q + r with N(r) < N(y), and gcd by iteration",
            all(z == (mul(y, divmod_z6(z, y)[0])[0] + divmod_z6(z, y)[1][0],
                     mul(y, divmod_z6(z, y)[0])[1] + divmod_z6(z, y)[1][1])
                and norm(divmod_z6(z, y)[1]) < norm(y)
                for z in box for y in box if y != (0, 0))
            and norm(gcd_z6((2, 1), (1, 2))) == 1)

    # ---- 2 -------------------------------------------------------------
    R.section("2. The six units, and why every count is a multiple of six")
    R.note("""
        Rotating by zeta, (a, b) -> (-b, a + b), is multiplication by the unit
        zeta and preserves the norm.  The norm-one elements are exactly the six
        powers of zeta (FLT's unitFinset); for n > 0 they act freely on the
        solutions of Q(x, y) = n, so each nonzero representation lies in a
        six-element orbit and 6 divides r(n).  The quotient r(n) / 6 counts
        orbits, i.e. elements of norm n up to multiplication by a unit.
    """)
    R.data(f"units of Z[zeta_6] = {units()}")
    R.check("the six listed elements have norm 1",
            all(norm(u) == 1 for u in units()))
    R.check("every norm-one element of the box is one of those six",
            all(z in units()
                for z in [(a, b) for a in range(-3, 4) for b in range(-3, 4)]
                if norm(z) == 1))
    R.check("zeta^6 = 1 and the orbit of a nonzero element has six distinct points",
            all(rot(rot(rot(rot(rot(rot(z)))))) == z
                for z in [(a, b) for a in range(-3, 4) for b in range(-3, 4)])
            and len(set(unit_orbits(7)[0])) == 6)
    R.data("n : " + "  ".join(f"{n:>3}" for n in range(0, 21)))
    R.data("r(n): " + "  ".join(f"{repr_count(n):>3}" for n in range(0, 21)))
    R.check("6 divides r(n) for every n = 1 .. 63",
            all(repr_count(n) % 6 == 0 for n in range(1, N)))
    R.check("the unit orbits partition the solutions, each of size six",
            all(len(o) == 6 and len(set(o)) == 6 for n in range(1, 40)
                for o in unit_orbits(n))
            and all(len(unit_orbits(n)) * 6 == repr_count(n) for n in range(1, 40)))
    R.check("r(0) = 1, the exceptional orbit of the origin",
            repr_count(0) == 1 and len(unit_orbits(0)) == 1)

    # ---- 3 -------------------------------------------------------------
    R.section("3. The character chi_{-3}, the divisor sum, and the main identity")
    R.note("""
        chi_{-3} is the nontrivial character mod 3: it is multiplicative and
        vanishes exactly on the multiples of 3.  The divisor sum sigma_chi(n)
        = sum_{d | n} chi_{-3}(d) counts divisors congruent to 1 mod 3 minus
        those congruent to 2 mod 3.  The main identity of the arithmetic half
        is r(n) = 6 sigma_chi(n) for n >= 1.
    """)
    R.data("n      : " + "  ".join(f"{n:>3}" for n in range(1, 16)))
    R.data("chi(n) : " + "  ".join(f"{chi_minus_3(n):>3}" for n in range(1, 16)))
    R.data("sig(n) : " + "  ".join(f"{sigma_chi(n):>3}" for n in range(1, 16)))
    R.data("r(n)   : " + "  ".join(f"{repr_count(n):>3}" for n in range(1, 16)))
    R.data(f"representations of 7:  {repr_solutions(7)}")
    R.data(f"13 has {len(repr_solutions(13))} representations"
           f" in {len(unit_orbits(13))} unit orbits, e.g. {unit_orbits(13)[0]}")
    R.check("chi_{-3} is multiplicative on coprime arguments and vanishes iff 3 | n",
            all(chi_minus_3(m * n) == chi_minus_3(m) * chi_minus_3(n)
                for m in range(1, 20) for n in range(1, 20) if math.gcd(m, n) == 1)
            and all((chi_minus_3(n) == 0) == (n % 3 == 0) for n in range(1, 200)))
    R.check("r(n) = 6 sigma_chi(n) for n = 1 .. 63 (FLT: reprCountEqCoeffE1Chi3)",
            all(repr_count(n) == 6 * sigma_chi(n) for n in range(1, N)))
    R.check("r(n) = 6 (d_1(n) - d_2(n)): divisors mod 3",
            all(repr_count(n) == 6 * (sum(1 for d in range(1, n + 1) if n % d == 0 and d % 3 == 1)
                                      - sum(1 for d in range(1, n + 1) if n % d == 0 and d % 3 == 2))
                for n in range(1, N)))

    # ---- 4 -------------------------------------------------------------
    R.section("4. The local laws: 3 ramifies, p = 1 mod 3 splits, p = 2 mod 3 is inert")
    R.note("""
        The proof of r(n) = 6 sigma_chi(n) is local.  In Z[zeta_6], the rational
        prime 3 ramifies as (1 - zeta)^2 up to a unit, a prime p = 1 mod 3
        splits as p = pi * conj(pi) with N(pi) = p, and a prime p = 2 mod 3
        stays prime with norm p^2.  Counting elements of norm p^k (up to the
        six units) gives 6(k + 1) in the split case, 6 or 0 according as k is
        even or odd in the inert case, and 6 for all k when p = 3.  These are
        exactly the values of 6 sigma_chi(p^k).  FLT isolates the two
        nontrivial residuals as SplitPrimePowCount and OrbitCountMultiplicative
        and then assembles them by induction over the prime factorization of n.
    """)
    split_primes = [p for p in range(2, 100) if sp.isprime(p) and sigma_chi(p) == 2]
    inert_primes = [p for p in range(2, 100) if sp.isprime(p) and sigma_chi(p) == 0]
    R.data(f"p = 1 mod 3 (split): {split_primes}")
    R.data(f"p = 2 mod 3 (inert): {inert_primes}")
    R.check("split p = 1 mod 3: r(p^k) = 6 (k + 1) for every p < 100, p^k < 64",
            all(repr_count(p ** k) == 6 * (k + 1)
                for p in split_primes for k in range(6) if p ** k < N))
    R.check("inert p = 2 mod 3: r(p^k) = 6 for even k, 0 for odd k",
            all(repr_count(p ** k) == (6 if k % 2 == 0 else 0)
                for p in inert_primes for k in range(6) if p ** k < N))
    R.check("a split prime is represented: r(p) = 12 for every p = 1 mod 3 below 100",
            all(repr_count(p) == 12 for p in split_primes))
    R.check("an inert prime is not represented: r(p) = 0 for every p = 2 mod 3 below 100",
            all(repr_count(p) == 0 for p in inert_primes))
    R.check("p = 3 ramifies: r(3^k) = 6 and r(3 m) = r(m) for every computed m",
            all(repr_count(3 ** k) == 6 for k in range(4))
            and all(repr_count(3 * m) == repr_count(m) for m in range(1, N // 3)))
    R.check("coprime multiplicativity: 6 r(m n) = r(m) r(n) for coprime m, n < 24",
            all(6 * repr_count(m * n) == repr_count(m) * repr_count(n)
                for m in range(1, 24) for n in range(1, 24) if math.gcd(m, n) == 1))
    R.check("multiplicativity genuinely needs coprimality: 6 r(4) != r(2) r(2)",
            6 * repr_count(4) != repr_count(2) * repr_count(2))

    # ---- 5 -------------------------------------------------------------
    R.section("5. The q-expansion: theta is e1Chi3")
    R.note("""
        Collecting the representation counts into a power series gives the
        theta series of the hexagonal lattice; the main identity says it is
        FLT's e1Chi3, the q-expansion of the weight-one Eisenstein series
        E_1(1, chi_{-3}).  Its constant term is 1 (the origin), and every
        positive-degree coefficient is 6 sigma_chi(n), hence divisible by 6
        and congruent to 1 modulo 3.
    """)
    theta = theta_series(N)
    e1 = e1chi3_series(N)
    R.data("theta  = " + poly_line(theta) + " + ...")
    R.data("e1Chi3 = " + poly_line(e1) + " + ...")
    R.check("theta and 1 + 6 sum sigma_chi(n) q^n agree to q^63",
            theta == e1)
    R.check("the positive coefficients are 6 sigma_chi(n), divisible by 6",
            all(theta[n] == 6 * sigma_chi(n) and theta[n] % 6 == 0
                for n in range(1, N)))
    R.check("e1Chi3 - 1 is divisible by 3 coefficientwise (FLT: three_dvd_coeff_mul_e1Chi3_sub)",
            all((theta[n] - (1 if n == 0 else 0)) % 3 == 0 for n in range(N)))

    # ---- 6 -------------------------------------------------------------
    R.section("6. The analytic half: T, Fricke and U_3 functional equations")
    R.note("""
        Poisson summation for the rank-two lattice Z[zeta_6] turns the theta
        series into itself at the Fricke translate: theta(-1/(3 tau)) =
        -i sqrt(3) tau theta(tau).  Together with the evident
        theta(tau + 1) = theta(tau) and the derived law
        theta(tau/(1 - 3 tau)) = (1 - 3 tau) theta(tau) for the other
        generator U_3 of Gamma_0(3), this is the weight-one modularity.  The
        checks below evaluate the (rapidly convergent) sum numerically at
        tau = 2i; they illustrate the identities rather than proving them.
    """)
    fricke_err = abs(theta_value(-1 / (3 * SIGMA)) + 1j * math.sqrt(3) * SIGMA * theta_value(SIGMA))
    u_err = abs(theta_value(SIGMA / (1 - 3 * SIGMA)) - (1 - 3 * SIGMA) * theta_value(SIGMA))
    t_err = abs(theta_value(SIGMA + 1) - theta_value(SIGMA))
    R.data(f"tau = {SIGMA.imag:g}i, truncation |x|, |y| <= {TRUNC};"
           f"  theta(tau) = {theta_value(SIGMA).real:.6f} + {theta_value(SIGMA).imag:.6f}i")
    R.check("theta(-1/(3 tau)) = -i sqrt(3) tau theta(tau) (Fricke)",
            fricke_err < 1e-9)
    R.check("theta(tau + 1) = theta(tau) (the T generator)", t_err < 1e-9)
    R.check("theta(tau/(1 - 3 tau)) = (1 - 3 tau) theta(tau) (the U_3 generator)",
            u_err < 1e-9)

    # ---- 7 -------------------------------------------------------------
    R.section("7. The formalization")
    R.note("""
        FLT's proof (P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean) has
        the same two halves.  The arithmetic half defines the custom Euclidean
        domain HexInt = Z[zeta_6], proves the splitting law for primes and the
        orbit count, and concludes reprCountEqCoeffE1Chi3.  The analytic half
        defines hexTheta, proves the Poisson/Fricke identity
        hexTheta_eq_mul_self_neg_inv, and assembles a modular form of weight 1
        on Gamma_1(3) from the T and U_3 slash laws and boundedness at the
        cusps.  The headline EisensteinWeightOne.e1Chi3IsModular is the
        statement that e1Chi3 is that form's q-expansion; the demo's section 3
        is the coefficient identity it rests on, and section 6 is the
        functional equation.
    """)
    R.note("""
        For the integral-structure route (math/013) the point is that this
        weight-one form generates the low-weight part of the Gamma_1(N)
        spaces with integral q-expansions, and its mod-3 congruence to 1 powers
        the weight-two mod-3 congruence lift.
    """)

    R.finish()


if __name__ == "__main__":
    main()
