"""The hexagonal form x^2 + xy + y^2 and the ring Z[zeta_6] = Z[zeta_3].

An Eisenstein integer a + b*zeta (zeta = exp(i*pi/3), so zeta^2 = zeta - 1) is
stored as the pair ``(a, b)``.  Its norm is the hexagonal form

    N(a + b zeta) = (a + b zeta)(a + b zeta^-1) = a^2 + a b + b^2,

positive definite and of discriminant -3.  Multiplication, conjugation, the six
units and rotation by zeta are the arithmetic of the ring; the number of
representations of n by the form is the number of elements of norm n.

This is the arithmetic side of the weight-one chi_{-3} Eisenstein series

    e1Chi3 = 1 + 6 sum_{n>=1} sigma_chi(n) q^n,   sigma_chi(n) = sum_{d|n} chi_{-3}(d),

whose q-coefficients are exactly these representation counts.  The series and
character are FLT's ``EisensteinWeightOne.e1Chi3`` and
``EisensteinWeightOne.chiNegThree`` / ``sigmaChi`` (Definitions/Def_ModularForm_EisensteinChiNegThree.lean,
pin aa2d8b3).
"""

import math

import sympy as sp

# zeta = exp(i*pi/3) = 1/2 + i sqrt(3)/2, a primitive sixth root of unity.
ZETA = (0, 1)


def hexform(x, y):
    """The hexagonal form x^2 + x y + y^2."""
    return x * x + x * y + y * y


def mul(z, w):
    """Product in Z[zeta]: (a + b z)(c + d z) = (ac - bd) + (ad + bc + bd) z."""
    a, b = z
    c, d = w
    return (a * c - b * d, a * d + b * c + b * d)


def conj(z):
    """Complex conjugation: conj(a + b z) = (a + b) - b z."""
    a, b = z
    return (a + b, -b)


def norm(z):
    """The hexagonal-form norm N(a + b z) = a^2 + a b + b^2."""
    return hexform(z[0], z[1])


def rot(z):
    """Rotation by zeta, i.e. multiplication by (0, 1): (a, b) -> (-b, a + b)."""
    return mul(ZETA, z)


def units():
    """The six units of Z[zeta], in the order FLT's ``unitFinset`` lists them."""
    return ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))


def unit_orbit(z):
    """The six rotations of z (the orbit of z under the units)."""
    out = []
    w = z
    for _ in range(6):
        out.append(w)
        w = rot(w)
    return tuple(out)


def repr_solutions(n):
    """All (x, y) in Z^2 with x^2 + x y + y^2 = n.

    The bound follows from x^2 + y^2 <= 2 Q(x, y) = 2n.
    """
    if n == 0:
        return ((0, 0),)
    bound = math.isqrt(2 * n) + 1
    return tuple(
        (x, y)
        for x in range(-bound, bound + 1)
        for y in range(-bound, bound + 1)
        if hexform(x, y) == n
    )


def repr_count(n):
    """The number of representations of n by x^2 + x y + y^2."""
    return len(repr_solutions(n))


def unit_orbits(n):
    """Partition the representations of n into their six-element unit orbits."""
    remaining = set(repr_solutions(n))
    orbits = []
    while remaining:
        z = next(iter(remaining))
        orb = unit_orbit(z)
        orbits.append(orb)
        remaining.difference_update(orb)
    return tuple(orbits)


def chi_minus_3(n):
    """The nontrivial Dirichlet character mod 3, as a Z-valued function."""
    r = n % 3
    if r == 1:
        return 1
    if r == 2:
        return -1
    return 0


def sigma_chi(n):
    """sum_{d | n} chi_{-3}(d), FLT's ``sigmaChi``."""
    return sum(chi_minus_3(d) for d in sp.divisors(n))


def theta_series(N):
    """Coefficients of theta = sum_{x,y} q^(x^2+x y+y^2), up to q^(N-1)."""
    return [1 if n == 0 else repr_count(n) for n in range(N)]


def e1chi3_series(N):
    """Coefficients of e1Chi3 = 1 + 6 sum sigma_chi(n) q^n, up to q^(N-1)."""
    return [1] + [6 * sigma_chi(n) for n in range(1, N)]


def factorint(n):
    """Prime factorization of n, from sympy (the trusted implementation)."""
    return sp.factorint(n)


def divmod_z6(x, y):
    """A Euclidean division in Z[zeta] (nearest lattice point for the norm).

    FLT's ``HexInt`` uses exactly this quotient: the nearest integer to
    (2u + n) / (2n) coordinatewise after multiplying by the conjugate.
    """
    if y == (0, 0):
        raise ZeroDivisionError("division by zero in Z[zeta]")
    n = norm(y)
    p = mul(x, conj(y))
    q = ((2 * p[0] + n) // (2 * n), (2 * p[1] + n) // (2 * n))
    return q, (x[0] - mul(y, q)[0], x[1] - mul(y, q)[1])


def gcd_z6(x, y):
    """Euclidean gcd in Z[zeta]."""
    while y != (0, 0):
        _, r = divmod_z6(x, y)
        x, y = y, r
    return x
