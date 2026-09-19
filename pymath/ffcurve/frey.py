"""The Frey curve and its invariants.

A Frey package is a solution of ``a^p + b^p = c^p`` with ``p >= 5`` prime,
``gcd(a, b) = 1``, ``a = 3 mod 4`` and ``2 | b`` (so after normalisation
``a, c`` are odd and ``b`` is even).  The associated curve is

    y^2 = x (x - a^p) (x + b^p),

with the integral model

    y^2 + x y = x^3 + ((b^p - 1 - a^p)/4) x^2 - (a^p b^p / 16) x.

Write ``X = a^p``, ``Y = b^p``, ``Z = X + Y = c^p``.  Then

    Delta = X^2 Y^2 Z^2 / 2^8 = (a b c)^(2p) / 2^8,
    c_4   = X^2 + X Y + Y^2 = Z^2 - X Y = c^(2p) - (a b)^p,
    j     = c_4^3 / Delta = 2^8 (X^2 + X Y + Y^2)^3 / (X Y Z)^2.

``Delta * 2^8 = ((a b c)^2)^p`` is a p-th power, and the curve is semistable:
at every prime ``q | a b c`` one has ``q ∤ c_4``, so the reduction is
multiplicative (the formalization's ``IsSemistableModel`` is exactly
``q | Delta -> not q | c_4``).  Hence the conductor is the squarefree number
``rad(a b c)``.

This module supplies the Weierstrass invariants and the Frey specialisations;
all of it is exact, and symbolic where the demo needs identities in ``X, Y``.
"""

import sympy as sp


def invariants(a1, a2, a3, a4, a6):
    """The standard b2, b4, b6, b8 of a Weierstrass equation."""
    b2 = a1 ** 2 + 4 * a2
    b4 = 2 * a4 + a1 * a3
    b6 = a3 ** 2 + 4 * a6
    b8 = a1 ** 2 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 ** 2 - a4 ** 2
    return b2, b4, b6, b8


def discriminant(a1, a2, a3, a4, a6):
    b2, b4, b6, b8 = invariants(a1, a2, a3, a4, a6)
    return sp.expand(-b2 ** 2 * b8 - 8 * b4 ** 3 - 27 * b6 ** 2 + 9 * b2 * b4 * b6)


def c4(a1, a2, a3, a4, a6):
    b2, b4, _, _ = invariants(a1, a2, a3, a4, a6)
    return sp.expand(b2 ** 2 - 24 * b4)


def frey_int(X, Y):
    """Integral Weierstrass coefficients of the Frey curve, X = a^p, Y = b^p."""
    return (1, (Y - 1 - X) / 4, 0, -X * Y / 16, 0)


def frey_naive(X, Y):
    """y^2 = x (x - X) (x + Y) as Weierstrass coefficients."""
    return (0, Y - X, 0, -X * Y, 0)


def frey_c4(X, Y):
    return X ** 2 + X * Y + Y ** 2


def frey_c4_via_c(X, Y, Z):
    return Z ** 2 - X * Y


def frey_discriminant(X, Y):
    """(X Y (X+Y))^2 / 2^8, the integral model's discriminant (exact)."""
    Xs, Ys = sp.sympify(X), sp.sympify(Y)
    return Xs ** 2 * Ys ** 2 * (Xs + Ys) ** 2 / 256


def frey_discriminant_naive(X, Y):
    Xs, Ys = sp.sympify(X), sp.sympify(Y)
    return 16 * Xs ** 2 * Ys ** 2 * (Xs + Ys) ** 2


def frey_j(X, Y):
    return sp.simplify(frey_c4(X, Y) ** 3 / frey_discriminant(X, Y))


def prime_factors(n):
    return sorted(sp.factorint(abs(int(n))).keys())


def radical(n):
    r = 1
    for q in prime_factors(n):
        r *= q
    return r


def is_squarefree(n):
    return all(e == 1 for e in sp.factorint(abs(int(n))).values())


def is_semistable(delta, c4_value):
    """The formalization's criterion: q | Delta implies q does not divide c4."""
    return all(int(c4_value) % q != 0 for q in prime_factors(delta))
