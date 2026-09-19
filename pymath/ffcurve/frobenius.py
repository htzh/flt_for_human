"""Frobenius and its characteristic polynomial, for an elliptic curve.

For ``E`` over ``F_q`` the ``q``-power Frobenius ``pi`` satisfies

    pi^2 - a_q pi + q = 0,        a_q = q + 1 - #E(F_q),

so the characteristic polynomial is ``T^2 - a_q T + q``: its trace is ``a_q``
and its determinant is ``q``.  Hasse's bound is ``|a_q| <= 2 sqrt(q)``, which
for integral ``a_q`` is the exact condition ``a_q^2 <= 4q``; equivalently the
two roots ``alpha, beta`` satisfy ``alpha beta = q`` and
``|alpha| = |beta| = sqrt(q)``.

The polynomial determines the point counts over every extension:

    #E(F_{q^k}) = q^k + 1 - a_{q^k},

where ``a_{q^k} = alpha^k + beta^k`` obeys the recurrence

    a_{q^k} = a_q a_{q^{k-1}} - q a_{q^{k-2}},   a_1 = 2,  a_q.

This is the elliptic-curve case of the Tate module statement: ``T_l E`` is
free of rank 2, and Frobenius acts on it by a matrix with this characteristic
polynomial.  In the formalization the same polynomial appears as the
``IsAttachedTo`` clause ``X^2 - a X + l`` and, for the Jacobian, in the rank
``2g`` statement.
"""

import sympy as sp


def trace_power(a_q, q, k):
    """a_{q^k}, i.e. the trace of the k-th power of Frobenius."""
    if k == 0:
        return 2
    if k == 1:
        return a_q
    prev, cur = 2, a_q
    for _ in range(2, k + 1):
        prev, cur = cur, a_q * cur - q * prev
    return cur


def cardinality_over_extension(a_q, q, k):
    """#E(F_{q^k}) as predicted by the characteristic polynomial."""
    return q ** k + 1 - trace_power(a_q, q, k)


def hasse_ok(a_q, q):
    """Hasse's bound |a_q| <= 2 sqrt(q), in exact integer form a_q^2 <= 4q."""
    return a_q * a_q <= 4 * q


def charpoly_expr(a_q, q):
    T = sp.symbols("T")
    return T ** 2 - a_q * T + q


def charpoly_roots(a_q, q):
    T = sp.symbols("T")
    return sp.solve(charpoly_expr(a_q, q), T)


def root_modulus_squared(a_q, q):
    """The common value |alpha|^2 = |beta|^2, simplified by sympy."""
    r = charpoly_roots(a_q, q)[0]
    return sp.simplify(sp.Abs(r) ** 2)
