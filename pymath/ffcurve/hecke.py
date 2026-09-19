"""Hecke operators on q-expansions.

For a modular form ``f = sum a_n q^n`` of weight ``k`` and level ``N``, and a
prime ``p`` not dividing ``N``, the Hecke operator is defined analytically as

    heckeT k p f = heckeU k p f + (p^(k-1) f(p tau)),

and on q-expansions this is

    (T_p f)_n = a_{n p} + p^(k-1) a_{n / p},   a_{n/p} = 0 unless p | n.

A normalized eigenform satisfies ``T_p f = a_p f``; evaluating that at
``n = p^r`` gives the recursion

    a_{p^(r+2)} = a_p a_{p^(r+1)} - p^(k-1) a_{p^r}.

The operators commute, ``T_p T_q = T_q T_p``.  ``operator_matrix`` computes the
matrix of ``T_p`` on a finite-dimensional space spanned by known q-expansions,
which makes that commutativity checkable.

Only the coefficients up to ``q^(N-1)`` are known, so a coefficient of
``T_p f`` is exact only for indices below ``exact_range(p, N)``; the helpers
take that bound into account.
"""

import itertools

import sympy as sp


def act_Tp(a, p, k, N):
    """Coefficients of T_p f below q^N, from a = (a_0, ..., a_{N-1})."""
    out = [0] * N
    for n in range(N):
        v = a[n * p] if n * p < N else 0
        if n % p == 0:
            v += p ** (k - 1) * a[n // p]
        out[n] = v
    return out


def exact_range(p, N):
    """Number of coefficients of T_p f that are exact from data below q^N."""
    return (N - 1) // p + 1


def eigenform_ratio(f, g, N, limit=None):
    """Return c with f = c g below q^limit, or None if there is none."""
    limit = N if limit is None else limit
    ratio = None
    for n in range(limit):
        if g[n]:
            ratio = sp.Rational(f[n], g[n])
            break
    if ratio is None:
        return None
    if all(sp.Rational(f[n]) == ratio * g[n] for n in range(limit)):
        return ratio
    return None


def operator_matrix(basis, p, k, N):
    """Matrix of T_p in ``basis``, using only coefficients exact below q^N."""
    d = len(basis)
    limit = exact_range(p, N)
    imgs = [act_Tp(b, p, k, N) for b in basis]
    cands = [n for n in range(limit) if any(b[n] for b in basis)]
    chosen = None
    for idx in itertools.combinations(cands, d):
        M = sp.Matrix([[basis[j][n] for j in range(d)] for n in idx])
        if M.det() != 0:
            chosen = (idx, M)
            break
    if chosen is None:
        raise ValueError("no invertible coefficient matrix found")
    idx, M = chosen
    cols = [M.solve(sp.Matrix([img[n] for n in idx])) for img in imgs]
    return sp.Matrix(d, d, lambda i, j: cols[j][i])


def commutes(basis, p, q, k, N):
    """(do T_p and T_q commute on the span of basis, A_p, A_q)."""
    A = operator_matrix(basis, p, k, N)
    B = operator_matrix(basis, q, k, N)
    return A * B == B * A, A, B
