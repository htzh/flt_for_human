"""Formal q-expansions over the integers, truncated to a fixed precision.

Coefficients are exact integers held in a list, entry ``k`` being the
coefficient of ``q^k``.  This is enough for the classical q-expansions the FLT
formalization keeps as power series over ``Z`` (``PowerSeries ℤ``):

* ``eisenstein4 = 1 + 240 sum sigma_3(n) q^n``
* ``eisenstein6 = 1 - 504 sum sigma_5(n) q^n``
* ``etaProd = prod_{n>=1} (1 - q^n)``, and ``Delta / q = etaProd^24``
* ``jNum = eisenstein4^3 / (Delta / q)``, and ``jq = q^-1 * jNum``

so ``jNum`` is the ``q``-expansion of ``E_4^3 / Delta`` shifted, i.e.
``1 + 744 q + 196884 q^2 + ...``.  ``Delta`` itself is ``q * (Delta / q)``, whose
coefficients are the Ramanujan tau function.

Everything here is exact integer arithmetic; only ``sigma`` uses sympy
(``divisor_sigma``).
"""

import sympy as sp


def sigma(k, n):
    """Sum of the k-th powers of the divisors of n."""
    return int(sp.divisor_sigma(n, k))


def eisenstein4(N):
    """E_4 = 1 + 240 sum sigma_3(n) q^n, as N integer coefficients."""
    return [1] + [240 * sigma(3, n) for n in range(1, N)]


def eisenstein6(N):
    """E_6 = 1 - 504 sum sigma_5(n) q^n."""
    return [1] + [-504 * sigma(5, n) for n in range(1, N)]


def one(N):
    return [1] + [0] * (N - 1)


def add(a, b, N):
    return [a[i] + b[i] for i in range(N)]


def sub(a, b, N):
    return [a[i] - b[i] for i in range(N)]


def scale(a, c, N):
    return [c * a[i] for i in range(N)]


def mul(a, b, N):
    """Truncated product of two N-term series."""
    out = [0] * N
    for i in range(N):
        ai = a[i]
        if ai:
            for j in range(N - i):
                out[i + j] += ai * b[j]
    return out


def pow_series(a, k, N):
    r = one(N)
    for _ in range(k):
        r = mul(r, a, N)
    return r


def inv_series(a, N):
    """Inverse of a series with constant term 1 or -1."""
    a0 = a[0]
    assert a0 in (1, -1), "only units with constant term +-1 are supported"
    b = [0] * N
    b[0] = a0  # 1 / a0
    for n in range(1, N):
        s = sum(a[i] * b[n - i] for i in range(1, n + 1))
        b[n] = -a0 * s
    return b


def shift(a, e, N):
    """Multiply by q^e (e >= 0), truncated to N terms."""
    if e == 0:
        return list(a)
    return [0] * e + list(a)[:N - e]


def eta_prod(N):
    """prod_{n>=1} (1 - q^n), truncated to N terms."""
    r = one(N)
    for n in range(1, N):
        factor = one(N)
        factor[n] = -1
        r = mul(r, factor, N)
    return r


def delta_over_q(N):
    """Delta / q = etaProd^24: constant term 1, integer coefficients."""
    return pow_series(eta_prod(N), 24, N)


def delta(N):
    """Delta = q * (Delta / q); coefficient of q^n is the Ramanujan tau(n)."""
    return shift(delta_over_q(N), 1, N)


def tau(N):
    """The Ramanujan tau function as a list: tau(k) for k = 0..N-1, tau(0)=0."""
    return delta(N)


def delta_from_eisenstein(N):
    """(E_4^3 - E_6^2) / 1728, the other definition of Delta."""
    e4 = eisenstein4(N)
    e6 = eisenstein6(N)
    diff = sub(pow_series(e4, 3, N), pow_series(e6, 2, N), N)
    assert all(d % 1728 == 0 for d in diff), "not divisible by 1728"
    return [d // 1728 for d in diff]


def j_num(N):
    """jNum = E_4^3 / (Delta / q) = 1 + 744 q + 196884 q^2 + ..."""
    return mul(pow_series(eisenstein4(N), 3, N), inv_series(delta_over_q(N), N), N)


def j_coeffs(N):
    """Coefficients of j = q^-1 * jNum, as a dict {exponent: coefficient}."""
    jn = j_num(N)
    return {e: jn[e + 1] for e in range(-1, N - 1)}
