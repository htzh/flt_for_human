"""Level arithmetic for Ribet's level lowering.

Ribet's theorem, in the form the FLT proof uses it
(``FreyPackage.level_lowering_odd_prime_of_conductorLevel``): if a
representation is modular of a conductor level ``N``, irreducible, and
unramified at a prime ``q`` with ``q != 2``, ``q != p`` and ``q | N``, then it
is modular of some level ``M | N`` with ``q`` not dividing ``M``.  There is a
companion step at ``p`` itself
(``level_lowering_at_p_of_conductorLevel``) removing ``p`` from the level.

Iterating removes every odd prime, so the Frey curve's conductor level
``rad(a b c)`` descends to its 2-part, which is 2 -- and there are no nonzero
weight-2 cusp forms of level 2, which is the contradiction closing the proof.

This module does the arithmetic: squarefree conductor levels, exact division,
the descent chain, and the p-step bookkeeping.  A conductor level is
squarefree (``IsConductorLevel.squarefree``), so "exactly dividing" is just
"dividing"; the check below also shows what a squared factor would block.
"""

import sympy as sp


def prime_factors(n):
    return sorted(sp.factorint(abs(int(n))).keys())


def radical(n):
    r = 1
    for q in prime_factors(n):
        r *= q
    return r


def is_squarefree(n):
    return all(e == 1 for e in sp.factorint(abs(int(n))).values())


def divides_exactly(q, n):
    """q || n: q divides n but q^2 does not."""
    return n % q == 0 and n % (q * q) != 0


def removable_odd_primes(N, p):
    """The primes q that the odd-prime lowering step can remove."""
    return [q for q in prime_factors(N)
            if q != 2 and q != p and divides_exactly(q, N)]


def lower(N, q):
    """N/q when q divides N exactly once, else None."""
    return N // q if divides_exactly(q, N) else None


def descent_chain(N, p):
    """The chain of levels: remove odd primes q != p, then p.

    Returns [(level, prime removed to reach it), ...], starting at (N, None).
    """
    chain = [(N, None)]
    cur = N
    while True:
        rem = removable_odd_primes(cur, p)
        if not rem:
            break
        q = rem[0]
        cur //= q
        chain.append((cur, q))
    if p != 2 and p in prime_factors(cur):
        cur //= p
        chain.append((cur, p))
    return chain


def two_part(N):
    """The 2-part of a squarefree N: 2 if N is even, else 1."""
    return 2 if N % 2 == 0 else 1


def conductor_level(a, b, c):
    """rad(a b c), the conductor of the Frey curve."""
    return radical(a * b * c)
