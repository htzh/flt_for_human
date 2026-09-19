"""Residues of meromorphic differentials, and the residue theorem.

On a smooth projective curve C, a nonzero meromorphic differential omega has
only finitely many poles, and at each of them one can take the residue.  The
residue theorem is

    sum_P res_P(omega) = 0.

On the projective line, for omega = f(x) dx, the residue at a finite point a is
the coefficient of 1/(x - a) in f, i.e. ``sympy.residue(f, x, a)``; the residue
at infinity is computed with x = 1/t, which turns omega into
``-f(1/t)/t^2 dt``, whose residue at t = 0 is the one sought.

For a principal differential the theorem is immediate: if omega = d log F =
F'/F dx for a rational function F, the residue at P is the order of F at P, and
the sum of the orders is zero because a function has as many zeros as poles.
That is the form used for the elliptic-curve check below, where the orders are
the coefficients of div(F).

The formalization states the adelic version: ``ResidueTheorem`` says the Weil
pairing of omega with the principal adele of f vanishes, i.e.
sum over places of res_v(f omega) = 0.
"""

import sympy as sp

x = sp.symbols("x")
t = sp.symbols("t")


def residue_finite(f, a):
    """residue of f(x) dx at x = a."""
    return sp.residue(f, x, a)


def residue_infinity(f):
    """residue of f(x) dx at infinity, via x = 1/t."""
    g = sp.simplify(-f.subs(x, 1 / t) / t ** 2)
    return sp.residue(g, t, 0)


def poles(f):
    """Finite poles with multiplicities: [(root, multiplicity), ...]."""
    _, den = sp.fraction(sp.together(f))
    return list(sp.roots(sp.Poly(den, x)).items())


def residue_table(f):
    """[(pole, multiplicity, residue), ...] for the finite poles."""
    return [(a, m, sp.simplify(residue_finite(f, a))) for a, m in poles(f)]


def residue_sum(f):
    """Sum of all residues, finite and at infinity."""
    total = sum(r for _, _, r in residue_table(f)) + residue_infinity(f)
    return sp.simplify(total)


def log_derivative_residues(f):
    """Residues of d log F = F'/F dx, as orders of F.

    Returns a dict {point: order}, with ``sp.oo`` for the point at infinity.
    A zero of order m gives residue +m, a pole of order m gives -m.
    """
    num, den = sp.fraction(sp.together(f))
    npoly, dpoly = sp.Poly(num, x), sp.Poly(den, x)
    out = {}
    for a, m in sp.roots(npoly).items():
        out[a] = out.get(a, 0) + m
    for a, m in sp.roots(dpoly).items():
        out[a] = out.get(a, 0) - m
    out[sp.oo] = dpoly.degree() - npoly.degree()
    return out


def log_derivative_sum(f):
    return sum(log_derivative_residues(f).values())
