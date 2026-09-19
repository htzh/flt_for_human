"""Divisors on an elliptic curve, principal divisors, and Pic^0.

A divisor is a formal integer combination of rational points of the curve.  On
a smooth curve the degree-zero divisors modulo principal divisors form
``Pic^0``; for an elliptic curve the map

    P |-> [P] - [O]

is a group isomorphism ``E -> Pic^0``.  This module supplies just enough to
exhibit that concretely:

* ``Divisor`` — formal sums, degree, support;
* ``line_divisor`` / ``vertical_divisor`` — divisors of the functions cutting
  out chords, tangents and verticals;
* ``chord_tangent_divisor`` — the principal divisor
  ``[P] + [Q] - [P+Q] - [O]`` that realises the group law in ``Pic^0``;
* ``abel_jacobi_sum`` and ``is_principal`` — for genus 1 a degree-zero divisor
  is principal exactly when the group sum of its points is ``O``.

This mirrors ``AlgebraicCurve.Divisor``, ``Divisor.degree``,
``Divisor.IsPrincipal`` and ``Pic0`` in the FLT formalization, in the elliptic
curve case where divisors are finite sums of points rather than of places.
"""


class Divisor:
    """A formal sum of rational points of an elliptic curve E.

    ``terms`` is either a dict ``{point: coefficient}`` (fine when the points
    are distinct) or an iterable of ``(point, coefficient)`` pairs.  Use the
    pair form whenever the same point can occur twice, such as ``[P] - [Q]``
    with ``P == Q``: a dict literal would collapse the two entries.
    """

    def __init__(self, E, terms=None):
        self.E = E
        self.terms = {}
        if terms is None:
            items = ()
        elif isinstance(terms, dict):
            items = terms.items()
        else:
            items = terms  # an iterable of (point, coefficient) pairs
        for P, n in items:
            if n:
                self.terms[P] = self.terms.get(P, 0) + n
        self.terms = {P: n for P, n in self.terms.items() if n}

    # -- arithmetic ------------------------------------------------------

    def __add__(self, other):
        out = dict(self.terms)
        for P, n in other.terms.items():
            out[P] = out.get(P, 0) + n
        return Divisor(self.E, out)

    def __neg__(self):
        return Divisor(self.E, {P: -n for P, n in self.terms.items()})

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, k):
        return Divisor(self.E, {P: k * n for P, n in self.terms.items()})

    __rmul__ = __mul__

    def __eq__(self, other):
        return self.terms == other.terms

    def __hash__(self):
        return hash(frozenset(self.terms.items()))

    # -- invariants ------------------------------------------------------

    def coeff(self, P):
        return self.terms.get(P, 0)

    def support(self):
        return sorted(self.terms, key=lambda P: _point_key(self.E.F, P))

    def degree(self):
        return sum(self.terms.values())

    def is_zero(self):
        return not self.terms

    def format(self):
        F = self.E.F
        if not self.terms:
            return "0"
        parts = []
        for P in self.support():
            n = self.terms[P]
            pt = "O" if P is None else f"({F.format(P[0])}, {F.format(P[1])})"
            mag = f"[{pt}]" if abs(n) == 1 else f"{abs(n)}[{pt}]"
            if not parts:
                parts.append(mag if n > 0 else "-" + mag)
            else:
                parts.append((" + " if n > 0 else " - ") + mag)
        return "".join(parts)

    def __repr__(self):
        return self.format()


def _point_key(F, P):
    """Canonical ordering of points, by the field's element key."""
    if P is None:
        return (1, 0, 0)
    return (0, F.key(P[0]), F.key(P[1]))


def ordered_points(E):
    """All rational points in a deterministic order, infinity last."""
    return sorted(E.points(), key=lambda P: _point_key(E.F, P))


def abel_jacobi_sum(E, D):
    """The group sum sum_P n_P * P of a divisor; None means O.

    For a principal divisor of a curve of genus 1 this is O.  It is the
    elliptic-curve case of the Abel-Jacobi map.
    """
    S = None
    for P in D.support():
        S = E.add(S, E.mul(D.coeff(P), P))
    return S


def is_principal(E, D):
    """Genus-1 criterion: D is principal iff deg D = 0 and sum = O."""
    return D.degree() == 0 and abel_jacobi_sum(E, D) is None


# ----------------------------------------------------------------------
# Divisors of the standard functions
# ----------------------------------------------------------------------


def vertical_divisor(E, C):
    """div of the vertical line x = x_C: [C] + [-C] - 2[O]."""
    if C is None:
        return Divisor(E)
    if E.F.eq(C[1], E.F.zero()):  # C = -C, tangent is vertical
        return Divisor(E, {C: 2, None: -2})
    return Divisor(E, {C: 1, E.neg(C): 1, None: -2})


def line_divisor(E, A, B):
    """div of the line through A and B (the tangent when A == B).

    A line meets the curve in three points counted with multiplicity, so the
    divisor is [A] + [B] + [C] - 3[O] with C = -(A+B); when the line is
    vertical it is [A] + [-A] - 2[O].
    """
    if A is None and B is None:
        raise ValueError("the line through two copies of O is not defined")
    if A is None:
        return vertical_divisor(E, B)
    if B is None:
        return vertical_divisor(E, A)
    if A == B:
        if E.F.eq(A[1], E.F.zero()):
            return vertical_divisor(E, A)
        C = E.neg(E.add(A, A))
        return Divisor(E, [(A, 2), (C, 1), (None, -3)])
    if A == E.neg(B):
        return vertical_divisor(E, A)
    C = E.neg(E.add(A, B))
    return Divisor(E, [(A, 1), (B, 1), (C, 1), (None, -3)])


def chord_tangent_divisor(E, A, B):
    """The principal divisor [A] + [B] - [A+B] - [O].

    It is div(line through A,B) - div(vertical through A+B), so it exhibits
    the group law of E inside Pic^0.
    """
    if A is None and B is None:
        return Divisor(E)
    return line_divisor(E, A, B) - vertical_divisor(E, E.add(A, B))


def divisor_x(E):
    """div(x): zeros where x = 0 (double at a 2-torsion point), pole of order
    2 at O.  Only the rational part is returned."""
    D = Divisor(E)
    for P in ordered_points(E):
        if P is not None and E.F.eq(P[0], E.F.zero()):
            mult = 2 if E.F.eq(P[1], E.F.zero()) else 1
            D = D + Divisor(E, {P: mult})
    return D - Divisor(E, {None: 2})


def divisor_y(E):
    """div(y): simple zeros at the 2-torsion points, pole of order 3 at O."""
    D = Divisor(E)
    for P in ordered_points(E):
        if P is not None and E.F.eq(P[1], E.F.zero()):
            D = D + Divisor(E, {P: 1})
    return D - Divisor(E, {None: 3})
