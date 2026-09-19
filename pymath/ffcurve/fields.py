"""Finite fields on top of sympy.

``GF(p)`` and ``GF(p**k)``, with all polynomial arithmetic delegated to sympy:
elements are sympy ``Poly`` objects with ``modulus=p``, reduction and inversion
use ``Poly.rem`` / ``Poly.invert``, and the defining polynomial is chosen by
``Poly.is_irreducible``.  Nothing here reimplements polynomial arithmetic.

The only thing this module adds is a uniform, representation-hiding interface
(``add``, ``mul``, ``inv``, ``pow``, ``frob``, ``elements``, ``key``, ...) so
that curve code does not care which field it runs over.  Elements are opaque,
hashable and comparable; use ``key`` to order them and ``format`` to print them.

Two sympy facts this module absorbs:

* ``sympy.GF(25)`` is ``Z/25``, not a field; extension fields are built as
  ``GF(p)[t]/(f)`` with ``Poly(..., modulus=p)``.
* sympy prints coefficients in a symmetric range (``3`` shows as ``-2`` mod 5),
  so ``format`` and ``key`` reduce to ``[0, p)``.
"""

from itertools import product

from sympy import Poly, symbols

_x = symbols("x")


class FiniteField:
    """GF(p**k), sympy-backed.  ``k=1`` is the prime field GF(p)."""

    def __init__(self, p, k=1, modulus=None):
        assert p > 1 and k >= 1, "need a prime p and degree k >= 1"
        self.p = p
        self.k = k
        self.order = p ** k
        if k == 1:
            self.modulus = None
        else:
            self.modulus = modulus if modulus is not None else self._find_modulus()

    # -- construction ---------------------------------------------------

    def _find_modulus(self):
        """The first monic irreducible of degree k, in lexicographic order."""
        for cand in product(range(self.p), repeat=self.k):
            f = self._poly(list(cand) + [1])
            if f.is_irreducible:
                return f
        raise RuntimeError(f"no irreducible polynomial of degree {self.k} over GF({self.p})")

    def _poly(self, coeffs_ascending):
        """A Poly from ascending coefficients (sympy wants them descending)."""
        return Poly.from_list(list(reversed(coeffs_ascending)), _x, modulus=self.p)

    def _reduce(self, poly):
        return poly if self.modulus is None else poly.rem(self.modulus)

    # -- elements -------------------------------------------------------

    def zero(self):
        return self._reduce(self._poly([0]))

    def one(self):
        return self._reduce(self._poly([1]))

    def from_int(self, n):
        return self._reduce(self._poly([n % self.p]))

    def from_coeffs(self, coeffs_ascending):
        return self._reduce(self._poly(list(coeffs_ascending)))

    def elements(self):
        if self.k == 1:
            return [self.from_int(i) for i in range(self.p)]
        return [self.from_coeffs(c) for c in product(range(self.p), repeat=self.k)]

    # -- arithmetic -----------------------------------------------------

    def add(self, a, b):
        return self._reduce(a + b)

    def sub(self, a, b):
        return self._reduce(a - b)

    def neg(self, a):
        return self._reduce(-a)

    def mul(self, a, b):
        return self._reduce(a * b)

    def pow(self, a, n):
        if n < 0:
            return self.pow(self.inv(a), -n)
        return self._reduce(a ** n)

    def inv(self, a):
        if self.k == 1:
            return self._reduce(a ** (self.p - 2))
        return a.invert(self.modulus)

    def div(self, a, b):
        return self.mul(a, self.inv(b))

    def frob(self, a):
        """The p-power Frobenius."""
        return self._reduce(a ** self.p)

    def eq(self, a, b):
        return a == b

    # -- display / ordering ---------------------------------------------

    def _coeffs_ascending(self, a):
        cs = a.all_coeffs() or [0]
        asc = [int(c) % self.p for c in reversed(cs)]
        return asc + [0] * (self.k - len(asc))

    def key(self, a):
        """A canonical integer key, for deterministic ordering."""
        asc = self._coeffs_ascending(a)
        return sum(c * (self.p ** i) for i, c in enumerate(asc))

    def format(self, a):
        """Printable form, coefficients in [0, p)."""
        return self._format_coeffs(self._coeffs_ascending(a))

    def _format_coeffs(self, asc):
        if self.k == 1:
            return str(asc[0])
        terms = []
        for i in range(len(asc) - 1, -1, -1):
            c = asc[i]
            if c == 0:
                continue
            if i == 0:
                terms.append(str(c))
            elif i == 1:
                terms.append("t" if c == 1 else f"{c}*t")
            else:
                terms.append(f"t^{i}" if c == 1 else f"{c}*t^{i}")
        return " + ".join(terms) if terms else "0"

    def modulus_format(self):
        if self.modulus is None:
            return None
        cs = [int(c) % self.p for c in reversed(self.modulus.all_coeffs())]
        return self._format_coeffs(cs)

    def __repr__(self):
        if self.k == 1:
            return f"GF({self.p})"
        return f"GF({self.p}^{self.k}) = GF({self.p})[t]/({self.modulus_format()})"
