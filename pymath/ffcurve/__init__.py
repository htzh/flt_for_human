"""ffcurve — finite fields and elliptic curves for the pymath demos.

Fields are sympy-backed (``fields.FiniteField``): ``Poly(modulus=p)`` does the
polynomial arithmetic, reduction, inversion and irreducibility testing.

Elliptic curves and Miller's Weil pairing are supplied here (``elliptic.py``),
because sympy has no finite-field elliptic curve and no Weil pairing.

The package also carries ``lattices.py``, the 2x2 integer-matrix machinery
(Smith and Hermite normal forms, row/column lattices, the projective line over
Z/N) used by the Gamma_0 index demo.
"""

from .elliptic import EllipticCurve
from .fields import FiniteField

__all__ = ["FiniteField", "EllipticCurve"]
