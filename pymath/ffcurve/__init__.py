"""ffcurve — finite fields and elliptic curves for the pymath demos.

Fields are sympy-backed (``fields.FiniteField``): ``Poly(modulus=p)`` does the
polynomial arithmetic, reduction, inversion and irreducibility testing.

Elliptic curves and Miller's Weil pairing are supplied here (``elliptic.py``),
because sympy has no finite-field elliptic curve and no Weil pairing.
"""

from .elliptic import EllipticCurve
from .fields import FiniteField

__all__ = ["FiniteField", "EllipticCurve"]
