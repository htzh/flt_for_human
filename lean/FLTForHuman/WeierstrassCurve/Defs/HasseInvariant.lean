/-
  The Hasse invariant of a Weierstrass curve and the Legendre normal form.

  * `WeierstrassCurve.hasseInvariant q W` — the coefficient of degree `q - 1` in the `(q - 1)/2`-th power
    of the two-torsion cubic of `W`, the mod-`q` Hasse invariant of the curve.
  * `WeierstrassCurve.legendreCurve t` — the curve `y² = x(x - 1)(x - t)`.
  * `ModularCurve.ssJSetHasse q K` — the set of `j`-invariants at which every elliptic curve over `K`
    has vanishing Hasse invariant: the supersingular locus.

  Transcribed from the pin's definition file (pinned `aa2d8b3`)
  `Definitions/Def_WeierstrassCurve_HasseInvariant.lean` (24 lines), at the pin's names.

  spec-pin: Definitions/Def_WeierstrassCurve_HasseInvariant.lean
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.Polynomial.Basic

set_option autoImplicit false

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

noncomputable def hasseInvariant (q : ℕ) (W : WeierstrassCurve R) : R :=
  (W.twoTorsionPolynomial.toPoly ^ ((q - 1) / 2)).coeff (q - 1)

def legendreCurve (t : R) : WeierstrassCurve R :=
  ⟨0, -(1 + t), 0, t, 0⟩

end WeierstrassCurve

namespace ModularCurve

def ssJSetHasse (q : ℕ) (K : Type*) [Field K] : Set K :=
  {j | ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j → W.hasseInvariant q = 0}

end ModularCurve

end
