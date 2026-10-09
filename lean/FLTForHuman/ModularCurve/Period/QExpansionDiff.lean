/-
The `q`-expansion of a Kähler differential along a place extension.  This is the
`QExpansionDiff` half of the pin's `Definitions/Def_ModularCurve_QExpansionDiff.lean`
(pinned `aa2d8b3`); the file's `Theta` half (`thetaL`, `thetaL_apply`) is homed in
`ModularCurve/Period/QExpansionDerivative.lean`, and its `TraceDiff` half in
`AlgebraicCurve/Differential/TraceDiff.lean`.  Statements are transcribed verbatim.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_QExpansionDiff.lean>
-/
import FLTForHuman.ModularCurve.Period.QExpansionDerivative
import Mathlib.RingTheory.Kaehler.Basic

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section QExpansionDiff

variable {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L]

def IsQExpansionDiffAlong (σ : F →ₐ[K] LaurentSeries L) (φ : Ω[F⁄K] →ₗ[K] LaurentSeries L) :
    Prop :=
  (∀ x : F, φ (KaehlerDifferential.D K F x) = thetaL L (σ x)) ∧
    ∀ (f : F) (ω : Ω[F⁄K]), φ (f • ω) = σ f * φ ω

open scoped Classical in

def qExpansionDiffAlong (σ : F →ₐ[K] LaurentSeries L) : Ω[F⁄K] →ₗ[K] LaurentSeries L :=
  if h : ∃ φ : Ω[F⁄K] →ₗ[K] LaurentSeries L, IsQExpansionDiffAlong σ φ then h.choose else 0

end QExpansionDiff

end ModularCurve
