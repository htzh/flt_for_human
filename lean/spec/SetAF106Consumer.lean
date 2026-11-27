import FLTForHuman.ModularCurve.Gamma0DedekindPsi
import FLTForHuman.ModularCurve.ModularPolynomialHasseDescent

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries ModularCurve UpperHalfPlane
open scoped MatrixGroups

namespace SetAF106Consumer

/-! ## Zone 1 — the modular polynomial's datum is a subsingleton (order E)

Order E's uniqueness row says two `ModularPolynomialData`s at the same level are equal; the
*consequence* a downstream development uses is that the datum type is a subsingleton — which is what
makes "the" modular polynomial well defined without carrying a choice. -/

theorem subsingleton_modularPolynomialData (N : ℕ) [NeZero N] :
    Subsingleton (ModularCurve.ModularPolynomialData N) :=
  ⟨fun d d' => ModularCurve.ModularPolynomialData.eq_all N d d'⟩

/-! ## Zone 2 — the `Γ₀` index bound at level one (order E)

Order E's `dedekindPsi` row, instantiated: the number of points of `Γ₀(1) \ SL₂(ℤ)` is at most
`ψ(1) = 1`, i.e. the level-one quotient is a point.  This is the row's use in the fibre count, at the
smallest level, and it needs both the row and mathlib's `𝒮ℒ`/`Gamma0` API. -/

theorem card_quotient_gamma0_one_le :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 1)).subgroupOf 𝒮ℒ) ≤ ModularCurve.dedekindPsi 1 :=
  ModularCurve.card_quotient_gamma0_le_dedekindPsi 1

/-! ## Zone 3 — the datum type is a subsingleton *and* its elements are equal to a chosen one

The two rows of order E composed: from zone 1, every datum equals any fixed one — the form in which a
consumer eliminates a `ModularPolynomialData` hypothesis without naming the equality. -/

theorem exists_eq_modularPolynomialData (N : ℕ) [NeZero N]
    (d : ModularCurve.ModularPolynomialData N) :
    ∃ d₀ : ModularCurve.ModularPolynomialData N, ∀ d' : ModularCurve.ModularPolynomialData N,
      d' = d₀ := by
  refine ⟨d, fun d' => ?_⟩
  exact subsingleton_modularPolynomialData N |>.elim d' d

end SetAF106Consumer
