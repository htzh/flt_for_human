/-
The pole divisor of a transcendental element.

For an element `x` transcendental over `K` with `K⟮x⟯` finite over `F`, the divisor
`v ↦ max 0 (-v.ord x)` is realised by an actual divisor — the pole divisor of `x`.  The
proof takes the divisor of `x` from `HasPrincipalDivisors` (available because `F/K` is a
curve by `isCurveOver_of_isAlgClosed_of_transcendental`) and truncates it at each place.

This is the pin's `exists_poleDivisor_of_transcendental`; it lives above the `IsCurveOver`
layer because the pin's proof opens with `isCurveOver_of_isAlgClosed_of_transcendental`,
which is not available in `Defs/PoleDivisorPackage.lean`.

spec-pin: Theorems/Thm_AlgebraicCurve_exists_poleDivisor_of_transcendental.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_poleDivisor_of_transcendental.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Defs.PoleDivisorPackage

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

theorem exists_poleDivisor_of_transcendental {K F : Type*} [Field K] [IsAlgClosed K] [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (-v.ord x) := by
  have hcurve : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  obtain ⟨P, hP, -⟩ :=
    (hcurve.toHasPrincipalDivisors (K := K) (F := F)).exists_divisor x hx0
  refine ⟨(-P) ⊔ 0, fun v => ?_⟩
  show max ((-P) v) ((0 : Divisor K F) v) = max 0 (-v.ord x)
  rw [Finsupp.neg_apply, hP v, Finsupp.coe_zero, Pi.zero_apply, max_comm]

end AlgebraicCurve
