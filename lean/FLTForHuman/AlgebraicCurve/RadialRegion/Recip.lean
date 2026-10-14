/-
The public headline `AlgebraicCurve.RadialRegion.exists_recip`: inversion of a
radial region centred at 0.

Tier 1 over the tier-3 engine
`FLTForHuman/AlgebraicCurve/RadialRegion/Engine/Recip.lean`. The statement is the
pin's `Theorems/Thm_AlgebraicCurve_RadialRegion_exists_recip.lean` wrapper
verbatim -- that wrapper, not the pin's `S_` top-level `solution`, is the
checker's statement authority -- and the proof is the one-line application of the
engine's kernel `AlgebraicCurve.RadialRegion.RadialRecip.exists_recip`, exactly as
the pin's `solution` forwards to it.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_recip.lean>
-/
import FLTForHuman.AlgebraicCurve.RadialRegion.Engine.Recip

set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

namespace AlgebraicCurve.RadialRegion

-- pin: exists_recip (Theorems/Thm_AlgebraicCurve_RadialRegion_exists_recip.lean)
theorem exists_recip (R : RadialRegion) (hq : R.q = 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = R.N ∧ (0 : ℂ) ∈ R'.Kint ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.K ↔ w⁻¹ ∉ R.Kint)) ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.Kint ↔ w⁻¹ ∉ R.K)) ∧
      (∀ θ : ℝ, R'.loop θ = (R.loop (2 * π - θ))⁻¹) ∧
      ∃ σ : Fin R.N ≃ Fin R'.N,
        (∀ k : Fin R.N, R'.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' R.arcIcc k) ∧
        (∀ k : Fin R.N, (fun w : ℂ => w⁻¹) '' R'.arcSet (σ k) = R.arcSet k) := by
  exact RadialRecip.exists_recip (R := R) (hq := hq)

end AlgebraicCurve.RadialRegion
