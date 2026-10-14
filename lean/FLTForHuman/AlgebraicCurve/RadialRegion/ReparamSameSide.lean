/-
The public headline `AlgebraicCurve.RadialRegion.exists_reparam_same_side`:
transporting a radial arc across a shared side, in the "same side" variant.

Tier 1 over the tier-3 engine
`FLTForHuman/AlgebraicCurve/RadialRegion/Engine/Reparam.lean`. The statement is the
pin's `Theorems/Thm_AlgebraicCurve_RadialRegion_exists_reparam_same_side.lean`
wrapper verbatim — that wrapper, not the pin's `S_` top-level `solution`, is the
checker's statement authority — and the proof is the one-line application of the
engine's `AlgebraicCurve.RadialRegion.SegmentReparam.exists_reparam_same_side`,
exactly as the pin's `solution` forwards to it.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_reparam_same_side.lean>
-/
import FLTForHuman.AlgebraicCurve.RadialRegion.Engine.Reparam

set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

namespace AlgebraicCurve.RadialRegion

-- pin: exists_reparam_same_side (Theorems/Thm_AlgebraicCurve_RadialRegion_exists_reparam_same_side.lean)
theorem exists_reparam_same_side :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a a' : ℝ), 0 < a → 0 < a' →
      R.q.re + a = R'.q.re + a' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
      (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.cos t / a')⁻¹) →
      (R'.arcIcc k' ⊆ Ioo (-(π / 2)) (π / 2) ∨ R'.arcIcc k' ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (b b' : ℝ), 0 < b → 0 < b' →
      R.q.re - b = R'.q.re - b' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹) → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b')⁻¹) → R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c c' : ℝ), 0 < c → 0 < c' →
      R.q.im + c = R'.q.im + c' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.sin t / c')⁻¹) → R'.arcIcc k' ⊆ Ioo 0 π →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (d d' : ℝ), 0 < d → 0 < d' →
      R.q.im - d = R'.q.im - d' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹) → R.arcIcc k ⊆ Ioo π (2 * π) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d')⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := by
  exact SegmentReparam.exists_reparam_same_side

end AlgebraicCurve.RadialRegion
