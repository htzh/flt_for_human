/-
The public headline `AlgebraicCurve.RadialRegion.exists_refine_exact`: a radial
region refines to any finite break set.

Tier 1 over the tier-3 engine
`FLTForHuman/AlgebraicCurve/RadialRegion/Engine/RefineExact.lean`. The statement
is the pin's `Theorems/Thm_AlgebraicCurve_RadialRegion_exists_refine_exact.lean`
wrapper verbatim — that wrapper, not the pin's `S_` section-implicit `solution`,
is the checker's statement authority — and the proof is the one-line application
of the engine's kernel `AlgebraicCurve.RadialRegion.RadialRefine.exists_refine_exact`,
exactly as the pin's `solution` forwards to it.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_refine_exact.lean>
-/
import FLTForHuman.AlgebraicCurve.RadialRegion.Engine.RefineExact

set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

namespace AlgebraicCurve.RadialRegion

-- pin: exists_refine_exact (Theorems/Thm_AlgebraicCurve_RadialRegion_exists_refine_exact.lean)
theorem exists_refine_exact (R : RadialRegion) (T : Finset ℝ)
    (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * π) :
    ∃ R' : RadialRegion,
      R'.q = R.q ∧ R'.r = R.r ∧ R'.K = R.K ∧ R'.Kint = R.Kint ∧ R'.loop = R.loop ∧
      Set.range R'.φs = Set.range R.φs ∪ (T : Set ℝ) ∧
      R'.N + 1 = (Set.range R.φs ∪ (T : Set ℝ)).ncard ∧
      (∀ k' : Fin R'.N, ∀ t ∈ Set.range R.φs ∪ (T : Set ℝ),
        t ∉ Ioo (R'.φs k'.castSucc) (R'.φs k'.succ)) ∧
      (∀ k' : Fin R'.N, ∃ k : Fin R.N, R'.arcIcc k' ⊆ R.arcIcc k) := by
  exact RadialRefine.exists_refine_exact (R := R) (T := T) (hT := hT)

end AlgebraicCurve.RadialRegion
