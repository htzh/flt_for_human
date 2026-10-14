/-
The public headline `AlgebraicCurve.RadialRegion.exists_isOpen_starConvex_subset`:
an open star-convex neighbourhood of `R.q` inside any open set containing `R.K`.

Tier 1 over the tier-3 engine
`FLTForHuman/AlgebraicCurve/RadialRegion/Engine/IsOpenStarConvex.lean`. The
statement is the pin's
`Theorems/Thm_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean`
wrapper verbatim -- that wrapper, not the pin's `S_` top-level `solution`, is the
checker's statement authority -- and the proof is exactly the pin's `solution`,
forwarding to the engine's kernel
`AlgebraicCurve.RadialRegion.CellPeriods.exists_Kscaled_subset`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean>
-/
import FLTForHuman.AlgebraicCurve.RadialRegion.Engine.IsOpenStarConvex

set_option autoImplicit false

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

namespace AlgebraicCurve.RadialRegion

universe u

-- pin: exists_isOpen_starConvex_subset (Theorems/Thm_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean)
theorem exists_isOpen_starConvex_subset (R : RadialRegion) (T : Set ℂ)
    (hT : IsOpen T) (hKT : R.K ⊆ T) :
    ∃ V : Set ℂ, IsOpen V ∧ R.q ∈ V ∧ StarConvex ℝ R.q V ∧ R.K ⊆ V ∧ V ⊆ T := by
  obtain ⟨s, hs, hsub⟩ := CellPeriods.exists_Kscaled_subset R hT hKT
  have hs0 : 0 < s := by linarith
  exact ⟨CellPeriods.Kscaled R s, CellPeriods.isOpen_Kscaled R hs0, CellPeriods.q_mem_Kscaled R hs0,
    CellPeriods.starConvex_Kscaled R hs0, CellPeriods.K_subset_Kscaled R hs, hsub⟩

end AlgebraicCurve.RadialRegion
