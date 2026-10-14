/-
The public headline `AlgebraicCurve.RadialRegion.exists_pow_pullback_laps`: the
`e`-fold pullback of a radial region under `z ↦ q + z^e`.

Tier 1 over the tier-3 engine
`FLTForHuman/AlgebraicCurve/RadialRegion/Engine/PowPullback.lean`. The statement
is the pin's
`Theorems/Thm_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps.lean` wrapper
verbatim -- that wrapper, not the pin's `S_` top-level `solution`, is the
checker's statement authority -- and the proof is the one-line application of the
engine's kernel `AlgebraicCurve.RadialRegion.PowPullback.exists_pow_pullback_laps`,
exactly as the pin's `solution` forwards to it.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps.lean>
-/
import FLTForHuman.AlgebraicCurve.RadialRegion.Engine.PowPullback

set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

namespace AlgebraicCurve.RadialRegion

-- pin: exists_pow_pullback_laps (Theorems/Thm_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps.lean)
theorem exists_pow_pullback_laps (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = e * R.N ∧
      (∀ u : ℂ, u ∈ R'.K ↔ R.q + u ^ e ∈ R.K) ∧
      (∀ u : ℂ, u ∈ R'.Kint ↔ R.q + u ^ e ∈ R.Kint) ∧
      (∀ ψ : ℝ, R.q + R'.loop ψ ^ e = R.loop ((e : ℝ) * ψ)) ∧
      ∃ lap : Fin e → Fin R.N → Fin R'.N,
        Function.Bijective (fun jk : Fin e × Fin R.N => lap jk.1 jk.2) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          R'.arcIcc (lap j k) = (fun t : ℝ => (2 * π * ((j : ℕ) : ℝ) + t) / (e : ℝ)) '' R.arcIcc k) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          (fun u : ℂ => R.q + u ^ e) '' R'.arcSet (lap j k) = R.arcSet k) ∧
        (∀ (j : Fin e) (k : Fin R.N), Set.InjOn (fun u : ℂ => R.q + u ^ e) (R'.arcSet (lap j k))) ∧
        (∀ k : Fin R.N, ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
          Pairwise (fun j j' => Disjoint (U j) (U j')) ∧ ∀ j, R'.arcSet (lap j k) ⊆ U j) := by
  exact PowPullback.exists_pow_pullback_laps (R := R) (hN := hN) (e := e) (he := he)

end AlgebraicCurve.RadialRegion
