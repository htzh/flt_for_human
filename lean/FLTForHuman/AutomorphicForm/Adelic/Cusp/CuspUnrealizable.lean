/-
  No arithmetic genuine cuspidal realization on a centre-cut Siegel cover.

  If `c ≤ 0 < d₁ < d₂` and a finite union of right translates of the centre-cut
  Siegel set `centreCutSiegelSet K c u d₁ d₂` covers the centre of `GL₂(𝔸_K)`,
  then the production pins of that cover admit no arithmetic genuine cuspidal
  realization: there is no `SmoothCuspRealizationAt` whose `toFun` is continuous.

  The proof reduces a putative realization `R` to the engine's general
  contradiction `CentreCutEngine.no_function_of_ne_zero`, applied to
  `R.centralChar`, `R.toFun`, the automorphy half of `R.smoothCusp`, the
  continuity hypothesis, and a point where `R.toFun` is nonzero
  (`R.exists_ne_zero`). The `u = 0` branch is the engine's parameter-avoidance
  lemma. The shared measure-theoretic and adelic development is ported once in
  `CentreCutEngine.lean` (tier 3); this module is a façade holding only the
  headline.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre.lean`
  (pinned `aa2d8b3`, 892 lines), whose statement is the `Theorems/` wrapper
  verbatim.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.CentreCutEngine

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent
open NumberField.AdelicVolume
open scoped ENNReal

namespace AutomorphicForm

open CentreCutEngine

/-- A centre-cut Siegel cover of the centre admits no arithmetic genuine cuspidal
realization, provided `c ≤ 0 < d₁ < d₂`. -/
theorem not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : c ≤ 0) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Φ : HeckeEigensystem K ℂ) :
    ¬ IsArithGenuineCuspRealizable K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) Φ := by
  intro hreal
  obtain ⟨R, hR⟩ := hreal
  by_cases hu : u = 0
  · subst hu
    exact not_coversModCentre_of_u_eq_zero T hcov
  · obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
    exact no_function_of_ne_zero hc hd hu hcov _ _ _ R.centralChar R.toFun R.smoothCusp.1.1 hR g₀ hg₀

end AutomorphicForm
