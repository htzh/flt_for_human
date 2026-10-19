/-
  Vanishing of a continuous automorphic function on a centre-cut Siegel cover.

  Let `W` be a finite union of right translates of the centre-cut Siegel set
  `centreCutSiegelSet F c u d₁ d₂` with `c ≤ 0 < d₁ < d₂` (the central parameter
  `c` nonpositive and the determinant window nonempty). If `W` covers the centre
  of `GL₂(𝔸_F)` — `CoversModCentre F W` — then every continuous automorphic
  function `φ` at the production pins of `W` is zero. The proof is the classical
  disjoint-translates argument: a point `g₀` with `φ g₀ ≠ 0` gives, after a
  central rescaling into the window and a small open neighbourhood `O` on which
  `φ` stays nonzero, infinitely many disjoint translates of `O` inside `W`;
  left invariance of `φ` makes `‖φ‖²` have the same integral on each translate,
  so its integral over `W` is infinite, contradicting `MemLp φ 2 (μ.restrict W)`
  from the automorphy hypothesis. The case `u = 0` is handled by the engine's
  parameter-avoidance lemma.

  This module is the **façade**: the shared measure-theoretic and adelic engine is
  in `CentreCutEngine.lean`, ported once and public (tier 3). Here only the
  headline is stated; its proof invokes the engine's general contradiction
  `CentreCutEngine.no_function_of_ne_zero`. Transcribed from
  `P2M/Sol/S_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean`
  (pinned `aa2d8b3`, 902 lines), whose statement is the `Theorems/` wrapper
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

/-- A continuous automorphic function at the production pins of a centre-cut Siegel
cover is zero, provided the cover is a cover of the centre and `c ≤ 0 < d₁ < d₂`. -/
theorem eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : c ≤ 0) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ) :
    φ = 0 := by
  by_cases hu : u = 0
  · subst hu
    exact absurd hcov (not_coversModCentre_of_u_eq_zero T)
  · funext g
    by_contra hg
    exact no_function_of_ne_zero hc hd hu hcov _ _ _ ξ φ hφ hcont g hg

end AutomorphicForm
