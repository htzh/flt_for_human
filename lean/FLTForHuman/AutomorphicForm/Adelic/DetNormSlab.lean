/-
  Automorphy transfers from a slab fundamental domain to a centre-cut cover.

  If the centre-cut Siegel cover `W = ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂`
  covers the centre, and `S` is a fundamental domain for the global-points subgroup
  inside a determinant slab `α ≤ ‖det‖ ≤ β`, then an automorphic function at the
  production pins of `W` is also automorphic at the production pins of `S`. The
  proof supplies the slab covering `N` of `W` from
  `exists_finset_central_slab_covering_of_coversModCentre`, turns it into a
  `CoveredBy` statement, and applies the shared `MemLp` transfer
  `memLp_of_coveredBy` from `PeterssonSlabPairing.lean`.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean`
  (pinned `aa2d8b3`, 325 lines). The 18-helper prelude is the shared slab prelude
  promoted public in `PeterssonSlabPairing.lean` (tier 3); this module holds only
  the headline. The statement is the pin's `Theorems/` wrapper verbatim.
-/
import FLTForHuman.AutomorphicForm.Adelic.PeterssonSlabPairing

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open FundamentalDomainSlab
open AutomorphicForm.PeterssonSlabPairing

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm

set_option linter.style.haveILetI false in
/-- Automorphy at a centre-cut cover transfers to a slab fundamental domain. -/
theorem isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) (S : Set (AdelicGL2 (𝓞 F) F))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ) :
    IsAutomorphicFnAt F
      (productionPinsOf F S
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ := by
  obtain ⟨N, hN⟩ :=
    exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov α β hα
  have hX : CoveredBy (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N (slab F α β) :=
    coveredBy_of_forall hN
  obtain ⟨hfn, hmem⟩ := h
  letI := (productionPinsOf F S (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
  letI : MeasureSpace (AdelicGL2 (𝓞 F) F) :=
    ⟨(productionPinsOf F S (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ⟩
  refine ⟨hfn, ?_⟩
  exact memLp_of_coveredBy (χ := fun n => ((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)) hmem hfn.left_invariant
    (fun n w => hfn.central_transform ⟨n, Subgroup.mem_top n⟩ w) (fun n => Units.ne_zero _) hS hSs hX

end AutomorphicForm
