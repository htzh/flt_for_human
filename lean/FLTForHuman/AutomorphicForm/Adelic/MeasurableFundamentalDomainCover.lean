/-
  Measurable fundamental domains inside centre-cut Siegel covers.

  Two twin headlines: given a centre-cut Siegel cover `W = ⋃ x ∈ T, (· * x) ''
  centreCutSiegelSet K c u d₁ d₂` and a determinant slab `e₁ ≤ ‖det‖ ≤ e₂`, there
  is a measurable set `𝓕` that is a fundamental domain for the global-points
  subgroup inside the slab and is contained in a finite union of translates of
  either the integral windowed Siegel set or the centre-cut Siegel set.

  The shared 107-line measure-theory engine
  `exists_measurableSet_isFundamentalDomain_subset` (a measurable fundamental
  domain inside any measurable set meeting every orbit) is ported once in
  `PeterssonSlabPairing.lean`; this module holds the two `main` developments and
  the two headlines. The two pin `S_` files differ only in the final set
  (`integralWindowedSiegelSet` versus `centreCutSiegelSet`) and in the
  determinant parameter names; the proofs are otherwise identical.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre.lean`
  and its `…_centreCutSiegelSet_…` twin (pinned `aa2d8b3`, 267 / 266 lines).
  The statements are the pin `Theorems/` wrappers verbatim.
-/
import FLTForHuman.AutomorphicForm.Adelic.PeterssonSlabPairing
import FLTForHuman.AutomorphicForm.Adelic.DetNormSlabFundamentalDomain

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
  NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open FundamentalDomainSlab
open AutomorphicForm.PeterssonSlabPairing

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

variable {F : Type} [Field F] [NumberField F]

set_option linter.style.haveILetI false in
private theorem main_integral (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) :
    ∃ (c' u' : ℝ) (tset : Finset (AdelicGL2 (𝓞 F) F)) (𝓕 : Set (AdelicGL2 (𝓞 F) F)),
      0 < c' ∧ MeasurableSet 𝓕 ∧
      𝓕 ⊆ slab F e₁ e₂ ∧
      IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F e₁ e₂)) ∧
      𝓕 ⊆ ⋃ t ∈ tset, (· * t) '' integralWindowedSiegelSet F c' u' := by
  classical
  haveI := smulInvariantMeasure_slab (F := F) e₁ e₂
  obtain ⟨S, hSslab, hS⟩ :=
    exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F e₁ e₂
  obtain ⟨N, hN⟩ := exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov
    e₁ e₂ he₁
  let tOf : (AdeleRing (𝓞 F) F)ˣ × AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F :=
    fun p => centralScalar (𝓞 F) F p.1 * p.2
  let E : Set (AdelicGL2 (𝓞 F) F) :=
    ⋃ p ∈ N ×ˢ T, (· * tOf p) '' centreCutSiegelSet F c u d₁ d₂
  have hEm : MeasurableSet E := by
    refine Finset.measurableSet_biUnion _ fun p _ => ?_
    rw [Set.image_mul_right]
    exact (measurable_mul_const _) (measurableSet_centreCutSiegelSet c u d₁ d₂)
  have hEcov : ∀ g ∈ slab F e₁ e₂, ∃ γ : ↥(Γp F), γ • g ∈ E ∩ slab F e₁ e₂ := by
    intro g hg
    obtain ⟨γ, n, hn, x, hx, hmem⟩ := hN g hg
    refine ⟨⟨globalPoints (𝓞 F) F γ, γ, rfl⟩, ?_, ?_⟩
    · show globalPoints (𝓞 F) F γ * g ∈ E
      exact Set.mem_iUnion₂.mpr ⟨(n, x), Finset.mem_product.mpr ⟨hn, hx⟩, hmem⟩
    · show dn (globalPoints (𝓞 F) F γ * g) ∈ Set.Icc e₁ e₂
      rw [dn_globalPoints_mul]; exact hg
  obtain ⟨𝓕, h𝓕m, h𝓕E, h𝓕⟩ := exists_measurableSet_isFundamentalDomain_subset (G := ↥(Γp F))
    hS hSslab ((hEm.inter (measurableSet_slab e₁ e₂))) hEcov
  refine ⟨c ^ (∑ w : InfinitePlace F, w.mult), u, (N ×ˢ T).image tOf, 𝓕, pow_pos hc _, h𝓕m,
    fun g hg => (h𝓕E hg).2, h𝓕, fun g hg => ?_⟩
  obtain ⟨p, hp, hgp⟩ := Set.mem_iUnion₂.mp (h𝓕E hg).1
  obtain ⟨s, hs, rfl⟩ := hgp
  refine Set.mem_iUnion₂.mpr ⟨tOf p, Finset.mem_image_of_mem tOf hp, s,
    centreCutSiegelSet_subset_integralWindowedSiegelSet hc.le hs, rfl⟩

set_option linter.style.haveILetI false in
private theorem main_centre (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) :
    ∃ (d₁' d₂' : ℝ) (tset : Finset (AdelicGL2 (𝓞 F) F)) (𝓕 : Set (AdelicGL2 (𝓞 F) F)),
      0 < d₁' ∧ MeasurableSet 𝓕 ∧
      𝓕 ⊆ slab F e₁ e₂ ∧
      IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F e₁ e₂)) ∧
      𝓕 ⊆ ⋃ t ∈ tset, (· * t) '' centreCutSiegelSet F c u d₁' d₂' := by
  classical
  haveI := smulInvariantMeasure_slab (F := F) e₁ e₂
  obtain ⟨S, hSslab, hS⟩ :=
    exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F e₁ e₂
  obtain ⟨N, hN⟩ := exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov
    e₁ e₂ he₁
  let tOf : (AdeleRing (𝓞 F) F)ˣ × AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F :=
    fun p => centralScalar (𝓞 F) F p.1 * p.2
  let E : Set (AdelicGL2 (𝓞 F) F) :=
    ⋃ p ∈ N ×ˢ T, (· * tOf p) '' centreCutSiegelSet F c u d₁ d₂
  have hEm : MeasurableSet E := by
    refine Finset.measurableSet_biUnion _ fun p _ => ?_
    rw [Set.image_mul_right]
    exact (measurable_mul_const _) (measurableSet_centreCutSiegelSet c u d₁ d₂)
  have hEcov : ∀ g ∈ slab F e₁ e₂, ∃ γ : ↥(Γp F), γ • g ∈ E ∩ slab F e₁ e₂ := by
    intro g hg
    obtain ⟨γ, n, hn, x, hx, hmem⟩ := hN g hg
    refine ⟨⟨globalPoints (𝓞 F) F γ, γ, rfl⟩, ?_, ?_⟩
    · show globalPoints (𝓞 F) F γ * g ∈ E
      exact Set.mem_iUnion₂.mpr ⟨(n, x), Finset.mem_product.mpr ⟨hn, hx⟩, hmem⟩
    · show dn (globalPoints (𝓞 F) F γ * g) ∈ Set.Icc e₁ e₂
      rw [dn_globalPoints_mul]; exact hg
  obtain ⟨𝓕, h𝓕m, h𝓕E, h𝓕⟩ := exists_measurableSet_isFundamentalDomain_subset (G := ↥(Γp F))
    hS hSslab ((hEm.inter (measurableSet_slab e₁ e₂))) hEcov
  refine ⟨d₁, d₂, (N ×ˢ T).image tOf, 𝓕, hd₁, h𝓕m,
    fun g hg => (h𝓕E hg).2, h𝓕, fun g hg => ?_⟩
  obtain ⟨p, hp, hgp⟩ := Set.mem_iUnion₂.mp (h𝓕E hg).1
  obtain ⟨s, hs, rfl⟩ := hgp
  exact Set.mem_iUnion₂.mpr ⟨tOf p, Finset.mem_image_of_mem tOf hp, s, hs, rfl⟩

set_option linter.unusedVariables false in
/-- A measurable fundamental domain inside a union of integral-windowed Siegel
translates. -/
theorem exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ (c' u' : ℝ) (tset : Finset (AdelicGL2 (𝓞 K) K)) (𝓕 : Set (AdelicGL2 (𝓞 K) K)),
      0 < c' ∧ MeasurableSet 𝓕 ∧
      𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      𝓕 ⊆ ⋃ t ∈ tset, (· * t) '' integralWindowedSiegelSet K c' u' :=
  main_integral c u d₁ d₂ T hc hd hcov e₁ e₂ he₁

set_option linter.unusedVariables false in
/-- A measurable fundamental domain inside a union of centre-cut Siegel
translates. -/
theorem exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ (d₁' d₂' : ℝ) (tset : Finset (AdelicGL2 (𝓞 K) K)) (𝓕 : Set (AdelicGL2 (𝓞 K) K)),
      0 < d₁' ∧ MeasurableSet 𝓕 ∧
      𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      𝓕 ⊆ ⋃ t ∈ tset, (· * t) '' centreCutSiegelSet K c u d₁' d₂' :=
  main_centre c u d₁ d₂ T hd₁ hd hcov e₁ e₂ he₁

end AutomorphicForm
