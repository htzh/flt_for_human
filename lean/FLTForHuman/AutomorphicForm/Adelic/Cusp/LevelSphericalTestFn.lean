/-
  The flat and level-spherical test functions on the cuspidal spectrum.

  Two rows, one theme — the test functions the level-spherical approximate identity is built from:

  * `isFactorizableTestFn_flat`: `flat F σ f = f * ‖det‖^{-σ}` (conjugated, inverted, modulus-twisted)
    is factorizable when `f` is.  Both halves are the modulus twist applied to a conjugated test
    factor, which is exactly what `isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` and
    `isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` (SET-AF55's B4,
    `Cusp/ConstituentModulus.lean`) provide, plus the dictionary `adelicArchGLIncl_glArch_mul_finEmbed_glFin`
    that splits an adelic element into its archimedean and finite halves.
  * `exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType`: for a level-spherical `f` of type
    `tys`, a lift `T_c` that commutes with `rightConv · f` commutes with the **Hecke coset sum**
    `heckeCosetSum` at `g ∈ K_f` up to the pin's `U N`-coset bookkeeping — the row the level-spherical
    approximate identity spends to move a Hecke operator past a lift.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isFactorizableTestFn_flat.lean` (63 lines) and
  `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType.lean`
  (295 lines), with the statements from the wrappers of the same names. The pin's label namespace
  `FlatFactProof` is rectified to the word namespace `FlatFactorizability`; its one helper stays
  `private`.

  Assumes from earlier modules: `Cusp/ConstituentModulus.lean` (the finite modulus twist, SET-AF55),
  `Adelic/IsotypicArchType.lean` (the archimedean twin), `Adelic/RightConvCosetSum.lean`
  (`cosetSum_rightConv_of_isLevelSphericalOfType`), `Cusp/SpectrumOrthogonality.lean` (SET-AF55's B5),
  `Cusp/Spectrum{Lift,Translation,ConvAction,Pairing}.lean` and `Adelic/RightConvPreservation.lean`.

  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isFactorizableTestFn_flat.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isFactorizableTestFn_flat.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ConstituentModulus
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrierAPI
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumLift
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumOrthogonality
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumPairing
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumTranslation
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumConvAction
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.IsotypicArchType
import FLTForHuman.AutomorphicForm.Adelic.RightConvCosetSum
import FLTForHuman.AutomorphicForm.Adelic.RightConvPreservation
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightChar
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace FlatFactorizability

variable {F : Type} [Field F] [NumberField F]

private theorem adelicArchGLIncl_glArch_mul_finEmbed_glFin (y : AdelicGL2 (𝓞 F) F) :
    adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y) = y := by
  apply Units.ext
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · show ((glArch (𝓞 F) F (adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y)) :
        GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
        = ((glArch (𝓞 F) F y : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix _ _ _)
    rw [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  · show ((glFin (𝓞 F) F (adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
        = ((glFin (𝓞 F) F y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _)
    rw [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]

end FlatFactorizability

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.isFactorizableTestFn_flat
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    IsFactorizableTestFn F (flat F σ f) := by
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
  refine ⟨fun y => conj (fa y⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ),
    fun b => conj (ff b⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F b)) ^ (-σ) : ℝ) : ℂ),
    AutomorphicForm.CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow F σ fa hfa,
    AutomorphicForm.CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow F σ ff hff, fun g => ?_⟩
  show conj (f g⁻¹) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-σ) : ℝ) : ℂ) = _

  have hdet : Matrix.GeneralLinearGroup.det g
      = Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F g))
        * Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F g)) := by
    rw [← map_mul, FlatFactorizability.adelicArchGLIncl_glArch_mul_finEmbed_glFin]
  have hN : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-σ)
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F g))) ^ (-σ)
        * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F g))) ^ (-σ) := by
    rw [hdet, NumberField.TateGlobal.ideleNorm_mul,
      Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos _).le (NumberField.TateGlobal.ideleNorm_pos _).le]
  rw [hfeq, map_inv, map_inv, map_mul, hN, Complex.ofReal_mul]
  ring

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hσ : HasModulus F ξ σ) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N) f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F) (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (h1 : ∀ i, ∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, ∃ u'' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, reps i = u' * g * u'')
    (h2 : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, ∃ u'' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, x = u' * g * u'') → ∃ i, ∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, x = reps i * u')
    (h3 : ∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N → i = j) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ), S.comp Tc = Tc.comp S ∧
      ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
        (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N →
        ∃ h : (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) ∈ cuspMemberSubmodule F Φ₀ ξ,
          S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i), h⟩ := by
  classical
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  have : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier
    exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

  have hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ (fdPins F Φ₀).U N, f (u' * x) = f x := by
    obtain ⟨fa, -, -, -, hfac⟩ := hsph
    intro x u' hu'
    have harch : AdelicLevel.glArch (𝓞 F) F u' = 1 := (Subgroup.mem_inf.mp hu').2
    have himg : (AdelicLevel.glFin (𝓞 F) F u' * AdelicLevel.glFin (𝓞 F) F x ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) ↔
        (AdelicLevel.glFin (𝓞 F) F x ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) := by
      constructor
      · rintro ⟨k, hk, hkz⟩
        refine ⟨u'⁻¹ * k, Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hk, ?_⟩
        rw [map_mul, map_inv, hkz, inv_mul_cancel_left]
      · rintro ⟨k, hk, hkx⟩
        exact ⟨u' * k, Subgroup.mul_mem _ hu' hk, by rw [map_mul, hkx]⟩
    rw [hfac, hfac x, map_mul, harch, one_mul, map_mul]
    simp only [Set.indicator_apply, himg]
  have hfU' : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ (fdPins F Φ₀).U N, f (x * u') = f x := by
    obtain ⟨fa, -, -, -, hfac⟩ := hsph
    intro x u' hu'
    have harch : AdelicLevel.glArch (𝓞 F) F u' = 1 := (Subgroup.mem_inf.mp hu').2
    have himg : (AdelicLevel.glFin (𝓞 F) F x * AdelicLevel.glFin (𝓞 F) F u' ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) ↔
        (AdelicLevel.glFin (𝓞 F) F x ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) := by
      constructor
      · rintro ⟨k, hk, hkz⟩
        refine ⟨k * u'⁻¹, Subgroup.mul_mem _ hk (Subgroup.inv_mem _ hu'), ?_⟩
        rw [map_mul, map_inv, hkz, mul_inv_cancel_right]
      · rintro ⟨k, hk, hkx⟩
        exact ⟨k * u', Subgroup.mul_mem _ hk hu', by rw [map_mul, hkx]⟩
    rw [hfac, hfac x, map_mul, harch, mul_one, map_mul]
    simp only [Set.indicator_apply, himg]

  obtain ⟨Tf, -, hTf, -, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfcs
  have memf : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ := by
    intro φ
    have hcont : (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨φ.2.1.1.1, φ.2.2⟩
    have hmaps := hTf.mapsTo φ hcont
    refine ⟨⟨⟨hmaps.1, ?_⟩, AutomorphicForm.isKfSmooth_rightConv F φ f hf⟩, hmaps.2⟩
    exact AutomorphicForm.isCuspidalFn_rightConv F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) φ φ.2.2 φ.2.1.1.2 f hf
  have hdense : Dense (Set.range (toCuspSubcarrier F hΦ₀ σ ξ)) := by
    rw [Subtype.dense_iff]
    intro v hv
    have hv' : v ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hv
    refine closure_mono ?_ hv'
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩, ⟨_, rfl⟩, rfl⟩
  have hTc_eq : (cuspSubcarrier F hΦ₀ σ ξ).subtypeL.comp Tc = Tf.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL := by
    refine ContinuousLinearMap.ext_on (hdense.mono Submodule.subset_span) ?_
    rintro _ ⟨φ, rfl⟩
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.subtypeL_apply,
      hcomm φ (memf φ), toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact (hTf.comm φ ⟨φ.2.1.1.1, φ.2.2⟩).symm
  have hTc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), ((Tc v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) = Tf v := fun v =>
    congrArg (fun A : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] Carrier F Φ₀ σ => A v) hTc_eq

  have hLcH : cuspLevelSubcarrier F hΦ₀ σ ξ N ≤ cuspSubcarrier F hΦ₀ σ ξ := by
    unfold cuspLevelSubcarrier cuspSubcarrier
    exact Submodule.topologicalClosure_mono (Submodule.map_mono (Submodule.comap_mono inf_le_left))
  set LH : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) := Submodule.comap (cuspSubcarrier F hΦ₀ σ ξ).subtype (cuspLevelSubcarrier F hΦ₀ σ ξ N) with hLH
  have hLHclosed : IsClosed (LH : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
    have h1 : IsClosed ((cuspLevelSubcarrier F hΦ₀ σ ξ N : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
      unfold cuspLevelSubcarrier
      exact Submodule.isClosed_topologicalClosure _
    exact h1.preimage continuous_subtype_val
  have : CompleteSpace ↥LH := hLHclosed.completeSpace_coe
  set PN : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := LH.starProjection with hPN

  have hrange : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Tc v ∈ LH := by
    intro v
    show ((Tc v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ cuspLevelSubcarrier F hΦ₀ σ ξ N
    rw [hTc v]
    exact AutomorphicForm.CuspidalSpectrum.map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ N f hf hfU
      Tf hTf (Submodule.mem_map_of_mem v.2)
  have hker : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), v ∈ LHᗮ → Tc v = 0 := by
    intro v hv
    apply Subtype.ext
    rw [hTc v]
    refine AutomorphicForm.CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant
      F hΦ₀ σ ξ N f hf hfU' Tf hTf v v.2 ?_
    rw [Submodule.mem_orthogonal]
    intro y hy
    exact (Submodule.mem_orthogonal _ _).mp hv ⟨y, hLcH hy⟩ hy

  have hL := fun i => AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ (reps i)
  choose Tr Tr' hTr hTr' hadj hnorm using hL
  have memr : ∀ (i : Fin n) (φ : AdelicGL2 (𝓞 F) F → ℂ), φ ∈ cuspMemberSubmodule F Φ₀ ξ →
      rightTranslate F (reps i) φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun i φ hφ =>
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (reps i) φ hφ
  have hinv : ∀ (i : Fin n) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), Tr i (v : Carrier F Φ₀ σ) ∈ cuspSubcarrier F hΦ₀ σ ξ := by
    intro i v
    have hM : ∀ x ∈ ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)),
        Tr i x ∈ ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
      rintro _ ⟨ψ, hψ, rfl⟩
      refine ⟨⟨rightTranslate F (reps i) ψ, (memr i ψ hψ).1.1.1⟩, memr i ψ hψ, ?_⟩
      exact ((hTr i).comm ψ ⟨ψ.2, hψ.2⟩).symm
    have hv : (v : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact v.2
    have h1 := image_closure_subset_closure_image (Tr i).continuous ⟨(v : Carrier F Φ₀ σ), hv, rfl⟩
    have h2 := closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hM x hx) h1
    rw [← Submodule.topologicalClosure_coe] at h2
    exact h2
  let Sraw : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    ((∑ i, Tr i).comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) fun v => by
      simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hinv i v
  have Sraw_apply : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), (Sraw v : Carrier F Φ₀ σ) = ∑ i, Tr i v := by
    intro v
    show ((∑ i, Tr i).comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL) v = _
    simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply]
    rfl

  have memsum : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) ∈ cuspMemberSubmodule F Φ₀ ξ := by
    intro φ
    have hfeq : (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) =
        ∑ i, rightTranslate F (reps i) (φ : AdelicGL2 (𝓞 F) F → ℂ) := by
      funext x; simp only [Finset.sum_apply, rightTranslate_apply]
    rw [hfeq]
    exact Submodule.sum_mem _ fun i _ => memr i φ φ.2
  have Sraw_lift : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      Sraw (toCuspSubcarrier F hΦ₀ σ ξ φ) =
        toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i), memsum φ⟩ := by
    intro φ
    apply Subtype.ext
    rw [Sraw_apply, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    have hstep : ∀ i, Tr i (toCarrier F hΦ₀ σ ξ ⟨φ, φ.2.1.1.1⟩) =
        toCarrier F hΦ₀ σ ξ ⟨rightTranslate F (reps i) φ, (memr i φ φ.2).1.1.1⟩ :=
      fun i => (hTr i).comm φ ⟨φ.2.1.1.1, φ.2.2⟩
    simp only [hstep]
    rw [← map_sum]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext x
    simp only [Finset.sum_apply, rightTranslate_apply]

  have key : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)),
      (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N →
      Sraw (Tc (toCuspSubcarrier F hΦ₀ σ ξ φ)) = Tc (Sraw (toCuspSubcarrier F hΦ₀ σ ξ φ)) := by
    intro φ hφU
    rw [hcomm φ (memf φ), Sraw_lift, Sraw_lift, hcomm _ (memf _)]
    congr 1
    apply Subtype.ext
    exact AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N hN
      (tys : AutomorphicForm.ArchTypeFamily F) f hsph g hg n reps h1 h2 h3 φ φ.2.2 hφU
  have hcommL : ∀ w : ↥LH, Sraw (Tc (w : ↥(cuspSubcarrier F hΦ₀ σ ξ))) = Tc (Sraw (w : ↥(cuspSubcarrier F hΦ₀ σ ξ))) := by

    let DL : Set ↥LH := {w | ∃ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)),
      (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ∧ (w : ↥(cuspSubcarrier F hΦ₀ σ ξ)) = toCuspSubcarrier F hΦ₀ σ ξ φ}
    have hDL : Dense DL := by
      rw [Subtype.dense_iff]
      intro z hz
      rw [closure_subtype]
      have hz' : ((z : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
          (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
            (cuspMemberSubmodule F Φ₀ ξ ⊓ levelInvariantSubmodule F (fdPins F Φ₀) N))) : Set (Carrier F Φ₀ σ)) := by
        rw [← Submodule.topologicalClosure_coe]
        exact hz
      refine closure_mono ?_ hz'
      rintro _ ⟨ψ, hψ, rfl⟩
      have hψm : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := (Submodule.mem_inf.mp hψ).1
      have hψU : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N := (Submodule.mem_inf.mp hψ).2
      have hmemLH : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ LH := by
        show ((toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ cuspLevelSubcarrier F hΦ₀ σ ξ N
        rw [toCuspSubcarrier_apply_coe]
        unfold cuspLevelSubcarrier
        exact Submodule.le_topologicalClosure _ ⟨ψ, hψ, rfl⟩
      exact ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩, ⟨⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩, hmemLH⟩, ⟨⟨ψ, hψm⟩, hψU, rfl⟩, rfl⟩, rfl⟩
    have hext : ((Sraw.comp Tc).comp LH.subtypeL) = ((Tc.comp Sraw).comp LH.subtypeL) := by
      refine ContinuousLinearMap.ext_on (hDL.mono Submodule.subset_span) ?_
      rintro w ⟨φ, hφU, hw⟩
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      rw [hw]
      exact key φ hφU
    intro w
    have := congrArg (fun A : ↥LH →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) => A w) hext
    simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using this

  refine ⟨Sraw.comp PN, ?_, ?_⟩
  · ext1 v
    have hPT : PN (Tc v) = Tc v := Submodule.starProjection_eq_self_iff.mpr (hrange v)
    have hdec : Tc v = Tc (PN v) := by
      have h0 : Tc (v - PN v) = 0 := hker _ (Submodule.sub_starProjection_mem_orthogonal v)
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have hPmem : PN v ∈ LH := by
      rw [hPN]
      exact (LH.orthogonalProjectionOnto v).2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hPT, hdec]
    exact hcommL ⟨PN v, hPmem⟩
  · intro φ hφU
    refine ⟨memsum φ, ?_⟩
    have hmemLH : toCuspSubcarrier F hΦ₀ σ ξ φ ∈ LH := by
      show ((toCuspSubcarrier F hΦ₀ σ ξ φ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ cuspLevelSubcarrier F hΦ₀ σ ξ N
      rw [toCuspSubcarrier_apply_coe]
      unfold cuspLevelSubcarrier
      refine Submodule.le_topologicalClosure _ ⟨⟨φ, φ.2.1.1.1⟩, ?_, rfl⟩
      exact Submodule.mem_inf.mpr ⟨φ.2, hφU⟩
    rw [ContinuousLinearMap.comp_apply, Submodule.starProjection_eq_self_iff.mpr hmemLH]
    exact Sraw_lift φ
