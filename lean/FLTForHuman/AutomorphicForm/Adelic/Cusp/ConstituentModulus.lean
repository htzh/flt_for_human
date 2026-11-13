/-
  A cusp constituent has a modulus, and its test factor survives a conjugation twist.

  `exists_hasModulus_of_isCuspConstituent`: the central character of an irreducible
  cuspidal subrepresentation (an `IsCuspConstituent`) is a modulus character.  Its carrier
  meets the `K`-finite one and the `K`-finite carrier sits in the continuous-member carrier,
  so a non-zero member of the constituent is a continuous automorphic function with a
  character, and `exists_hasModulus_of_isAutomorphicFnAt_of_continuous` gives the exponent.

  `isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow`: `b ↦ conj (ff b⁻¹) * ‖det b‖^{-σ}` is again a
  finite test factor.  Both factors are locally constant — `ff` composed with inversion and
  conjugation, and `‖det ·‖^{-σ}`, which is locally constant because `‖det k‖ = 1` on
  `finiteIntegralGL2` — and the support is `(tsupport ff)⁻¹`, compact.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent.lean`
  (37 lines) and
  `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow.lean`
  (59 lines), with the statements from the wrappers of the same names.

  Assumes from earlier modules: `Cusp/SpectrumCarrierAPI.lean` (the modulus row for a continuous
  automorphic function), `Cusp/SpectrumCarrier.lean` (the carriers), `IsotypicCuspSpace.lean`
  (the constituent datum), `Adelic/IdeleNormDetGlue.lean` (the determinant norm as a product of
  archimedean norms) and `NumberTheory/AdelicDock/LocalEmbedding.lean` (`finEmbed`).

  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrierAPI
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDetGlue
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V) :
    ∃ σ : ℝ, HasModulus F ξ σ := by
  classical
  obtain ⟨φ, hφV, hφ0⟩ := (Submodule.ne_bot_iff V).mp hV.2.1
  have hle : cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
      (adelicBox F)) ξ ≤ contMemberSubmodule F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ξ := by
    refine Submodule.span_le.mpr ?_
    rintro ψ ⟨hsat, hcont, -⟩
    have h1 : rightTranslate F 1 ψ = ψ := funext fun y => by rw [rightTranslate_apply, mul_one]
    have h := hsat 1
    rw [h1] at h
    exact ⟨h.1.1, hcont⟩
  have hφ := hle (hV.1.le hφV)
  exact AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous F
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ξ φ hφ.1 hφ.2 hφ0

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
open scoped ComplexConjugate

theorem AutomorphicForm.CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    IsFinTestFactor F (fun b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => conj (ff b⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F b)) ^ (-σ) : ℝ) : ℂ)) := by
  classical
  obtain ⟨hlc, hK⟩ := hff

  have hone : ∀ k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F), k ∈ finiteIntegralGL2 (𝓞 F) F →
      NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F k)) = 1 := by
    intro k hk
    rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult
      (AdelicDock.finEmbed (𝓞 F) F k) (by rw [AdelicDock.glFin_finEmbed]; exact hk)]
    refine Finset.prod_eq_one fun w _ => ?_
    have hw : NumberField.AdelicVolume.archDetNorm w (AdelicDock.finEmbed (𝓞 F) F k) = 1 := by
      unfold NumberField.AdelicVolume.archDetNorm
      rw [AdelicDock.glArch_finEmbed, map_one, Units.val_one, Matrix.det_one, norm_one]
    rw [hw, one_pow]

  have hNlc : IsLocallyConstant fun b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F b)) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun b => ?_
    have hopen : IsOpen ((fun b' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => b⁻¹ * b') ⁻¹'
        (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))) :=
      (isOpen_finiteLevelZero (𝓞 F) F (N := ⊤) (by simp)).preimage
        (continuous_const.mul continuous_id)
    have hmem : b ∈ (fun b' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => b⁻¹ * b') ⁻¹'
        (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
      show b⁻¹ * b ∈ finiteIntegralGL2 (𝓞 F) F
      rw [inv_mul_cancel]; exact one_mem _
    filter_upwards [hopen.mem_nhds hmem] with b' hb'
    have hb'' : b' = b * (b⁻¹ * b') := by group
    conv_lhs => rw [hb'']
    rw [map_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul, hone _ hb', mul_one]
  refine ⟨?_, ?_⟩
  · refine IsLocallyConstant.mul ?_ ?_
    · exact (hlc.comp_continuous continuous_inv).comp (fun z : ℂ => conj z)
    · exact hNlc.comp (fun r : ℝ => ((r ^ (-σ) : ℝ) : ℂ))
  · refine HasCompactSupport.intro (K := (tsupport ff)⁻¹) hK.inv ?_
    intro b hb
    have hb' : b⁻¹ ∉ tsupport ff := fun h => hb (by simpa using Set.inv_mem_inv.mpr h)
    show conj (ff b⁻¹) * _ = 0
    rw [image_eq_zero_of_notMem_tsupport hb', map_zero, zero_mul]
