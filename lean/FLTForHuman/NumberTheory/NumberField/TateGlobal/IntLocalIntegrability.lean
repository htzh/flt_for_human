/-
  Local integrability of the archimedean densities and the archimedean decay
  lemmas: `integrable_comp_val_comap_mulMeasure_iff` and its multiplicative-Haar
  specialization `integrable_mulHaarCompletion_comp_val_iff`, the norm of the
  completion character (`distribHaarChar_completion_eq_pow_mult`), the
  coordinate-wise bound `norm_coord_le_norm_ringEquiv`, the Schwartz decay
  `schwartz_mul_one_add_norm_pow_le`/`schwartz_le_prod_one_add_norm` and the
  integrability `integrable_one_add_norm_mul_distribHaarChar_rpow`.  The one
  B-only declaration of B's early `NumberField.TateGlobal` block, `unitAtHom_val`,
  is re-declared here for the later modules that need it.

  Transcribed from the pin's `Fold_TateReference` (`CompVal`), `Fold_FujisakiC3b`
  (`M4aLocalCFT.FujisakiC3`) and `Fold_ArchDecay` (`M4aLocalCFT.ArchDecay`)
  sections, declared lines 2879-3375 of file B, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_integrable_zetaIntegrand.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped, as are the file-scoped
  `set_option maxHeartbeats 3200000` / `maxSynthPendingDepth 3` (B 3113/3115) and
  the `set_option synthInstance.maxHeartbeats 800000 in` wrappers of the
  `Fold_TateReference` block (B 2896/2899/2903/3041); the port's global instances
  elaborate all of them at the low edit cap.  `M4aLocalCFT.` is renamed to
  `NumberField.TateGlobal.`, the pin's `omit [NumberField F] in` prefixes are kept,
  and the pin's deprecated `if_pos`/`if_neg` are spelled `ite_eq_left`/`ite_eq_right`
  (proof-only).  `integrable_mulHaarCompletion_comp_val_iff` keeps the pin's
  (unused) `[NumberField F]` section binder, so its declaration carries a
  per-declaration `linter.unusedSectionVars` suppression.  No file-wide option
  beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ReferenceMeasure

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion NumberField.InfiniteAdeleRing
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal Classical

section Fold_TateReference

open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

-- pin: unitAtHom_val (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:339)
theorem unitAtHom_val (x : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    (unitAtHom w x : w.adicCompletion F) = ((x : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w :=
  rfl

section CompVal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

variable [MeasurableSpace Kˣ]

-- pin: integrable_comp_val_comap_mulMeasure_iff (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:2879)
theorem integrable_comp_val_comap_mulMeasure_iff (hval : MeasurableEmbedding (Units.val : Kˣ → K))
    (μ : Measure K) (φ : K → ℂ) :
    Integrable (fun t : Kˣ => φ (t : K)) (Measure.comap Units.val (mulMeasure μ)) ↔ Integrable φ (mulMeasure μ) := by
  show Integrable (φ ∘ Units.val) _ ↔ _
  rw [← hval.integrable_map_iff, hval.map_comap, range_units_val, mulMeasure_restrict_compl_zero]

end CompVal

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]

-- The pin's binder shape keeps the (unused) `[NumberField F]` section variable, which
-- `linter.unusedSectionVars` flags; suppress it here rather than change the statement.
set_option linter.unusedSectionVars false in
-- pin: integrable_mulHaarCompletion_comp_val_iff (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:2999)
theorem integrable_mulHaarCompletion_comp_val_iff (w : InfinitePlace F) (μ : Measure w.Completion)
    (φ : w.Completion → ℂ) :
    Integrable (fun t : (w.Completion)ˣ => φ (t : w.Completion)) (ArchMulHaarCompletion.mulHaarCompletion w μ)
      ↔ Integrable φ (mulMeasure μ) :=
  integrable_comp_val_comap_mulMeasure_iff (ArchMulHaarCompletion.measurableEmbedding_val_completion w) μ φ

end NumberField.TateGlobal

end

end Fold_TateReference

section Fold_FujisakiC3b

open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal

noncomputable section

namespace NumberField
namespace TateGlobal
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
-- pin: distribHaarChar_completion_eq_pow_mult (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:3129)
theorem distribHaarChar_completion_eq_pow_mult (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion] (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ w.mult := by
  rcases isReal_or_isComplex w with hv | hv
  · rw [ArchMulHaarCompletion.distribHaarChar_completion_of_isReal w hv, mult_isReal ⟨w, hv⟩]
  · rw [ArchMulHaarCompletion.distribHaarChar_completion_of_isComplex w hv, mult_isComplex ⟨w, hv⟩]

end FujisakiC3

end NumberField.TateGlobal

end

end Fold_FujisakiC3b

section Fold_ArchDecay

open NumberField.TateGlobal LanglandsTunnell.TateLocal Finset

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
namespace TateGlobal
namespace ArchDecay

variable {F : Type} [Field F] [NumberField F]

-- pin: norm_coord_le_norm_ringEquiv (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:3163)
theorem norm_coord_le_norm_ringEquiv (x : InfiniteAdeleRing F) (w : InfinitePlace F) :
    ‖x w‖ ≤ ‖ringEquiv_mixedSpace F x‖ := by
  rcases w.isReal_or_isComplex with hw | hw
  · have hiso : ‖Completion.extensionEmbeddingOfIsReal hw (x w)‖ = ‖x w‖ :=
      (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _
    calc ‖x w‖ = ‖(ringEquiv_mixedSpace F x).1 ⟨w, hw⟩‖ := hiso.symm
      _ ≤ ‖(ringEquiv_mixedSpace F x).1‖ := norm_le_pi_norm _ _
      _ ≤ ‖ringEquiv_mixedSpace F x‖ := norm_fst_le _
  · have hiso : ‖Completion.extensionEmbedding w (x w)‖ = ‖x w‖ :=
      (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
    calc ‖x w‖ = ‖(ringEquiv_mixedSpace F x).2 ⟨w, hw⟩‖ := hiso.symm
      _ ≤ ‖(ringEquiv_mixedSpace F x).2‖ := norm_le_pi_norm _ _
      _ ≤ ‖ringEquiv_mixedSpace F x‖ := norm_snd_le _

-- pin: schwartz_mul_one_add_norm_pow_le (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:3177)
theorem schwartz_mul_one_add_norm_pow_le (g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)
    (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ y : mixedEmbedding.mixedSpace F,
      ‖g y‖ * (1 + ‖y‖) ^ k ≤ C := by
  have hbound : ∀ j : ℕ, ∃ Cj : ℝ, 0 < Cj ∧ ∀ y, ‖g y‖ * ‖y‖ ^ j ≤ Cj := by
    intro j
    obtain ⟨Cj, hCj, hj⟩ := g.decay j 0
    refine ⟨Cj, hCj, fun y => ?_⟩
    have h := hj y
    rw [norm_iteratedFDeriv_zero] at h
    calc ‖g y‖ * ‖y‖ ^ j = ‖y‖ ^ j * ‖g y‖ := mul_comm _ _
      _ ≤ Cj := h
  choose Cj hCjpos hCjle using hbound
  refine ⟨∑ j ∈ range (k + 1), k.choose j * Cj j, ?_, fun y => ?_⟩
  · refine Finset.sum_pos (fun j hj => ?_) ⟨0, mem_range.mpr (Nat.succ_pos k)⟩
    have h1 : (0 : ℝ) < k.choose j := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp (mem_range.mp hj))
    exact mul_pos h1 (hCjpos j)
  · have hexp : (1 + ‖y‖) ^ k = ∑ j ∈ range (k + 1), ‖y‖ ^ j * k.choose j := by
      rw [add_comm]
      simpa using add_pow ‖y‖ 1 k
    rw [hexp, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    calc ‖g y‖ * (‖y‖ ^ j * k.choose j) = k.choose j * (‖g y‖ * ‖y‖ ^ j) := by ring
      _ ≤ k.choose j * Cj j :=
          mul_le_mul_of_nonneg_left (hCjle j y) (Nat.cast_nonneg _)

-- pin: schwartz_le_prod_one_add_norm (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:3203)
theorem schwartz_le_prod_one_add_norm (g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ x : InfiniteAdeleRing F,
      ‖g (ringEquiv_mixedSpace F x)‖ * ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N ≤ C := by
  obtain ⟨C, hC, hle⟩ :=
    schwartz_mul_one_add_norm_pow_le (F := F) g (N * Fintype.card (InfinitePlace F))
  refine ⟨C, hC, fun x => ?_⟩
  set y := ringEquiv_mixedSpace F x with hy
  have hprod : ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N
      ≤ (1 + ‖y‖) ^ (N * Fintype.card (InfinitePlace F)) := by
    have hstep : ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N
        ≤ ∏ _w : InfinitePlace F, (1 + ‖y‖) ^ N := by
      refine Finset.prod_le_prod₀ (fun w _ => by positivity) (fun w _ => ?_)
      have h1 : (1 : ℝ) + ‖x w‖ ≤ 1 + ‖y‖ := by
        have h2 := norm_coord_le_norm_ringEquiv x w
        rw [← hy] at h2
        linarith
      exact pow_le_pow_left₀ (by positivity) h1 N
    calc ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N
        ≤ ∏ _w : InfinitePlace F, (1 + ‖y‖) ^ N := hstep
      _ = ((1 + ‖y‖) ^ N) ^ Fintype.card (InfinitePlace F) := by
          rw [Finset.prod_const, Finset.card_univ]
      _ = (1 + ‖y‖) ^ (N * Fintype.card (InfinitePlace F)) := by rw [← pow_mul]
  calc ‖g y‖ * ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N
      ≤ ‖g y‖ * (1 + ‖y‖) ^ (N * Fintype.card (InfinitePlace F)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ C := hle y

variable [∀ w : InfinitePlace F, MeasurableSpace w.Completion]

variable [∀ w : InfinitePlace F, BorelSpace w.Completion]

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ]

variable [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]

variable (w : InfinitePlace F)

-- The pin's proof introduces the `IsAddHaarMeasure` instance of a pushed-forward
-- measure with `haveI`; the goal is a proposition, which `linter.style.haveILetI` flags.
-- The pin keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`, which
-- `linter.overlappingInstances` sees as overlapping.
set_option linter.style.haveILetI false in
set_option linter.overlappingInstances false in
omit [NumberField F] in
-- pin: integrable_one_add_norm_mul_distribHaarChar_rpow (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:3241)
theorem integrable_one_add_norm_mul_distribHaarChar_rpow
    (μ : Measure w.Completion) [μ.IsAddHaarMeasure] [μ.Regular] {σ : ℝ} (hσ : 1 ≤ σ) {N : ℝ}
    (hN : (w.mult : ℝ) * σ < N) :
    Integrable (fun t : (w.Completion)ˣ =>
      (1 + ‖(t : w.Completion)‖) ^ (-N) * ((distribHaarChar w.Completion t : ℝ≥0) : ℝ) ^ σ)
      (ArchMulHaarCompletion.mulHaarCompletion w μ) := by
  set φ : w.Completion → ℂ := fun x =>
    (((1 + ‖x‖) ^ (-N) * ‖x‖ ^ ((w.mult : ℝ) * σ) : ℝ) : ℂ) with hφ
  have hΔ : ∀ t : (w.Completion)ˣ,
      ((distribHaarChar w.Completion t : ℝ≥0) : ℝ) ^ σ
        = ‖(t : w.Completion)‖ ^ ((w.mult : ℝ) * σ) := by
    intro t
    rw [FujisakiC3.distribHaarChar_completion_eq_pow_mult]
    push_cast
    rw [← Real.rpow_natCast ‖(t : w.Completion)‖ w.mult, ← Real.rpow_mul (norm_nonneg _)]
  have hmult : w.mult ≠ 0 := by
    rcases w.isReal_or_isComplex with hw | hw
    · rw [InfinitePlace.mult, ite_eq_left hw]; omega
    · rw [InfinitePlace.mult, ite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)]; omega
  have hΔall : ∀ t : (w.Completion)ˣ,
      distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ w.mult :=
    FujisakiC3.distribHaarChar_completion_eq_pow_mult w
  have hmulM : Integrable φ (mulMeasure μ) := by
    rw [ArchMulHaarCompletion.mulMeasure_completion_eq w w.mult hmult hΔall]
    have hdens : Measurable fun x : w.Completion => ((‖x‖₊ ^ w.mult : ℝ≥0∞))⁻¹ :=
      ((measurable_nnnorm.pow_const w.mult).coe_nnreal_ennreal).inv
    have hfin : ∀ᵐ x ∂(μ.restrict {(0 : w.Completion)}ᶜ), ((‖x‖₊ ^ w.mult : ℝ≥0∞))⁻¹ < ⊤ := by
      refine (ae_restrict_iff' (measurableSet_singleton (0 : w.Completion)).compl).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hx0 : x ≠ 0 := hx
      have h1 : (0 : ℝ≥0) < ‖x‖₊ ^ w.mult := pow_pos (nnnorm_pos.mpr hx0) _
      simp only [ENNReal.inv_lt_top]
      exact_mod_cast ENNReal.coe_pos.mpr h1
    rw [integrable_withDensity_iff_integrable_smul' hdens hfin]
    have hβ : (0 : ℝ) ≤ (σ - 1) * (w.mult : ℝ) := by
      have h0 : (0 : ℝ) ≤ σ - 1 := by linarith
      positivity
    have hbr : Integrable
        (fun x : w.Completion => (1 + ‖x‖) ^ (-(N - (σ - 1) * (w.mult : ℝ)))) μ := by
      rcases w.isReal_or_isComplex with hw | hw
      · set iso := Completion.isometryEquivRealOfIsReal hw with hiso
        set me : w.Completion ≃ᵐ ℝ := iso.toHomeomorph.toMeasurableEquiv with hme
        haveI hHaar : (μ.map me).IsAddHaarMeasure :=
          AddEquiv.isAddHaarMeasure_map μ
            (Completion.ringEquivRealOfIsReal hw).toAddEquiv
            iso.continuous iso.symm.continuous
        have hmult1 : w.mult = 1 := by rw [InfinitePlace.mult, ite_eq_left hw]
        have hR : Integrable
            (fun y : ℝ => (1 + ‖y‖) ^ (-(N - (σ - 1) * (w.mult : ℝ)))) (μ.map me) := by
          refine integrable_one_add_norm ?_
          have hfr : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
          simp only [hfr, hmult1] at hN ⊢
          push_cast at hN ⊢
          linarith
        have h2 := (MeasureTheory.integrable_map_equiv me
          (fun y : ℝ => (1 + ‖y‖) ^ (-(N - (σ - 1) * (w.mult : ℝ))))).mp hR
        refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
        have h0 : iso (0 : w.Completion) = 0 :=
          map_zero (Completion.ringEquivRealOfIsReal hw)
        have hnorm : ‖me x‖ = ‖x‖ := iso.isometry.norm_map_of_map_zero h0 x
        simp only [Function.comp_apply, hnorm]
      · set iso := Completion.isometryEquivComplexOfIsComplex hw with hiso
        set me : w.Completion ≃ᵐ ℂ := iso.toHomeomorph.toMeasurableEquiv with hme
        haveI hHaar : (μ.map me).IsAddHaarMeasure :=
          AddEquiv.isAddHaarMeasure_map μ
            (Completion.ringEquivComplexOfIsComplex hw).toAddEquiv
            iso.continuous iso.symm.continuous
        have hmult2 : w.mult = 2 := by
          rw [InfinitePlace.mult, ite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)]
        have hC : Integrable
            (fun y : ℂ => (1 + ‖y‖) ^ (-(N - (σ - 1) * (w.mult : ℝ)))) (μ.map me) := by
          refine integrable_one_add_norm ?_
          simp only [Complex.finrank_real_complex, hmult2] at hN ⊢
          push_cast at hN ⊢
          linarith
        have h2 := (MeasureTheory.integrable_map_equiv me
          (fun y : ℂ => (1 + ‖y‖) ^ (-(N - (σ - 1) * (w.mult : ℝ))))).mp hC
        refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
        have h0 : iso (0 : w.Completion) = 0 :=
          map_zero (Completion.ringEquivComplexOfIsComplex hw)
        have hnorm : ‖me x‖ = ‖x‖ := iso.isometry.norm_map_of_map_zero h0 x
        simp only [Function.comp_apply, hnorm]
    refine Integrable.mono' (hbr.restrict (s := {(0 : w.Completion)}ᶜ)) ?_ ?_
    ·
      refine (Measurable.aestronglyMeasurable ?_)
      have hm1 : Measurable fun x : w.Completion => (((‖x‖₊ ^ w.mult : ℝ≥0∞))⁻¹).toReal :=
        hdens.ennreal_toReal
      have hm2 : Measurable φ := by
        rw [hφ]
        fun_prop
      exact (hm1.smul hm2)
    ·
      refine Filter.Eventually.of_forall fun x => ?_
      rcases eq_or_ne x 0 with rfl | hx0
      · simp only [hφ, nnnorm_zero, ENNReal.coe_zero, zero_pow hmult, ENNReal.inv_zero,
          ENNReal.toReal_top, zero_smul, norm_zero]
        positivity
      · have hnx : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
        have htoReal : (((‖x‖₊ ^ w.mult : ℝ≥0∞))⁻¹).toReal = (‖x‖ ^ (w.mult : ℕ))⁻¹ := by
          simp [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
        rw [norm_smul, htoReal, hφ]
        have hφnorm : ‖(((1 + ‖x‖) ^ (-N) * ‖x‖ ^ ((w.mult : ℝ) * σ) : ℝ) : ℂ)‖
            = (1 + ‖x‖) ^ (-N) * ‖x‖ ^ ((w.mult : ℝ) * σ) := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_of_nonneg (by positivity)
        rw [hφnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (‖x‖ ^ (w.mult : ℕ))⁻¹)]
        have hpowinv : (‖x‖ ^ (w.mult : ℕ))⁻¹ = ‖x‖ ^ (-(w.mult : ℝ)) := by
          rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
        rw [hpowinv]
        have hcollect : ‖x‖ ^ (-(w.mult : ℝ)) * ((1 + ‖x‖) ^ (-N) * ‖x‖ ^ ((w.mult : ℝ) * σ))
            = (1 + ‖x‖) ^ (-N) * ‖x‖ ^ ((σ - 1) * (w.mult : ℝ)) := by
          rw [mul_comm ((1 + ‖x‖) ^ (-N)) (‖x‖ ^ ((w.mult : ℝ) * σ)), ← mul_assoc,
            ← Real.rpow_add hnx]
          ring_nf
        rw [hcollect]
        have hmono : ‖x‖ ^ ((σ - 1) * (w.mult : ℝ)) ≤ (1 + ‖x‖) ^ ((σ - 1) * (w.mult : ℝ)) :=
          Real.rpow_le_rpow (norm_nonneg _) (by linarith) hβ
        calc (1 + ‖x‖) ^ (-N) * ‖x‖ ^ ((σ - 1) * (w.mult : ℝ))
            ≤ (1 + ‖x‖) ^ (-N) * (1 + ‖x‖) ^ ((σ - 1) * (w.mult : ℝ)) := by
              refine mul_le_mul_of_nonneg_left hmono ?_
              positivity
          _ = (1 + ‖x‖) ^ (-(N - (σ - 1) * (w.mult : ℝ))) := by
              rw [← Real.rpow_add (by positivity)]
              ring_nf
  have hdock := (integrable_comp_val_comap_mulMeasure_iff
    (ArchMulHaarCompletion.measurableEmbedding_val_completion w) μ φ).mpr hmulM
  have heq : ∀ t : (w.Completion)ˣ,
      (1 + ‖(t : w.Completion)‖) ^ (-N) * ((distribHaarChar w.Completion t : ℝ≥0) : ℝ) ^ σ
        = (φ (t : w.Completion)).re := by
    intro t
    rw [hφ, hΔ t]
    simp [Complex.ofReal_re]
  have hre := hdock.re
  exact hre.congr (Filter.Eventually.of_forall fun t => (heq t).symm)

end ArchDecay

end NumberField.TateGlobal

end

end Fold_ArchDecay
