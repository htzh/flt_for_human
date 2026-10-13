/-
  The norm integrands and their integrability: the archimedean, finite and
  assembled norms `archLocalNormIntegrand`/`finLocalNormIntegrand`/
  `archNormIntegrand`/`sNormIntegrand`, the factorized norm identity
  `norm_apply_asm_mul_ideleNorm_rpow`, the product integrability on
  `archRef`/`sRef`/`refMeasure`, the equivalence
  `integrableOn_unitsOutside_iff_integrable_refMeasure` and its norm consequence
  `integrableOn_unitsOutside_norm_mul_ideleNorm_rpow`; then the local finite leg:
  `toNNReal_exp`, `coe_distribHaarChar_adicCompletion_eq_norm`,
  `modulus_adicCompletion_eq_nnnorm`, `measurable_modulus_adicCompletion`,
  `integrable_comp_val_comap_mulMeasure_iff'`,
  `integrable_norm_mul_modulus_rpow_mulMeasure` and
  `integrable_finLocalNormIntegrand`.

  Transcribed from the pin's `Fold_TateFubiniNorm` and `Fold_LocalBoxIntegrable`
  sections (`NumberField.TateGlobal` blocks), declared lines 5046-5394 of file B,
  pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_integrable_zetaIntegrand.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped; `M4aLocalCFT.` is renamed
  to `NumberField.TateGlobal.`.  `Mathlib.MeasureTheory.Integral.Prod` is imported
  for `Integrable.mul_prod`, which the pin gets through its broader prelude.  The
  two pin sections are kept as separate `section`s so their `variable` scopes do not
  leak into each other.

  **Deferred (mathlib drift).**  The pin's `integrable_refMeasure_mul`
  (B 5146) is *not* transcribed: at mathlib `v4.34.0` every product-measure
  integration lemma (`Integrable.mul_prod`, `AEStronglyMeasurable.comp_fst`,
  `lintegral_prod_le`, ...) requires the second factor to be `SFinite`, while the
  pin's statement has no such hypothesis (its mathlib `v4.33.0` proved
  `Integrable.op_fst_snd` with `omit [SFinite ν]`).  The statement therefore has no
  proof at the port's mathlib without adding hypotheses to it, which would be a
  statement change.  Its only consumer
  `integrableOn_unitsOutside_norm_mul_ideleNorm_rpow` (B 5190) is proved here by
  inlining that step, because its own section supplies
  `[∀ w, (μa w).IsAddHaarMeasure]`/`[∀ v, (μf v).IsAddHaarMeasure]` and hence the
  missing `SFinite` instances.  See the dispatch report.

  No file-wide option beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.UnifPowBridge
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion NumberField.InfiniteAdeleRing
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal Classical

section Fold_TateFubiniNorm

open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

section NormIntegrands

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- pin: archLocalNormIntegrand (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5046)
def archLocalNormIntegrand (g : (w : InfinitePlace F) → w.Completion → ℂ) (σ : ℝ) (w : InfinitePlace F)
    (u : (w.Completion)ˣ) : ℝ :=
  ‖g w u‖ * ((distribHaarChar (w.Completion) u : ℝ≥0) : ℝ) ^ σ

-- pin: finLocalNormIntegrand (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5050)
def finLocalNormIntegrand (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (σ : ℝ)
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) : ℝ :=
  ‖h v u‖ * ((distribHaarChar (v.adicCompletion F) u : ℝ≥0) : ℝ) ^ σ

-- pin: archNormIntegrand (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5054)
def archNormIntegrand (g : (w : InfinitePlace F) → w.Completion → ℂ) (σ : ℝ) (a : (InfiniteAdeleRing F)ˣ) : ℝ :=
  ∏ w, archLocalNormIntegrand g σ w (archPiUnits a w)

-- pin: sNormIntegrand (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5057)
def sNormIntegrand (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (σ : ℝ)
    (t : SUnits (F := F) S) : ℝ :=
  ∏ v : S, finLocalNormIntegrand h σ v.1 (t v)

-- pin: norm_apply_asm_mul_ideleNorm_rpow (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5061)
theorem norm_apply_asm_mul_ideleNorm_rpow {f : AdeleRing (𝓞 F) F → ℂ}
    {g : (w : InfinitePlace F) → w.Completion → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsFactorizableStandardOutside f S g h) (σ : ℝ) (q : Q (F := F) S) :
    ‖f (asm S q)‖ * ideleNorm F (asm S q) ^ σ
      = archNormIntegrand g σ q.1 * (sNormIntegrand S h σ q.2.1 * (1 : DeepUnits (F := F) S → ℝ) q.2.2) := by
  rw [apply_asm_of_isFactorizableStandardOutside S hf, norm_mul, norm_prod, norm_prod, ideleNorm_asm S,
    Real.mul_rpow (Finset.prod_nonneg fun w _ => NNReal.coe_nonneg _)
      (Finset.prod_nonneg fun v _ => NNReal.coe_nonneg _),
    ← Real.finsetProd_rpow _ _ (fun w _ => NNReal.coe_nonneg _) σ,
    ← Real.finsetProd_rpow _ _ (fun v _ => NNReal.coe_nonneg _) σ, Pi.one_apply, mul_one]
  unfold archNormIntegrand sNormIntegrand archLocalNormIntegrand finLocalNormIntegrand
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end NormIntegrands

section ArchOnly

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion))

variable [∀ w, (μa w).IsAddHaarMeasure]

-- pin: integrable_archRef_prod (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5087)
theorem integrable_archRef_prod {L : Type} [NormedCommRing L] (φ : (w : InfinitePlace F) → (w.Completion)ˣ → L)
    (hφ : ∀ w, Integrable (φ w) (ArchMulHaarCompletion.mulHaarCompletion w (μa w))) :
    Integrable (fun a : (InfiniteAdeleRing F)ˣ => ∏ w, φ w (archPiUnits a w)) (archRef μa) := by
  unfold archRef
  refine ((archPiUnits (F := F)).symm.toHomeomorph.measurableEmbedding.integrable_map_iff).2 ?_
  have hcomp : ((fun a : (InfiniteAdeleRing F)ˣ => ∏ w, φ w (archPiUnits a w))
        ∘ ((archPiUnits (F := F)).symm.toHomeomorph))
      = fun t => ∏ w, φ w (t w) := by
    funext t
    show (∏ w, φ w (archPiUnits ((archPiUnits (F := F)).symm t) w)) = _
    simp only [ContinuousMulEquiv.apply_symm_apply]
  rw [hcomp]
  exact Integrable.fintype_prod_dep hφ

end ArchOnly

section SOnly

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]

-- pin: integrable_sRef_prod (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5114)
theorem integrable_sRef_prod {L : Type} [NormedCommRing L] (φ : (v : S) → (v.1.adicCompletion F)ˣ → L)
    (hφ : ∀ v, Integrable (φ v) (MulHaarFromAdditive.mulHaar (μf v.1))) :
    Integrable (fun t : SUnits (F := F) S => ∏ v : S, φ v (t v)) (sRef S μf) := by
  unfold sRef
  exact Integrable.fintype_prod_dep hφ

end SOnly

section AssemblyOnly

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion))
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))

-- The pin's `integrable_refMeasure_mul` (B 5146) is DEFERRED here; see the module
-- header for the v4.34.0 `SFinite` drift that makes its statement unprovable as
-- written.  Its only consumer `integrableOn_unitsOutside_norm_mul_ideleNorm_rpow`
-- below inlines the step.

end AssemblyOnly

section Full

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

-- pin: integrableOn_unitsOutside_iff_integrable_refMeasure (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5175)
theorem integrableOn_unitsOutside_iff_integrable_refMeasure {E : Type} [NormedAddCommGroup E]
    (G : (AdeleRing (𝓞 F) F)ˣ → E) :
    IntegrableOn G (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν
      ↔ Integrable (fun q => G (asm S q)) (refMeasure S μa μf) := by
  rw [IntegrableOn, ← range_asm S, ← (measurableEmbedding_asm S).map_comap ν,
    (measurableEmbedding_asm S).integrable_map_iff]
  show Integrable (G ∘ asm S) (asmMeasure S ν) ↔ _
  rw [asmMeasure_eq_refConst_smul S μa μf ν]
  constructor
  · intro hG
    have hG' := hG.smul_measure_nnreal (c := (refConst S μa μf ν)⁻¹)
    rwa [smul_smul, inv_mul_cancel₀ (refConst_pos S μa μf ν).ne', one_smul] at hG'
  · intro hG
    exact hG.smul_measure_nnreal

-- pin: integrableOn_unitsOutside_norm_mul_ideleNorm_rpow (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5190)
theorem integrableOn_unitsOutside_norm_mul_ideleNorm_rpow {f : AdeleRing (𝓞 F) F → ℂ}
    {g : (w : InfinitePlace F) → w.Completion → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsFactorizableStandardOutside f S g h) (σ : ℝ)
    (hA : ∀ w, Integrable (archLocalNormIntegrand g σ w) (ArchMulHaarCompletion.mulHaarCompletion w (μa w)))
    (hB : ∀ v : S, Integrable (finLocalNormIntegrand h σ v.1) (MulHaarFromAdditive.mulHaar (μf v.1))) :
    IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ => ‖f x‖ * ideleNorm F x ^ σ)
      (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν := by
  rw [integrableOn_unitsOutside_iff_integrable_refMeasure S μa μf ν]
  -- Inlined `integrable_refMeasure_mul` (see the module header): this section's
  -- `IsAddHaarMeasure` hypotheses supply the `SFinite` instances that v4.34.0 needs.
  have hprod : Integrable (fun q : Q (F := F) S =>
      archNormIntegrand g σ q.1 * (sNormIntegrand S h σ q.2.1 * (1 : DeepUnits (F := F) S → ℝ) q.2.2))
      (refMeasure S μa μf) :=
    (integrable_archRef_prod μa _ hA).mul_prod
      ((integrable_sRef_prod S μf _ hB).mul_prod (integrable_const 1))
  exact hprod.congr (ae_of_all _ fun q => (norm_apply_asm_mul_ideleNorm_rpow S hf σ q).symm)

end Full

end NumberField.TateGlobal

end

end Fold_TateFubiniNorm

section Fold_LocalBoxIntegrable

open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

-- pin: toNNReal_exp (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5243)
theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (a : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp a) = e ^ a := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]
  congr 1

-- pin: coe_distribHaarChar_adicCompletion_eq_norm (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5248)
theorem coe_distribHaarChar_adicCompletion_eq_norm (t : (v.adicCompletion F)ˣ) :
    ((distribHaarChar (v.adicCompletion F) t : ℝ≥0) : ℝ) = ‖(t : v.adicCompletion F)‖ := by
  rw [NumberField.FinitePlace.norm_def, ValuedOrdBridge.valued_coe_units_eq_exp_neg_ord, toNNReal_exp,
    LocalHaarModulus.distribHaarChar_adicCompletion]

-- pin: modulus_adicCompletion_eq_nnnorm (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5253)
theorem modulus_adicCompletion_eq_nnnorm (x : v.adicCompletion F) : modulus x = ‖x‖₊ := by
  by_cases hx : x = 0
  · rw [hx, modulus_zero, nnnorm_zero]
  · apply NNReal.coe_injective
    rw [modulus_of_ne_zero hx, coe_nnnorm, coe_distribHaarChar_adicCompletion_eq_norm, Units.val_mk0]

-- pin: measurable_modulus_adicCompletion (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5259)
theorem measurable_modulus_adicCompletion [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] :
    Measurable (modulus : v.adicCompletion F → ℝ≥0) := by
  have h : (modulus : v.adicCompletion F → ℝ≥0) = fun x => ‖x‖₊ :=
    funext modulus_adicCompletion_eq_nnnorm
  rw [h]
  exact continuous_nnnorm.measurable

section CompVal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K] [MeasurableSpace Kˣ]

-- pin: integrable_comp_val_comap_mulMeasure_iff' (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5272)
theorem integrable_comp_val_comap_mulMeasure_iff' {E : Type} [NormedAddCommGroup E]
    (hval : MeasurableEmbedding (Units.val : Kˣ → K)) (μ : Measure K) (φ : K → E) :
    Integrable (fun t : Kˣ => φ (t : K)) (Measure.comap Units.val (mulMeasure μ))
      ↔ Integrable φ (mulMeasure μ) := by
  show Integrable (φ ∘ Units.val) _ ↔ _
  rw [← hval.integrable_map_iff, hval.map_comap, range_units_val, mulMeasure_restrict_compl_zero]

end CompVal

section FinLeg

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
  (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]

-- pin: integrable_norm_mul_modulus_rpow_mulMeasure (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5287)
theorem integrable_norm_mul_modulus_rpow_mulMeasure {φ : v.adicCompletion F → ℂ} (hφm : Measurable φ)
    (hφs : HasCompactSupport φ) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) {σ : ℝ} (hσ : 1 ≤ σ) :
    Integrable (fun x => ‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ) (mulMeasure μ) := by
  have hmod : Measurable (modulus : v.adicCompletion F → ℝ≥0) := measurable_modulus_adicCompletion
  have hmodR : Measurable (fun x : v.adicCompletion F => ((modulus x : ℝ≥0) : ℝ)) := hmod.coe_nnreal_real
  unfold mulMeasure
  refine (integrable_withDensity_iff_integrable_smul' (hmod.coe_nnreal_ennreal.inv) ?_).2 ?_
  · refine (ae_restrict_mem (measurableSet_singleton (0 : v.adicCompletion F)).compl).mono fun x hx => ?_
    exact ENNReal.inv_lt_top.2 (ENNReal.coe_pos.2 (modulus_pos hx))
  have hΨ : (fun x : v.adicCompletion F =>
        (((modulus x : ℝ≥0) : ℝ≥0∞)⁻¹).toReal • (‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ))
      = fun x => ((modulus x : ℝ≥0) : ℝ)⁻¹ * (‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ) := by
    funext x
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, smul_eq_mul]
  erw [hΨ]
  obtain ⟨M, hM⟩ := hφs.isCompact.isBounded.exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set M' : ℝ := max M 1 with hM'
  have hM'1 : 1 ≤ M' := le_max_right _ _
  have hbound : ∀ x : v.adicCompletion F,
      ‖((modulus x : ℝ≥0) : ℝ)⁻¹ * (‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ)‖ ≤ C * M' ^ (σ - 1) := by
    intro x
    by_cases hxK : x ∈ tsupport φ
    · by_cases hx : x = 0
      · subst hx
        rw [modulus_zero, NNReal.coe_zero, Real.zero_rpow (by linarith), mul_zero, mul_zero, norm_zero]
        exact mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _)
      · have hm0 : (0 : ℝ) < ((modulus x : ℝ≥0) : ℝ) := NNReal.coe_pos.2 (modulus_pos hx)
        have hmM : ((modulus x : ℝ≥0) : ℝ) ≤ M' := by
          rw [modulus_adicCompletion_eq_nnnorm, coe_nnnorm]
          exact (hM x hxK).trans (le_max_left _ _)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hm0.le)
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hm0.le _))),
          show ((modulus x : ℝ≥0) : ℝ)⁻¹ * (‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ)
            = ‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ (σ - 1) by
            rw [Real.rpow_sub_one hm0.ne' σ]; field_simp]
        exact mul_le_mul (hC x) (Real.rpow_le_rpow hm0.le hmM (by linarith)) (Real.rpow_nonneg hm0.le _) hC0
    · rw [image_eq_zero_of_notMem_tsupport hxK, norm_zero, zero_mul, mul_zero, norm_zero]
      exact mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _)
  have hmeas : Measurable (fun x : v.adicCompletion F =>
      ((modulus x : ℝ≥0) : ℝ)⁻¹ * (‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ)) :=
    hmodR.inv.mul (hφm.norm.mul (hmodR.pow_const σ))
  have hsupp : Function.support (fun x : v.adicCompletion F =>
      ((modulus x : ℝ≥0) : ℝ)⁻¹ * (‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ)) ⊆ tsupport φ := by
    intro x hx
    by_contra hxK
    apply hx
    show ((modulus x : ℝ≥0) : ℝ)⁻¹ * (‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ) = 0
    rw [image_eq_zero_of_notMem_tsupport hxK, norm_zero, zero_mul, mul_zero]
  have hon : IntegrableOn (fun x : v.adicCompletion F =>
      ((modulus x : ℝ≥0) : ℝ)⁻¹ * (‖φ x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ)) (tsupport φ) μ :=
    Measure.integrableOn_of_bounded hφs.isCompact.measure_lt_top.ne hmeas.aestronglyMeasurable
      (ae_of_all _ hbound)
  exact ((integrableOn_iff_integrable_of_support_subset hsupp).1 hon).integrableOn

variable [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]

-- pin: integrable_finLocalNormIntegrand (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5344)
theorem integrable_finLocalNormIntegrand {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hm : Measurable (h v)) (hs : HasCompactSupport (h v)) {C : ℝ} (hC : ∀ x, ‖h v x‖ ≤ C) {σ : ℝ}
    (hσ : 1 ≤ σ) :
    Integrable (finLocalNormIntegrand h σ v) (MulHaarFromAdditive.mulHaar μ) := by
  have key := (integrable_comp_val_comap_mulMeasure_iff' MulHaarFromAdditive.measurableEmbedding_val μ
    (fun x => ‖h v x‖ * ((modulus x : ℝ≥0) : ℝ) ^ σ)).2
    (integrable_norm_mul_modulus_rpow_mulMeasure μ hm hs hC hσ)
  unfold finLocalNormIntegrand
  simp_rw [← modulus_coe_units]
  exact key

end FinLeg

end NumberField.TateGlobal

end

end Fold_LocalBoxIntegrable
