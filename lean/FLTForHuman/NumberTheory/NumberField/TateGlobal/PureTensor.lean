/-
  The pure-tensor shell analysis: continuity of the pure tensor
  (`continuous_pureTensor`) and of the idèle norm along `asm`
  (`continuous_ideleNorm_asm`), the two shell integrability lemmas
  `integrableOn_zetaIntegrand_shell_of_nonneg` and `integrableOn_norm_translate`,
  the vanishing `pureTensor_eq_zero_of_shell_neg` on negative shells, and the
  master shell decomposition `hole_of_measures`.

  Transcribed from the pin's `Fold_G1Discharge` section
  (`M4aLocalCFT.G1Discharge`), declared lines 5717-6082 of file B, pinned
  `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_integrable_zetaIntegrand.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped, as is the
  `set_option maxHeartbeats 3200000 in` on `hole_of_measures` (B 5973); all
  declarations elaborate at the port's low edit cap.  `M4aLocalCFT.` is renamed to
  `NumberField.TateGlobal.`.  The pin's shared `preimage_mul_smul` (A∩B) is not
  re-derived: the ported `NumberField.TateGlobal.G2Proof.preimage_mul_smul` is used
  instead.  The pin's deprecated `if_pos`/`if_neg` are spelled
  `ite_eq_left`/`ite_eq_right` (proof-only).  The pin's `omit [...] in` and
  `include μa μf in` prefixes are kept.  No file-wide option beyond
  `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.HMajorant
import FLTForHuman.NumberTheory.NumberField.TateGlobal.EulerFactors
import FLTForHuman.NumberTheory.AdelicBox

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion NumberField.InfiniteAdeleRing
open NumberField.AdelicFourier
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal Classical

section Fold_G1Discharge

open NumberField.AdelicFourier AutomorphicForm IsDedekindDomain Finset Set

open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Classical Pointwise

noncomputable section

namespace NumberField
namespace TateGlobal
namespace G1Discharge

variable {F : Type} [Field F] [NumberField F]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

variable [∀ w : InfinitePlace F, MeasurableSpace w.Completion]

variable [∀ w : InfinitePlace F, BorelSpace w.Completion]

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ]

variable [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]

variable [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]

variable [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]

variable [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

variable (μa : (w : InfinitePlace F) → Measure w.Completion)

variable (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))

variable [∀ w, (μa w).IsAddHaarMeasure] [∀ w, (μa w).Regular]

variable [∀ v, (μf v).IsAddHaarMeasure] [∀ v, (μf v).Regular]

variable (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [∀ w : InfinitePlace F, BorelSpace w.Completion]
  [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace w.Completion]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
-- pin: continuous_pureTensor (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5717)
theorem continuous_pureTensor (g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) :
    Continuous fun x : AdeleRing (𝓞 F) F => g (ringEquiv_mixedSpace F x.1) * h x.2 :=
  ((g.continuous.comp ((AdelicBox.continuous_ringEquiv_mixedSpace F).comp continuous_fst)).mul
    (hlc.continuous.comp continuous_snd))

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
-- pin: continuous_ideleNorm_asm (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5733)
theorem continuous_ideleNorm_asm (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous fun q : TateGlobal.Q (F := F) S => ideleNorm F (TateGlobal.asm S q) := by
  have hfix : (fun q : TateGlobal.Q (F := F) S => ideleNorm F (TateGlobal.asm S q))
      = fun q => (∏ w, ((distribHaarChar (w.Completion) (TateGlobal.archPiUnits q.1 w) : ℝ≥0) : ℝ))
        * ∏ v : S, ((distribHaarChar (v.1.adicCompletion F) (q.2.1 v) : ℝ≥0) : ℝ) := by
    funext q
    exact TateGlobal.ideleNorm_asm S q
  rw [hfix]
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetProd _ fun w _ => ?_
    have harch : Continuous fun q : TateGlobal.Q (F := F) S =>
        TateGlobal.archPiUnits q.1 w :=
      (continuous_apply w).comp ((TateGlobal.archPiUnits (F := F)).continuous.comp continuous_fst)
    have hΔcont : Continuous fun t : (w.Completion)ˣ =>
        ((distribHaarChar (w.Completion) t : ℝ≥0) : ℝ) := by
      have hfix2 : (fun t : (w.Completion)ˣ => ((distribHaarChar (w.Completion) t : ℝ≥0) : ℝ))
          = fun t : (w.Completion)ˣ => ‖(t : w.Completion)‖ ^ (w.mult : ℕ) := by
        funext t
        rw [FujisakiC3.distribHaarChar_completion_eq_pow_mult]
        push_cast
        rfl
      rw [hfix2]
      exact (continuous_norm.comp Units.continuous_val).pow _
    exact hΔcont.comp harch
  · refine continuous_finsetProd _ fun v _ => ?_
    have hfin : Continuous fun q : TateGlobal.Q (F := F) S => q.2.1 v :=
      (continuous_apply v).comp (continuous_fst.comp continuous_snd)
    have hΔv : Continuous fun t : (v.1.adicCompletion F)ˣ =>
        ((distribHaarChar (v.1.adicCompletion F) t : ℝ≥0) : ℝ) := by
      have hfix3 : (fun t : (v.1.adicCompletion F)ˣ =>
          ((distribHaarChar (v.1.adicCompletion F) t : ℝ≥0) : ℝ))
          = fun t : (v.1.adicCompletion F)ˣ => ((‖((t : v.1.adicCompletion F))‖₊ : ℝ≥0) : ℝ) := by
        funext t
        rw [← modulus_coe_units, TateGlobal.modulus_adicCompletion_eq_nnnorm]
      rw [hfix3]
      exact continuous_subtype_val.comp ((continuous_nnnorm.comp Units.continuous_val))
    exact hΔv.comp hfin

include μa μf in
omit [∀ w, (μa w).Regular] [∀ v, (μf v).Regular] in
-- pin: integrableOn_zetaIntegrand_shell_of_nonneg (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5794)
theorem integrableOn_zetaIntegrand_shell_of_nonneg
    {g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ} {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hlc : IsLocallyConstant h)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 F) F χ) {s : ℂ}
    {C_g C_h : ℝ} (hCg : 0 < C_g) (hCh : 0 < C_h) {N : ℕ}
    (hgle : ∀ x : InfiniteAdeleRing F,
      ‖g (ringEquiv_mixedSpace F x)‖ * ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N ≤ C_g)
    (hhb : ∀ y, ‖h y‖ ≤ C_h)
    (ϖ : Uniformizers F) (m : HeightOneSpectrum (𝓞 F) → ℕ) (w₀ : InfinitePlace F)
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hbox : ∀ v ∈ S, ∀ y ∈ tsupport h, (y : FiniteAdeleRing (𝓞 F) F) v ∈ ShellSupport.boxAt ϖ v (m v))
    (hHint : IntegrableOn
      (fun x : (AdeleRing (𝓞 F) F)ˣ => ‖H (C_g * C_h) N w₀ ϖ m S ↑x‖ * ideleNorm F x ^ s.re)
      (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk0 : ∀ v ∈ S, k v = 0) :
    IntegrableOn
      (fun x : (AdeleRing (𝓞 F) F)ˣ =>
        (g (ringEquiv_mixedSpace F ((x : AdeleRing (𝓞 F) F)).1) * h ((x : AdeleRing (𝓞 F) F)).2)
          * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
      (TateGlobal.shell S k) ν := by
  rw [TateGlobal.shell_eq_smul ϖ (fun v hv => hk0 v hv)]
  set c : (AdeleRing (𝓞 F) F)ˣ := unifPow ϖ k with hc
  have hemb : MeasurableEmbedding (fun u : (AdeleRing (𝓞 F) F)ˣ => c * u) :=
    (Homeomorph.mulLeft c).measurableEmbedding
  have hmp := measurePreserving_mul_left ν c
  rw [← hmp.integrableOn_comp_preimage hemb, G2Proof.preimage_mul_smul c]
  rw [TateGlobal.integrableOn_unitsOutside_iff_integrable_refMeasure S μa μf ν]
  set Φ : TateGlobal.Q (F := F) S → ℂ := fun q =>
    (g (ringEquiv_mixedSpace F ((((c * TateGlobal.asm S q : (AdeleRing (𝓞 F) F)ˣ)) : AdeleRing (𝓞 F) F)).1)
        * h ((((c * TateGlobal.asm S q : (AdeleRing (𝓞 F) F)ˣ)) : AdeleRing (𝓞 F) F)).2)
      * ((χ (c * TateGlobal.asm S q) : ℂˣ) : ℂ)
      * ((ideleNorm F (c * TateGlobal.asm S q) : ℝ) : ℂ) ^ s with hΦ
  show Integrable Φ (TateGlobal.refMeasure S μa μf)
  have hΦc : Continuous Φ := by
    rw [hΦ]
    have hasm : Continuous fun q : TateGlobal.Q (F := F) S => c * TateGlobal.asm S q :=
      (continuous_const_mul c).comp (TateGlobal.continuous_asm S)
    have hval : Continuous fun q : TateGlobal.Q (F := F) S =>
        ((c * TateGlobal.asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) :=
      Units.continuous_val.comp hasm
    have hnorm : Continuous fun q : TateGlobal.Q (F := F) S =>
        ideleNorm F (c * TateGlobal.asm S q) := by
      have hfix : (fun q : TateGlobal.Q (F := F) S => ideleNorm F (c * TateGlobal.asm S q))
          = fun q => ideleNorm F c * ideleNorm F (TateGlobal.asm S q) := by
        funext q
        exact TateGlobal.ideleNorm_mul c _
      rw [hfix]
      exact continuous_const.mul (continuous_ideleNorm_asm S)
    refine Continuous.mul (Continuous.mul ((continuous_pureTensor g hlc).comp hval) ?_) ?_
    · exact Units.continuous_val.comp (hχc.comp hasm)
    · refine (Complex.continuous_ofReal.comp hnorm).cpow continuous_const fun q => ?_
      exact Complex.ofReal_mem_slitPlane.mpr (TateGlobal.ideleNorm_pos _)
  have hdom : ∀ q : TateGlobal.Q (F := F) S,
      ‖Φ q‖ ≤ ideleNorm F c ^ s.re *
        (‖H (C_g * C_h) N w₀ ϖ m S ↑(TateGlobal.asm S q)‖
          * ideleNorm F (TateGlobal.asm S q) ^ s.re) := by
    intro q
    have hq : TateGlobal.asm S q ∈ unitsOutside S := TateGlobal.asm_mem_unitsOutside S q
    have hsplit : ‖Φ q‖
        = ‖g (ringEquiv_mixedSpace F ((((c * TateGlobal.asm S q :
            (AdeleRing (𝓞 F) F)ˣ)) : AdeleRing (𝓞 F) F)).1)
            * h ((((c * TateGlobal.asm S q : (AdeleRing (𝓞 F) F)ˣ)) : AdeleRing (𝓞 F) F)).2‖
          * ideleNorm F (c * TateGlobal.asm S q) ^ s.re := by
      rw [hΦ]
      rw [norm_mul, norm_mul, hχu _, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast TateGlobal.ideleNorm_pos _)]
    rw [hsplit, TateGlobal.ideleNorm_mul,
      Real.mul_rpow (TateGlobal.ideleNorm_pos _).le (TateGlobal.ideleNorm_pos _).le]
    have hfle := norm_f_le_H hCg hCh hgle hhb ϖ m w₀ hbox hk0 hq
    have hb0 : (0:ℝ) ≤ ideleNorm F c ^ s.re := Real.rpow_nonneg (TateGlobal.ideleNorm_pos _).le _
    have hb1 : (0:ℝ) ≤ ideleNorm F (TateGlobal.asm S q) ^ s.re :=
      Real.rpow_nonneg (TateGlobal.ideleNorm_pos _).le _
    calc ‖g _ * h _‖ * (ideleNorm F c ^ s.re * ideleNorm F (TateGlobal.asm S q) ^ s.re)
        ≤ ‖H (C_g * C_h) N w₀ ϖ m S ↑(TateGlobal.asm S q)‖
            * (ideleNorm F c ^ s.re * ideleNorm F (TateGlobal.asm S q) ^ s.re) := by
          refine mul_le_mul_of_nonneg_right hfle (by positivity)
      _ = ideleNorm F c ^ s.re * (‖H (C_g * C_h) N w₀ ϖ m S ↑(TateGlobal.asm S q)‖
            * ideleNorm F (TateGlobal.asm S q) ^ s.re) := by ring
  have hHref : Integrable (fun q : TateGlobal.Q (F := F) S =>
      ‖H (C_g * C_h) N w₀ ϖ m S ↑(TateGlobal.asm S q)‖
        * ideleNorm F (TateGlobal.asm S q) ^ s.re) (TateGlobal.refMeasure S μa μf) :=
    (TateGlobal.integrableOn_unitsOutside_iff_integrable_refMeasure S μa μf ν _).mp hHint
  refine Integrable.mono' (hHref.const_mul (ideleNorm F c ^ s.re))
    hΦc.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
  simpa [mul_assoc] using hdom q

include μa μf in
omit [∀ w, (μa w).Regular] [∀ v, (μf v).Regular] in
-- pin: integrableOn_norm_translate (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5883)
theorem integrableOn_norm_translate
    {g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ} {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hlc : IsLocallyConstant h) {σ : ℝ} (hσ0 : 0 ≤ σ)
    {C_g C_h : ℝ} (hCg : 0 < C_g) (hCh : 0 < C_h) {N : ℕ}
    (hgle : ∀ x : InfiniteAdeleRing F,
      ‖g (ringEquiv_mixedSpace F x)‖ * ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N ≤ C_g)
    (hhb : ∀ y, ‖h y‖ ≤ C_h)
    (ϖ : Uniformizers F) (m : HeightOneSpectrum (𝓞 F) → ℕ) (w₀ : InfinitePlace F)
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hbox : ∀ v ∈ S, ∀ y ∈ tsupport h, (y : FiniteAdeleRing (𝓞 F) F) v ∈ ShellSupport.boxAt ϖ v (m v))
    (hHint : IntegrableOn
      (fun x : (AdeleRing (𝓞 F) F)ˣ => ‖H (C_g * C_h) N w₀ ϖ m S ↑x‖ * ideleNorm F x ^ σ)
      (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk0 : ∀ v ∈ S, k v = 0) :
    IntegrableOn
      (fun u : (AdeleRing (𝓞 F) F)ˣ =>
        ‖g (ringEquiv_mixedSpace F (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1)
          * h (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2‖
          * ideleNorm F u ^ σ)
      (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν := by
  rw [TateGlobal.integrableOn_unitsOutside_iff_integrable_refMeasure S μa μf ν]
  set c : (AdeleRing (𝓞 F) F)ˣ := unifPow ϖ k with hc
  have hΦc : Continuous fun q : TateGlobal.Q (F := F) S =>
      ‖g (ringEquiv_mixedSpace F (((c * TateGlobal.asm S q : (AdeleRing (𝓞 F) F)ˣ) :
          AdeleRing (𝓞 F) F)).1)
        * h (((c * TateGlobal.asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2‖
        * ideleNorm F (TateGlobal.asm S q) ^ σ := by
    have hasm : Continuous fun q : TateGlobal.Q (F := F) S => c * TateGlobal.asm S q :=
      (continuous_const_mul c).comp (TateGlobal.continuous_asm S)
    have hval : Continuous fun q : TateGlobal.Q (F := F) S =>
        ((c * TateGlobal.asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) :=
      Units.continuous_val.comp hasm
    refine Continuous.mul (continuous_norm.comp ((continuous_pureTensor g hlc).comp hval)) ?_
    exact (continuous_ideleNorm_asm S).rpow_const fun q => Or.inr hσ0
  have hHref : Integrable (fun q : TateGlobal.Q (F := F) S =>
      ‖H (C_g * C_h) N w₀ ϖ m S ↑(TateGlobal.asm S q)‖
        * ideleNorm F (TateGlobal.asm S q) ^ σ) (TateGlobal.refMeasure S μa μf) :=
    (TateGlobal.integrableOn_unitsOutside_iff_integrable_refMeasure S μa μf ν _).mp hHint
  refine Integrable.mono' hHref hΦc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  have hq : TateGlobal.asm S q ∈ unitsOutside S := TateGlobal.asm_mem_unitsOutside S q
  have hfle := norm_f_le_H hCg hCh hgle hhb ϖ m w₀ hbox hk0 hq
  have hb1 : (0:ℝ) ≤ ideleNorm F (TateGlobal.asm S q) ^ σ :=
    Real.rpow_nonneg (TateGlobal.ideleNorm_pos _).le _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right hfle hb1

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [∀ w : InfinitePlace F, BorelSpace w.Completion]
  [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace w.Completion]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
-- pin: pureTensor_eq_zero_of_shell_neg (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5942)
theorem pureTensor_eq_zero_of_shell_neg
    {g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ} {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hsupp : tsupport h ⊆ ShellSupport.integralOff S)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ¬ 0 ≤ k)
    {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ TateGlobal.shell S k) :
    g (ringEquiv_mixedSpace F ((x : AdeleRing (𝓞 F) F)).1) * h ((x : AdeleRing (𝓞 F) F)).2 = 0 := by
  rw [Finsupp.le_def, not_forall] at hk
  obtain ⟨v₀, hv₀⟩ := hk
  rw [not_le] at hv₀
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hv₀
  have hxk : TateGlobal.expVec S x = k := hx
  have hv₀S : v₀ ∉ S := by
    intro hmem
    have h0 := TateGlobal.expVec_apply_of_mem x hmem
    rw [hxk] at h0
    omega
  have hord : ordAt v₀ (unitAtHom v₀ x) = k v₀ := by
    have h1 := TateGlobal.expVec_apply_of_not_mem x hv₀S
    rw [hxk] at h1
    exact h1.symm
  have hnotint : ((x : AdeleRing (𝓞 F) F)).2 ∉ ShellSupport.integralOff S := by
    intro hmem
    have hin := hmem v₀ hv₀S
    have hval := TateGlobal.unitAtHom_val x v₀
    rw [← hval] at hin
    have hnn := (mem_integers_iff_ordAt_nonneg v₀ _).mp hin
    omega
  rw [ShellSupport.apply_eq_zero hsupp hnotint, mul_zero]

-- The pin keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`, which
-- `linter.overlappingInstances` sees as overlapping.
set_option linter.overlappingInstances false in
include μa μf in
-- pin: hole_of_measures (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5974)
theorem hole_of_measures
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    {s : ℂ} (hs : 1 < s.re) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℝ), 0 ≤ M
      ∧ (∀ k : TateGlobal.ExpIndex (F := F) S, IntegrableOn
          (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
          (TateGlobal.shell S k.1) ν)
      ∧ (∀ k : TateGlobal.ExpIndex (F := F) S, 0 ≤ k.1 →
          (∫ x in TateGlobal.shell S k.1,
              ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν)
            ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat) * M)
      ∧ (∀ k : TateGlobal.ExpIndex (F := F) S, ¬ 0 ≤ k.1 →
          (∫ x in TateGlobal.shell S k.1,
              ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν) = 0) := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
  obtain ⟨S, hsupp⟩ := ShellSupport.exists_finset_tsupport_subset hcs
  set ϖ : Uniformizers F := someUniformizers with hϖ
  choose m hbox using fun v => ShellSupport.exists_box hcs ϖ v
  have hbox' : ∀ v ∈ S, ∀ y ∈ tsupport h,
      (y : FiniteAdeleRing (𝓞 F) F) v ∈ ShellSupport.boxAt ϖ v (m v) :=
    fun v _ y hy => hbox v y hy
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  set N : ℕ := ⌈2 * s.re⌉₊ + 1 with hNdef
  have hN : 2 * s.re < (N : ℝ) := by
    have h1 := Nat.le_ceil (2 * s.re)
    have h2 : (⌈2 * s.re⌉₊ : ℝ) < ((⌈2 * s.re⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [hNdef]
    linarith
  obtain ⟨C_g, hCg, hgle⟩ := ArchDecay.schwartz_le_prod_one_add_norm (F := F) g N
  obtain ⟨C_h, hCh, hhb⟩ := exists_bound_of_locallyConstant hlc hcs
  have hσ1 : 1 ≤ s.re := hs.le
  have hσ0 : (0 : ℝ) ≤ s.re := le_trans zero_le_one hσ1
  have hHint := integrableOn_H μa μf ν (C_g * C_h) w₀ ϖ m S hσ1 hN
  have hmeasU : MeasurableSet (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) := by
    rw [← TateGlobal.range_asm S]
    exact (TateGlobal.measurableEmbedding_asm S).measurableSet_range
  have hmeasShell : ∀ (k : HeightOneSpectrum (𝓞 F) →₀ ℤ), (∀ v ∈ S, k v = 0) →
      MeasurableSet (TateGlobal.shell S k) := by
    intro k hk0
    rw [TateGlobal.shell_eq_smul ϖ hk0]
    show MeasurableSet ((fun u => unifPow ϖ k * u) '' _)
    exact (Homeomorph.mulLeft (unifPow ϖ k)).measurableEmbedding.measurableSet_image' hmeasU
  set M₀ : ℝ := ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
      ‖H (C_g * C_h) N w₀ ϖ m S ↑u‖ * ideleNorm F u ^ s.re ∂ν with hM₀
  refine ⟨S, M₀, ?_, ?_, ?_, ?_⟩
  · rw [hM₀]
    exact integral_nonneg fun u =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (TateGlobal.ideleNorm_pos _).le _)
  ·
    intro k
    by_cases hk : 0 ≤ k.1
    · exact integrableOn_zetaIntegrand_shell_of_nonneg μa μf ν hlc hχc hχu
        hCg hCh hgle hhb ϖ m w₀ hbox' hHint k.2
    · refine (integrableOn_congr_fun (g := 0) (fun x hx => ?_) (hmeasShell k.1 k.2)).mpr
        (integrableOn_zero)
      simp only [Pi.zero_apply, pureTensor_eq_zero_of_shell_neg hsupp hk hx, zero_mul]
  ·
    intro k hk
    refine ShellTranslate.setIntegral_shell_norm_le
      (f := fun x : AdeleRing (𝓞 F) F => g (ringEquiv_mixedSpace F x.1) * h x.2)
      (s := s) (M := M₀) ν ϖ hχu k hk ?_
    rw [hM₀]
    have hMint := integrableOn_norm_translate μa μf ν hlc hσ0 hCg hCh hgle hhb ϖ m w₀
      hbox' hHint k.2
    refine setIntegral_mono_on hMint hHint hmeasU fun u hu => ?_
    have hfle := norm_f_le_H hCg hCh hgle hhb ϖ m w₀ hbox' k.2 hu
    exact mul_le_mul_of_nonneg_right hfle
      (Real.rpow_nonneg (TateGlobal.ideleNorm_pos _).le _)
  ·
    intro k hk
    rw [setIntegral_congr_fun (hmeasShell k.1 k.2) (g := 0) fun x hx => by
      simp only [Pi.zero_apply, pureTensor_eq_zero_of_shell_neg hsupp hk hx, zero_mul, norm_zero]]
    exact integral_zero _ _

end G1Discharge

end NumberField.TateGlobal

end

end Fold_G1Discharge
