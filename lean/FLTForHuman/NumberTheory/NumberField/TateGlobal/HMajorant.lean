/-
  The majorant `H` for the pure tensor and its discharge: the uniformizer choice
  `someUniformizers`, the archimedean factor `gH`, the finite box function `hH`,
  the assembled majorant `H`, its factorizability
  `isFactorizableStandardOutside_H`, the compactness `isCompact_boxAt`, the
  locally-constant bound `exists_bound_of_locallyConstant`, the Schwartz division
  form `schwartz_le_div_form`, `mult_le_two`, the local majorants
  `hA_majorant`/`hB_majorant`, the integrability `integrableOn_H` and the two
  pointwise bounds `norm_h_le_boxProd`/`norm_f_le_H`.

  Transcribed from the pin's `Fold_IdeleIdealClass` (`NumberField.TateGlobal`) and
  `Fold_G1Discharge` (`M4aLocalCFT.G1Discharge`) sections, declared lines
  5395-5716 of file B, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_integrable_zetaIntegrand.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped, as are the file-scoped
  `set_option maxHeartbeats 3200000` / `maxSynthPendingDepth 3` (B 5377/5379); all
  declarations elaborate at the port's low edit cap.  `M4aLocalCFT.` is renamed to
  `NumberField.TateGlobal.` and the pin's `omit [...] in` prefixes are kept.  The
  two pin sections are kept as separate `section`s.  No file-wide option beyond
  `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IntLocalIntegrability
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ShellSupport
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion NumberField.InfiniteAdeleRing
open NumberField.AdelicFourier
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal Classical

section Fold_IdeleIdealClass

open NumberField.TateGlobal LanglandsTunnell.TateLocal

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

-- pin: someUniformizers (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5395)
def someUniformizers : Uniformizers F where
  ϖ v :=
    let ϖ := (ValuedOrdBridge.exists_irreducible_valued (F := F) (v := v)).choose
    have hirr : Irreducible ϖ :=
      (ValuedOrdBridge.exists_irreducible_valued (F := F) (v := v)).choose_spec.1
    have h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := fun h =>
      hirr.ne_zero (Subtype.ext h)
    Units.mk0 _ h0
  ordAt_eq_one v := by
    set ϖ := (ValuedOrdBridge.exists_irreducible_valued (F := F) (v := v)).choose
    have hirr : Irreducible ϖ :=
      (ValuedOrdBridge.exists_irreducible_valued (F := F) (v := v)).choose_spec.1
    have h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := fun h =>
      hirr.ne_zero (Subtype.ext h)
    show ordAt v (Units.mk0 _ h0) = 1
    exact IsDiscreteValuationRing.ord_ofMul_mk0_of_irreducible _ hirr h0

end NumberField.TateGlobal

end

end Fold_IdeleIdealClass

section Fold_G1Discharge

open NumberField.AdelicFourier AutomorphicForm IsDedekindDomain Finset Set

open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Classical Pointwise

noncomputable section

namespace NumberField
namespace TateGlobal
namespace G1Discharge

variable {F : Type} [Field F] [NumberField F]

-- pin: gH (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5441)
def gH (C : ℝ) (N : ℕ) (w₀ w : InfinitePlace F) (z : w.Completion) : ℂ :=
  (if w = w₀ then (C : ℂ) else 1) * ((1 + ‖z‖) ^ (-(N : ℝ)) : ℝ)

-- pin: hH (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5444)
def hH (ϖ : Uniformizers F) (m : HeightOneSpectrum (𝓞 F) → ℕ) (v : HeightOneSpectrum (𝓞 F))
    (y : v.adicCompletion F) : ℂ :=
  (ShellSupport.boxAt ϖ v (m v)).indicator 1 y

-- pin: H (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5448)
def H (C : ℝ) (N : ℕ) (w₀ : InfinitePlace F) (ϖ : Uniformizers F)
    (m : HeightOneSpectrum (𝓞 F) → ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : AdeleRing (𝓞 F) F) : ℂ :=
  (integralOutside S).indicator
    (fun x => (∏ w, gH C N w₀ w (x.1 w)) * ∏ v ∈ S, hH ϖ m v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x

-- pin: isFactorizableStandardOutside_H (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5454)
theorem isFactorizableStandardOutside_H (C : ℝ) (N : ℕ) (w₀ : InfinitePlace F)
    (ϖ : Uniformizers F) (m : HeightOneSpectrum (𝓞 F) → ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsFactorizableStandardOutside (H C N w₀ ϖ m S) S (gH C N w₀) (hH ϖ m) :=
  fun _x => rfl

-- pin: isCompact_boxAt (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5459)
theorem isCompact_boxAt (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    IsCompact (ShellSupport.boxAt ϖ v m) := by
  have hne : (((ϖ.ϖ v ^ m : (v.adicCompletion F)ˣ)) : v.adicCompletion F) ≠ 0 :=
    Units.ne_zero _
  have h : ShellSupport.boxAt ϖ v m
      = (Homeomorph.mulLeft₀ _ hne) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext y
    rw [Set.mem_preimage, Homeomorph.coe_mulLeft₀]
    exact Iff.rfl
  rw [h]
  exact (Homeomorph.isCompact_preimage _).mpr
    (LocalZetaUnramified.isCompact_integers (F := F) (v := v))

-- pin: exists_bound_of_locallyConstant (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5472)
theorem exists_bound_of_locallyConstant {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, ‖h y‖ ≤ C := by
  have himg : IsCompact (h '' tsupport h) := hcs.image hlc.continuous
  obtain ⟨C0, hC0⟩ := himg.isBounded.exists_norm_le
  refine ⟨max C0 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y => ?_⟩
  by_cases hy : y ∈ tsupport h
  · exact (hC0 _ (Set.mem_image_of_mem h hy)).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
    positivity

-- pin: schwartz_le_div_form (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5483)
theorem schwartz_le_div_form {g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ} {N : ℕ} {C : ℝ}
    (hle : ∀ x : InfiniteAdeleRing F,
      ‖g (ringEquiv_mixedSpace F x)‖ * ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N ≤ C)
    (x : InfiniteAdeleRing F) :
    ‖g (ringEquiv_mixedSpace F x)‖ ≤ C * ∏ w : InfinitePlace F, ((1 + ‖x w‖) ^ (-(N : ℝ)) : ℝ) := by
  have hpos : (0 : ℝ) < ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N :=
    Finset.prod_pos fun w _ => by positivity
  have hinv : ∏ w : InfinitePlace F, ((1 + ‖x w‖) ^ (-(N : ℝ)) : ℝ)
      = (∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [hinv, ← div_eq_mul_inv]
  exact (le_div_iff₀ hpos).mpr (hle x)

omit [NumberField F] in
-- pin: mult_le_two (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5499)
theorem mult_le_two (w : InfinitePlace F) : w.mult ≤ 2 := by
  rw [InfinitePlace.mult]
  split <;> omega

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

-- The pin keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`, which
-- `linter.overlappingInstances` sees as overlapping.
set_option linter.overlappingInstances false in
omit [NumberField F] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
-- pin: hA_majorant (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5535)
theorem hA_majorant (μa : (w : InfinitePlace F) → Measure w.Completion)
    [∀ w, (μa w).IsAddHaarMeasure] [∀ w, (μa w).Regular]
    (C : ℝ) {N : ℕ} (w₀ : InfinitePlace F) {σ : ℝ} (hσ : 1 ≤ σ) (hN : 2 * σ < (N : ℝ)) :
    ∀ w, Integrable (TateGlobal.archLocalNormIntegrand (gH C N w₀) σ w)
      (ArchMulHaarCompletion.mulHaarCompletion w (μa w)) := by
  intro w
  have hNw : (w.mult : ℝ) * σ < N := by
    have h2 : (w.mult : ℝ) ≤ 2 := by exact_mod_cast mult_le_two w
    have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le one_pos hσ
    nlinarith
  have hbase := ArchDecay.integrable_one_add_norm_mul_distribHaarChar_rpow w (μa w) hσ hNw
  have hconst := hbase.const_mul ‖(if w = w₀ then (C : ℂ) else 1 : ℂ)‖
  refine hconst.congr (Filter.Eventually.of_forall fun t => ?_)
  show ‖(if w = w₀ then (C : ℂ) else 1 : ℂ)‖ *
      ((1 + ‖(t : w.Completion)‖) ^ (-(N : ℝ)) * ((distribHaarChar w.Completion t : ℝ≥0) : ℝ) ^ σ)
    = TateGlobal.archLocalNormIntegrand (gH C N w₀) σ w t
  rw [TateGlobal.archLocalNormIntegrand, gH]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + ‖(t : w.Completion)‖) ^ (-(N : ℝ)))]
  ring

set_option linter.overlappingInstances false in
omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace w.Completion]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
-- pin: hB_majorant (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5562)
theorem hB_majorant (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure] [∀ v, (μf v).Regular]
    (ϖ : Uniformizers F) (m : HeightOneSpectrum (𝓞 F) → ℕ)
    {S : Finset (HeightOneSpectrum (𝓞 F))} {σ : ℝ} (hσ : 1 ≤ σ) :
    ∀ v : S, Integrable (TateGlobal.finLocalNormIntegrand (hH ϖ m) σ v.1)
      (MulHaarFromAdditive.mulHaar (μf v.1)) := by
  intro v
  refine TateGlobal.integrable_finLocalNormIntegrand (μf v.1) ?_ ?_ (C := 1) ?_ hσ
  · exact (measurable_const.indicator
      (ShellSupport.isOpen_boxAt ϖ v.1 (m v.1)).measurableSet)
  · refine HasCompactSupport.intro (isCompact_boxAt ϖ v.1 (m v.1)) fun y hy => ?_
    rw [hH, Set.indicator_of_notMem hy]
  · intro y
    rw [hH]
    by_cases hy : y ∈ ShellSupport.boxAt ϖ v.1 (m v.1)
    · rw [Set.indicator_of_mem hy]; simp
    · rw [Set.indicator_of_notMem hy]; simp

set_option linter.overlappingInstances false in
-- pin: integrableOn_H (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5580)
theorem integrableOn_H (μa : (w : InfinitePlace F) → Measure w.Completion)
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ w, (μa w).IsAddHaarMeasure] [∀ w, (μa w).Regular]
    [∀ v, (μf v).IsAddHaarMeasure] [∀ v, (μf v).Regular]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (C : ℝ) {N : ℕ} (w₀ : InfinitePlace F) (ϖ : Uniformizers F)
    (m : HeightOneSpectrum (𝓞 F) → ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {σ : ℝ} (hσ : 1 ≤ σ) (hN : 2 * σ < (N : ℝ)) :
    IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ => ‖H C N w₀ ϖ m S ↑x‖ * ideleNorm F x ^ σ)
      (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν :=
  TateGlobal.integrableOn_unitsOutside_norm_mul_ideleNorm_rpow S μa μf ν
    (isFactorizableStandardOutside_H C N w₀ ϖ m S) σ
    (hA_majorant μa C w₀ hσ hN) (hB_majorant μf ϖ m hσ)

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
-- pin: norm_h_le_boxProd (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5606)
theorem norm_h_le_boxProd {h : FiniteAdeleRing (𝓞 F) F → ℂ} {C_h : ℝ} (hC : 0 < C_h)
    (hhb : ∀ y, ‖h y‖ ≤ C_h) (ϖ : Uniformizers F) (m : HeightOneSpectrum (𝓞 F) → ℕ)
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hbox : ∀ v ∈ S, ∀ y ∈ tsupport h, (y : FiniteAdeleRing (𝓞 F) F) v ∈ ShellSupport.boxAt ϖ v (m v))
    (y : FiniteAdeleRing (𝓞 F) F) :
    ‖h y‖ ≤ C_h * ∏ v ∈ S, ‖hH ϖ m v (y v)‖ := by
  by_cases hy : y ∈ tsupport h
  · have hone : ∀ v ∈ S, ‖hH ϖ m v (y v)‖ = 1 := fun v hv => by
      rw [hH, Set.indicator_of_mem (hbox v hv y hy)]
      simp
    rw [Finset.prod_congr rfl hone, Finset.prod_const_one, mul_one]
    exact hhb y
  · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
    have hnn : ∀ v ∈ S, (0:ℝ) ≤ ‖hH ϖ m v (y v)‖ := fun v _ => norm_nonneg _
    positivity

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
-- pin: norm_f_le_H (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5634)
theorem norm_f_le_H {g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ}
    {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    {C_g C_h : ℝ} (hCg : 0 < C_g) (hCh : 0 < C_h) {N : ℕ}
    (hgle : ∀ x : InfiniteAdeleRing F,
      ‖g (ringEquiv_mixedSpace F x)‖ * ∏ w : InfinitePlace F, (1 + ‖x w‖) ^ N ≤ C_g)
    (hhb : ∀ y, ‖h y‖ ≤ C_h)
    (ϖ : Uniformizers F) (m : HeightOneSpectrum (𝓞 F) → ℕ) (w₀ : InfinitePlace F)
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hbox : ∀ v ∈ S, ∀ y ∈ tsupport h, (y : FiniteAdeleRing (𝓞 F) F) v ∈ ShellSupport.boxAt ϖ v (m v))
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk0 : ∀ v ∈ S, k v = 0)
    {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    ‖(g (ringEquiv_mixedSpace F ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1))
        * h ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2‖
      ≤ ‖H (C_g * C_h) N w₀ ϖ m S ↑u‖ := by
  set x : AdeleRing (𝓞 F) F := ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
  have harch : x.1 = ((u : AdeleRing (𝓞 F) F)).1 := by
    show ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = _
    rw [Units.val_mul]
    show ((unifPow ϖ k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 * _ = _
    rw [unifPow_val_fst, one_mul]
  have hScoord : ∀ v ∈ S, (x.2 : FiniteAdeleRing (𝓞 F) F) v = ((u : AdeleRing (𝓞 F) F)).2 v :=
    fun v hv => unifPow_mul_val_snd_apply_of_mem ϖ hk0 u hv
  have huint : ((u : AdeleRing (𝓞 F) F)) ∈ integralOutside S := by
    have h0 := (unifPow_mul_mem_integralOutside_iff ϖ (k := 0) hu).mpr fun v _ => le_rfl
    have h1 : unifPow ϖ (0 : HeightOneSpectrum (𝓞 F) →₀ ℤ) = 1 := by
      rw [unifPow, Finsupp.prod_zero_index]
    rwa [h1, one_mul] at h0
  have hg1 : ‖g (ringEquiv_mixedSpace F x.1)‖
      ≤ C_g * ∏ w : InfinitePlace F, ((1 + ‖((u : AdeleRing (𝓞 F) F)).1 w‖) ^ (-(N : ℝ)) : ℝ) := by
    rw [harch]
    exact schwartz_le_div_form hgle _
  have hh1 : ‖h x.2‖ ≤ C_h * ∏ v ∈ S, ‖hH ϖ m v (((u : AdeleRing (𝓞 F) F)).2 v)‖ := by
    have := norm_h_le_boxProd hCh hhb ϖ m hbox x.2
    rwa [Finset.prod_congr rfl (fun v hv => by rw [hScoord v hv])] at this
  have hHnorm : ‖H (C_g * C_h) N w₀ ϖ m S ↑u‖
      = (C_g * C_h) * (∏ w : InfinitePlace F, ((1 + ‖((u : AdeleRing (𝓞 F) F)).1 w‖) ^ (-(N : ℝ)) : ℝ))
        * ∏ v ∈ S, ‖hH ϖ m v (((u : AdeleRing (𝓞 F) F)).2 v)‖ := by
    rw [H, Set.indicator_of_mem huint, norm_mul, norm_prod, norm_prod]
    have hfac : ∀ w : InfinitePlace F, ‖gH (C_g * C_h) N w₀ w (((u : AdeleRing (𝓞 F) F)).1 w)‖
        = (if w = w₀ then (C_g * C_h) else 1) * ((1 + ‖((u : AdeleRing (𝓞 F) F)).1 w‖) ^ (-(N : ℝ)) : ℝ) := by
      intro w
      rcases eq_or_ne w w₀ with hw | hw
      · rw [gH, ite_eq_left hw, ite_eq_left hw, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          abs_of_nonneg (by positivity :
            (0:ℝ) ≤ (1 + ‖((u : AdeleRing (𝓞 F) F)).1 w‖) ^ (-(N : ℝ)))]
      · rw [gH, ite_eq_right hw, ite_eq_right hw, norm_mul, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity :
            (0:ℝ) ≤ (1 + ‖((u : AdeleRing (𝓞 F) F)).1 w‖) ^ (-(N : ℝ)))]
    rw [Finset.prod_congr rfl fun w _ => hfac w, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ w₀ (fun _ => C_g * C_h), ite_eq_left (Finset.mem_univ w₀)]
  calc ‖g (ringEquiv_mixedSpace F x.1) * h x.2‖
      = ‖g (ringEquiv_mixedSpace F x.1)‖ * ‖h x.2‖ := norm_mul _ _
    _ ≤ (C_g * ∏ w : InfinitePlace F, ((1 + ‖((u : AdeleRing (𝓞 F) F)).1 w‖) ^ (-(N : ℝ)) : ℝ))
        * (C_h * ∏ v ∈ S, ‖hH ϖ m v (((u : AdeleRing (𝓞 F) F)).2 v)‖) := by
        refine mul_le_mul hg1 hh1 (norm_nonneg _) ?_
        have : (0:ℝ) < ∏ w : InfinitePlace F, ((1 + ‖((u : AdeleRing (𝓞 F) F)).1 w‖) ^ (-(N : ℝ)) : ℝ) :=
          Finset.prod_pos fun w _ => Real.rpow_pos_of_pos (by positivity) _
        positivity
    _ = ‖H (C_g * C_h) N w₀ ϖ m S ↑u‖ := by rw [hHnorm]; ring

end G1Discharge

end NumberField.TateGlobal

end

end Fold_G1Discharge
