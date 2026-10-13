/-
  Infinite-place Borel structures and Haar measures, and the product formula for the
  distributive Haar character of the adèle ring.

  At a real infinite place `w`, `w.Completion` is `ℝ` up to isometry and carries the
  pushforward `placeMeasureReal` of Lebesgue measure; at a complex place it is `ℂ` and
  carries `placeMeasureComplex`. `placeMeasure` records that the scaling factor of
  `x ↦ a * x` is `‖a‖ ^ w.mult`, and `archMeasure` is the product of these measures over
  the infinite places. Gluing the archimedean and finite parts by `adelicMeasure`
  (`infMeasure × finMeasure`, with `finMeasure` normalized on the integral finite adèles
  `refSet`/`zhatCompacts`) gives the additive Haar measure against which the
  Bruhat-transversal integrals are taken. The final section computes
  `distribHaarChar` on the finite idèles as a product of norms.

  Transcribed from `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  lines 146–657 (pinned `aa2d8b3`), keeping the pin namespaces `M4aS4` and
  `NumberField.AdeleRing`. The pin's `import Mathlib` is replaced by specific mathlib
  modules, and the pin's `set_option synthInstance.maxHeartbeats 640000 in` above
  `regular_adelicMeasure` is dropped (the declaration fits the low cap).

  The pin spells the level layer's `integralFiniteAdeles` qualified as
  `AdelicBox.integralFiniteAdeles`; the port homes it in `NumberField.AdelicLevel`, so a
  `-- port-only` alias restores the pin's qualified spelling.
-/
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Complex.Module

set_option autoImplicit false

open MeasureTheory Complex NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum TopologicalSpace Filter
open scoped Pointwise ENNReal NNReal NumberField.AdelicCountability

noncomputable section

namespace NumberField.AdelicBox

section Finite

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

-- port-only: the pin's qualified spelling `AdelicBox.integralFiniteAdeles` for the
-- level layer's home `NumberField.AdelicLevel.integralFiniteAdeles`.
@[reducible] def integralFiniteAdeles : Set (FiniteAdeleRing R K) :=
  AdelicLevel.integralFiniteAdeles R K

end Finite

end NumberField.AdelicBox

namespace M4aS4

-- pin: map_mul_left_volume_real (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:148)
theorem map_mul_left_volume_real {c : ℝ} (hc : c ≠ 0) :
    (volume : Measure ℝ).map (fun x => c * x) = ‖c‖ₑ⁻¹ • volume := by
  have h := Real.map_volume_mul_left hc
  rw [show ((c * ·) : ℝ → ℝ) = fun x => c * x from rfl] at h
  rw [h, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hc), Real.enorm_eq_ofReal_abs]

-- pin: det_restrictScalars_mulLeft_complex (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:154)
theorem det_restrictScalars_mulLeft_complex (c : ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) = normSq c := by
  rw [← LinearMap.det_toMatrix basisOneI]
  have hM : (LinearMap.toMatrix basisOneI basisOneI ((LinearMap.mulLeft ℂ c).restrictScalars ℝ))
      = !![c.re, -c.im; c.im, c.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hM, Matrix.det_fin_two_of]
  simp [normSq_apply]

-- pin: map_mul_left_volume_complex (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:165)
theorem map_mul_left_volume_complex {c : ℂ} (hc : c ≠ 0) :
    (volume : Measure ℂ).map (fun x => c * x) = (‖c‖ₑ ^ 2)⁻¹ • volume := by
  have hdet : LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) ≠ 0 := by
    rw [det_restrictScalars_mulLeft_complex]
    exact (normSq_pos.mpr hc).ne'
  have hfun : (fun x => c * x) = ⇑((LinearMap.mulLeft ℂ c).restrictScalars ℝ) := by
    ext x; simp [LinearMap.mulLeft_apply]
  have habs : |LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ)| = ‖c‖ ^ 2 := by
    rw [det_restrictScalars_mulLeft_complex, abs_of_nonneg (normSq_nonneg c), normSq_eq_norm_sq]
  calc (volume : Measure ℂ).map (fun x => c * x)
      = volume.map ⇑((LinearMap.mulLeft ℂ c).restrictScalars ℝ) := by rw [← hfun]
    _ = ENNReal.ofReal |(LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ))⁻¹| • volume :=
        Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet
    _ = (‖c‖ₑ ^ 2)⁻¹ • volume := by
        rw [abs_inv, habs, ENNReal.ofReal_inv_of_pos (pow_pos (norm_pos_iff.mpr hc) 2),
          ENNReal.ofReal_pow (norm_nonneg c), ofReal_norm]

-- pin: volume_image_mul_left_real (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:182)
theorem volume_image_mul_left_real {c : ℝ} (hc : c ≠ 0) {S : Set ℝ} (hS : MeasurableSet S) :
    volume ((fun x => c * x) '' S) = ‖c‖ₑ * volume S := by
  have himg : (fun x => c * x) '' S = (fun x => c⁻¹ * x) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_mul_cancel_left₀ hc] using hx
    · intro hy
      exact ⟨c⁻¹ * y, hy, by field_simp⟩
  rw [himg, ← Measure.map_apply (measurable_const_mul _) hS,
    map_mul_left_volume_real (inv_ne_zero hc)]
  simp [Measure.smul_apply, smul_eq_mul, enorm_inv, hc]

-- pin: volume_image_mul_left_complex (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:195)
theorem volume_image_mul_left_complex {c : ℂ} (hc : c ≠ 0) {S : Set ℂ} (hS : MeasurableSet S) :
    volume ((fun x => c * x) '' S) = ‖c‖ₑ ^ 2 * volume S := by
  have himg : (fun x => c * x) '' S = (fun x => c⁻¹ * x) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_mul_cancel_left₀ hc] using hx
    · intro hy
      exact ⟨c⁻¹ * y, hy, by field_simp⟩
  rw [himg, ← Measure.map_apply (measurable_const_mul _) hS,
    map_mul_left_volume_complex (inv_ne_zero hc)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [enorm_inv hc, ENNReal.inv_pow, inv_inv]

variable (F : Type) [Field F] [NumberField F]

-- pin: placeBorel (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:211)
@[reducible] def placeBorel (w : InfinitePlace F) : MeasurableSpace (w.Completion) := borel _

attribute [local instance] placeBorel

-- pin: placeBorelSpace (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:215)
scoped instance placeBorelSpace (w : InfinitePlace F) : BorelSpace (w.Completion) := ⟨rfl⟩

variable {F}

-- pin: placeMeasureReal (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:219)
def placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) : Measure (w.Completion) :=
  (volume : Measure ℝ).map (Completion.ringEquivRealOfIsReal hw).symm

-- pin: placeMeasureComplex (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:222)
def placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) : Measure (w.Completion) :=
  (volume : Measure ℂ).map (Completion.ringEquivComplexOfIsComplex hw).symm

variable (F) in
open Classical in

-- pin: placeMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:228)
def placeMeasure (w : InfinitePlace F) : Measure (w.Completion) :=
  if hw : w.IsReal then placeMeasureReal hw
  else placeMeasureComplex (not_isReal_iff_isComplex.mp hw)

-- pin: isAddHaarMeasure_placeMeasureReal (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:232)
scoped instance isAddHaarMeasure_placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) :
    (placeMeasureReal hw).IsAddHaarMeasure := by
  unfold placeMeasureReal
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivRealOfIsReal hw).symm.continuous
    (Completion.isometryEquivRealOfIsReal hw).continuous

-- pin: isAddHaarMeasure_placeMeasureComplex (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:240)
scoped instance isAddHaarMeasure_placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) :
    (placeMeasureComplex hw).IsAddHaarMeasure := by
  unfold placeMeasureComplex
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivComplexOfIsComplex hw).symm : ℂ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous
    (Completion.isometryEquivComplexOfIsComplex hw).continuous

-- pin: secondCountable_completion (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:248)
scoped instance secondCountable_completion (w : InfinitePlace F) :
    SecondCountableTopology (w.Completion) := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact (Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isEmbedding.secondCountableTopology
  · exact (Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isEmbedding.secondCountableTopology

omit [NumberField F] in

-- pin: placeMeasureReal_image_mul (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:256)
theorem placeMeasureReal_image_mul {w : InfinitePlace F} (hw : w.IsReal)
    {a : w.Completion} (ha : a ≠ 0) {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasureReal hw ((fun x => a * x) '' S) = ‖a‖ₑ * placeMeasureReal hw S := by
  set e := Completion.ringEquivRealOfIsReal hw with he
  have hea : e a ≠ 0 := fun h => ha (by simpa using congrArg e.symm h)
  have hmeas_symm : Measurable (⇑e.symm) :=
    (Completion.isometryEquivRealOfIsReal hw).symm.continuous.measurable
  have himgS : MeasurableSet ((fun x => a * x) '' S) := by
    have heq : (fun x => a * x) '' S = (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv '' S := rfl
    rw [heq, MeasurableEquiv.measurableSet_image]
    exact hS
  have hpre : ⇑e.symm ⁻¹' ((fun x => a * x) '' S) = (fun r => e a * r) '' (⇑e.symm ⁻¹' S) := by
    ext r
    constructor
    · rintro ⟨s, hs, hsr⟩
      refine ⟨e s, by simpa using hs, ?_⟩
      have := congrArg e hsr
      simpa [map_mul] using this
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, ht, by simp [map_mul]⟩
  have hnorm : ‖e a‖ = ‖a‖ := by
    have h0 : e (0 : w.Completion) = 0 := map_zero e
    calc ‖e a‖ = dist (e a) (e 0) := by rw [h0, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbeddingOfIsReal hw).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  have henorm : ‖e a‖ₑ = ‖a‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, hnorm]
  unfold placeMeasureReal
  rw [Measure.map_apply hmeas_symm himgS, Measure.map_apply hmeas_symm hS, hpre,
    volume_image_mul_left_real hea (hmeas_symm hS), henorm]

omit [NumberField F] in

-- pin: placeMeasureComplex_image_mul (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:289)
theorem placeMeasureComplex_image_mul {w : InfinitePlace F} (hw : w.IsComplex)
    {a : w.Completion} (ha : a ≠ 0) {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasureComplex hw ((fun x => a * x) '' S) = ‖a‖ₑ ^ 2 * placeMeasureComplex hw S := by
  set e := Completion.ringEquivComplexOfIsComplex hw with he
  have hea : e a ≠ 0 := fun h => ha (by simpa using congrArg e.symm h)
  have hmeas_symm : Measurable (⇑e.symm) :=
    (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.measurable
  have himgS : MeasurableSet ((fun x => a * x) '' S) := by
    have heq : (fun x => a * x) '' S = (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv '' S := rfl
    rw [heq, MeasurableEquiv.measurableSet_image]
    exact hS
  have hpre : ⇑e.symm ⁻¹' ((fun x => a * x) '' S) = (fun r => e a * r) '' (⇑e.symm ⁻¹' S) := by
    ext r
    constructor
    · rintro ⟨s, hs, hsr⟩
      refine ⟨e s, by simpa using hs, ?_⟩
      have := congrArg e hsr
      simpa [map_mul] using this
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, ht, by simp [map_mul]⟩
  have hnorm : ‖e a‖ = ‖a‖ := by
    have h0 : e (0 : w.Completion) = 0 := map_zero e
    calc ‖e a‖ = dist (e a) (e 0) := by rw [h0, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbedding w).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  have henorm : ‖e a‖ₑ = ‖a‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, hnorm]
  unfold placeMeasureComplex
  rw [Measure.map_apply hmeas_symm himgS, Measure.map_apply hmeas_symm hS, hpre,
    volume_image_mul_left_complex hea (hmeas_symm hS), henorm]

omit [NumberField F] in

-- pin: placeMeasure_image_mul (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:322)
theorem placeMeasure_image_mul (w : InfinitePlace F) {a : w.Completion} (ha : a ≠ 0)
    {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasure F w ((fun x => a * x) '' S) = ‖a‖ₑ ^ w.mult * placeMeasure F w S := by
  unfold placeMeasure
  split
  · next hw =>
    rw [placeMeasureReal_image_mul hw ha hS,
      show w.mult = 1 from by simp [mult, hw], pow_one]
  · next hw =>
    rw [placeMeasureComplex_image_mul (not_isReal_iff_isComplex.mp hw) ha hS,
      show w.mult = 2 from by simp [mult, hw]]

-- pin: isAddHaarMeasure_placeMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:334)
scoped instance isAddHaarMeasure_placeMeasure (w : InfinitePlace F) :
    (placeMeasure F w).IsAddHaarMeasure := by
  unfold placeMeasure
  split
  · exact isAddHaarMeasure_placeMeasureReal _
  · exact isAddHaarMeasure_placeMeasureComplex _

-- pin: sigmaCompact_completion (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:341)
scoped instance sigmaCompact_completion (w : InfinitePlace F) : SigmaCompactSpace (w.Completion) :=
  inferInstance

-- pin: sigmaFinite_placeMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:344)
scoped instance sigmaFinite_placeMeasure (w : InfinitePlace F) : SigmaFinite (placeMeasure F w) :=
  inferInstance

variable (F) in

-- pin: archMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:349)
def archMeasure : Measure ((w : InfinitePlace F) → w.Completion) :=
  Measure.pi (fun w => placeMeasure F w)

-- pin: isFiniteMeasureOnCompacts_archMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:352)
scoped instance isFiniteMeasureOnCompacts_archMeasure : IsFiniteMeasureOnCompacts (archMeasure F) := by
  unfold archMeasure; infer_instance

-- pin: isOpenPosMeasure_archMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:355)
scoped instance isOpenPosMeasure_archMeasure : (archMeasure F).IsOpenPosMeasure := by
  unfold archMeasure; infer_instance

-- pin: sigmaFinite_archMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:358)
scoped instance sigmaFinite_archMeasure : SigmaFinite (archMeasure F) := by
  unfold archMeasure; infer_instance

-- pin: isAddLeftInvariant_archMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:361)
scoped instance isAddLeftInvariant_archMeasure : (archMeasure F).IsAddLeftInvariant := by
  constructor
  intro a
  have hmeas : Measurable (fun x : (w : InfinitePlace F) → w.Completion => a + x) :=
    measurable_const.add measurable_id
  refine Eq.symm (Measure.pi_eq fun B hB => ?_)
  have hpre : (fun x : (w : InfinitePlace F) → w.Completion => a + x) ⁻¹' Set.pi Set.univ B
      = Set.pi Set.univ (fun w => (fun t => a w + t) ⁻¹' B w) := by
    ext x
    simp [Set.mem_pi, Pi.add_apply]
  unfold archMeasure
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hB), hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact measure_preimage_add (placeMeasure F w) (a w) (B w)

-- pin: isAddHaarMeasure_archMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:376)
scoped instance isAddHaarMeasure_archMeasure : (archMeasure F).IsAddHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance
    toIsAddLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }

omit [NumberField F] in

-- pin: image_mul_pi (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:383)
theorem image_mul_pi (a : (w : InfinitePlace F) → w.Completion)
    (B : (w : InfinitePlace F) → Set (w.Completion)) :
    (fun x => a * x) '' Set.pi Set.univ B
      = Set.pi Set.univ (fun w => (fun t => a w * t) '' B w) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro w _
    exact ⟨y w, hy w (Set.mem_univ w), rfl⟩
  · intro hx
    choose b hb hab using fun w => hx w (Set.mem_univ w)
    refine ⟨fun w => b w, fun w _ => hb w, ?_⟩
    funext w
    exact hab w

-- pin: archMeasure_image_mul_pi (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:398)
theorem archMeasure_image_mul_pi (a : (w : InfinitePlace F) → w.Completion)
    (ha : ∀ w, a w ≠ 0) (B : (w : InfinitePlace F) → Set (w.Completion))
    (hB : ∀ w, MeasurableSet (B w)) :
    archMeasure F ((fun x => a * x) '' Set.pi Set.univ B)
      = (∏ w, ‖a w‖ₑ ^ w.mult) * archMeasure F (Set.pi Set.univ B) := by
  rw [image_mul_pi a B]
  unfold archMeasure
  rw [Measure.pi_pi, Measure.pi_pi]
  calc ∏ w, placeMeasure F w ((fun t => a w * t) '' B w)
      = ∏ w, (‖a w‖ₑ ^ w.mult * placeMeasure F w (B w)) := by
        refine Finset.prod_congr rfl fun w _ => ?_
        exact placeMeasure_image_mul w (ha w) (hB w)
    _ = (∏ w, ‖a w‖ₑ ^ w.mult) * ∏ w, placeMeasure F w (B w) := Finset.prod_mul_distrib

-- pin: properSpace_completion₀ (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:412)
scoped instance properSpace_completion₀ (w : InfinitePlace F) : ProperSpace (w.Completion) :=
  AdelicBox.properSpace_completion F w

omit [NumberField F] in
-- pin: placeMeasure_pos_closedBall (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:416)
theorem placeMeasure_pos_closedBall (w : InfinitePlace F) :
    0 < placeMeasure F w (Metric.closedBall (0 : w.Completion) 1) :=
  ((Metric.isOpen_ball (x := (0 : w.Completion)) (ε := 1)).measure_pos (placeMeasure F w)
    (Metric.nonempty_ball.mpr one_pos)).trans_le
    (measure_mono Metric.ball_subset_closedBall)

omit [NumberField F] in
-- pin: placeMeasure_closedBall_lt_top (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:423)
theorem placeMeasure_closedBall_lt_top (w : InfinitePlace F) :
    placeMeasure F w (Metric.closedBall (0 : w.Completion) 1) < ⊤ :=
  (isCompact_closedBall (0 : w.Completion) 1).measure_lt_top

variable (F) in
-- pin: infMS (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:428)
@[reducible] def infMS : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))

attribute [local instance] infMS

-- pin: infBorelSpace (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:433)
scoped instance infBorelSpace : BorelSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))

variable (F) in
-- pin: finBorel (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:437)
@[reducible] def finBorel : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _

attribute [local instance] finBorel

-- pin: finBorelSpace (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:441)
scoped instance finBorelSpace : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

variable (F) in
-- pin: adeleMS (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:444)
@[reducible] def adeleMS : MeasurableSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

attribute [local instance] adeleMS

-- pin: adeleBorelSpaceProd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:449)
scoped instance adeleBorelSpaceProd : BorelSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (BorelSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

-- pin: secondCountable_infiniteAdeles (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:452)
scoped instance secondCountable_infiniteAdeles : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

-- pin: secondCountable_adeleRing (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:455)
scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

variable (F) in

-- pin: zhatCompacts (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:460)
def zhatCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 F) F) where
  carrier := AdelicBox.integralFiniteAdeles (𝓞 F) F
  isCompact' := AdelicBox.isCompact_integralFiniteAdeles F
  interior_nonempty' := by
    rw [(AdelicBox.isOpen_integralFiniteAdeles F).interior_eq]
    exact ⟨0, fun v => zero_mem _⟩

variable (F) in

-- pin: finMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:469)
def finMeasure : Measure (FiniteAdeleRing (𝓞 F) F) :=
  Measure.addHaarMeasure (zhatCompacts F)

-- pin: isAddHaarMeasure_finMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:472)
scoped instance isAddHaarMeasure_finMeasure : (finMeasure F).IsAddHaarMeasure := by
  unfold finMeasure; infer_instance

-- pin: sigmaFinite_finMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:475)
scoped instance sigmaFinite_finMeasure : SigmaFinite (finMeasure F) := by
  unfold finMeasure; infer_instance

variable (F) in

-- pin: infMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:480)
def infMeasure : Measure (InfiniteAdeleRing F) := archMeasure F

-- pin: isAddHaarMeasure_infMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:482)
scoped instance isAddHaarMeasure_infMeasure : (infMeasure F).IsAddHaarMeasure :=
  inferInstanceAs ((archMeasure F).IsAddHaarMeasure)

-- pin: sigmaFinite_infMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:485)
scoped instance sigmaFinite_infMeasure : SigmaFinite (infMeasure F) :=
  inferInstanceAs (SigmaFinite (archMeasure F))

variable (F) in
-- pin: adelicMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:489)
def adelicMeasure : Measure (AdeleRing (𝓞 F) F) :=
  (infMeasure F).prod (finMeasure F)

-- pin: isAddHaarMeasure_adelicMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:492)
scoped instance isAddHaarMeasure_adelicMeasure : (adelicMeasure F).IsAddHaarMeasure :=
  inferInstanceAs
    ((((infMeasure F).prod (finMeasure F)) :
      Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)).IsAddHaarMeasure)

-- pin: sigmaFinite_adelicMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:497)
scoped instance sigmaFinite_adelicMeasure : SigmaFinite (adelicMeasure F) :=
  inferInstanceAs (SigmaFinite
    (((infMeasure F).prod (finMeasure F)) :
      Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)))

variable (F) in

-- pin: refSet (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:504)
def refSet : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
  (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
    (AdelicBox.integralFiniteAdeles (𝓞 F) F)

variable (F) in
-- pin: isCompact_refSet (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:509)
theorem isCompact_refSet : IsCompact (refSet F) :=
  (isCompact_univ_pi fun w => isCompact_closedBall (0 : w.Completion) 1).prod
    (AdelicBox.isCompact_integralFiniteAdeles F)

variable (F) in
-- pin: interior_refSet_nonempty (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:514)
theorem interior_refSet_nonempty : (interior (refSet F)).Nonempty := by
  have hopen : IsOpen ((Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)
      ×ˢ (AdelicBox.integralFiniteAdeles (𝓞 F) F)) :=
    (isOpen_set_pi Set.finite_univ fun w _ => Metric.isOpen_ball).prod
      (AdelicBox.isOpen_integralFiniteAdeles F)
  have hsub : ((Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)
      ×ˢ (AdelicBox.integralFiniteAdeles (𝓞 F) F)) ⊆ refSet F :=
    Set.prod_mono (Set.pi_mono fun w _ => Metric.ball_subset_closedBall) le_rfl
  have hmem : ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F)) ∈
      ((Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)
        ×ˢ (AdelicBox.integralFiniteAdeles (𝓞 F) F)) := by
    refine Set.mem_prod.mpr ⟨fun w _ => ?_, fun v => zero_mem _⟩
    exact Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)
  exact ⟨_, interior_maximal hsub hopen hmem⟩

variable (F) in
-- pin: adelicMeasure_refSet_ne_top (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:530)
theorem adelicMeasure_refSet_ne_top :
    (archMeasure F).prod (finMeasure F) (refSet F) ≠ ⊤ := by
  unfold refSet
  rw [Measure.prod_prod]
  exact ENNReal.mul_ne_top
    (by
      show archMeasure F _ ≠ ⊤
      unfold archMeasure
      rw [Measure.pi_pi]
      exact (ENNReal.prod_lt_top fun w _ => placeMeasure_closedBall_lt_top w).ne)
    ((AdelicBox.isCompact_integralFiniteAdeles F).measure_lt_top).ne

-- pin: regular_adelicMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:543)
scoped instance regular_adelicMeasure : (adelicMeasure F).Regular :=
  Measure.regular_of_isAddLeftInvariant (μ := adelicMeasure F)
    (K := refSet F) (isCompact_refSet F) (interior_refSet_nonempty F)
    (adelicMeasure_refSet_ne_top F)

variable (F) in
-- pin: finMeasure_zhat (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:549)
theorem finMeasure_zhat : finMeasure F (AdelicBox.integralFiniteAdeles (𝓞 F) F) = 1 :=
  Measure.addHaarMeasure_self (K₀ := zhatCompacts F)

variable (F) in
-- pin: adelicMeasure_refSet_ne_zero (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:553)
theorem adelicMeasure_refSet_ne_zero :
    (archMeasure F).prod (finMeasure F) (refSet F) ≠ 0 := by
  unfold refSet
  rw [Measure.prod_prod]
  refine mul_ne_zero ?_ ?_
  · show archMeasure F _ ≠ 0
    unfold archMeasure
    rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun w _ => (placeMeasure_pos_closedBall w).ne'
  · rw [finMeasure_zhat]
    exact one_ne_zero

-- pin: arch_component_ne_zero (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:565)
theorem arch_component_ne_zero (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (a : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  intro h0
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) a.mul_inv
  rw [show ((a : AdeleRing (𝓞 F) F) * (↑a⁻¹ : AdeleRing (𝓞 F) F)).1 w
      = (a : AdeleRing (𝓞 F) F).1 w * (↑a⁻¹ : AdeleRing (𝓞 F) F).1 w from rfl, h0, zero_mul] at h
  exact zero_ne_one h

-- pin: distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:573)
theorem distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
    (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : (a : AdeleRing (𝓞 F) F).2 = 1) :
    (distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ)
      = ∏ w : InfinitePlace F, ‖(a : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
  classical

  set aArch : (w : InfinitePlace F) → w.Completion :=
    (show (w : InfinitePlace F) → w.Completion from (a : AdeleRing (𝓞 F) F).1) with haArch
  have haw : ∀ w, aArch w ≠ 0 := fun w => arch_component_ne_zero a w
  have hs₀ : adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) ≠ 0 :=
    adelicMeasure_refSet_ne_zero F
  have hsfin : adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) ≠ ⊤ :=
    adelicMeasure_refSet_ne_top F

  have hsplit : (a • (show Set (AdeleRing (𝓞 F) F) from refSet F))
      = (show Set (AdeleRing (𝓞 F) F) from
          (((fun x => aArch * x) ''
            (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)) ×ˢ
            (AdelicBox.integralFiniteAdeles (𝓞 F) F))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨(show InfiniteAdeleRing F from y.1), hy.1, rfl⟩, ?_⟩
      show ((a : AdeleRing (𝓞 F) F) * y).2 ∈ _
      rw [show ((a : AdeleRing (𝓞 F) F) * y).2 = (a : AdeleRing (𝓞 F) F).2 * y.2 from rfl, ha,
        one_mul]
      exact hy.2
    · rintro ⟨⟨y1, hy1, hxy1⟩, hx2⟩
      refine ⟨(show AdeleRing (𝓞 F) F from ((show InfiniteAdeleRing F from y1), x.2)),
        ⟨hy1, hx2⟩, Prod.ext ?_ ?_⟩
      · show (show InfiniteAdeleRing F from aArch * y1) = x.1
        exact hxy1
      · show (a : AdeleRing (𝓞 F) F).2 * x.2 = x.2
        rw [ha, one_mul]

  have harch : archMeasure F ((fun x => aArch * x) ''
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1))
      = (∏ w, ‖aArch w‖ₑ ^ w.mult) * archMeasure F
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) :=
    archMeasure_image_mul_pi aArch haw
      (fun w => Metric.closedBall (0 : w.Completion) 1) (fun w => measurableSet_closedBall)
  have hcompute : (archMeasure F).prod (finMeasure F)
      ((((fun x => aArch * x) ''
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)) ×ˢ
        (AdelicBox.integralFiniteAdeles (𝓞 F) F)))
      = ((∏ w : InfinitePlace F, ‖aArch w‖₊ ^ w.mult : ℝ≥0) : ℝ≥0∞)
        * (archMeasure F).prod (finMeasure F) (refSet F) := by
    unfold refSet
    rw [Measure.prod_prod, Measure.prod_prod, harch, mul_assoc]
    congr 1
    rw [ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ENNReal.coe_pow, enorm_eq_nnnorm]

  have hμgs : adelicMeasure F (a • (show Set (AdeleRing (𝓞 F) F) from refSet F))
      = ((∏ w : InfinitePlace F, ‖aArch w‖₊ ^ w.mult : ℝ≥0) : ℝ≥0∞)
        * adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) := by
    rw [hsplit]
    exact hcompute
  have key := distribHaarChar_eq_of_measure_smul_eq_mul (μ := adelicMeasure F)
    (s := (show Set (AdeleRing (𝓞 F) F) from refSet F)) (g := a) hs₀ hsfin hμgs
  rw [key]
  push_cast [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  rfl

end M4aS4

namespace NumberField

namespace AdeleRing

-- pin: distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one_impl (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:648)
theorem distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one_impl
    (F : Type) [Field F] [NumberField F]
    (a : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (ha : (a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).2 = 1) :
    (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) a : ℝ)
      = ∏ w : NumberField.InfinitePlace F,
          ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).1 w‖ ^ w.mult :=
  M4aS4.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one a ha

end NumberField.AdeleRing

end
