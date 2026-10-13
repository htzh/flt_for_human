/-
  The archimedean multiplicative Haar measures.

  `ArchMulHaarReal`: `distribHaarChar ℝ t = ‖t‖₊`.
  `ArchMulHaarComplex`: `distribHaarChar ℂ t = ‖t‖₊ ^ 2`, via the determinant of
  `Algebra.lmul ℝ ℂ c`.
  `ArchMulHaarCompletion`: for `w : InfinitePlace F`, transfer the character along
  the ring equivalences `w.Completion ≃+* ℝ`/`≃+* ℂ`
  (`distribHaarChar_eq_of_ringEquiv`), identify it with `‖·‖₊ ^ d` for `d = 1, 2`,
  and build `mulHaarCompletion w μ` as a Haar measure on `(w.Completion)ˣ`
  (`isHaarMeasure_mulHaarCompletion`, `_of_isReal`, `_of_isComplex`, `_total`).

  Transcribed from the pin's `M4aLocalCFT.ArchMulHaarReal`/`ArchMulHaarComplex`/
  `ArchMulHaarCompletion` blocks, declared lines 2142–2647 of file A, pinned
  `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Chapter-prefix rename (work order §3.1): `M4aLocalCFT.ArchMulHaarReal` etc.
  become `NumberField.TateGlobal.ArchMulHaarReal` etc.; the three sub-namespaces
  are kept separate (the archimedean `measure_units_smul`/`mulMeasure_units_smul`/
  `image_val_subset_compl_zero` are a different, independent block from
  `MulHaarFromAdditive`).

  Build notes: the pin's `p2m_*` scaffolding is dropped; `open
  NumberField.InfinitePlace`/`NumberField.InfinitePlace.Completion` replace the
  pin's `p2m_open` of those namespaces.  No file-wide option beyond
  `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.MulHaar

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open MeasureTheory Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise NumberField.TateGlobal

section Fold_ArchMulHaar

noncomputable section

namespace NumberField

namespace TateGlobal

namespace ArchMulHaarReal

variable (μ : Measure ℝ) [μ.IsAddHaarMeasure]

-- pin: distribHaarChar_real (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2142)
theorem distribHaarChar_real (t : ℝˣ) : distribHaarChar ℝ t = ‖(t : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := Icc (0 : ℝ) 1)
    (by simp [Real.volume_Icc]) (by simp [Real.volume_Icc]) ?_
  have hset : t • Icc (0 : ℝ) 1 = (t : ℝ) • Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def]
  rw [hset, Measure.addHaar_smul volume (t : ℝ) (Icc (0 : ℝ) 1),
    Module.finrank_self, pow_one, Real.volume_Icc]
  rw [← Real.norm_eq_abs, ofReal_norm]
  rfl

variable [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]


end ArchMulHaarReal

namespace ArchMulHaarComplex

-- pin: det_lmul_complex (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2188)
theorem det_lmul_complex (c : ℂ) :
    LinearMap.det (Algebra.lmul ℝ ℂ c) = Complex.normSq c := by
  have hap : ∀ x : ℂ, (Algebra.lmul ℝ ℂ c) x = c * x := fun _ => rfl
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, hap]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

-- pin: smul_set_eq_image_lmul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2196)
theorem smul_set_eq_image_lmul (c : ℂ) (s : Set ℂ) :
    c • s = (Algebra.lmul ℝ ℂ c) '' s := by
  ext x
  simp [Set.mem_smul_set]

-- pin: measure_smul_complex (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2201)
theorem measure_smul_complex (μ : Measure ℂ) [μ.IsAddHaarMeasure] (c : ℂ)
    (s : Set ℂ) :
    μ (c • s) = (‖c‖₊ ^ 2 : ℝ≥0∞) * μ s := by
  rw [smul_set_eq_image_lmul, Measure.addHaar_image_linearMap μ _ s, det_lmul_complex]
  congr 1
  rw [abs_of_nonneg (Complex.normSq_nonneg c), ← Complex.norm_mul_self_eq_normSq,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm, sq]
  rfl

-- pin: distribHaarChar_complex (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2210)
theorem distribHaarChar_complex (t : ℂˣ) : distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume)
    (s := Metric.ball (0 : ℂ) 1)
    (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos)) measure_ball_lt_top.ne ?_
  have hset : t • Metric.ball (0 : ℂ) 1 = ((t : ℂ)) • Metric.ball (0 : ℂ) 1 := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def]
  rw [hset, measure_smul_complex volume (t : ℂ)]
  norm_cast

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure]

variable [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]


end ArchMulHaarComplex

namespace ArchMulHaarCompletion

set_option linter.style.haveILetI false in
-- pin: distribHaarChar_eq_of_ringEquiv (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2257)
-- The `letI`/`haveI` supply the `IsAddHaarMeasure`/`Regular`
-- instances of the pulled-back measure `μK`.
theorem distribHaarChar_eq_of_ringEquiv {K L : Type} [Field K] [Field L]
    [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace L] [IsTopologicalRing L] [LocallyCompactSpace L]
    [MeasurableSpace L] [BorelSpace L]
    (Φ : K ≃+* L) (hΦ : Continuous Φ) (hΦs : Continuous Φ.symm)
    (μL : Measure L) [μL.IsAddHaarMeasure] [μL.Regular]
    {B : Set L} (hB : MeasurableSet B) (hB0 : μL B ≠ 0) (hBt : μL B ≠ ∞)
    (t : Kˣ) :
    distribHaarChar K t = distribHaarChar L (Units.map (Φ : K →+* L).toMonoidHom t) := by
  set e : L ≃+ K := Φ.symm.toAddEquiv with he
  have hecont : Continuous e := hΦs
  have hescont : Continuous e.symm := hΦ
  letI μK : Measure K := μL.map e
  haveI : μK.IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μL e hecont hescont
  haveI : μK.Regular :=
    Measure.Regular.map (⟨e.toEquiv, hecont, hescont⟩ : L ≃ₜ K)
  have key : ∀ (S : Set L), MeasurableSet S → μK (⇑Φ ⁻¹' S) = μL S := by
    intro S hS
    have hpre : ⇑e ⁻¹' (⇑Φ ⁻¹' S) = S := by
      ext x
      simp only [Set.mem_preimage, he]
      rw [show (Φ.symm.toAddEquiv x : K) = Φ.symm x from rfl, RingEquiv.apply_symm_apply]
    rw [show μK = μL.map e from rfl,
      Measure.map_apply hecont.measurable (hΦ.measurable hS), hpre]
  have hsmeas : MeasurableSet (⇑Φ ⁻¹' B) := hΦ.measurable hB
  have hs0 : μK (⇑Φ ⁻¹' B) ≠ 0 := by rw [key B hB]; exact hB0
  have hst : μK (⇑Φ ⁻¹' B) ≠ ∞ := by rw [key B hB]; exact hBt
  have hcomm : ∀ (u : Kˣ) (y : K),
      Φ ((u : K) * y) = ((Units.map (Φ : K →+* L).toMonoidHom u : Lˣ) : L) * Φ y := by
    intro u y
    rw [map_mul]
    rfl
  have hts : (t • (⇑Φ ⁻¹' B) : Set K)
      = ⇑Φ ⁻¹' ((Units.map (Φ : K →+* L).toMonoidHom t) • B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Set.mem_preimage.mpr ?_
      have hfwd : Φ (t • y) = (Units.map (Φ : K →+* L).toMonoidHom t) • Φ y := by
        rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul]
        exact hcomm t y
      show Φ (t • y) ∈ (Units.map (Φ : K →+* L).toMonoidHom t) • B
      rw [hfwd]
      exact Set.smul_mem_smul_set hy
    · intro hx
      have hx' : Φ x ∈ (Units.map (Φ : K →+* L).toMonoidHom t) • B := Set.mem_preimage.mp hx
      refine ⟨(t⁻¹ : Kˣ) • x, Set.mem_preimage.mpr ?_, smul_inv_smul t x⟩
      have hbwd : Φ ((t⁻¹ : Kˣ) • x)
          = ((Units.map (Φ : K →+* L).toMonoidHom t)⁻¹ : Lˣ) • Φ x := by
        rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, hcomm t⁻¹ x, map_inv]
      rw [hbwd]
      exact Set.mem_smul_set_iff_inv_smul_mem.mp hx'
  have hmul : μK (t • (⇑Φ ⁻¹' B))
      = distribHaarChar L (Units.map (Φ : K →+* L).toMonoidHom t) * μK (⇑Φ ⁻¹' B) := by
    have hBs : MeasurableSet ((Units.map (Φ : K →+* L).toMonoidHom t) • B) := by
      have : ((Units.map (Φ : K →+* L).toMonoidHom t) • B : Set L)
          = (fun y => (((Units.map (Φ : K →+* L).toMonoidHom t)⁻¹ : Lˣ) : L) * y) ⁻¹' B := by
        ext y
        rw [Set.mem_smul_set_iff_inv_smul_mem]
        rfl
      rw [this]
      exact hB.preimage (measurable_const_mul _)
    rw [hts, key _ hBs, key B hB, ← distribHaarChar_mul (μ := μL)]
  exact distribHaarChar_eq_of_measure_smul_eq_mul hs0 hst hmul

variable {F : Type} [Field F]

-- pin: nnnorm_ringEquivReal (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2325)
theorem nnnorm_ringEquivReal {w : InfinitePlace F} (hv : w.IsReal)
    (x : w.Completion) : ‖ringEquivRealOfIsReal hv x‖₊ = ‖x‖₊ := by
  ext
  exact (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) x

-- pin: nnnorm_ringEquivComplex (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2330)
theorem nnnorm_ringEquivComplex {w : InfinitePlace F} (hv : w.IsComplex)
    (x : w.Completion) : ‖ringEquivComplexOfIsComplex hv x‖₊ = ‖x‖₊ := by
  ext
  exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

variable (w : InfinitePlace F) [MeasurableSpace w.Completion] [BorelSpace w.Completion]

-- pin: distribHaarChar_completion_of_isReal (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2337)
theorem distribHaarChar_completion_of_isReal (hv : w.IsReal) (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ 1 := by
  have hiso := isometry_extensionEmbeddingOfIsReal hv
  have hcont : Continuous (ringEquivRealOfIsReal hv) := hiso.continuous
  have hconts : Continuous (ringEquivRealOfIsReal hv).symm := by
    have : Isometry (isometryEquivRealOfIsReal hv).symm := (isometryEquivRealOfIsReal hv).symm.isometry
    exact this.continuous
  rw [distribHaarChar_eq_of_ringEquiv (ringEquivRealOfIsReal hv) hcont hconts volume
    (B := Metric.ball 0 1) measurableSet_ball
    ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr one_pos)).ne')
    measure_ball_lt_top.ne t, ArchMulHaarReal.distribHaarChar_real, pow_one]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact nnnorm_ringEquivReal hv _

-- pin: distribHaarChar_completion_of_isComplex (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2351)
theorem distribHaarChar_completion_of_isComplex (hv : w.IsComplex) (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ 2 := by
  have hcont : Continuous (ringEquivComplexOfIsComplex hv) := (isometry_extensionEmbedding w).continuous
  have hconts : Continuous (ringEquivComplexOfIsComplex hv).symm := by
    have : Isometry (isometryEquivComplexOfIsComplex hv).symm :=
      (isometryEquivComplexOfIsComplex hv).symm.isometry
    exact this.continuous
  rw [distribHaarChar_eq_of_ringEquiv (ringEquivComplexOfIsComplex hv) hcont hconts volume
    (B := Metric.ball 0 1) measurableSet_ball
    ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr one_pos)).ne')
    measure_ball_lt_top.ne t, ArchMulHaarComplex.distribHaarChar_complex]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact congrArg (fun a => a ^ 2) (nnnorm_ringEquivComplex hv _)

-- pin: modulus_completion_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2366)
omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem modulus_completion_eq (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    (a : w.Completion) : modulus a = ‖a‖₊ ^ d := by
  by_cases h : a = 0
  · subst h
    rw [modulus_zero, nnnorm_zero, zero_pow hd]
  · rw [modulus_of_ne_zero h, hΔ (Units.mk0 a h)]
    rfl

variable {μ : Measure w.Completion} [μ.IsAddHaarMeasure] [μ.Regular]

-- pin: mulMeasure_completion_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2378)
omit [BorelSpace w.Completion] [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulMeasure_completion_eq (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    mulMeasure μ = (μ.restrict {0}ᶜ).withDensity fun x => ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ := by
  rw [mulMeasure]
  congr 1
  funext x
  rw [modulus_completion_eq w d hd hΔ]
  norm_cast

-- pin: measurable_nnnorm_pow_inv (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2387)
theorem measurable_nnnorm_pow_inv (d : ℕ) :
    Measurable fun x : w.Completion => ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ :=
  ((measurable_nnnorm.coe_nnreal_ennreal).pow_const d).inv

-- pin: units_smul_set_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2392)
omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem units_smul_set_eq (t : (w.Completion)ˣ) (E : Set w.Completion) :
    (t • E : Set w.Completion) = (t : w.Completion) • E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

set_option linter.overlappingInstances false in
-- pin: measure_units_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2401)
-- The pin's statement keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`.
theorem measure_units_smul (d : ℕ)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    (t : (w.Completion)ˣ) (E : Set w.Completion) :
    μ ((t : w.Completion) • E) = (‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞) * μ E := by
  rw [← units_smul_set_eq, ← distribHaarChar_mul (μ := μ) t E, hΔ t]
  norm_cast

set_option linter.overlappingInstances false in
-- pin: map_units_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2408)
-- The pin's statement keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`.
theorem map_units_smul (d : ℕ) (_hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    (t : (w.Completion)ˣ) :
    Measure.map ((t : w.Completion) • ·) μ = ((‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞))⁻¹ • μ := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_const_smul _) hA, Measure.smul_apply, smul_eq_mul]
  have hpre : ((t : w.Completion) • ·) ⁻¹' A = ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • A := by
    ext x
    constructor
    · intro hx
      refine ⟨(t : w.Completion) • x, hx, ?_⟩
      show ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • (t : w.Completion) • x = x
      rw [smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero t), one_smul]
    · rintro ⟨y, hy, rfl⟩
      show (t : w.Completion) • ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • y ∈ A
      rw [smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero t), one_smul]
      exact hy
  rw [hpre, measure_units_smul w d hΔ t⁻¹ A]
  congr 1
  rw [Units.val_inv_eq_inv_val, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr (Units.ne_zero t)),
    ← ENNReal.inv_pow]

-- pin: smul_set_subset_compl_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2431)
omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem smul_set_subset_compl_zero (t : (w.Completion)ˣ) {E : Set w.Completion}
    (hE0 : E ⊆ {0}ᶜ) : (t : w.Completion) • E ⊆ ({0}ᶜ : Set w.Completion) := by
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_mul]
  exact mul_ne_zero (Units.ne_zero t) (fun h => hE0 hy (by simp [h]))

-- pin: measurableSet_units_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2437)
theorem measurableSet_units_smul (t : (w.Completion)ˣ) {E : Set w.Completion}
    (hE : MeasurableSet E) : MeasurableSet ((t : w.Completion) • E) := by
  have h : (t : w.Completion) • E
      = (fun x => ((t⁻¹ : (w.Completion)ˣ) : w.Completion) * x) ⁻¹' E := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (Units.ne_zero t), Set.mem_preimage]
    rw [Units.val_inv_eq_inv_val]
    rfl
  rw [h]
  exact hE.preimage (measurable_const_mul _)

set_option linter.overlappingInstances false in
-- pin: mulMeasure_units_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2448)
-- The pin's statement keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`.
theorem mulMeasure_units_smul (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    (t : (w.Completion)ˣ) {E : Set w.Completion}
    (hE : MeasurableSet E) (hE0 : E ⊆ {0}ᶜ) :
    mulMeasure μ ((t : w.Completion) • E) = mulMeasure μ E := by
  have hne : ((‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞)) ≠ 0 :=
    pow_ne_zero d (ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr (Units.ne_zero t)))
  have hnt : ((‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞)) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hcE : MeasurableSet ((t : w.Completion) • E) := measurableSet_units_smul w t hE
  rw [mulMeasure_completion_eq w d hd hΔ, withDensity_apply _ hcE, withDensity_apply _ hE,
    Measure.restrict_restrict hcE, Measure.restrict_restrict hE,
    Set.inter_eq_left.mpr (smul_set_subset_compl_zero w t hE0), Set.inter_eq_left.mpr hE0]
  have hμ : μ = (‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞) • Measure.map ((t : w.Completion) • ·) μ := by
    rw [map_units_smul w d hd hΔ t, smul_smul, ENNReal.mul_inv_cancel hne hnt, one_smul]
  have hpre : ((t : w.Completion) • ·) ⁻¹' ((t : w.Completion) • E) = E := by
    ext x
    simp only [Set.mem_preimage]
    exact Set.smul_mem_smul_set_iff₀ (Units.ne_zero t) E x
  calc ∫⁻ x in (t : w.Completion) • E, ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ
      = (‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞)
          * ∫⁻ x in (t : w.Completion) • E, ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹
              ∂(Measure.map ((t : w.Completion) • ·) μ) := by
        conv_lhs => rw [hμ]
        rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    _ = (‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞)
          * ∫⁻ y in E, ((‖(t : w.Completion) • y‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
        rw [setLIntegral_map hcE (measurable_nnnorm_pow_inv w d) (measurable_const_smul _), hpre]
    _ = ∫⁻ y in E, ((‖y‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
        have hint : ∀ y : w.Completion, (((‖(t : w.Completion) • y‖₊ ^ d : ℝ≥0∞)))⁻¹
            = ((‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞))⁻¹ * ((‖y‖₊ ^ d : ℝ≥0∞))⁻¹ := by
          intro y
          rw [smul_eq_mul, nnnorm_mul, ENNReal.coe_mul, mul_pow]
          exact ENNReal.mul_inv (Or.inl hne) (Or.inl (ENNReal.pow_ne_top ENNReal.coe_ne_top))
        simp only [hint]
        rw [lintegral_const_mul _ (measurable_nnnorm_pow_inv w d), ← mul_assoc,
          ENNReal.mul_inv_cancel hne hnt, one_mul]

-- pin: isOpenEmbedding_val_completion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2486)
omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem isOpenEmbedding_val_completion :
    Topology.IsOpenEmbedding (Units.val : (w.Completion)ˣ → w.Completion) :=
  Units.isOpenEmbedding_val

-- pin: image_val_subset_compl_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2491)
omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem image_val_subset_compl_zero (A : Set (w.Completion)ˣ) :
    (Units.val '' A : Set w.Completion) ⊆ {0}ᶜ := by
  rintro x ⟨u, _, rfl⟩
  exact u.ne_zero

-- pin: image_val_preimage_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2497)
omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem image_val_preimage_mul (t : (w.Completion)ˣ) (A : Set (w.Completion)ˣ) :
    (Units.val '' ((fun u => t * u) ⁻¹' A) : Set w.Completion)
      = ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨((t * u : (w.Completion)ˣ) : w.Completion), ⟨t * u, hu, rfl⟩, ?_⟩
    show ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • ((t * u : (w.Completion)ˣ) : w.Completion)
        = (u : w.Completion)
    rw [smul_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val, ← mul_assoc,
      inv_mul_cancel₀ (Units.ne_zero t), one_mul]
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨t⁻¹ * v, by simpa using hv, ?_⟩
    show ((t⁻¹ * v : (w.Completion)ˣ) : w.Completion)
        = ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • (v : w.Completion)
    rw [Units.val_mul, smul_eq_mul]

variable [MeasurableSpace (w.Completion)ˣ] [BorelSpace (w.Completion)ˣ]

-- pin: measurableEmbedding_val_completion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2516)
theorem measurableEmbedding_val_completion :
    MeasurableEmbedding (Units.val : (w.Completion)ˣ → w.Completion) :=
  (isOpenEmbedding_val_completion w).measurableEmbedding

set_option linter.overlappingInstances false in
-- pin: mulHaarCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2520)
-- The pin's statement keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`.
def mulHaarCompletion (μ : Measure w.Completion) : Measure (w.Completion)ˣ :=
  Measure.comap Units.val (mulMeasure μ)

-- pin: mulHaarCompletion_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2524)
omit [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulHaarCompletion_apply {A : Set (w.Completion)ˣ} (hA : MeasurableSet A) :
    mulHaarCompletion w μ A = mulMeasure μ (Units.val '' A) :=
  Measure.comap_apply _ (fun _ _ h => Units.ext h)
    (fun _ hs => (measurableEmbedding_val_completion w).measurableSet_image' hs) _ hA

set_option linter.overlappingInstances false in
-- pin: isMulLeftInvariant_mulHaarCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2529)
-- The pin's statement keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`.
theorem isMulLeftInvariant_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    (mulHaarCompletion w μ).IsMulLeftInvariant := by
  refine ⟨fun t => ?_⟩
  refine Measure.ext fun A hA => ?_
  have hmt : Measurable fun u : (w.Completion)ˣ => t * u :=
    (Homeomorph.mulLeft t).continuous.measurable
  rw [Measure.map_apply hmt hA]
  have hpre : MeasurableSet ((fun u => t * u) ⁻¹' A) := hA.preimage hmt
  rw [mulHaarCompletion_apply w hpre, mulHaarCompletion_apply w hA, image_val_preimage_mul]
  exact mulMeasure_units_smul w d hd hΔ t⁻¹
    ((measurableEmbedding_val_completion w).measurableSet_image' hA)
    (image_val_subset_compl_zero w A)

-- pin: mulMeasure_image_val_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2544)
omit [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulMeasure_image_val_eq (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    {A : Set (w.Completion)ˣ} (hA : MeasurableSet A) :
    mulMeasure μ (Units.val '' A)
      = ∫⁻ x in (Units.val '' A), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
  have hAm : MeasurableSet (Units.val '' A : Set w.Completion) :=
    (measurableEmbedding_val_completion w).measurableSet_image' hA
  rw [mulMeasure_completion_eq w d hd hΔ, withDensity_apply _ hAm, Measure.restrict_restrict hAm,
    Set.inter_eq_left.mpr (image_val_subset_compl_zero w A)]

-- pin: isFiniteMeasureOnCompacts_mulHaarCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2555)
omit [μ.Regular] in
theorem isFiniteMeasureOnCompacts_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    IsFiniteMeasureOnCompacts (mulHaarCompletion w μ) := by
  refine ⟨fun K hK => ?_⟩
  rw [mulHaarCompletion_apply w hK.measurableSet, mulMeasure_image_val_eq w d hd hΔ hK.measurableSet]
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hKc : IsCompact (Units.val '' K : Set w.Completion) :=
    hK.image (isOpenEmbedding_val_completion w).continuous
  obtain ⟨x₀, hx₀K, hx₀min⟩ :=
    hKc.exists_isMinOn (hne.image _) continuous_norm.continuousOn
  have hx₀0 : x₀ ≠ 0 := image_val_subset_compl_zero w K hx₀K
  have hb : ∀ x ∈ (Units.val '' K : Set w.Completion),
      ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ≤ ((‖x₀‖₊ ^ d : ℝ≥0∞))⁻¹ := by
    intro x hx
    refine ENNReal.inv_le_inv.mpr ?_
    have : ‖x₀‖₊ ≤ ‖x‖₊ := by exact_mod_cast (isMinOn_iff.mp hx₀min) x hx
    exact_mod_cast pow_le_pow_left' this d
  calc ∫⁻ x in (Units.val '' K), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ
      ≤ ∫⁻ _ in (Units.val '' K), ((‖x₀‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ :=
        setLIntegral_mono' hKc.measurableSet hb
    _ = ((‖x₀‖₊ ^ d : ℝ≥0∞))⁻¹ * μ (Units.val '' K) := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.mpr (ENNReal.pow_pos (ENNReal.coe_pos.mpr (nnnorm_pos.mpr hx₀0)) d))
        hKc.measure_lt_top

-- pin: isOpenPosMeasure_mulHaarCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2582)
omit [μ.Regular] in
theorem isOpenPosMeasure_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    (mulHaarCompletion w μ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [mulHaarCompletion_apply w hU.measurableSet, mulMeasure_image_val_eq w d hd hΔ hU.measurableSet]
  obtain ⟨u, hu⟩ := hne
  set W : Set w.Completion := (Units.val '' U)
      ∩ Metric.ball ((u : (w.Completion)ˣ) : w.Completion) (‖((u : (w.Completion)ˣ) : w.Completion)‖ / 2)
    with hW
  have hWo : IsOpen W :=
    ((isOpenEmbedding_val_completion w).isOpenMap _ hU).inter Metric.isOpen_ball
  have hWne : W.Nonempty :=
    ⟨(u : w.Completion), ⟨u, hu, rfl⟩,
      Metric.mem_ball_self (half_pos (norm_pos_iff.mpr (Units.ne_zero u)))⟩
  have hbound : ∀ x ∈ W,
      ((((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0∞)))⁻¹
        ≤ ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ := by
    intro x hx
    refine ENNReal.inv_le_inv.mpr ?_
    have hxb : ‖x‖₊ ≤ ‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2 := by
      have hdist := Metric.mem_ball.mp hx.2
      rw [dist_eq_norm] at hdist
      have : ‖x‖ ≤ ‖((u : (w.Completion)ˣ) : w.Completion)‖ * 2 := by
        have h1 := norm_le_norm_add_norm_sub' x ((u : (w.Completion)ˣ) : w.Completion)
        nlinarith [norm_nonneg ((u : (w.Completion)ˣ) : w.Completion),
          norm_nonneg (x - ((u : (w.Completion)ˣ) : w.Completion))]
      exact_mod_cast this
    calc ((‖x‖₊ ^ d : ℝ≥0) : ℝ≥0∞)
        ≤ (((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast pow_le_pow_left' hxb d
      _ = ((((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0∞))) := by push_cast; ring
  have hpos : (0 : ℝ≥0∞) < ∫⁻ x in (Units.val '' U), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
    calc (0 : ℝ≥0∞)
        < ((((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0∞)))⁻¹ * μ W := by
          refine ENNReal.mul_pos ?_ (hWo.measure_pos μ hWne).ne'
          exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top (ENNReal.mul_ne_top
            ENNReal.coe_ne_top (by simp)))
      _ = ∫⁻ _ in W, ((((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0∞)))⁻¹ ∂μ :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in W, ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := setLIntegral_mono' hWo.measurableSet hbound
      _ ≤ ∫⁻ x in (Units.val '' U), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ :=
          lintegral_mono_set Set.inter_subset_left
  exact hpos.ne'

set_option linter.overlappingInstances false in
-- pin: isHaarMeasure_mulHaarCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2626)
-- The pin's statement keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`.
theorem isHaarMeasure_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    (mulHaarCompletion w μ).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_mulHaarCompletion w d hd hΔ
    toIsMulLeftInvariant := isMulLeftInvariant_mulHaarCompletion w d hd hΔ
    toIsOpenPosMeasure := isOpenPosMeasure_mulHaarCompletion w d hd hΔ }

set_option linter.overlappingInstances false in
-- pin: isHaarMeasure_mulHaarCompletion_of_isReal (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2633)
-- The pin's statement keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`.
theorem isHaarMeasure_mulHaarCompletion_of_isReal (hv : w.IsReal) :
    (mulHaarCompletion w μ).IsHaarMeasure :=
  isHaarMeasure_mulHaarCompletion w 1 one_ne_zero
    (distribHaarChar_completion_of_isReal w hv)

set_option linter.overlappingInstances false in
-- pin: isHaarMeasure_mulHaarCompletion_of_isComplex (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2638)
-- The pin's statement keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`.
theorem isHaarMeasure_mulHaarCompletion_of_isComplex (hv : w.IsComplex) :
    (mulHaarCompletion w μ).IsHaarMeasure :=
  isHaarMeasure_mulHaarCompletion w 2 two_ne_zero
    (distribHaarChar_completion_of_isComplex w hv)

set_option linter.overlappingInstances false in
-- pin: isHaarMeasure_mulHaarCompletion_total (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2643)
-- The pin's statement keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`.
theorem isHaarMeasure_mulHaarCompletion_total :
    (mulHaarCompletion w μ).IsHaarMeasure :=
  (w.isReal_or_isComplex).elim
    (isHaarMeasure_mulHaarCompletion_of_isReal w)
    (isHaarMeasure_mulHaarCompletion_of_isComplex w)


end ArchMulHaarCompletion

end TateGlobal

end NumberField

end

end Fold_ArchMulHaar
