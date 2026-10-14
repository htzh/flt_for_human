/-
  The multiplicative Haar measure on the units of the completed field, built from
  the additive one.

  `mulHaar μ` is the pushforward of the additive `mulMeasure μ` along
  `Units.val`; `isOpenEmbedding_val` is the openness of `Units.val`, the order
  shifts `ord_ofMul_zpow_piUnit` and the shell decomposition
  `genShell`/`iUnion_genShell`/`genShell_disjoint` feed `mulMeasure_units_smul`,
  which is what makes `mulHaar μ` left-invariant, finite on compacts and positive
  on opens, hence a Haar measure (`isHaarMeasure_mulHaar`).

  Transcribed from the pin's `M4aLocalCFT.MulHaarFromAdditive` block, declared
  lines 1774–2105 of file A, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Chapter-prefix rename (work order §3.1): `M4aLocalCFT.MulHaarFromAdditive`
  becomes `NumberField.TateGlobal.MulHaarFromAdditive`; the sub-namespace is kept
  (it declares `measure_units_smul`/`mulMeasure_units_smul`/`image_val_subset_compl_zero`
  again in the archimedean block, with different statements).  The pin's
  `private theorem _root_.M4aLocalCFT.MulHaarFromAdditive.isOpenEmbedding_val` and
  its `p2m_export` line become a plain `private theorem isOpenEmbedding_val`.  The
  pin's `LocalHaarModulus.distribHaarChar_adicCompletion` and
  `LocalHaarModulus.measure_smul_integers` are the
  `NumberField.TateGlobal.LocalHaarModulus` declarations of `DistribHaarChar.lean`,
  so the pin's qualifiers stay (this namespace is a sibling, not a child).

  Build notes: the pin's `p2m_*` scaffolding is dropped; no file-wide option beyond
  `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.LocalZetaUnramified

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel MeasureTheory Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise NumberField.TateGlobal

section Fold_MulHaarFromAdditive

noncomputable section

namespace NumberField

namespace TateGlobal

namespace MulHaarFromAdditive

open LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

-- pin: isOpenEmbedding_val (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1774)
-- public since the `AutomorphicForm.LocalIntertwining` prelude needs it (it is `private` in the
-- pin, which re-copies it per file); see topics/automorphicForm/TOPIC-local-intertwining-weyl-integrand.md.
theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have hr : Set.range (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F)
      = {(0 : v.adicCompletion F)}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [hr]
  exact isClosed_singleton.isOpen_compl

-- pin: image_val_subset_compl_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1786)
theorem image_val_subset_compl_zero (A : Set (v.adicCompletion F)ˣ) :
    (Units.val '' A) ⊆ {(0 : v.adicCompletion F)}ᶜ := by
  rintro x ⟨u, _, rfl⟩
  exact u.ne_zero

-- pin: smul_set_eq_preimage (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1791)
theorem smul_set_eq_preimage {c : v.adicCompletion F} (hc : c ≠ 0)
    (S : Set (v.adicCompletion F)) :
    c • S = (fun y => c⁻¹ * y) ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

-- pin: isOpen_smul_set (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1801)
theorem isOpen_smul_set {c : v.adicCompletion F} (hc : c ≠ 0)
    {S : Set (v.adicCompletion F)} (hS : IsOpen S) :
    IsOpen (c • S) := by
  have h : c • S = (Homeomorph.mulLeft₀ c hc) '' S := by
    ext x
    simp [Homeomorph.coe_mulLeft₀, Set.mem_smul_set, smul_eq_mul, Set.mem_image]
  rw [h]
  exact (Homeomorph.mulLeft₀ c hc).isOpenMap _ hS

-- pin: image_val_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1810)
theorem image_val_smul (g : (v.adicCompletion F)ˣ) (A : Set (v.adicCompletion F)ˣ) :
    Units.val '' (g • A) = (g : v.adicCompletion F) • (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨u, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(a : v.adicCompletion F), ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g * a, ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩

variable {ϖ : v.adicCompletionIntegers F}

-- pin: isOpen_shellSet (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1821)
theorem isOpen_shellSet (hϖ : Irreducible ϖ) (k : ℕ) : IsOpen (shellSet hϖ k) := by
  unfold shellSet
  refine IsOpen.sdiff (isOpen_smul_set (Units.ne_zero _) ?_) ?_
  · exact Valued.isOpen_valuationSubring _
  · rw [smul_set_eq_preimage (Units.ne_zero _)]
    exact (Valued.isClosed_valuationSubring _).preimage (continuous_const_mul _)

-- pin: one_mem_shellSet_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1828)
theorem one_mem_shellSet_zero (hϖ : Irreducible ϖ) :
    (1 : v.adicCompletion F) ∈ shellSet hϖ 0 := by
  have h10 : (1 : v.adicCompletion F) ≠ 0 := one_ne_zero
  rw [mem_shellSet_iff_ord_eq hϖ 0 h10]
  have h1 : Units.mk0 (1 : v.adicCompletion F) h10 = 1 := Units.ext (by simp)
  rw [h1]
  simp

-- pin: ord_ofMul_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1836)
theorem ord_ofMul_mul (u w : (v.adicCompletion F)ˣ) :
    IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul (u * w))
      = IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul u)
        + IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul w) := by
  have h : Additive.ofMul (u * w) = Additive.ofMul u + Additive.ofMul w := rfl
  rw [h, map_add]

-- pin: ord_ofMul_zpow_piUnit (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1843)
theorem ord_ofMul_zpow_piUnit (hϖ : Irreducible ϖ) (k : ℤ) :
    IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ ^ k)) = k := by
  have h : Additive.ofMul (piUnit hϖ ^ k) = k • Additive.ofMul (piUnit hϖ) := rfl
  rw [h, map_zsmul, ord_piUnit hϖ, smul_eq_mul, mul_one]

-- pin: genShell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1848)
def genShell (hϖ : Irreducible ϖ) (k : ℤ) : Set (v.adicCompletion F) :=
  ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0

-- pin: mem_genShell_iff (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1851)
theorem mem_genShell_iff (hϖ : Irreducible ϖ) {k : ℤ} {x : v.adicCompletion F} (hx : x ≠ 0) :
    x ∈ genShell hϖ k
      ↔ IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx)) = k := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    have hu : Units.mk0 _ hx = piUnit hϖ ^ k * Units.mk0 y hy0 :=
      Units.ext (by simp [smul_eq_mul])
    rw [hu, ord_ofMul_mul, ord_ofMul_zpow_piUnit hϖ,
      (mem_shellSet_iff_ord_eq hϖ 0 hy0).mp hy]
    simp
  · intro hord
    have hne : (((piUnit hϖ ^ k)⁻¹ * Units.mk0 x hx : (v.adicCompletion F)ˣ)
        : v.adicCompletion F) ≠ 0 := Units.ne_zero _
    refine ⟨_, (mem_shellSet_iff_ord_eq hϖ 0 hne).mpr ?_, ?_⟩
    · have hmk : Units.mk0 _ hne = (piUnit hϖ ^ k)⁻¹ * Units.mk0 x hx :=
        Units.ext (by simp)
      rw [hmk, ord_ofMul_mul,
        show ((piUnit hϖ ^ k)⁻¹ : (v.adicCompletion F)ˣ) = piUnit hϖ ^ (-k) from
          (zpow_neg _ _).symm,
        ord_ofMul_zpow_piUnit hϖ, hord]
      simp
    · show (↑(piUnit hϖ ^ k) : v.adicCompletion F) • _ = x
      rw [smul_eq_mul, ← Units.val_mul, mul_inv_cancel_left, Units.val_mk0]

-- pin: genShell_disjoint (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1876)
theorem genShell_disjoint (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint (genShell hϖ)) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  rintro x hxk hxl
  have hx : x ≠ 0 := by
    rcases hxk with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    simp only [smul_eq_mul]
    exact mul_ne_zero (Units.ne_zero _) hy0
  exact hkl (((mem_genShell_iff hϖ hx).mp hxk).symm.trans ((mem_genShell_iff hϖ hx).mp hxl))

-- pin: iUnion_genShell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1888)
theorem iUnion_genShell (hϖ : Irreducible ϖ) :
    (⋃ k : ℤ, genShell hϖ k) = {(0 : v.adicCompletion F)}ᶜ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    simp only [smul_eq_mul]
    exact mul_ne_zero (Units.ne_zero _) hy0
  · intro hx
    exact ⟨_, (mem_genShell_iff hϖ hx).mpr rfl⟩

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

-- pin: measurableSet_smul_set (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1902)
theorem measurableSet_smul_set {c : v.adicCompletion F} (hc : c ≠ 0)
    {S : Set (v.adicCompletion F)} (hS : MeasurableSet S) :
    MeasurableSet (c • S) := by
  rw [smul_set_eq_preimage hc]
  exact hS.preimage (measurable_const_mul _)

-- pin: measurableSet_genShell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1908)
theorem measurableSet_genShell (hϖ : Irreducible ϖ) (k : ℤ) :
    MeasurableSet (genShell hϖ k) :=
  measurableSet_smul_set (Units.ne_zero _) (measurableSet_shellSet hϖ 0)

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

-- pin: mulMeasure_eq_of_subset_smul_shell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1915)
omit [BorelSpace (v.adicCompletion F)] [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulMeasure_eq_of_subset_smul_shell (hϖ : Irreducible ϖ)
    (w : (v.adicCompletion F)ˣ) {S : Set (v.adicCompletion F)} (hS : MeasurableSet S)
    (hsub : S ⊆ (w : v.adicCompletion F) • shellSet hϖ 0) :
    mulMeasure μ S = ((modulus (w : v.adicCompletion F) : ℝ≥0∞))⁻¹ * μ S := by
  have hmod : ∀ x ∈ S, modulus x = modulus (w : v.adicCompletion F) := by
    intro x hx
    rcases hsub hx with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    show modulus ((w : v.adicCompletion F) • y) = modulus (w : v.adicCompletion F)
    have hval : (w : v.adicCompletion F) • y
        = ((w * Units.mk0 y hy0 : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      simp [smul_eq_mul]
    rw [hval, modulus_coe_units, map_mul]
    have h1 : distribHaarChar (v.adicCompletion F) (Units.mk0 y hy0) = 1 := by
      rw [LocalHaarModulus.distribHaarChar_adicCompletion,
        (mem_shellSet_iff_ord_eq hϖ 0 hy0).mp hy]
      simp
    rw [h1, mul_one, ← modulus_coe_units]
  have hS0 : S ⊆ {(0 : v.adicCompletion F)}ᶜ := by
    intro x hx
    rcases hsub hx with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_mul]
    exact mul_ne_zero w.ne_zero hy0
  rw [mulMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS,
    Set.inter_eq_left.mpr hS0,
    setLIntegral_congr_fun hS (fun x hx => by rw [hmod x hx]),
    setLIntegral_const]

set_option linter.overlappingInstances false in
-- pin: measure_units_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1944)
theorem measure_units_smul (u : (v.adicCompletion F)ˣ) (S : Set (v.adicCompletion F)) :
    μ ((u : v.adicCompletion F) • S)
      = (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) * μ S := by
  rw [distribHaarChar_mul]
  rfl

set_option linter.overlappingInstances false in
-- pin: mulMeasure_units_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1950)
theorem mulMeasure_units_smul (hϖ : Irreducible ϖ) (u : (v.adicCompletion F)ˣ)
    {T : Set (v.adicCompletion F)} (hT : MeasurableSet T)
    (hT0 : T ⊆ {(0 : v.adicCompletion F)}ᶜ) :
    mulMeasure μ ((u : v.adicCompletion F) • T) = mulMeasure μ T := by
  classical
  have hTdec : T = ⋃ k : ℤ, T ∩ genShell hϖ k := by
    rw [← Set.inter_iUnion, iUnion_genShell hϖ, Set.inter_eq_left.mpr hT0]
  have hmeasT : ∀ k : ℤ, MeasurableSet (T ∩ genShell hϖ k) :=
    fun k => hT.inter (measurableSet_genShell hϖ k)
  have hdisT : Pairwise (Function.onFun Disjoint (fun k => T ∩ genShell hϖ k)) :=
    fun _ _ hkl => ((genShell_disjoint hϖ hkl).mono inter_subset_right inter_subset_right)
  have hudec : (u : v.adicCompletion F) • T
      = ⋃ k : ℤ, (u : v.adicCompletion F) • (T ∩ genShell hϖ k) := by
    conv_lhs => rw [hTdec]
    rw [Set.smul_set_iUnion]
  have hmeasU : ∀ k : ℤ, MeasurableSet ((u : v.adicCompletion F) • (T ∩ genShell hϖ k)) :=
    fun k => measurableSet_smul_set u.ne_zero (hmeasT k)
  have hdisU : Pairwise
      (Function.onFun Disjoint (fun k => (u : v.adicCompletion F) • (T ∩ genShell hϖ k))) := by
    intro k l hkl
    rw [Function.onFun, smul_set_eq_preimage u.ne_zero, smul_set_eq_preimage u.ne_zero]
    exact (hdisT hkl).preimage _
  have hper : ∀ k : ℤ, mulMeasure μ ((u : v.adicCompletion F) • (T ∩ genShell hϖ k))
      = mulMeasure μ (T ∩ genShell hϖ k) := by
    intro k
    set w : (v.adicCompletion F)ˣ := piUnit hϖ ^ k with hw
    have hsub₁ : T ∩ genShell hϖ k ⊆ (w : v.adicCompletion F) • shellSet hϖ 0 :=
      fun x hx => hx.2
    have hsub₂ : (u : v.adicCompletion F) • (T ∩ genShell hϖ k)
        ⊆ ((u * w : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0 := by
      rintro x ⟨y, hy, rfl⟩
      rcases hsub₁ hy with ⟨z, hz, rfl⟩
      exact ⟨z, hz, by simp [smul_eq_mul, mul_assoc]⟩
    rw [mulMeasure_eq_of_subset_smul_shell μ hϖ (u * w) (hmeasU k) hsub₂,
      mulMeasure_eq_of_subset_smul_shell μ hϖ w (hmeasT k) hsub₁,
      measure_units_smul μ u]
    rw [modulus_coe_units, modulus_coe_units, map_mul]
    have hu0 : (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr distribHaarChar_pos.ne'
    have huT : (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inl hu0) (Or.inl huT)]
    calc (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞)⁻¹
          * (distribHaarChar (v.adicCompletion F) w : ℝ≥0∞)⁻¹
          * ((distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) * μ (T ∩ genShell hϖ k))
        = (distribHaarChar (v.adicCompletion F) w : ℝ≥0∞)⁻¹
          * ((distribHaarChar (v.adicCompletion F) u : ℝ≥0∞)⁻¹
            * (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞)) * μ (T ∩ genShell hϖ k) := by
          ring
      _ = (distribHaarChar (v.adicCompletion F) w : ℝ≥0∞)⁻¹ * μ (T ∩ genShell hϖ k) := by
          rw [ENNReal.inv_mul_cancel hu0 huT, mul_one]
  rw [hudec, measure_iUnion hdisU hmeasU]
  conv_rhs => rw [hTdec, measure_iUnion hdisT hmeasT]
  exact tsum_congr hper

variable [MeasurableSpace ((v.adicCompletion F)ˣ)] [BorelSpace ((v.adicCompletion F)ˣ)]

-- pin: measurableEmbedding_val (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2006)
theorem measurableEmbedding_val :
    MeasurableEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
  isOpenEmbedding_val.measurableEmbedding

set_option linter.overlappingInstances false in
-- pin: mulHaar (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2010)
def mulHaar : Measure (v.adicCompletion F)ˣ :=
  Measure.comap Units.val (mulMeasure μ)

-- pin: mulHaar_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2014)
omit [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulHaar_apply {A : Set (v.adicCompletion F)ˣ} (hA : MeasurableSet A) :
    mulHaar μ A = mulMeasure μ (Units.val '' A) :=
  Measure.comap_apply _ (fun _ _ h => Units.ext h)
    (fun _ hs => measurableEmbedding_val.measurableSet_image' hs) _ hA

set_option linter.overlappingInstances false in
-- pin: isMulLeftInvariant_mulHaar (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2019)
theorem isMulLeftInvariant_mulHaar (hϖ : Irreducible ϖ) :
    (mulHaar μ).IsMulLeftInvariant := by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  have hpre : (fun h => g * h) ⁻¹' A = g⁻¹ • A := by
    ext a
    simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have hApre : MeasurableSet ((fun h => g * h) ⁻¹' A) :=
    hA.preimage (measurable_const_mul g)
  rw [hpre] at hApre ⊢
  rw [mulHaar_apply μ hApre, mulHaar_apply μ hA, image_val_smul]
  exact mulMeasure_units_smul μ hϖ g⁻¹ (measurableEmbedding_val.measurableSet_image' hA)
    (image_val_subset_compl_zero A)

set_option linter.overlappingInstances false in
set_option linter.style.haveILetI false in
-- pin: isFiniteMeasureOnCompacts_mulHaar (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2033)
-- The pin keeps both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`; the `haveI` supplies
-- the `T2Space` instance the compactness API needs.
theorem isFiniteMeasureOnCompacts_mulHaar (hϖ : Irreducible ϖ) :
    IsFiniteMeasureOnCompacts (mulHaar μ) := by
  haveI hT2 : T2Space ((v.adicCompletion F)ˣ) := Units.isEmbedding_val₀.t2Space
  constructor
  intro C hC
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  rw [mulHaar_apply μ hCm]
  have hC' : IsCompact (Units.val '' C) := hC.image Units.isEmbedding_val₀.continuous
  have hC'0 : (Units.val '' C) ⊆ {(0 : v.adicCompletion F)}ᶜ := image_val_subset_compl_zero C
  have hcov : (Units.val '' C) ⊆ ⋃ x : Units.val '' C,
      ((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2) : (v.adicCompletion F)ˣ)
        : v.adicCompletion F) • shellSet hϖ 0 := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, 1, one_mem_shellSet_zero hϖ, ?_⟩
    -- v4.34.0: the pin's `simp [smul_eq_mul]` leaves `↑(mk0 …) = x` unsolved.
    show ((Units.mk0 x (hC'0 hx) : (v.adicCompletion F)ˣ) : v.adicCompletion F) • (1 : v.adicCompletion F) = x
    rw [smul_eq_mul, mul_one]
    exact Units.val_mk0 (hC'0 hx)
  have hopen : ∀ x : Units.val '' C, IsOpen
      (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2) : (v.adicCompletion F)ˣ)
        : v.adicCompletion F) • shellSet hϖ 0) :=
    fun _ => isOpen_smul_set (Units.ne_zero _) (isOpen_shellSet hϖ 0)
  obtain ⟨t, ht⟩ := hC'.elim_finite_subcover _ hopen hcov
  calc mulMeasure μ (Units.val '' C)
      ≤ mulMeasure μ (⋃ x ∈ t,
          (Units.val '' C) ∩ (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2)
            : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0)) := by
        refine measure_mono fun y hy => ?_
        rcases Set.mem_iUnion₂.mp (ht hy) with ⟨x, hxt, hyx⟩
        exact Set.mem_iUnion₂.mpr ⟨x, hxt, hy, hyx⟩
    _ ≤ ∑ x ∈ t, mulMeasure μ ((Units.val '' C)
          ∩ (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2)
            : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0)) :=
        measure_biUnion_finset_le _ _
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.mpr fun x _ => ?_
        have hmeas : MeasurableSet ((Units.val '' C)
            ∩ (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2)
              : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0)) :=
          (hC'.isClosed.measurableSet).inter
            (measurableSet_smul_set (Units.ne_zero _) (measurableSet_shellSet hϖ 0))
        rw [mulMeasure_eq_of_subset_smul_shell μ hϖ _ hmeas inter_subset_right]
        refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr ?_) ?_
        · rw [modulus_coe_units]
          exact ENNReal.coe_pos.mpr distribHaarChar_pos
        · refine lt_of_le_of_lt (measure_mono (inter_subset_right.trans
            (Set.smul_set_mono (shellSet_subset_integers hϖ 0)))) ?_
          rw [LocalHaarModulus.measure_smul_integers μ]
          exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_integers_lt_top μ)

-- pin: isOpenPosMeasure_mulHaar (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2081)
omit [μ.Regular] in
theorem isOpenPosMeasure_mulHaar (hϖ : Irreducible ϖ) :
    (mulHaar μ).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rw [mulHaar_apply μ hU.measurableSet]
  obtain ⟨u₀, hu₀⟩ := hUne
  have hUim : IsOpen (Units.val '' U) := isOpenEmbedding_val.isOpenMap _ hU
  have hWopen : IsOpen ((Units.val '' U)
      ∩ ((u₀ : v.adicCompletion F) • shellSet hϖ 0)) :=
    hUim.inter (isOpen_smul_set (Units.ne_zero _) (isOpen_shellSet hϖ 0))
  have hWne : ((Units.val '' U)
      ∩ ((u₀ : v.adicCompletion F) • shellSet hϖ 0)).Nonempty := by
    refine ⟨(u₀ : v.adicCompletion F), ⟨u₀, hu₀, rfl⟩, 1, one_mem_shellSet_zero hϖ, ?_⟩
    simp [smul_eq_mul]
  have hWpos : 0 < mulMeasure μ ((Units.val '' U)
      ∩ ((u₀ : v.adicCompletion F) • shellSet hϖ 0)) := by
    rw [mulMeasure_eq_of_subset_smul_shell μ hϖ u₀ hWopen.measurableSet inter_subset_right]
    refine ENNReal.mul_pos ?_ (hWopen.measure_pos μ hWne).ne'
    exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  exact (hWpos.trans_le (measure_mono inter_subset_left)).ne'

set_option linter.overlappingInstances false in
-- pin: isHaarMeasure_mulHaar (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:2102)
theorem isHaarMeasure_mulHaar (hϖ : Irreducible ϖ) : (mulHaar μ).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_mulHaar μ hϖ
    toIsMulLeftInvariant := isMulLeftInvariant_mulHaar μ hϖ
    toIsOpenPosMeasure := isOpenPosMeasure_mulHaar μ hϖ }


end MulHaarFromAdditive

end TateGlobal

end NumberField

end

end Fold_MulHaarFromAdditive
