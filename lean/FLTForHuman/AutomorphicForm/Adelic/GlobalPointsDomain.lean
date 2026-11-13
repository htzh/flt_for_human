/-
  The global points have a fundamental domain among the adelic points.

  The countable subgroup `GL_2(K)` of the global points acts on `GL_2(A)`; the determinant-norm
  slab `{x | a <= |det x| <= b}` is a measurable, `Gamma_p`-invariant set whose dyadic copies are
  disjoint and cover the points with non-zero determinant, so the group action is free enough to
  admit a fundamental domain, and `IsFundamentalDomain` follows from the dyadic decomposition by
  `isFundamentalDomain_iUnion_of_restrict` and `isFundamentalDomain_inter_restrict`.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range.lean` (165 lines: nine
  `private` helpers and the headline), with the statement from the wrapper of the same name.  The
  pin writes its helpers at the file's own namespace level; the port puts them in the rectified word
  namespace `GlobalPointsDomain`, still `private`, so the module's public surface is the headline.

  Assumes from earlier modules: `Adelic/DetNormSlabFundamentalDomain.lean`
  (`exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc`),
  `Adelic/IdeleNormDet.lean` (`ideleNorm_det_globalPoints`) and
  `NumberTheory/NumberField/TateGlobalIdeleNormDet.lean`
  (`measurableSet_setOf_ideleNorm_det_mem_Icc`).

  spec-pin: Theorems/Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDet
import FLTForHuman.AutomorphicForm.Adelic.DetNormSlabFundamentalDomain
import FLTForHuman.AutomorphicForm.Adelic.MeasurableFundamentalDomainCover
import FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Topology ProbabilityTheory
open scoped NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace GlobalPointsDomain

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

open Set NumberField.TateGlobal AutomorphicForm
open scoped Pointwise

private theorem nullMeasurableSet_of_restrict {X : Type} [MeasurableSpace X] {μ : Measure X} {S T : Set X}
    (hST : S ⊆ T) (h : NullMeasurableSet S (μ.restrict T)) : NullMeasurableSet S μ := by
  obtain ⟨m, hmS, hm, hmeq⟩ := h.exists_measurable_subset_ae_eq
  refine hm.nullMeasurableSet.congr ?_
  rw [ae_eq_set] at hmeq ⊢
  refine ⟨?_, ?_⟩
  · rw [Set.sdiff_eq_empty.2 hmS, measure_empty]
  · have h2 := hmeq.2
    rwa [Measure.restrict_eq_self μ (Set.sdiff_subset.trans hST)] at h2

private theorem isFundamentalDomain_inter_restrict {G X : Type} [Group G] [MulAction G X]
    [MeasurableSpace X] (μ : Measure X) {S T U : Set X} (hU : MeasurableSet U) (hUT : U ⊆ T)
    (hUinv : ∀ (g : G) (x : X), x ∈ U → g • x ∈ U) (h : IsFundamentalDomain G S (μ.restrict T)) :
    IsFundamentalDomain G (S ∩ U) (μ.restrict U) where
  nullMeasurableSet := by
    have hle : μ.restrict U ≤ μ.restrict T := Measure.restrict_mono hUT le_rfl
    exact (h.nullMeasurableSet.mono_ac (Measure.absolutelyContinuous_of_le hle)).inter
      hU.nullMeasurableSet
  ae_covers := by
    have h1 : ∀ᵐ x ∂μ.restrict U, ∃ g : G, g • x ∈ S :=
      ae_restrict_of_ae_restrict_of_subset hUT h.ae_covers
    filter_upwards [h1, ae_restrict_mem hU] with x hx hxU
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, hg, hUinv g x hxU⟩
  aedisjoint := by
    intro g₁ g₂ hne
    have h0 : μ.restrict T (g₁ • S ∩ g₂ • S) = 0 := h.aedisjoint hne
    have hle : μ.restrict U ≤ μ.restrict T := Measure.restrict_mono hUT le_rfl
    show μ.restrict U (g₁ • (S ∩ U) ∩ g₂ • (S ∩ U)) = 0
    apply measure_mono_null
      (inter_subset_inter (smul_set_mono inter_subset_left) (smul_set_mono inter_subset_left))
    exact le_antisymm ((Measure.le_iff'.1 hle _).trans h0.le) zero_le

private theorem isFundamentalDomain_iUnion_of_restrict {G X ι : Type} [Group G] [MulAction G X]
    [MeasurableSpace X] [Countable ι] (μ : Measure X) (P : ι → Set X)
    (hPm : ∀ k, MeasurableSet (P k)) (hPinv : ∀ k (g : G) (x : X), x ∈ P k → g • x ∈ P k)
    (hPdisj : ∀ k l, k ≠ l → ∀ x, x ∈ P k → x ∉ P l) (hPcov : ∀ x, ∃ k, x ∈ P k) (S : ι → Set X)
    (hSP : ∀ k, S k ⊆ P k) (hS : ∀ k, IsFundamentalDomain G (S k) (μ.restrict (P k))) :
    IsFundamentalDomain G (⋃ k, S k) μ where
  nullMeasurableSet :=
    NullMeasurableSet.iUnion fun k => nullMeasurableSet_of_restrict (hSP k) (hS k).nullMeasurableSet
  ae_covers := by
    rw [ae_iff]
    refine measure_mono_null (t := ⋃ k, ({x : X | ¬ ∃ g : G, g • x ∈ S k} ∩ P k)) (fun x hx => ?_)
      (measure_iUnion_null fun k => ?_)
    · have hx' : ¬ ∃ g : G, g • x ∈ ⋃ k, S k := hx
      obtain ⟨k, hk⟩ := hPcov x
      refine mem_iUnion.2 ⟨k, ?_, hk⟩
      show ¬ ∃ g : G, g • x ∈ S k
      rintro ⟨g, hg⟩
      exact hx' ⟨g, mem_iUnion.2 ⟨k, hg⟩⟩
    · have hk := (hS k).ae_covers
      rw [ae_iff, Measure.restrict_apply' (hPm k)] at hk
      exact hk
  aedisjoint := by
    intro g₁ g₂ hne
    show μ (g₁ • (⋃ k, S k) ∩ g₂ • (⋃ k, S k)) = 0
    refine measure_mono_null (t := ⋃ k, (g₁ • S k ∩ g₂ • S k)) (fun x hx => ?_)
      (measure_iUnion_null fun k => ?_)
    · obtain ⟨hx₁, hx₂⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hx₁
      obtain ⟨z, hz, hzx⟩ := hx₂
      obtain ⟨k, hyk⟩ := mem_iUnion.1 hy
      obtain ⟨l, hzl⟩ := mem_iUnion.1 hz
      have h1 : g₁ • y ∈ P k := hPinv k g₁ y (hSP k hyk)
      have h2 : g₁ • y ∈ P l := by
        change g₂ • z = g₁ • y at hzx
        rw [← hzx]
        exact hPinv l g₂ z (hSP l hzl)
      have hkl : k = l := by
        by_contra hkl
        exact hPdisj k l hkl _ h1 h2
      cases hkl
      exact mem_iUnion.2 ⟨k, ⟨y, hyk, rfl⟩, ⟨z, hzl, hzx⟩⟩
    · have h0 : μ.restrict (P k) (g₁ • S k ∩ g₂ • S k) = 0 := (hS k).aedisjoint hne
      have hsub : g₁ • S k ∩ g₂ • S k ⊆ P k := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := hx.1
        exact hPinv k g₁ y (hSP k hy)
      rwa [Measure.restrict_eq_self μ hsub] at h0

private def detSlab (F : Type) [Field F] [NumberField F] (a b : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Ico a b}

private theorem measurableSet_detSlab (F : Type) [Field F] [NumberField F] (a b : ℝ) :
    MeasurableSet (detSlab F a b) := by
  have h : detSlab F a b =
      {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc a b} \
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc b b} := by
    ext g
    simp only [detSlab, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨h₁, h₂.le⟩, fun h => absurd h.1 (not_le.2 h₂)⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨h₁, lt_of_le_of_ne h₂ fun e => h₃ ⟨e.ge, e.le⟩⟩
  rw [h]
  exact (measurableSet_setOf_ideleNorm_det_mem_Icc F a b).diff
    (measurableSet_setOf_ideleNorm_det_mem_Icc F b b)

private theorem detSlab_subset_Icc (F : Type) [Field F] [NumberField F] (a b : ℝ) :
    detSlab F a b ⊆
      {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc a b} :=
  fun _ hg => Ico_subset_Icc_self hg

private theorem smul_mem_detSlab (F : Type) [Field F] [NumberField F] (a b : ℝ)
    (γ : (globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F) (hx : x ∈ detSlab F a b) :
    γ • x ∈ detSlab F a b := by
  obtain ⟨γ₀, hγ₀⟩ := MonoidHom.mem_range.1 γ.2
  simp only [detSlab, Set.mem_ofPred_eq] at hx ⊢
  rw [Subgroup.smul_def, smul_eq_mul, ← hγ₀, map_mul, ideleNorm_mul, ideleNorm_det_globalPoints,
    one_mul]
  exact hx

private theorem detSlab_dyadic_disjoint (F : Type) [Field F] [NumberField F] (k l : ℤ) (hkl : k ≠ l)
    (x : AdelicGL2 (𝓞 F) F) (hk : x ∈ detSlab F ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) :
    x ∉ detSlab F ((2 : ℝ) ^ l) ((2 : ℝ) ^ (l + 1)) := by
  intro hl
  simp only [detSlab, Set.mem_ofPred_eq, Set.mem_Ico] at hk hl
  rcases hkl.lt_or_gt with h | h
  · have : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ l := zpow_le_zpow_right₀ one_le_two (by omega)
    linarith [hk.2, hl.1]
  · have : (2 : ℝ) ^ (l + 1) ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ one_le_two (by omega)
    linarith [hl.2, hk.1]

private theorem exists_mem_detSlab_dyadic (F : Type) [Field F] [NumberField F] (x : AdelicGL2 (𝓞 F) F) :
    ∃ k : ℤ, x ∈ detSlab F ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) := by
  obtain ⟨k, hk⟩ :=
    exists_mem_Ico_zpow (ideleNorm_pos (Matrix.GeneralLinearGroup.det x)) (one_lt_two : (1 : ℝ) < 2)
  exact ⟨k, hk⟩


end GlobalPointsDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isFundamentalDomain_globalPoints_range (F : Type) [Field F] [NumberField F] :
    ∃ D : Set (AdelicGL2 (𝓞 F) F),
      IsFundamentalDomain (globalPoints (𝓞 F) F).range D (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  choose S _ hS_fd using fun k : ℤ =>
    exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F ((2 : ℝ) ^ k)
      ((2 : ℝ) ^ (k + 1))
  refine ⟨⋃ k : ℤ, S k ∩ GlobalPointsDomain.detSlab F ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)),
    GlobalPointsDomain.isFundamentalDomain_iUnion_of_restrict _
      (fun k : ℤ => GlobalPointsDomain.detSlab F ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (fun k => GlobalPointsDomain.measurableSet_detSlab F _ _)
      (fun k γ x hx => GlobalPointsDomain.smul_mem_detSlab F _ _ γ x hx)
      (fun k l hkl x hk => GlobalPointsDomain.detSlab_dyadic_disjoint F k l hkl x hk)
      (GlobalPointsDomain.exists_mem_detSlab_dyadic F) _
      (fun k => Set.inter_subset_right) fun k => ?_⟩
  exact GlobalPointsDomain.isFundamentalDomain_inter_restrict _
    (GlobalPointsDomain.measurableSet_detSlab F _ _)
    (GlobalPointsDomain.detSlab_subset_Icc F _ _)
    (fun γ x hx => GlobalPointsDomain.smul_mem_detSlab F _ _ γ x hx) (hS_fd k)
