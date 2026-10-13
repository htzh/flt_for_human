/-
  Entry boxes and the uniform bound on the `M`-factor.

  `matBox C`/`unitBox C` are the matrix and group boxes of entrywise-`C` matrices;
  `unitBox C` is compact when `C` is, and a continuous function on the group is bounded on
  `unitBox C · g`. The adèlic section specializes to `archBall`, `entrySet = slab archBall
  integralFiniteAdeles`, shows it compact, and proves that the idempotent selection
  `selE`/`selZ`/`(1 - selE)·a` keeps all matrix entries in `entrySet` — hence
  `mFactor a b ∈ unitBox (entrySet F)` and `φ (mFactor a b * g)` is bounded uniformly in
  `a`, the uniform M-bound feeding the Weierstrass test.

  Transcribed from `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  lines 1127–1320 (pinned `aa2d8b3`), sections `EntryBox`, `NormBounds`, `AdelicBoxSec`
  of the pin namespace `AutomorphicForm.WeylIntegrable`.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Transfer
import Mathlib.Topology.Algebra.Group.Units

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain Matrix
open IsDedekindDomain.HeightOneSpectrum
open NumberField.AdelicBox
open NumberField.AdelicHaar
open scoped Classical

noncomputable section

namespace AutomorphicForm

namespace WeylIntegrable

section EntryBox

variable {A : Type*} [CommRing A]

-- pin: matBox (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1131)
def matBox (C : Set A) : Set (Matrix (Fin 2) (Fin 2) A) := {M | ∀ i j, M i j ∈ C}

omit [CommRing A] in
-- pin: isCompact_matBox (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1134)
theorem isCompact_matBox [TopologicalSpace A] {C : Set A} (hC : IsCompact C) : IsCompact (matBox C) := by
  have : matBox C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => C := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC

-- pin: unitBox (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1140)
def unitBox (C : Set A) : Set (GL (Fin 2) A) := {k | (k : Matrix (Fin 2) (Fin 2) A) ∈ matBox C ∧ ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) ∈ matBox C}

-- pin: unitBox_eq_preimage (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1142)
theorem unitBox_eq_preimage (C : Set A) :
    unitBox C = Units.embedProduct (Matrix (Fin 2) (Fin 2) A) ⁻¹' (matBox C ×ˢ (MulOpposite.op '' matBox C)) := by
  ext k
  simp only [unitBox, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, M, hM, hMk⟩
    refine ⟨h1, ?_⟩
    have : M = ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := MulOpposite.op_injective hMk
    rwa [← this]

-- pin: isCompact_unitBox (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1153)
theorem isCompact_unitBox [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] {C : Set A} (hC : IsCompact C) :
    IsCompact (unitBox C) := by
  rw [unitBox_eq_preimage]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_matBox hC).prod ((isCompact_matBox hC).image MulOpposite.continuous_op))

-- pin: exists_bound_on_unitBox (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1159)
theorem exists_bound_on_unitBox [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] {C : Set A} (hC : IsCompact C)
    {φ : GL (Fin 2) A → ℂ} (hφ : Continuous φ) (g : GL (Fin 2) A) : ∃ B : ℝ, ∀ k ∈ unitBox C, ‖φ (k * g)‖ ≤ B :=
  (isCompact_unitBox hC).exists_bound_of_continuousOn (hφ.comp (continuous_id.mul continuous_const)).continuousOn

end EntryBox

section NormBounds

variable {R : Type*} [NormedRing R]

-- pin: norm_mul_le_of_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1170)
theorem norm_mul_le_of_le {a b : R} {s t : ℝ} (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ t) (hs : 0 ≤ s) : ‖a * b‖ ≤ s * t :=
  (norm_mul_le a b).trans (mul_le_mul ha hb (norm_nonneg _) hs)

-- pin: entry_bounds (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1173)
theorem entry_bounds [NormOneClass R] {e z p : R} (he : ‖e‖ ≤ 1) (hz : ‖z‖ ≤ 1) (hp : ‖p‖ ≤ 1) :
    ‖e‖ ≤ 9 ∧ ‖1 - e‖ ≤ 9 ∧ ‖1 - e + e * z‖ ≤ 9 ∧ ‖p + e‖ ≤ 9 ∧
    ‖(2 * e - 1) * (p + e)‖ ≤ 9 ∧ ‖-((2 * e - 1) * (1 - e))‖ ≤ 9 ∧ ‖-((2 * e - 1) * (1 - e + e * z))‖ ≤ 9 ∧ ‖(2 * e - 1) * e‖ ≤ 9 := by
  have h1 : ‖(1 : R)‖ ≤ 1 := norm_one.le
  have h1e : ‖1 - e‖ ≤ 2 := (norm_sub_le_of_le h1 he).trans (by norm_num)
  have hsel : ‖2 * e - 1‖ ≤ 3 := by rw [two_mul]; exact (norm_sub_le_of_le (norm_add_le_of_le he he) h1).trans (by norm_num)
  have h3 : ‖1 - e + e * z‖ ≤ 3 := (norm_add_le_of_le h1e (norm_mul_le_of_le he hz zero_le_one)).trans (by norm_num)
  have h4 : ‖p + e‖ ≤ 2 := (norm_add_le_of_le hp he).trans (by norm_num)
  refine ⟨he.trans (by norm_num), h1e.trans (by norm_num), h3.trans (by norm_num), h4.trans (by norm_num), ?_, ?_, ?_, ?_⟩
  · exact (norm_mul_le_of_le hsel h4 (by norm_num)).trans (by norm_num)
  · rw [norm_neg]; exact (norm_mul_le_of_le hsel h1e (by norm_num)).trans (by norm_num)
  · rw [norm_neg]; exact (norm_mul_le_of_le hsel h3 (by norm_num)).trans (by norm_num)
  · exact (norm_mul_le_of_le hsel he (by norm_num)).trans (by norm_num)

end NormBounds

section AdelicBoxSec

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

-- pin: archBall (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1198)
def archBall : Set 𝔸∞ := {a | ∀ w, ‖a w‖ ≤ 9}

omit [NumberField F] in
-- the pin's `haveI` is load-bearing: it feeds the compactness instance below.
set_option linter.style.haveILetI false in
-- pin: isCompact_archBall (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1201)
theorem isCompact_archBall : IsCompact (archBall F) := by
  haveI := fun w => AdelicBox.properSpace_completion F w
  have : archBall F = Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 9 := by
    ext a; exact ⟨fun h w _ => mem_closedBall_zero_iff.mpr (h w), fun h w => mem_closedBall_zero_iff.mp (h w (Set.mem_univ _))⟩
  rw [this]
  exact isCompact_univ_pi fun w => isCompact_closedBall _ _

-- pin: entrySet (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1208)
def entrySet : Set 𝔸 := slab F (archBall F) (integralFiniteAdeles (𝓞 F) F)

-- pin: isCompact_entrySet (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1210)
theorem isCompact_entrySet : IsCompact (entrySet F) := by
  have : entrySet F = (fun p : 𝔸∞ × 𝔸f => (p : 𝔸)) '' (archBall F ×ˢ integralFiniteAdeles (𝓞 F) F) := by
    ext x; simp only [entrySet, mem_slab]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(x.1, x.2), ⟨h1, h2⟩, rfl⟩, by rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩⟩
  rw [this]
  exact ((isCompact_archBall F).prod (isCompact_integralFiniteAdeles F)).image continuous_id

-- pin: mem_entrySet (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1217)
theorem mem_entrySet {u : 𝔸} : u ∈ entrySet F ↔ (∀ w, ‖u.1 w‖ ≤ 9) ∧ ∀ v, u.2 v ∈ v.adicCompletionIntegers F := Iff.rfl

-- pin: cInf (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1219)
def cInf (w : InfinitePlace F) : 𝔸 →+* w.Completion := (Pi.evalRingHom _ w).comp (RingHom.fst 𝔸∞ 𝔸f)

-- pin: cFin (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1221)
def cFin (v : HeightOneSpectrum (𝓞 F)) : 𝔸 →+* v.adicCompletion F where
  toFun u := u.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

-- pin: cInf_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1228)
theorem cInf_apply (w : InfinitePlace F) (u : 𝔸) : cInf F w u = u.1 w := rfl
-- pin: cFin_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1229)
theorem cFin_apply (v : HeightOneSpectrum (𝓞 F)) (u : 𝔸) : cFin F v u = u.2 v := rfl

-- pin: norm_selE_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1231)
theorem norm_selE_le (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖(selE F a b).1 w‖ ≤ 1 := by
  rw [selE_fst]; split_ifs <;> simp

-- pin: norm_selZ_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1234)
theorem norm_selZ_le (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖(selZ F a b).1 w‖ ≤ 1 := by
  rw [selZ_fst]; split_ifs with h
  · exact (norm_inv_lt_one_of_bigInf F h).le
  · simp

-- pin: norm_selP_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1239)
theorem norm_selP_le (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖((1 - selE F a b) * toAdele' F a b).1 w‖ ≤ 1 := by
  rw [mul_fst_apply, sub_fst_apply, one_fst_apply, selE_fst, toAdele'_fst]
  split_ifs with h
  · simp
  · rw [BigInf, not_lt] at h; simpa using h

-- pin: selE_mem (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1245)
theorem selE_mem (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selE F a b).2 v ∈ v.adicCompletionIntegers F := by
  rw [selE_snd]; split_ifs
  · exact one_mem _
  · exact zero_mem _

-- pin: selZ_mem (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1250)
theorem selZ_mem (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selZ F a b).2 v ∈ v.adicCompletionIntegers F := by
  rw [selZ_snd]; split_ifs with h
  · exact inv_mem_of_bigFin F h
  · exact one_mem _

-- pin: selP_mem (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1255)
theorem selP_mem (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) :
    ((1 - selE F a b) * toAdele' F a b).2 v ∈ v.adicCompletionIntegers F := by
  rw [mul_snd_apply, sub_snd_apply, one_snd_apply, selE_snd, toAdele'_snd]
  split_ifs with h
  · simp
  · rw [BigFin, not_not] at h; simpa using h

-- pin: entries_mem (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1262)
theorem entries_mem (ε z p : 𝔸)
    (hInf : ∀ w, ‖ε.1 w‖ ≤ 1 ∧ ‖z.1 w‖ ≤ 1 ∧ ‖p.1 w‖ ≤ 1)
    (hFin : ∀ v, ε.2 v ∈ v.adicCompletionIntegers F ∧ z.2 v ∈ v.adicCompletionIntegers F ∧ p.2 v ∈ v.adicCompletionIntegers F) :
    ε ∈ entrySet F ∧ 1 - ε ∈ entrySet F ∧ 1 - ε + ε * z ∈ entrySet F ∧ p + ε ∈ entrySet F ∧
    (2 * ε - 1) * (p + ε) ∈ entrySet F ∧ -((2 * ε - 1) * (1 - ε)) ∈ entrySet F ∧
    -((2 * ε - 1) * (1 - ε + ε * z)) ∈ entrySet F ∧ (2 * ε - 1) * ε ∈ entrySet F := by

  have I : ∀ (u : 𝔸), (∀ w, ‖cInf F w u‖ ≤ 9) → (∀ v, cFin F v u ∈ v.adicCompletionIntegers F) → u ∈ entrySet F :=
    fun u h1 h2 => (mem_entrySet F).mpr ⟨h1, h2⟩
  have two : ∀ v, (2 : v.adicCompletion F) * cFin F v ε - 1 ∈ v.adicCompletionIntegers F := fun v => by
    rw [two_mul]; exact sub_mem (add_mem (hFin v).1 (hFin v).1) (one_mem _)
  have B : ∀ w, _ := fun w => entry_bounds (hInf w).1 (hInf w).2.1 (hInf w).2.2
  refine ⟨I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_),
    I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_)⟩
  · simpa only [cInf_apply] using (B w).1
  · simpa only [cFin_apply] using (hFin v).1
  · simpa only [map_sub, map_one, cInf_apply] using (B w).2.1
  · simpa only [map_sub, map_one, cFin_apply] using sub_mem (one_mem _) (hFin v).1
  · simpa only [map_add, map_sub, map_mul, map_one, cInf_apply] using (B w).2.2.1
  · simpa only [map_add, map_sub, map_mul, map_one, cFin_apply] using add_mem (sub_mem (one_mem _) (hFin v).1) (mul_mem (hFin v).1 (hFin v).2.1)
  · simpa only [map_add, cInf_apply] using (B w).2.2.2.1
  · simpa only [map_add, cFin_apply] using add_mem (hFin v).2.2 (hFin v).1
  · simpa only [map_add, map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.1
  · simpa only [map_add, map_sub, map_mul, map_one, map_ofNat, cFin_apply] using mul_mem (two v) (add_mem (hFin v).2.2 (hFin v).1)
  · simpa only [map_neg, map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.2.1
  · simpa only [map_neg, map_sub, map_mul, map_one, map_ofNat, cFin_apply] using neg_mem (mul_mem (two v) (sub_mem (one_mem _) (hFin v).1))
  · simpa only [map_neg, map_add, map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.2.2.1
  · simpa only [map_neg, map_add, map_sub, map_mul, map_one, map_ofNat, cFin_apply] using
      neg_mem (mul_mem (two v) (add_mem (sub_mem (one_mem _) (hFin v).1) (mul_mem (hFin v).1 (hFin v).2.1)))
  · simpa only [map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.2.2.2
  · simpa only [map_sub, map_mul, map_one, map_ofNat, cFin_apply] using mul_mem (two v) (hFin v).1

-- pin: mFactor_mem_unitBox (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1294)
theorem mFactor_mem_unitBox (a : 𝔸∞) (b : 𝔸f) : mFactor F a b ∈ unitBox (entrySet F) := by
  obtain ⟨m1, m2, m3, m4, i1, i2, i3, i4⟩ := entries_mem F (selE F a b) (selZ F a b) ((1 - selE F a b) * toAdele' F a b)
    (fun w => ⟨norm_selE_le F a b w, norm_selZ_le F a b w, norm_selP_le F a b w⟩)
    (fun v => ⟨selE_mem F a b v, selZ_mem F a b v, selP_mem F a b v⟩)
  constructor
  · intro i j
    rw [coe_mFactor]
    fin_cases i <;> fin_cases j
    · exact m1
    · exact m2
    · exact m3
    · exact m4
  · intro i j
    rw [coe_mFactor_inv]
    fin_cases i <;> fin_cases j
    · exact i1
    · exact i2
    · exact i3
    · exact i4

-- the pin's `letI` is load-bearing: it feeds the instance search below.
set_option linter.style.haveILetI false in
-- pin: exists_bound_mFactor (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1314)
theorem exists_bound_mFactor {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ B : ℝ, ∀ (a : 𝔸∞) (b : 𝔸f), ‖φ (mFactor F a b * g)‖ ≤ B := by
  letI : TopologicalSpace 𝔸 := inferInstance
  obtain ⟨B, hB⟩ := exists_bound_on_unitBox (isCompact_entrySet F) hφ g
  exact ⟨B, fun a b => hB _ (mFactor_mem_unitBox F a b)⟩

end AdelicBoxSec

end WeylIntegrable

end AutomorphicForm

end
