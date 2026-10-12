/-
  Level structures on `GL₂(𝔸_K)`.

  `IsLevelZeroMatrix`/`IsLevelOneMatrix` are the congruence conditions on a finite
  adèle matrix (integral entries, lower-left divisible by `N`, and for level one
  `m 1 1 - 1` divisible by `N`); `finiteLevelZero`/`finiteLevelOne` are the
  corresponding subgroups of `GL₂(𝔸_K^fin)`, `finiteIntegralGL2` the level-`⊤` case.
  They are open, closed and compact, and their preimages under `glFin` give the
  adèlic subgroups `levelZero`/`levelOne` — the `U = levelOne ⊓ finiteAdelicGL2Subgroup`
  of the smoothing theorem.

  Transcribed verbatim from `Definitions/Def_NumberField_AdelicLevel.lean:306–620`
  (the pin's `FiniteLevel` and `Adelic` sections, pinned `aa2d8b3`), one of the four
  role modules the pin node is split into (playbook §3.1).
-/
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import Mathlib.Topology.Algebra.Group.Units

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct
open scoped RestrictedProduct Topology
open Topology

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

section FiniteLevel

structure IsLevelZeroMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop where
  integral : ∀ i j, m i j ∈ integralFiniteAdeles R K
  lowerLeft : m 1 0 ∈ idealBall R K N

structure IsLevelOneMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop extends IsLevelZeroMatrix R K N m where
  lowerRight : m 1 1 - 1 ∈ idealBall R K N

variable {R K}
variable {N : Ideal R}

theorem one_mem_integralFiniteAdeles : (1 : FiniteAdeleRing R K) ∈ integralFiniteAdeles R K :=
  fun _ => one_mem _

theorem zero_mem_integralFiniteAdeles : (0 : FiniteAdeleRing R K) ∈ integralFiniteAdeles R K :=
  fun _ => zero_mem _

theorem add_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ integralFiniteAdeles R K) : x + y ∈ integralFiniteAdeles R K :=
  fun v => add_mem (hx v) (hy v)

theorem mul_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ integralFiniteAdeles R K) : x * y ∈ integralFiniteAdeles R K :=
  fun v => mul_mem (hx v) (hy v)

theorem sub_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ integralFiniteAdeles R K) : x - y ∈ integralFiniteAdeles R K :=
  fun v => sub_mem (hx v) (hy v)

theorem valued_apply_le_one {x : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (v : HeightOneSpectrum R) : Valued.v (x v) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hx v)

theorem add_mem_idealBall {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ idealBall R K N) : x + y ∈ idealBall R K N := fun v =>
  (Valuation.map_add _ _ _).trans (max_le (hx v) (hy v))

theorem mul_mem_idealBall_left {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ idealBall R K N) : x * y ∈ idealBall R K N := fun v => by
  rw [coe_mul_apply, map_mul]
  calc Valued.v (x v) * Valued.v (y v) ≤ 1 * idealBound R N v :=
        mul_le_mul' (valued_apply_le_one hx v) (hy v)
    _ = idealBound R N v := one_mul _

theorem mul_mem_idealBall_right {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ integralFiniteAdeles R K) : x * y ∈ idealBall R K N := by
  rw [mul_comm]; exact mul_mem_idealBall_left hy hx

namespace IsLevelZeroMatrix

protected theorem one : IsLevelZeroMatrix R K N 1 where
  integral i j := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [Matrix.one_apply_ne (by decide)]
    exact zero_mem_idealBall N

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

protected theorem mul (hm : IsLevelZeroMatrix R K N m) (hm' : IsLevelZeroMatrix R K N m') :
    IsLevelZeroMatrix R K N (m * m') where
  integral i j := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_integralFiniteAdeles
      (mul_mem_integralFiniteAdeles (hm.integral i 0) (hm'.integral 0 j))
      (mul_mem_integralFiniteAdeles (hm.integral i 1) (hm'.integral 1 j))
  lowerLeft := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_idealBall (mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 0))
      (mul_mem_idealBall_left (hm.integral 1 1) hm'.lowerLeft)

end IsLevelZeroMatrix

namespace IsLevelOneMatrix

protected theorem one : IsLevelOneMatrix R K N 1 where
  toIsLevelZeroMatrix := .one
  lowerRight := by
    rw [Matrix.one_apply_eq, sub_self]
    exact zero_mem_idealBall N

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

protected theorem mul (hm : IsLevelOneMatrix R K N m) (hm' : IsLevelOneMatrix R K N m') :
    IsLevelOneMatrix R K N (m * m') where
  toIsLevelZeroMatrix := hm.toIsLevelZeroMatrix.mul hm'.toIsLevelZeroMatrix
  lowerRight := by
    have h : (m * m') 1 1 - 1
        = m 1 0 * m' 0 1 + ((m 1 1 - 1) * m' 1 1 + (m' 1 1 - 1)) := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h]
    exact add_mem_idealBall (mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 1))
      (add_mem_idealBall (mul_mem_idealBall_right hm.lowerRight (hm'.integral 1 1)) hm'.lowerRight)

end IsLevelOneMatrix

variable (R K) (N)

def finiteLevelZero : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelZeroMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelZeroMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' ha hb := ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
    by rw [mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

def finiteLevelOne : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelOneMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' ha hb := ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
    by rw [mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {R K N}

theorem mem_finiteLevelZero_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteLevelZero R K N ↔ IsLevelZeroMatrix R K N (g : Matrix _ _ _) ∧
      IsLevelZeroMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) :=
  Iff.rfl

theorem mem_finiteLevelOne_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteLevelOne R K N ↔ IsLevelOneMatrix R K N (g : Matrix _ _ _) ∧
      IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) :=
  Iff.rfl

variable (R K N)

theorem finiteLevelOne_le_finiteLevelZero : finiteLevelOne R K N ≤ finiteLevelZero R K N :=
  fun _ hg => ⟨hg.1.toIsLevelZeroMatrix, hg.2.toIsLevelZeroMatrix⟩

abbrev finiteIntegralGL2 : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) := finiteLevelZero R K ⊤

variable {R K} in
theorem mem_finiteIntegralGL2_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteIntegralGL2 R K ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈ integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
        i j ∈ integralFiniteAdeles R K :=
  ⟨fun h => ⟨h.1.integral, h.2.integral⟩, fun h =>
    ⟨⟨h.1, fun v => (idealBound_top v).symm ▸ valued_apply_le_one (h.1 1 0) v⟩,
     ⟨h.2, fun v => (idealBound_top v).symm ▸ valued_apply_le_one (h.2 1 0) v⟩⟩⟩

theorem isClosed_setOf_isLevelZeroMatrix :
    IsClosed {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m}
      = (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' integralFiniteAdeles R K)
        ∩ (fun m => m 1 0) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h => ⟨h.integral, h.lowerLeft⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isClosed_iInter fun i => isClosed_iInter fun j =>
      (isClosed_integralFiniteAdeles R K).preimage (continuous_id.matrix_elem i j)).inter
    ((isClosed_idealBall R K N).preimage (continuous_id.matrix_elem 1 0))

theorem isClosed_setOf_isLevelOneMatrix :
    IsClosed {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m}
      = {m | IsLevelZeroMatrix R K N m} ∩ (fun m => m 1 1 - 1) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun h => ⟨h.toIsLevelZeroMatrix, h.lowerRight⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isClosed_setOf_isLevelZeroMatrix R K N).inter
    ((isClosed_idealBall R K N).preimage ((continuous_id.matrix_elem 1 1).sub continuous_const))

variable {N} in
theorem isOpen_setOf_isLevelZeroMatrix (hN : N ≠ ⊥) :
    IsOpen {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m}
      = (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' integralFiniteAdeles R K)
        ∩ (fun m => m 1 0) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h => ⟨h.integral, h.lowerLeft⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_integralFiniteAdeles R K).preimage (continuous_id.matrix_elem i j)).inter
    ((isOpen_idealBall R K hN).preimage (continuous_id.matrix_elem 1 0))

variable {N} in
theorem isOpen_setOf_isLevelOneMatrix (hN : N ≠ ⊥) :
    IsOpen {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m}
      = {m | IsLevelZeroMatrix R K N m} ∩ (fun m => m 1 1 - 1) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun h => ⟨h.toIsLevelZeroMatrix, h.lowerRight⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isOpen_setOf_isLevelZeroMatrix R K hN).inter
    ((isOpen_idealBall R K hN).preimage ((continuous_id.matrix_elem 1 1).sub continuous_const))

variable {N} in

theorem isOpen_finiteLevelZero (hN : N ≠ ⊥) :
    IsOpen (finiteLevelZero R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isOpen_setOf_isLevelZeroMatrix R K hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLevelZeroMatrix R K hN).preimage Units.continuous_coe_inv)

variable {N} in

theorem isOpen_finiteLevelOne (hN : N ≠ ⊥) :
    IsOpen (finiteLevelOne R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isOpen_setOf_isLevelOneMatrix R K hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLevelOneMatrix R K hN).preimage Units.continuous_coe_inv)

theorem isClosed_finiteLevelZero :
    IsClosed (finiteLevelZero R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isClosed_setOf_isLevelZeroMatrix R K N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLevelZeroMatrix R K N).preimage Units.continuous_coe_inv)

theorem isClosed_finiteLevelOne :
    IsClosed (finiteLevelOne R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isClosed_setOf_isLevelOneMatrix R K N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLevelOneMatrix R K N).preimage Units.continuous_coe_inv)

section Compact

variable [Module.Free ℤ R] [Module.Finite ℤ R]

theorem isCompact_setOf_integral :
    IsCompact {g : GL (Fin 2) (FiniteAdeleRing R K) |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈ integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
        ∈ integralFiniteAdeles R K} := by
  set C : Set (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :=
    {m | ∀ i j, m i j ∈ integralFiniteAdeles R K} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 =>
        Set.pi Set.univ fun _ : Fin 2 => integralFiniteAdeles R K := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles R K
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Topology.IsClosedEmbedding.isCompact_preimage
      (show IsClosedEmbedding
          (Units.embedProduct (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) from
        Units.isClosedEmbedding_embedProduct)
      (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : {g : GL (Fin 2) (FiniteAdeleRing R K) |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈ integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
        ∈ integralFiniteAdeles R K}
      = (Units.embedProduct (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) ⁻¹'
        (C ×ˢ (MulOpposite.op '' C)) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      Set.mem_image, hC_def]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
    · rintro ⟨h1, m, hm, hm'⟩
      refine ⟨h1, ?_⟩
      have : m = ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :=
        MulOpposite.op_injective hm'
      rw [← this]; exact hm
  rw [heq]; exact hK

theorem isCompact_finiteLevelZero :
    IsCompact (finiteLevelZero R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  (isCompact_setOf_integral R K).of_isClosed_subset (isClosed_finiteLevelZero R K N)
    fun _ hg => ⟨hg.1.integral, hg.2.integral⟩

theorem isCompact_finiteLevelOne :
    IsCompact (finiteLevelOne R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  (isCompact_finiteLevelZero R K N).of_isClosed_subset (isClosed_finiteLevelOne R K N)
    (finiteLevelOne_le_finiteLevelZero R K N)

end Compact

end FiniteLevel

section Adelic

variable (N : Ideal R)

def levelZero : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelZero R K N).comap (glFin R K)

def levelOne : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelOne R K N).comap (glFin R K)

variable {R K N}

theorem mem_levelZero_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ levelZero R K N ↔ glFin R K g ∈ finiteLevelZero R K N := Iff.rfl

theorem mem_levelOne_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ levelOne R K N ↔ glFin R K g ∈ finiteLevelOne R K N := Iff.rfl

variable (R K N)

theorem levelOne_le_levelZero : levelOne R K N ≤ levelZero R K N :=
  Subgroup.comap_mono (finiteLevelOne_le_finiteLevelZero R K N)

variable {N} in

theorem isOpen_levelZero (hN : N ≠ ⊥) : IsOpen (levelZero R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isOpen_finiteLevelZero R K hN).preimage (continuous_glFin R K)

variable {N} in

theorem isOpen_levelOne (hN : N ≠ ⊥) : IsOpen (levelOne R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isOpen_finiteLevelOne R K hN).preimage (continuous_glFin R K)

theorem isClosed_levelZero : IsClosed (levelZero R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isClosed_finiteLevelZero R K N).preimage (continuous_glFin R K)

theorem isClosed_levelOne : IsClosed (levelOne R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isClosed_finiteLevelOne R K N).preimage (continuous_glFin R K)

end Adelic

end NumberField.AdelicLevel

end
