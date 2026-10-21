/-
  The congruence-subgroup lattice of `SL(2, ℤ)`.

  How `Γ(N) ⊆ Γ₁(N) ⊆ Γ₀(N)` sit inside `SL(2, ℤ)`, in four pieces, transcribed
  from the pinned FLT (`anthropics/fermats-last-theorem`, `aa2d8b3`):

  * `P2M/Sol/S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers.lean`
    (406 lines) — level lowering with a lower unipotent:
    `Γ(N/p) ≤ (Γ₁(N) ⊓ Γ(N/p ^ N.factorization p)) ⊔ zpowers (S * T^(N/p) * S⁻¹)`;
  * `P2M/Sol/S_CongruenceSubgroup_exists_finset_transversal_adapted_T_S.lean`
    (179 lines) — a finite transversal of `±Γ` adapted to `T` and `S`;
  * `P2M/Sol/S_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff.lean`
    (142 lines) — the first-column criteria for `±Γ₁(N)`;
  * `P2M/Sol/S_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd.lean`
    (85 lines) — `(Γ₁(M) ⊓ Γ₀(Mq)).relIndex (Γ₁(M)) = q` for `q ∣ M`.

  812 pin `S_` lines. The phase-3 note excluded the whole `CongruenceSubgroup.*`
  namespace on the *subject* filter ("modular forms — FLT-flavoured subject"), but read
  against the statements these four are group theory of mathlib's own congruence-subgroup
  API (`Gamma`, `Gamma0`, `Gamma1`, `ModularGroup.S`/`T`, `Subgroup.zpowers`,
  `Subgroup.relIndex`, `ZMod`) — no Weierstrass, no modular form, no Hecke operator, no
  adele — so the exclusion is corrected here. The fifth node of the namespace,
  `CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three`, is **not** ported: it is a lift
  of the private `Gamma0Three` engine of `ModularForms/WeightOne/EisensteinChiNegThree.lean`
  with a 51-module dependent wave (WORKORDER-PH3D §8).

  The four pin files are folded into this one module, keeping each one's `open` lines and
  its own namespace discipline: the pin's generated inner label `GammaGenSol` becomes
  `CongruenceSubgroup.LowerUnipotent`, `GCusp` becomes `CongruenceSubgroup.FirstColumn`
  and `IndexDvd` becomes `CongruenceSubgroup.Index`; every last name is kept, the pin's
  `private` helpers stay `private`, and the four `solution` wrappers are not ported (each
  headline is stated once, at the wrapper's name, with the `solution` body).

  Two prelude declarations are **imported, not re-proved**, both with the pin's statement
  read against the port's:

  * `det_eq` — `ModularForm.HeckeRepresentatives.det_eq`
    (`FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean`), same statement modulo the
    binder's name; the port's seven private copies are not added to;
  * `Gamma_le_Gamma1` — `CuspForm.LiNormSq.Gamma_le_Gamma1`
    (`FLTForHuman/ModularForms/Analytic/NormSqPow.lean`), the same statement
    `Gamma M ≤ Gamma1 M` with `M` a section variable of the port module, so it is applied
    as `... (M := N)` at its one use site.

  The pin's umbrella mathlib import is replaced by the targeted list below; its
  3,200,000-heartbeat override and its `p2m_reactivate` line are not carried
  (playbook §3.5).

spec-pin: Theorems/Thm_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers.lean
spec-pin: Theorems/Thm_CongruenceSubgroup_exists_finset_transversal_adapted_T_S.lean
spec-pin: Theorems/Thm_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff.lean
spec-pin: Theorems/Thm_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd.lean
spec-pin: P2M/Sol/S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers.lean
spec-pin: P2M/Sol/S_CongruenceSubgroup_exists_finset_transversal_adapted_T_S.lean
spec-pin: P2M/Sol/S_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff.lean
spec-pin: P2M/Sol/S_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd.lean
-/
import FLTForHuman.ModularForms.Analytic.NormSqPow
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace CongruenceSubgroup

/-! ## 1. Level lowering with a lower unipotent -/

namespace LowerUnipotent

open Matrix MatrixGroups CongruenceSubgroup Matrix.SpecialLinearGroup
open ModularForm.HeckeRepresentatives

def Low (x : ℤ) : SL(2, ℤ) := ⟨!![1, 0; x, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def Up (x : ℤ) : SL(2, ℤ) := ⟨!![1, x; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] lemma coe_Low (x : ℤ) : (Low x : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; x, 1] := rfl
@[scoped simp] lemma coe_Up (x : ℤ) : (Up x : Matrix (Fin 2) (Fin 2) ℤ) = !![1, x; 0, 1] := rfl

lemma Low_apply (x : ℤ) (i j : Fin 2) : (Low x) i j = !![(1 : ℤ), 0; x, 1] i j := rfl
lemma Up_apply (x : ℤ) (i j : Fin 2) : (Up x) i j = !![(1 : ℤ), x; 0, 1] i j := rfl

lemma Low_add (x y : ℤ) : Low (x + y) = Low x * Low y := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Low, coe_Low, coe_Low]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma Low_zero : Low 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma Low_neg (x : ℤ) : Low (-x) = (Low x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← Low_add, neg_add_cancel, Low_zero]

lemma Low_natMul (x : ℤ) (n : ℕ) : Low (n * x) = Low x ^ n := by
  induction n with
  | zero => simp [Low_zero]
  | succ n ih => rw [pow_succ, ← ih, ← Low_add]; congr 1; push_cast; ring

lemma Low_intMul (x : ℤ) (n : ℤ) : Low (n * x) = Low x ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, Low_natMul]
  · rw [_root_.zpow_neg, zpow_natCast, ← Low_natMul, ← Low_neg]; congr 1; ring

lemma Up_eq_T_zpow (x : ℤ) : Up x = ModularGroup.T ^ x := by
  ext i j
  rw [coe_Up, ModularGroup.coe_T_zpow]

lemma S_T_S_eq (n : ℤ) : ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S⁻¹ = Low (-n) := by
  ext i j
  rw [ModularGroup.S_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_neg,
    ModularGroup.coe_S, coe_Low]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section entries

variable (x : ℤ) (m : SL(2, ℤ))

lemma Up_mul_apply (i j : Fin 2) :
    (Up x * m) i j = !![m 0 0 + x * m 1 0, m 0 1 + x * m 1 1; m 1 0, m 1 1] i j := by
  show ((Up x * m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Up]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma mul_Low_apply (i j : Fin 2) :
    (m * Low x) i j = !![m 0 0 + m 0 1 * x, m 0 1; m 1 0 + m 1 1 * x, m 1 1] i j := by
  show ((m * Low x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Low]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma mul_Up_apply (i j : Fin 2) :
    (m * Up x) i j = !![m 0 0, m 0 0 * x + m 0 1; m 1 0, m 1 0 * x + m 1 1] i j := by
  show ((m * Up x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Up]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma Low_mul_apply (i j : Fin 2) :
    (Low x * m) i j = !![m 0 0, m 0 1; m 1 0 + x * m 0 0, m 1 1 + x * m 0 1] i j := by
  show ((Low x * m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Low]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end entries

lemma mem_Gamma_iff (n : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ Gamma n ↔ (n : ℤ) ∣ γ 0 0 - 1 ∧ (n : ℤ) ∣ γ 0 1 ∧ (n : ℤ) ∣ γ 1 0 ∧ (n : ℤ) ∣ γ 1 1 - 1 := by
  rw [Gamma_mem]
  have h1 : ∀ x : ℤ, ((x : ℤ) : ZMod n) = 1 ↔ (n : ℤ) ∣ x - 1 := fun x => by
    rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [h1, h1, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma Gamma_le_Gamma_of_dvd {A B : ℕ} (h : A ∣ B) : Gamma B ≤ Gamma A := by
  intro γ hγ
  rw [mem_Gamma_iff] at hγ ⊢
  have hAB : (A : ℤ) ∣ (B : ℤ) := Int.natCast_dvd_natCast.mpr h
  exact ⟨hAB.trans hγ.1, hAB.trans hγ.2.1, hAB.trans hγ.2.2.1, hAB.trans hγ.2.2.2⟩

lemma Low_mem_Gamma_of_dvd {n : ℕ} {x : ℤ} (h : (n : ℤ) ∣ x) : Low x ∈ Gamma n := by
  rw [mem_Gamma_iff]; simp [Low_apply, h]

lemma Up_mem_Gamma_of_dvd {n : ℕ} {x : ℤ} (h : (n : ℤ) ∣ x) : Up x ∈ Gamma n := by
  rw [mem_Gamma_iff]; simp [Up_apply, h]

lemma Up_mem_Gamma1 (n : ℕ) (x : ℤ) : Up x ∈ Gamma1 n := by
  rw [Gamma1_mem]; simp [Up_apply]

lemma mul_inv_mem_Gamma {n : ℕ} {x y : SL(2, ℤ)} (h : ∀ i j, (n : ℤ) ∣ y i j - x i j) :
    x * y⁻¹ ∈ Gamma n := by
  have hxy : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) x)
      = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) y := by
    ext i j
    rw [SL_reduction_mod_hom_val, SL_reduction_mod_hom_val, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact h i j
  rw [Gamma_mem', map_mul, map_inv, hxy, mul_inv_cancel]

section Main

variable {N p : ℕ} [NeZero N] (hp : p.Prime) (hpN : p ∣ N)

def G (N p : ℕ) : Subgroup SL(2, ℤ) :=
  (Gamma1 N ⊓ Gamma (N / p ^ N.factorization p)) ⊔
    Subgroup.zpowers (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹)

omit [NeZero N] in
lemma Low_mem_G (t : ℤ) : Low (t * ((N / p : ℕ) : ℤ)) ∈ G N p := by
  apply Subgroup.mem_sup_right
  rw [S_T_S_eq, show t * ((N / p : ℕ) : ℤ) = (-t) * (-((N / p : ℕ) : ℤ)) by ring, Low_intMul]
  exact Subgroup.zpow_mem_zpowers _ _

omit [NeZero N] in
lemma Low_mem_G_of_dvd {x : ℤ} (hx : (((N / p : ℕ) : ℤ)) ∣ x) : Low x ∈ G N p := by
  obtain ⟨t, rfl⟩ := hx
  rw [mul_comm]; exact Low_mem_G t

omit [NeZero N] in
lemma Up_mem_G {x : ℤ} (hx : ((N / p ^ N.factorization p : ℕ) : ℤ) ∣ x) : Up x ∈ G N p :=
  Subgroup.mem_sup_left ⟨Up_mem_Gamma1 N x, Up_mem_Gamma_of_dvd hx⟩

omit [NeZero N] in
lemma Gamma_le_G : Gamma N ≤ G N p := fun _γ hγ =>
  Subgroup.mem_sup_left ⟨CuspForm.LiNormSq.Gamma_le_Gamma1 (M := N) hγ,
    Gamma_le_Gamma_of_dvd (Nat.ordCompl_dvd N p) hγ⟩

include hp hpN

lemma setup :
    let q := p ^ N.factorization p
    let M := N / p ^ N.factorization p
    q * M = N ∧ (N / p) * p = N ∧ M ∣ N / p ∧ Nat.Coprime q M ∧ ¬ p ∣ M ∧ q ∣ N ∧ p ∣ q := by
  have hN : N ≠ 0 := NeZero.ne N
  have he : 0 < N.factorization p := hp.factorization_pos_of_dvd hN hpN
  refine ⟨Nat.ordProj_mul_ordCompl_eq_self N p, Nat.div_mul_cancel hpN, ?_, ?_,
    Nat.not_dvd_ordCompl hp hN, Nat.ordProj_dvd N p, dvd_pow_self p he.ne'⟩
  ·
    refine ⟨p ^ (N.factorization p - 1), ?_⟩
    have h1 : N = (N / p ^ N.factorization p) * p ^ N.factorization p :=
      (Nat.ordProj_mul_ordCompl_eq_self N p).symm.trans (mul_comm _ _)
    conv_lhs => rw [h1]
    rw [show p ^ N.factorization p = p ^ (N.factorization p - 1) * p by
      rw [← pow_succ, Nat.sub_add_cancel he], ← mul_assoc, Nat.mul_div_cancel _ hp.pos]
  · exact (Nat.coprime_ordCompl hp hN).pow_left _

lemma mem_G_of_not_dvd (m : SL(2, ℤ)) (hm : m ∈ Gamma (N / p)) (hd : ¬ (p : ℤ) ∣ m 1 1) :
    m ∈ G N p := by
  obtain ⟨hqM, hNp, hMN', hcop, hpM, hqN, hpq⟩ := setup hp hpN
  set q : ℕ := p ^ N.factorization p with hqdef
  set M : ℕ := N / p ^ N.factorization p with hMdef
  set N' : ℕ := N / p with hN'def
  have : Fact p.Prime := ⟨hp⟩
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNZ : (N : ℤ) = (N' : ℤ) * p := by exact_mod_cast hNp.symm
  have hNqM : (N : ℤ) = (q : ℤ) * M := by exact_mod_cast hqM.symm
  have hMN'Z : (M : ℤ) ∣ (N' : ℤ) := Int.natCast_dvd_natCast.mpr hMN'
  have hqNZ : (q : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hqN
  have hN'N : (N' : ℤ) ∣ (N : ℤ) := ⟨p, hNZ⟩
  have hMNZ : (M : ℤ) ∣ (N : ℤ) := hMN'Z.trans hN'N
  obtain ⟨ha, hb, hc, hdd⟩ := (mem_Gamma_iff _ _).mp hm

  obtain ⟨c', hc'⟩ := hc
  have hd0 : ((m 1 1 : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  set t : ℤ := -((((c' : ℤ) : ZMod p) * ((m 1 1 : ℤ) : ZMod p)⁻¹).val : ℤ) with htdef
  have ht : (p : ℤ) ∣ c' + m 1 1 * t := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, htdef]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_neg, mul_comm (((m 1 1 : ℤ) : ZMod p)), mul_assoc,
      inv_mul_cancel₀ hd0, mul_one, add_neg_cancel]
  set m₂ : SL(2, ℤ) := m * Low ((N' : ℤ) * t) with hm₂def
  have hm₂G : m₂ ∈ G N p ↔ m ∈ G N p := by
    rw [hm₂def]
    refine ⟨fun h => ?_, fun h => mul_mem h (Low_mem_G_of_dvd ⟨t, rfl⟩)⟩
    have := mul_mem h (inv_mem (Low_mem_G_of_dvd (N := N) (p := p) ⟨t, rfl⟩))
    rwa [mul_inv_cancel_right] at this
  rw [← hm₂G]

  have e₂00 : m₂ 0 0 = m 0 0 + m 0 1 * (N' * t) := by rw [hm₂def, mul_Low_apply]; rfl
  have e₂01 : m₂ 0 1 = m 0 1 := by rw [hm₂def, mul_Low_apply]; rfl
  have e₂10 : m₂ 1 0 = m 1 0 + m 1 1 * (N' * t) := by rw [hm₂def, mul_Low_apply]; rfl
  have e₂11 : m₂ 1 1 = m 1 1 := by rw [hm₂def, mul_Low_apply]; rfl
  have hc₂ : (N : ℤ) ∣ m₂ 1 0 := by
    rw [e₂10, hc', hNZ]
    have : (N' : ℤ) * c' + m 1 1 * (N' * t) = N' * (c' + m 1 1 * t) := by ring
    rw [this]
    exact mul_dvd_mul_left _ ht
  have hb₂ : (N' : ℤ) ∣ m₂ 0 1 := by rw [e₂01]; exact hb
  have ha₂ : (N' : ℤ) ∣ m₂ 0 0 - 1 := by
    rw [e₂00]
    have : m 0 0 + m 0 1 * (N' * t) - 1 = (m 0 0 - 1) + N' * (m 0 1 * t) := by ring
    rw [this]; exact dvd_add ha (dvd_mul_right _ _)
  have hd₂ : (N' : ℤ) ∣ m₂ 1 1 - 1 := by rw [e₂11]; exact hdd
  have hd₂p : ¬ (p : ℤ) ∣ m₂ 1 1 := by rw [e₂11]; exact hd
  have hdet₂ := det_eq m₂

  set β : ℤ := -(m₂ 0 1 * m₂ 0 0) with hβdef
  have hβM : (M : ℤ) ∣ β := by
    rw [hβdef]; exact (dvd_mul_of_dvd_left (hMN'Z.trans hb₂) _).neg_right
  set m₃ : SL(2, ℤ) := Up β * m₂ with hm₃def
  have hm₃G : m₃ ∈ G N p ↔ m₂ ∈ G N p := by
    rw [hm₃def]
    refine ⟨fun h => ?_, fun h => mul_mem (Up_mem_G hβM) h⟩
    have := mul_mem (inv_mem (Up_mem_G (N := N) (p := p) hβM)) h
    rwa [inv_mul_cancel_left] at this
  rw [← hm₃G]
  have e₃00 : m₃ 0 0 = m₂ 0 0 + β * m₂ 1 0 := by rw [hm₃def, Up_mul_apply]; rfl
  have e₃01 : m₃ 0 1 = m₂ 0 1 + β * m₂ 1 1 := by rw [hm₃def, Up_mul_apply]; rfl
  have e₃10 : m₃ 1 0 = m₂ 1 0 := by rw [hm₃def, Up_mul_apply]; rfl
  have e₃11 : m₃ 1 1 = m₂ 1 1 := by rw [hm₃def, Up_mul_apply]; rfl
  have hb₃ : (N : ℤ) ∣ m₃ 0 1 := by
    rw [e₃01, hβdef]
    have : m₂ 0 1 + -(m₂ 0 1 * m₂ 0 0) * m₂ 1 1 = -(m₂ 0 1 * m₂ 0 1) * m₂ 1 0 := by
      linear_combination (-(m₂ 0 1)) * hdet₂
    rw [this]; exact dvd_mul_of_dvd_right hc₂ _
  have hc₃ : (N : ℤ) ∣ m₃ 1 0 := by rw [e₃10]; exact hc₂
  have ha₃ : (N' : ℤ) ∣ m₃ 0 0 - 1 := by
    rw [e₃00]
    have : m₂ 0 0 + β * m₂ 1 0 - 1 = (m₂ 0 0 - 1) + β * m₂ 1 0 := by ring
    rw [this]; exact dvd_add ha₂ (dvd_mul_of_dvd_right (hN'N.trans hc₂) _)
  have hd₃ : (N' : ℤ) ∣ m₃ 1 1 - 1 := by rw [e₃11]; exact hd₂
  have hdet₃ := det_eq m₃
  have had₃ : (N : ℤ) ∣ m₃ 0 0 * m₃ 1 1 - 1 := by
    have : m₃ 0 0 * m₃ 1 1 - 1 = m₃ 0 1 * m₃ 1 0 := by linear_combination hdet₃
    rw [this]; exact dvd_mul_of_dvd_left hb₃ _

  set u : ℤ := (M : ℤ) * ((((M : ZMod q))⁻¹).val : ℤ) with hudef
  have : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
  have huq : (q : ℤ) ∣ u - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hudef]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one M hcop.symm, sub_self]
  have huM : (M : ℤ) ∣ u := ⟨_, rfl⟩
  set a₃ : ℤ := m₃ 0 0 with ha₃def
  set d₃ : ℤ := m₃ 1 1 with hd₃def
  set β₂ : ℤ := a₃ * u with hβ₂def
  set β₁ : ℤ := -u with hβ₁def
  set P : SL(2, ℤ) := Up β₂ * Low (1 - d₃) * Up β₁ * Low (1 - a₃) with hPdef
  have hLd : Low (1 - d₃) ∈ G N p := Low_mem_G_of_dvd (by
    have : 1 - d₃ = -(d₃ - 1) := by ring
    rw [this]; exact hd₃.neg_right)
  have hLa : Low (1 - a₃) ∈ G N p := Low_mem_G_of_dvd (by
    have : 1 - a₃ = -(a₃ - 1) := by ring
    rw [this]; exact ha₃.neg_right)
  have hβ₂M : (M : ℤ) ∣ β₂ := dvd_mul_of_dvd_right huM _
  have hβ₁M : (M : ℤ) ∣ β₁ := huM.neg_right
  have hPG : P ∈ G N p :=
    mul_mem (mul_mem (mul_mem (Up_mem_G hβ₂M) hLd) (Up_mem_G hβ₁M)) hLa

  have eP01 : P 0 1 = β₁ * (1 + β₂ * (1 - d₃)) + β₂ := by
    simp only [hPdef, mul_Up_apply, mul_Low_apply, Up_apply, of_apply, cons_val',
      cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring
  have eP11 : P 1 1 = β₁ * (1 - d₃) + 1 := by
    simp only [hPdef, mul_Up_apply, mul_Low_apply, Up_apply, of_apply, cons_val',
      cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring
  have eP00 : P 0 0 = (1 + β₂ * (1 - d₃)) + (β₁ * (1 + β₂ * (1 - d₃)) + β₂) * (1 - a₃) := by
    simp only [hPdef, mul_Up_apply, mul_Low_apply, Up_apply, of_apply, cons_val',
      cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring
  have eP10 : P 1 0 = (1 - d₃) + (β₁ * (1 - d₃) + 1) * (1 - a₃) := by
    simp only [hPdef, mul_Up_apply, mul_Low_apply, Up_apply, of_apply, cons_val',
      cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring

  have hqβ₁ : (q : ℤ) ∣ β₁ + 1 := by
    rw [hβ₁def, show -u + 1 = -(u - 1) by ring]; exact huq.neg_right
  have hqβ₂ : (q : ℤ) ∣ β₂ - a₃ := by
    rw [hβ₂def, show a₃ * u - a₃ = a₃ * (u - 1) by ring]; exact dvd_mul_of_dvd_right huq _
  have hqad : (q : ℤ) ∣ a₃ * d₃ - 1 := hqNZ.trans had₃
  have hq00 : (q : ℤ) ∣ P 0 0 - m₃ 0 0 := by
    rw [eP00, ← ha₃def]
    have : (1 + β₂ * (1 - d₃)) + (β₁ * (1 + β₂ * (1 - d₃)) + β₂) * (1 - a₃) - a₃
        = -(a₃ * d₃ - 1) + (β₂ - a₃) * (1 - d₃)
          + ((a₃ * d₃ - 1) + (β₂ - a₃) * d₃ + (β₁ + 1) * (1 + β₂ * (1 - d₃))) * (1 - a₃) := by
      ring
    rw [this]
    refine dvd_add (dvd_add hqad.neg_right (dvd_mul_of_dvd_left hqβ₂ _)) ?_
    exact dvd_mul_of_dvd_left (dvd_add (dvd_add hqad (dvd_mul_of_dvd_left hqβ₂ _))
      (dvd_mul_of_dvd_left hqβ₁ _)) _
  have hq01 : (q : ℤ) ∣ P 0 1 - m₃ 0 1 := by
    rw [eP01]
    have : β₁ * (1 + β₂ * (1 - d₃)) + β₂ - m₃ 0 1
        = (a₃ * d₃ - 1) + (β₂ - a₃) * d₃ + (β₁ + 1) * (1 + β₂ * (1 - d₃)) - m₃ 0 1 := by ring
    rw [this]
    exact dvd_sub (dvd_add (dvd_add hqad (dvd_mul_of_dvd_left hqβ₂ _))
      (dvd_mul_of_dvd_left hqβ₁ _)) (hqNZ.trans hb₃)
  have hq10 : (q : ℤ) ∣ P 1 0 - m₃ 1 0 := by
    rw [eP10]
    have : (1 - d₃) + (β₁ * (1 - d₃) + 1) * (1 - a₃) - m₃ 1 0
        = -(a₃ * d₃ - 1) + (β₁ + 1) * ((1 - d₃) * (1 - a₃)) - m₃ 1 0 := by ring
    rw [this]
    exact dvd_sub (dvd_add hqad.neg_right (dvd_mul_of_dvd_left hqβ₁ _)) (hqNZ.trans hc₃)
  have hq11 : (q : ℤ) ∣ P 1 1 - m₃ 1 1 := by
    rw [eP11, ← hd₃def]
    have : β₁ * (1 - d₃) + 1 - d₃ = (β₁ + 1) * (1 - d₃) := by ring
    rw [this]; exact dvd_mul_of_dvd_left hqβ₁ _

  have hMa : (M : ℤ) ∣ 1 - a₃ := by
    have : 1 - a₃ = -(a₃ - 1) := by ring
    rw [this]; exact (hMN'Z.trans ha₃).neg_right
  have hMd : (M : ℤ) ∣ 1 - d₃ := by
    have : 1 - d₃ = -(d₃ - 1) := by ring
    rw [this]; exact (hMN'Z.trans hd₃).neg_right
  have hM00 : (M : ℤ) ∣ P 0 0 - m₃ 0 0 := by
    rw [eP00, ← ha₃def]
    have : (1 + β₂ * (1 - d₃)) + (β₁ * (1 + β₂ * (1 - d₃)) + β₂) * (1 - a₃) - a₃
        = (1 - a₃) + β₂ * (1 - d₃) + (β₁ * (1 + β₂ * (1 - d₃)) + β₂) * (1 - a₃) := by ring
    rw [this]
    exact dvd_add (dvd_add hMa (dvd_mul_of_dvd_left hβ₂M _)) (dvd_mul_of_dvd_right hMa _)
  have hM01 : (M : ℤ) ∣ P 0 1 - m₃ 0 1 := by
    rw [eP01]
    exact dvd_sub (dvd_add (dvd_mul_of_dvd_left hβ₁M _) hβ₂M) (hMNZ.trans hb₃)
  have hM10 : (M : ℤ) ∣ P 1 0 - m₃ 1 0 := by
    rw [eP10]
    exact dvd_sub (dvd_add hMd (dvd_mul_of_dvd_right hMa _)) (hMNZ.trans hc₃)
  have hM11 : (M : ℤ) ∣ P 1 1 - m₃ 1 1 := by
    rw [eP11, ← hd₃def]
    have : β₁ * (1 - d₃) + 1 - d₃ = β₁ * (1 - d₃) + (1 - d₃) := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hMd _) hMd

  have hcopZ : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hN : ∀ i j, (N : ℤ) ∣ P i j - m₃ i j := by
    intro i j
    rw [hNqM]
    fin_cases i <;> fin_cases j
    · exact hcopZ.mul_dvd hq00 hM00
    · exact hcopZ.mul_dvd hq01 hM01
    · exact hcopZ.mul_dvd hq10 hM10
    · exact hcopZ.mul_dvd hq11 hM11
  have hmem : m₃ * P⁻¹ ∈ Gamma N := mul_inv_mem_Gamma hN
  have := mul_mem (Gamma_le_G hmem) hPG
  rwa [inv_mul_cancel_right] at this

theorem main : Gamma (N / p) ≤ G N p := by
  intro m hm
  obtain ⟨hqM, hNp, hMN', hcop, hpM, hqN, hpq⟩ := setup hp hpN
  by_cases hd : (p : ℤ) ∣ m 1 1
  ·
    have hL : Low (-((N / p : ℕ) : ℤ)) ∈ Gamma (N / p) := Low_mem_Gamma_of_dvd (dvd_neg.mpr dvd_rfl)
    have hm' : Low (-((N / p : ℕ) : ℤ)) * m ∈ Gamma (N / p) := mul_mem hL hm
    obtain ⟨ha, hb, hc, hdd⟩ := (mem_Gamma_iff _ _).mp hm
    have hdet := det_eq m

    have hpN' : ¬ (p : ℤ) ∣ ((N / p : ℕ) : ℤ) := by
      intro h
      have h1 : (p : ℤ) ∣ m 1 1 - 1 := h.trans hdd
      have : (p : ℤ) ∣ 1 := by
        have := dvd_sub hd h1; rwa [sub_sub_cancel] at this
      exact hp.one_lt.ne' (Int.natCast_dvd_natCast.mp (by simpa using this) |> Nat.dvd_one.mp)
    have hpb : ¬ (p : ℤ) ∣ m 0 1 := by
      intro h
      have : (p : ℤ) ∣ 1 := by
        rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_right hd _) (dvd_mul_of_dvd_left h _)
      exact hp.one_lt.ne' (Int.natCast_dvd_natCast.mp (by simpa using this) |> Nat.dvd_one.mp)
    have hd' : ¬ (p : ℤ) ∣ (Low (-((N / p : ℕ) : ℤ)) * m) 1 1 := by
      rw [Low_mul_apply]
      simp only [of_apply, cons_val', cons_val_one, empty_val', cons_val_fin_one]
      intro h
      have h2 : (p : ℤ) ∣ -((N / p : ℕ) : ℤ) * m 0 1 := by
        have := dvd_sub h hd; rwa [add_sub_cancel_left] at this
      rw [neg_mul, dvd_neg] at h2
      rcases (Int.Prime.dvd_mul' hp h2) with h3 | h3
      · exact hpN' h3
      · exact hpb h3
    have hmem := mem_G_of_not_dvd hp hpN _ hm' hd'
    have hLG : Low (-((N / p : ℕ) : ℤ)) ∈ G N p :=
      Low_mem_G_of_dvd (dvd_neg.mpr dvd_rfl)
    have := mul_mem (inv_mem hLG) hmem
    rwa [inv_mul_cancel_left] at this
  · exact mem_G_of_not_dvd hp hpN m hm hd

end Main

end LowerUnipotent

open LowerUnipotent in
theorem Gamma_div_le_gamma1_inf_Gamma_sup_zpowers
    (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N) :
    Gamma (N / p) ≤ (Gamma1 N ⊓ Gamma (N / p ^ N.factorization p)) ⊔
      Subgroup.zpowers (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) :=
  LowerUnipotent.main hp hpN

/-! ## 2. A finite transversal of `±Γ` adapted to `T` and `S` -/

theorem exists_finset_transversal_adapted_T_S
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hS₀ : ∀ j : ℤ, ModularGroup.S * ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.S * ModularGroup.T ^ j) ∉ Γ)
    (h₀ : ℕ) (hh₀ : 0 < h₀) (hT : ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ)
    (hmin : ∀ j : ℕ, 0 < j → j < h₀ → ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.T ^ j) ∉ Γ) :
    ∃ s : Finset SL(2, ℤ),
      (∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ Γ ∨ -(g * x⁻¹) ∈ Γ) ∧
      (∀ x ∈ s, ∀ y ∈ s, (x * y⁻¹ ∈ Γ ∨ -(x * y⁻¹) ∈ Γ) → x = y) ∧
      (∀ j : ℕ, j < h₀ → ModularGroup.T ^ j ∈ s) ∧ ModularGroup.S ∈ s ∧
      (∀ x ∈ s, (∀ j : ℕ, j < h₀ → x ≠ ModularGroup.T ^ j) → x ≠ ModularGroup.S →
        (∀ j : ℤ, x * ModularGroup.T ^ j ∉ Γ ∧ -(x * ModularGroup.T ^ j) ∉ Γ) ∧
        (x * ModularGroup.S⁻¹ ∉ Γ ∧ -(x * ModularGroup.S⁻¹) ∉ Γ)) := by
  classical

  have hneg_inv : ∀ g : SL(2, ℤ), (-g)⁻¹ = -g⁻¹ := fun g =>
    inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  let Γ' : Subgroup SL(2, ℤ) :=
    { carrier := {g | g ∈ Γ ∨ -g ∈ Γ}
      one_mem' := Or.inl Γ.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (Γ.mul_mem ha hb)
        · exact Or.inr (by rw [← mul_neg]; exact Γ.mul_mem ha hb)
        · exact Or.inr (by rw [← neg_mul]; exact Γ.mul_mem ha hb)
        · exact Or.inl (by rw [← neg_mul_neg]; exact Γ.mul_mem ha hb)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (Γ.inv_mem ha)
        · exact Or.inr (by rw [← hneg_inv]; exact Γ.inv_mem ha) }
  have hmemΓ' : ∀ g : SL(2, ℤ), g ∈ Γ' ↔ (g ∈ Γ ∨ -g ∈ Γ) := fun g => Iff.rfl
  have hnotΓ' : ∀ g : SL(2, ℤ), g ∉ Γ' ↔ (g ∉ Γ ∧ -g ∉ Γ) := fun g => by rw [hmemΓ', not_or]
  have hΓle : Γ ≤ Γ' := fun g hg => Or.inl hg
  have : Γ'.FiniteIndex := Subgroup.finiteIndex_of_le hΓle

  let Q := Quotient (QuotientGroup.rightRel Γ')
  let π : SL(2, ℤ) → Q := Quotient.mk _
  have hπ : ∀ x y : SL(2, ℤ), π x = π y ↔ y * x⁻¹ ∈ Γ' := fun x y => by
    rw [Quotient.eq]; exact QuotientGroup.rightRel_apply
  have hπout : ∀ c : Q, π (Quotient.out c) = c := fun c => Quotient.out_eq c
  have : Finite Q := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm
  let : Fintype Q := Fintype.ofFinite Q

  set T := ModularGroup.T with hTdef
  set S := ModularGroup.S with hSdef
  have hh : (0 : ℤ) < h₀ := by exact_mod_cast hh₀
  have hTh₀ : T ^ (h₀ : ℤ) ∈ Γ' := by rw [zpow_natCast]; exact hT
  have hTmul : ∀ q : ℤ, T ^ ((h₀ : ℤ) * q) ∈ Γ' := fun q => by
    rw [zpow_mul]; exact Γ'.zpow_mem hTh₀ q
  have hTsmall : ∀ n : ℤ, T ^ n ∈ Γ' → (h₀ : ℤ) ∣ n := by
    intro n hn
    set r := n % (h₀ : ℤ) with hr
    set q := n / (h₀ : ℤ) with hq
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hh.ne'
    have hrlt : r < h₀ := Int.emod_lt_of_pos _ hh
    have hrq : r + (h₀ : ℤ) * q = n := Int.emod_add_mul_ediv n h₀

    have hTr : T ^ (r.toNat : ℕ) ∈ Γ' := by
      have e : T ^ (r.toNat : ℕ) = T ^ n * (T ^ ((h₀ : ℤ) * q))⁻¹ := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hr0, ← zpow_neg, ← zpow_add]
        congr 1
        linarith
      rw [e]
      exact Γ'.mul_mem hn (Γ'.inv_mem (hTmul q))
    have hr00 : r.toNat = 0 := by
      by_contra hne
      have hpos : 0 < r.toNat := Nat.pos_of_ne_zero hne
      have hlt : r.toNat < h₀ := by
        have : ((r.toNat : ℕ) : ℤ) < h₀ := by rw [Int.toNat_of_nonneg hr0]; exact hrlt
        exact_mod_cast this
      exact ((hnotΓ' _).mpr (hmin r.toNat hpos hlt)) hTr
    have hr0' : r = 0 := by
      have := Int.toNat_of_nonneg hr0
      rw [hr00] at this
      exact_mod_cast this.symm
    exact Int.dvd_of_emod_eq_zero hr0'

  let P : Finset SL(2, ℤ) := insert S ((Finset.range h₀).image fun j => T ^ j)
  have hmemP : ∀ x : SL(2, ℤ), x ∈ P ↔ x = S ∨ ∃ j, j < h₀ ∧ x = T ^ j := by
    intro x
    simp only [P, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨j, hj, rfl⟩
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨j, hj, rfl⟩
  have hTS : ∀ i : ℕ, i < h₀ → π (T ^ i) ≠ π S := by
    intro i hi h
    rw [hπ] at h

    have : S * T ^ (-(i : ℤ)) ∈ Γ' := by rwa [zpow_neg, zpow_natCast]
    exact ((hnotΓ' _).mpr (hS₀ (-(i : ℤ)))) this
  have hTT : ∀ i j : ℕ, i < h₀ → j < h₀ → π (T ^ i) = π (T ^ j) → i = j := by
    intro i j hi hj h
    rw [hπ] at h
    have hmem : T ^ ((j : ℤ) - (i : ℤ)) ∈ Γ' := by
      rwa [zpow_sub, zpow_natCast, zpow_natCast]
    have hdvd := hTsmall _ hmem
    have habs : |(j : ℤ) - (i : ℤ)| < h₀ := by
      rw [abs_sub_lt_iff]; constructor <;> omega
    have h0 : (j : ℤ) - (i : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  have hPinj : ∀ x ∈ P, ∀ y ∈ P, π x = π y → x = y := by
    intro x hx y hy h
    rcases (hmemP x).mp hx with rfl | ⟨i, hi, rfl⟩ <;> rcases (hmemP y).mp hy with rfl | ⟨j, hj, rfl⟩
    · rfl
    · exact absurd h.symm (hTS j hj)
    · exact absurd h (hTS i hi)
    · rw [hTT i j hi hj h]

  let rest : Finset SL(2, ℤ) := (Finset.univ.filter fun c : Q => c ∉ P.image π).image Quotient.out
  have hmemrest : ∀ y : SL(2, ℤ), y ∈ rest ↔ ∃ c : Q, c ∉ P.image π ∧ Quotient.out c = y := by
    intro y
    simp only [rest, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  let s : Finset SL(2, ℤ) := P ∪ rest
  have hmems : ∀ x : SL(2, ℤ), x ∈ s ↔ x ∈ P ∨ x ∈ rest := fun x => Finset.mem_union

  have hsinj : ∀ x ∈ s, ∀ y ∈ s, π x = π y → x = y := by
    intro x hx y hy h
    rcases (hmems x).mp hx with hx | hx <;> rcases (hmems y).mp hy with hy | hy
    · exact hPinj x hx y hy h
    · obtain ⟨c, hc, rfl⟩ := (hmemrest y).mp hy
      exact absurd (Finset.mem_image.mpr ⟨x, hx, by rw [h, hπout]⟩) hc
    · obtain ⟨c, hc, rfl⟩ := (hmemrest x).mp hx
      exact absurd (Finset.mem_image.mpr ⟨y, hy, by rw [← h, hπout]⟩) hc
    · obtain ⟨c, hc, rfl⟩ := (hmemrest x).mp hx
      obtain ⟨c', hc', rfl⟩ := (hmemrest y).mp hy
      rw [hπout, hπout] at h
      rw [h]
  have hTs : ∀ j : ℕ, j < h₀ → T ^ j ∈ s := fun j hj =>
    (hmems _).mpr (Or.inl ((hmemP _).mpr (Or.inr ⟨j, hj, rfl⟩)))
  have hSs : S ∈ s := (hmems _).mpr (Or.inl ((hmemP _).mpr (Or.inl rfl)))
  refine ⟨s, ?_, ?_, hTs, hSs, ?_⟩
  ·
    intro g
    by_cases hc : π g ∈ P.image π
    · obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp hc
      exact ⟨x, (hmems _).mpr (Or.inl hx), (hπ x g).mp hxc⟩
    · refine ⟨Quotient.out (π g), (hmems _).mpr (Or.inr ((hmemrest _).mpr ⟨π g, hc, rfl⟩)), ?_⟩
      exact (hπ _ g).mp (hπout _)
  ·
    intro x hx y hy hxy
    exact (hsinj y hy x hx ((hπ y x).mpr hxy)).symm
  ·
    intro x hx hxT hxS
    constructor
    · intro j
      rw [← hnotΓ']
      intro hmem

      set r := (-j) % (h₀ : ℤ) with hr
      set q := (-j) / (h₀ : ℤ) with hq
      have hr0 : 0 ≤ r := Int.emod_nonneg _ hh.ne'
      have hrlt : r < h₀ := Int.emod_lt_of_pos _ hh
      have hrq : r + (h₀ : ℤ) * q = -j := Int.emod_add_mul_ediv (-j) h₀
      have hrn : r.toNat < h₀ := by
        have : ((r.toNat : ℕ) : ℤ) < h₀ := by rw [Int.toNat_of_nonneg hr0]; exact hrlt
        exact_mod_cast this
      have e : x * (T ^ (r.toNat : ℕ))⁻¹ = (x * T ^ j) * T ^ ((h₀ : ℤ) * q) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hr0, ← zpow_neg, mul_assoc, ← zpow_add]
        congr 2
        linarith
      have hcos : x * (T ^ (r.toNat : ℕ))⁻¹ ∈ Γ' := by rw [e]; exact Γ'.mul_mem hmem (hTmul q)
      have := hsinj x hx (T ^ r.toNat) (hTs _ hrn) ((hπ (T ^ r.toNat) x).mpr hcos).symm
      exact hxT _ hrn this
    · rw [← hnotΓ']
      intro hmem
      have := hsinj x hx S hSs ((hπ S x).mpr hmem).symm
      exact hxS this

/-! ## 3. First-column criteria for `±Γ₁(N)` -/

namespace FirstColumn

open Matrix

theorem coe_mul_T_zpow_mul_S_inv (β : SL(2, ℤ)) (j : ℤ) :
    ((β * ModularGroup.T ^ j * ModularGroup.S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-((β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * j + (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1), (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0;
         -((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * j + (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1), (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0] := by
  have hS : ((ModularGroup.S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, hS]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end FirstColumn

open FirstColumn in
theorem mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff
    (N : ℕ) (β : SL(2, ℤ)) :
    ((β ∈ CongruenceSubgroup.Gamma1 N ∨ -β ∈ CongruenceSubgroup.Gamma1 N) ↔
        (((β 1 0 : ℤ) : ZMod N) = 0 ∧
          (((β 0 0 : ℤ) : ZMod N) = 1 ∨ ((β 0 0 : ℤ) : ZMod N) = -1))) ∧
    ((∃ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma1 N ∨
        -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∈ CongruenceSubgroup.Gamma1 N) ↔
        (((β 1 0 : ℤ) : ZMod N) = 1 ∨ ((β 1 0 : ℤ) : ZMod N) = -1)) ∧
    (∃ a b : ZMod N, a * ((β 0 0 : ℤ) : ZMod N) + b * ((β 1 0 : ℤ) : ZMod N) = 1) := by

  set a : ℤ := (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have h := β.det_coe
    rw [Matrix.det_fin_two] at h
    simp only [← ha, ← hb, ← hc, ← hd] at h
    linarith
  have hdetN : (a : ZMod N) * (d : ZMod N) - (b : ZMod N) * (c : ZMod N) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    exact h

  have hmem : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N ↔
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) = 1 ∧ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = 1 ∧
        (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := fun γ => CongruenceSubgroup.Gamma1_mem N γ
  have hneg : ∀ (γ : SL(2, ℤ)) (i k : Fin 2), ((-γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i k = -((γ : Matrix (Fin 2) (Fin 2) ℤ) i k) := by
    intro γ i k
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  refine ⟨?_, ?_, ?_⟩
  ·
    constructor
    · rintro (h | h)
      · obtain ⟨h00, -, h10⟩ := (hmem β).mp h
        exact ⟨h10, Or.inl h00⟩
      · obtain ⟨h00, -, h10⟩ := (hmem (-β)).mp h
        rw [hneg] at h00 h10
        push_cast at h00 h10
        refine ⟨?_, Or.inr ?_⟩
        · have : ((c : ZMod N)) = 0 := by
            have h' : -(c : ZMod N) = 0 := h10
            exact neg_eq_zero.mp h'
          exact this
        · have h' : -(a : ZMod N) = 1 := h00
          have : (a : ZMod N) = -1 := by rw [← h']; ring
          exact this
    · rintro ⟨h10, h00 | h00⟩
      · left
        refine (hmem β).mpr ⟨h00, ?_, h10⟩
        have hc0 : (c : ZMod N) = 0 := h10
        have ha1 : (a : ZMod N) = 1 := h00
        have : (d : ZMod N) = 1 := by
          have h := hdetN
          rw [hc0, ha1, mul_zero, sub_zero, one_mul] at h
          exact h
        exact this
      · right
        refine (hmem (-β)).mpr ⟨?_, ?_, ?_⟩
        · rw [hneg]; push_cast
          have ha1 : (a : ZMod N) = -1 := h00
          show -(a : ZMod N) = 1
          rw [ha1, neg_neg]
        · rw [hneg]; push_cast
          have hc0 : (c : ZMod N) = 0 := h10
          have ha1 : (a : ZMod N) = -1 := h00
          show -(d : ZMod N) = 1
          have h := hdetN
          rw [hc0, ha1, mul_zero, sub_zero] at h
          linear_combination h
        · rw [hneg]; push_cast
          have hc0 : (c : ZMod N) = 0 := h10
          show -(c : ZMod N) = 0
          rw [hc0, neg_zero]
  ·
    constructor
    · rintro ⟨j, h | h⟩
      · obtain ⟨-, h11, -⟩ := (hmem _).mp h
        rw [FirstColumn.coe_mul_T_zpow_mul_S_inv] at h11
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one] at h11
        exact Or.inl h11
      · obtain ⟨-, h11, -⟩ := (hmem _).mp h
        rw [hneg, FirstColumn.coe_mul_T_zpow_mul_S_inv] at h11
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one] at h11
        push_cast at h11
        right
        have h' : -(c : ZMod N) = 1 := h11
        rw [← h']; ring
    · rintro (h10 | h10)
      ·
        refine ⟨-d, Or.inl ((hmem _).mpr ?_)⟩
        rw [FirstColumn.coe_mul_T_zpow_mul_S_inv]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one]
        push_cast
        have hc1 : (c : ZMod N) = 1 := h10
        refine ⟨?_, hc1, ?_⟩
        ·
          have h := hdetN
          rw [hc1, mul_one] at h
          linear_combination h
        ·
          rw [hc1]; ring
      ·
        refine ⟨d, Or.inr ((hmem _).mpr ?_)⟩
        rw [hneg, hneg, hneg, FirstColumn.coe_mul_T_zpow_mul_S_inv]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one]
        push_cast
        have hc1 : (c : ZMod N) = -1 := h10
        refine ⟨?_, ?_, ?_⟩
        ·
          have h := hdetN
          rw [hc1] at h
          linear_combination h
        · rw [hc1]; ring
        · rw [hc1]; ring
  ·
    exact ⟨(d : ZMod N), -(b : ZMod N), by linear_combination hdetN⟩

/-! ## 4. The relative index of `Γ₁(M) ⊓ Γ₀(Mq)` -/

namespace Index

variable {M : ℕ}

private theorem dvd_entry (γ : ↥(Gamma1 M)) : (M : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  have h := ((Gamma1_mem M γ).mp γ.2).2.2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

variable (M) (q : ℕ)

private noncomputable def cHom [NeZero M] (hq : q ∣ M) : ↥(Gamma1 M) →* Multiplicative (ZMod q) where
  toFun γ := Multiplicative.ofAdd ((((γ : SL(2, ℤ)) 1 0 / (M : ℤ) : ℤ) : ZMod q))
  map_one' := by simp
  map_mul' γ δ := by
    obtain ⟨k₁, hk₁⟩ := dvd_entry γ
    obtain ⟨k₂, hk₂⟩ := dvd_entry δ
    have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    have hmul : ((γ * δ : ↥(Gamma1 M)) : SL(2, ℤ)) 1 0 =
        (M : ℤ) * (k₁ * (δ : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 1 1 * k₂) := by
      have h1 : ((γ * δ : ↥(Gamma1 M)) : SL(2, ℤ)) 1 0 =
          (γ : SL(2, ℤ)) 1 0 * (δ : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 1 1 * (δ : SL(2, ℤ)) 1 0 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [h1, hk₁, hk₂]; ring
    rw [← ofAdd_add]
    congr 1
    rw [hmul, hk₁, hk₂, Int.mul_ediv_cancel_left _ hM, Int.mul_ediv_cancel_left _ hM,
      Int.mul_ediv_cancel_left _ hM]
    have ha : (((δ : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) = 1 := by
      have h := ((Gamma1_mem M δ).mp δ.2).1
      have h' := congrArg (ZMod.castHom hq (ZMod q)) h
      rwa [map_intCast, map_one] at h'
    have hd : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod q) = 1 := by
      have h := ((Gamma1_mem M γ).mp γ.2).2.1
      have h' := congrArg (ZMod.castHom hq (ZMod q)) h
      rwa [map_intCast, map_one] at h'
    push_cast
    rw [ha, hd, mul_one, one_mul]

private theorem cHom_apply [NeZero M] (hq : q ∣ M) (γ : ↥(Gamma1 M)) :
    cHom M q hq γ = Multiplicative.ofAdd ((((γ : SL(2, ℤ)) 1 0 / (M : ℤ) : ℤ) : ZMod q)) := rfl

private theorem cHom_eq_one_iff [NeZero M] (hq : q ∣ M) (γ : ↥(Gamma1 M)) :
    cHom M q hq γ = 1 ↔ (γ : SL(2, ℤ)) ∈ Gamma0 (M * q) := by
  obtain ⟨k, hk⟩ := dvd_entry γ
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [cHom_apply, ofAdd_eq_one, hk, Int.mul_ediv_cancel_left _ hM, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, hk, Nat.cast_mul]
  exact (mul_dvd_mul_iff_left hM).symm

private theorem cHom_surjective [NeZero M] (hq : q ∣ M) : Function.Surjective (cHom M q hq) := by
  intro x
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective (Multiplicative.toAdd x)
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  let A : SL(2, ℤ) := ⟨!![1, 0; (M : ℤ) * j, 1], by simp [Matrix.det_fin_two_of]⟩
  have hA : A ∈ Gamma1 M := by
    rw [Gamma1_mem]
    simp [A]
  refine ⟨⟨A, hA⟩, ?_⟩
  rw [cHom_apply]
  have h10 : ((⟨A, hA⟩ : ↥(Gamma1 M)) : SL(2, ℤ)) 1 0 = (M : ℤ) * j := by
    simp [A]
  rw [h10, Int.mul_ediv_cancel_left _ hM, hj]
  rfl

end Index

open Index in
theorem relIndex_gamma1_inf_gamma0_mul_of_dvd (M q : ℕ) [NeZero M] (hq : q ∣ M) :
    (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * q)).relIndex (CongruenceSubgroup.Gamma1 M) = q := by
  have hker : (Gamma1 M ⊓ Gamma0 (M * q)).subgroupOf (Gamma1 M) = (cHom M q hq).ker := by
    ext γ
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf, cHom_eq_one_iff]
    exact ⟨fun h => h.2, fun h => ⟨γ.2, h⟩⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (cHom_surjective M q hq),
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end CongruenceSubgroup
