/-
  The bottom-row and torsion-orbit counts of the level structure `Γ_H(M) ⊆ SL(2, ℤ)`
  (level `M ≥ 1`, `H ≤ (ZMod M)ˣ`):

  * every vector `v` of additive order `M` in `(ZMod M)²` is the bottom row of a
    matrix in `SL(2, ℤ)`, every bottom row has order `M`, and two bottom rows have
    the same `Γ_H(M)`-torsion orbit exactly when `b a⁻¹ ∈ Γ_H(M) ⊔ ⟨-1⟩`
    (`CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff`);
  * consequently, for any abelian group `A` with `A[M] ≃ (ZMod M)²`, the number of
    torsion orbits of points of order `M` is the index
    `[Γ_H(M) ⊔ ⟨-1⟩ : 1]` (`AddCommGroup.natCard_torsionOrbit_gammaH_eq_index`).

  The port of the two pin leaves

      `CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff` (300 pin
      lines) and `AddCommGroup.natCard_torsionOrbit_gammaH_eq_index` (368 pin lines),

  together with the statements of their `Theorems/` wrappers. The pin's `S_`
  developments are `namespace P2MKcLEVEL` and `namespace P2MKcXHCount`, kept here
  under the pin's own namespaces and its short names untouched. The pin's
  `Theorems/Thm_CohCarrier_…` import becomes the previous declaration in this
  module. It is a faithful transcription: no statement is weakened, no route is
  generalised, and the pin's proofs are carried verbatim (`spec/check_port.py`
  diffs every public declaration below against the four files named here).

  The mathematics. The bottom-row statements are determinant bookkeeping: a vector
  of order `M` has coprime coordinates, Bézout (`Nat.gcd_eq_gcd_ab`) completes it to
  a determinant-one matrix over `ZMod M`, and surjectivity of
  `SL(2, ℤ) → SL(2, ZMod M)` (`ModularCurve.surjective_specialLinearGroup_map_zmod`)
  lifts that matrix. The orbit statement reduces `u ∈ H ⊔ ⟨-1⟩` to `u ∈ H ∨ -u ∈ H`
  (`mem_Hpm_iff`, using `-1`'s order two), and `row M (b a⁻¹) = (0, u)` is exactly
  the `Γ_H`-condition (`row_of_mem_GammaH`, `mem_GammaH_of_row`). The count is then
  a bijection between `A`-orbits and `(ZMod M)²`-orbits (`theta`, from the given
  `e : (ZMod M)² ≃ A[M]`), the latter identified with the orbit of the level
  structure under `SL(2, ℤ)` and hence with the coset space
  (`MulAction.orbitEquivQuotientStabilizer`).

  Assumes: `FLTForHuman.ModularForms.Defs.CohCarrierLower` (the port of
  `Def_CohCarrier_Level`, providing `CohCarrier.GammaH`, `mem_GammaH_iff`,
  `gamma0Units`, `val_gamma0Units`),
  `FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul` (the port of
  `Thm_ModularCurve_surjective_specialLinearGroup_map_zmod`) and mathlib `v4.34.0`.
  No `Def_` module is re-proved.

  Drift against mathlib `v4.34.0`, and two recorded deviations:

  * `Set.equivOfEq` replaces the pin's `Equiv.setCongr` (the name now denotes
    `Set α ≃ Set β` for an `α ≃ β`), in `natCard_XV`;
  * `omit [NeZero M] in` is added to the 28 declarations the pin's file-wide
    `set_option linter.unusedSectionVars false` suppressed; the pin's `haveI` for
    `MulAction.IsPretransitive` is a `have` (the `linter.style.haveILetI`
    suggestion).
  * **Six residual `linter.unusedSectionVars` warnings, unavoidable without a
    suppression** (`addOrderOf_row`, `mem_orb_self`, `XH.eq_orb_of_mem`,
    `ractHom_injective`, `X0_val`, `theta_bijective`): each *proof* needs
    `[NeZero M]` (through `ZMod.natCast_zmod_val` and the `val_nsmul_V` chain) while
    its *statement* does not, so `omit` removes an instance the proof uses and Lean
    offers no other repair; the statement text is the pin's. Recorded, not hidden.

  spec-pin: Theorems/Thm_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff.lean
  spec-pin: Theorems/Thm_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index.lean
  spec-pin: P2M/Sol/S_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff.lean
  spec-pin: P2M/Sol/S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index.lean
-/

import FLTForHuman.ModularForms.Defs.CohCarrierLower
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

namespace P2MKcLEVEL

variable {M : ℕ} [NeZero M]

abbrev V (M : ℕ) : Type := ZMod M × ZMod M

omit [NeZero M] in
theorem nsmul_V (n : ℕ) (v : V M) : n • v = ((n : ZMod M) * v.1, (n : ZMod M) * v.2) := by
  ext <;> simp [nsmul_eq_mul]

theorem val_nsmul_V (u : ZMod M) (v : V M) : u.val • v = (u * v.1, u * v.2) := by
  rw [nsmul_V, ZMod.natCast_zmod_val]

omit [NeZero M] in
theorem M_nsmul_V (v : V M) : M • v = 0 := by
  rw [nsmul_V, ZMod.natCast_self]; simp

variable (H : Subgroup (ZMod M)ˣ)

abbrev orb (v : V M) : Set (V M) :=
  {w | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ w = (u : ZMod M).val • v}

theorem mem_orb_self (v : V M) : v ∈ orb H v :=
  ⟨1, Subgroup.one_mem _, by rw [val_nsmul_V]; simp⟩

theorem orb_eq_of_mem {v w : V M} (hw : w ∈ orb H v) : orb H w = orb H v := by
  obtain ⟨u, hu, rfl⟩ := hw
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * u, Subgroup.mul_mem _ ht hu, ?_⟩
    rw [val_nsmul_V, val_nsmul_V, val_nsmul_V, Units.val_mul]
    ext <;> simp [mul_assoc]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * u⁻¹, Subgroup.mul_mem _ ht (Subgroup.inv_mem _ hu), ?_⟩
    rw [val_nsmul_V, val_nsmul_V, val_nsmul_V, Units.val_mul]
    ext <;> simp [mul_assoc]

abbrev ent (M : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : ZMod M := ((g i j : ℤ) : ZMod M)

abbrev row (M : ℕ) (g : SL(2, ℤ)) : V M := (ent M g 1 0, ent M g 1 1)

def ract (v : V M) (g : SL(2, ℤ)) : V M :=
  (v.1 * ent M g 0 0 + v.2 * ent M g 1 0, v.1 * ent M g 0 1 + v.2 * ent M g 1 1)

omit [NeZero M] in
theorem ent_mul (g h : SL(2, ℤ)) (i j : Fin 2) :
    ent M (g * h) i j = ent M g i 0 * ent M h 0 j + ent M g i 1 * ent M h 1 j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

omit [NeZero M] in
theorem ent_one (i j : Fin 2) : ent M 1 i j = if i = j then 1 else 0 := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  split_ifs <;> simp

omit [NeZero M] in
theorem ent_neg (g : SL(2, ℤ)) (i j : Fin 2) : ent M (-g) i j = -ent M g i j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_neg]
  rw [Matrix.neg_apply]
  push_cast
  rfl

omit [NeZero M] in
theorem ract_one (v : V M) : ract v 1 = v := by
  simp only [ract, ent_one]
  simp

omit [NeZero M] in
theorem ract_mul (v : V M) (g h : SL(2, ℤ)) : ract v (g * h) = ract (ract v g) h := by
  simp only [ract, ent_mul]
  ext <;> ring

omit [NeZero M] in
theorem row_mul (g h : SL(2, ℤ)) : row M (g * h) = ract (row M g) h := by
  simp only [row, ract, ent_mul]

omit [NeZero M] in
theorem row_neg (g : SL(2, ℤ)) : row M (-g) = -row M g := by
  simp only [row, ent_neg]; rfl

omit [NeZero M] in
theorem ract_injective (g : SL(2, ℤ)) : Function.Injective (fun v : V M => ract v g) := by
  intro v w h
  have := congrArg (fun z => ract z g⁻¹) h
  simpa only [← ract_mul, mul_inv_cancel, ract_one] using this

theorem ract_zero_u (u : ZMod M) (a : SL(2, ℤ)) : ract ((0 : ZMod M), u) a = u.val • row M a := by
  rw [val_nsmul_V]
  simp [ract]

omit [NeZero M] in
theorem det_row (a : SL(2, ℤ)) : ent M a 0 0 * ent M a 1 1 - ent M a 0 1 * ent M a 1 0 = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe a
  rw [Matrix.det_fin_two] at hdet
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h
  simpa [ent, mul_comm] using h

omit [NeZero M] in
theorem addOrderOf_eq_of_combination (v : V M) (x y : ZMod M) (h : x * v.1 + y * v.2 = 1) :
    addOrderOf v = M := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (M_nsmul_V v)
  · have h0 : addOrderOf v • v = 0 := addOrderOf_nsmul_eq_zero v
    rw [nsmul_V] at h0
    have h1 : (addOrderOf v : ZMod M) * v.1 = 0 := congrArg Prod.fst h0
    have h2 : (addOrderOf v : ZMod M) * v.2 = 0 := congrArg Prod.snd h0
    have : (addOrderOf v : ZMod M) = 0 := by
      calc (addOrderOf v : ZMod M) = (addOrderOf v : ZMod M) * (x * v.1 + y * v.2) := by rw [h, mul_one]
        _ = x * ((addOrderOf v : ZMod M) * v.1) + y * ((addOrderOf v : ZMod M) * v.2) := by ring
        _ = 0 := by rw [h1, h2]; ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp this

set_option linter.unusedSectionVars false in
theorem addOrderOf_row (a : SL(2, ℤ)) : addOrderOf (row M a) = M :=
  addOrderOf_eq_of_combination (row M a) (-ent M a 0 1) (ent M a 0 0)
    (by have := det_row (M := M) a; linear_combination this)

theorem exists_combination_of_addOrderOf_eq (v : V M) (hv : addOrderOf v = M) :
    ∃ x y : ZMod M, x * v.1 + y * v.2 = 1 := by
  set c : ℕ := v.1.val with hc
  set d : ℕ := v.2.val with hd
  have hcv : (c : ZMod M) = v.1 := ZMod.natCast_zmod_val v.1
  have hdv : (d : ZMod M) = v.2 := ZMod.natCast_zmod_val v.2
  set g : ℕ := Nat.gcd c d with hg
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)

  have hcop : Nat.Coprime g M := by
    apply Nat.coprime_of_dvd
    intro k hk hkg hkM
    have hkc : k ∣ c := hkg.trans (Nat.gcd_dvd_left c d)
    have hkd : k ∣ d := hkg.trans (Nat.gcd_dvd_right c d)
    obtain ⟨m, hm⟩ := hkM
    have hcast : ∀ t : ℕ, k ∣ t → ((m * t : ℕ) : ZMod M) = 0 := by
      intro t ht
      obtain ⟨t', rfl⟩ := ht
      have : m * (k * t') = M * t' := by rw [hm]; ring
      rw [this, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    have hmv : m • v = 0 := by
      rw [nsmul_V, ← hcv, ← hdv, ← Nat.cast_mul, ← Nat.cast_mul, hcast c hkc, hcast d hkd]
      rfl
    have hdvd : M ∣ m := by rw [← hv]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hmv
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hm; exact NeZero.ne M hm)
    have hle : M ≤ m := Nat.le_of_dvd hmpos hdvd
    have hlt : m < M := by
      rw [hm]
      exact lt_mul_of_one_lt_left hmpos hk.one_lt
    omega

  obtain ⟨w, hw⟩ := (ZMod.isUnit_iff_coprime g M).mpr hcop
  have hbez := Nat.gcd_eq_gcd_ab c d
  have hbez' : (g : ZMod M) = v.1 * (Nat.gcdA c d : ZMod M) + v.2 * (Nat.gcdB c d : ZMod M) := by
    have h := congrArg (fun z : ℤ => (z : ZMod M)) hbez
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul] at h
    rw [hcv, hdv] at h
    exact h
  refine ⟨(w⁻¹ : (ZMod M)ˣ) * (Nat.gcdA c d : ZMod M), (w⁻¹ : (ZMod M)ˣ) * (Nat.gcdB c d : ZMod M), ?_⟩
  calc _ = ((w⁻¹ : (ZMod M)ˣ) : ZMod M) * (v.1 * (Nat.gcdA c d : ZMod M) + v.2 * (Nat.gcdB c d : ZMod M)) := by
        ring
    _ = 1 := by rw [← hbez', ← hw, Units.inv_mul]

theorem exists_row_eq (v : V M) (hv : addOrderOf v = M) :
    ∃ a : SL(2, ℤ), ((a 1 0 : ℤ) : ZMod M) = v.1 ∧ ((a 1 1 : ℤ) : ZMod M) = v.2 := by
  obtain ⟨x, y, hxy⟩ := exists_combination_of_addOrderOf_eq v hv
  let A' : SL(2, ZMod M) := ⟨!![y, -x; v.1, v.2], by
    rw [Matrix.det_fin_two_of]; linear_combination hxy⟩
  obtain ⟨a, ha⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod M A'
  have hent : ∀ i j, ((a i j : ℤ) : ZMod M) = (A' : Matrix (Fin 2) (Fin 2) (ZMod M)) i j := by
    intro i j
    have h := congrArg (fun g : SL(2, ZMod M) => (g : Matrix (Fin 2) (Fin 2) (ZMod M)) i j) ha
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      eq_intCast] at h
    exact h
  refine ⟨a, ?_, ?_⟩
  · rw [hent]; rfl
  · rw [hent]; rfl

theorem zpow_eq_or_of_sq {G : Type*} [Group G] (g : G) (hg : g ^ 2 = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have hk : g ^ k = g ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul]
    rw [show (g ^ (2 : ℤ)) = 1 by exact_mod_cast hg, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hk, h, zpow_zero]
  · right; rw [hk, h, zpow_one]

omit [NeZero M] in
theorem mem_zpowers_neg_one_units {u : (ZMod M)ˣ} (hu : u ∈ Subgroup.zpowers (-1 : (ZMod M)ˣ)) :
    u = 1 ∨ u = -1 := by
  obtain ⟨k, rfl⟩ := hu
  exact zpow_eq_or_of_sq (-1 : (ZMod M)ˣ) (by rw [neg_one_sq]) k

omit [NeZero M] in
theorem mem_Hpm_iff (u : (ZMod M)ˣ) : u ∈ H ⊔ Subgroup.zpowers (-1) ↔ u ∈ H ∨ -u ∈ H := by
  constructor
  · intro hu
    obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
    rcases mem_zpowers_neg_one_units hz with rfl | rfl
    · exact Or.inl (by rwa [mul_one])
    · exact Or.inr (by rwa [mul_neg_one, neg_neg])
  · rintro (hu | hu)
    · exact Subgroup.mem_sup_left hu
    · have : u = -u * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem_sup hu (Subgroup.mem_zpowers _)

theorem mem_zpowers_neg_one_SL {n : SL(2, ℤ)} (hn : n ∈ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    n = 1 ∨ n = -1 := by
  obtain ⟨k, rfl⟩ := hn
  exact zpow_eq_or_of_sq (-1 : SL(2, ℤ)) (by rw [neg_one_sq]) k

scoped instance normal_zpowers_neg_one : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases mem_zpowers_neg_one_SL hn with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · rw [mul_neg_one, neg_mul, mul_inv_cancel]; exact Subgroup.mem_zpowers _

theorem mem_sup_zpowers_neg_one_iff (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ)) :
    σ ∈ Γ ⊔ Subgroup.zpowers (-1) ↔ σ ∈ Γ ∨ -σ ∈ Γ := by
  constructor
  · intro h
    have h' : σ ∈ ((Γ ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := h
    rw [Subgroup.mul_normal] at h'
    obtain ⟨γ, hγ, n, hn, rfl⟩ := h'
    rcases mem_zpowers_neg_one_SL hn with rfl | rfl
    · exact Or.inl (by simpa using hγ)
    · exact Or.inr (by simpa using hγ)
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : σ = -σ * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem_sup h (Subgroup.mem_zpowers _)

omit [NeZero M] in
theorem row_of_mem_GammaH {σ : SL(2, ℤ)} (hσ : σ ∈ CohCarrier.GammaH M H) :
    ∃ u : (ZMod M)ˣ, u ∈ H ∧ row M σ = (0, (u : ZMod M)) := by
  obtain ⟨hσ0, hσH⟩ := CohCarrier.mem_GammaH_iff.mp hσ
  refine ⟨CohCarrier.gamma0Units M ⟨σ, hσ0⟩, hσH, ?_⟩
  have h10 : ent M σ 1 0 = 0 := CongruenceSubgroup.Gamma0_mem.mp hσ0
  refine Prod.ext h10 ?_
  rw [CohCarrier.val_gamma0Units]
  rfl

omit [NeZero M] in
theorem mem_GammaH_of_row {σ : SL(2, ℤ)} {u : (ZMod M)ˣ} (hu : u ∈ H)
    (hrow : row M σ = (0, (u : ZMod M))) : σ ∈ CohCarrier.GammaH M H := by
  have h10 : ent M σ 1 0 = 0 := congrArg Prod.fst hrow
  have h11 : ent M σ 1 1 = u := congrArg Prod.snd hrow
  have hσ0 : σ ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hσ0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨σ, hσ0⟩ = u := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units]
    exact h11
  rw [this]; exact hu

theorem orb_row_eq_iff (a b : SL(2, ℤ)) :
    orb H (row M a) = orb H (row M b) ↔ b * a⁻¹ ∈ CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1) := by
  set σ := b * a⁻¹ with hσ
  have hb : b = σ * a := by rw [hσ, inv_mul_cancel_right]
  have hrowb : row M b = ract (row M σ) a := by rw [hb, row_mul]
  rw [mem_sup_zpowers_neg_one_iff]
  constructor
  · intro h
    have hmem : row M b ∈ orb H (row M a) := by rw [h]; exact mem_orb_self H _
    obtain ⟨u, hu, hub⟩ := hmem
    rw [hrowb, ← ract_zero_u] at hub
    have hrowσ : row M σ = (0, (u : ZMod M)) := ract_injective a hub
    rcases (mem_Hpm_iff H u).mp hu with hu' | hu'
    · exact Or.inl (mem_GammaH_of_row H hu' hrowσ)
    · refine Or.inr (mem_GammaH_of_row H hu' ?_)
      rw [row_neg, hrowσ, Units.val_neg, Prod.neg_mk, neg_zero]
  · intro h

    obtain ⟨u, hu, hrowσ⟩ : ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ row M σ = (0, (u : ZMod M)) := by
      rcases h with h | h
      · obtain ⟨u, hu, hr⟩ := row_of_mem_GammaH H h
        exact ⟨u, Subgroup.mem_sup_left hu, hr⟩
      · obtain ⟨u, hu, hr⟩ := row_of_mem_GammaH H h
        refine ⟨-u, (mem_Hpm_iff H (-u)).mpr (Or.inr (by rwa [neg_neg])), ?_⟩
        rw [row_neg] at hr
        rw [← neg_neg (row M σ), hr, Units.val_neg, Prod.neg_mk, neg_zero]
    have hmem : row M b ∈ orb H (row M a) := ⟨u, hu, by rw [hrowb, hrowσ, ract_zero_u]⟩
    exact (orb_eq_of_mem H hmem).symm

end P2MKcLEVEL

open P2MKcLEVEL in
theorem CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (∀ v : ZMod M × ZMod M, addOrderOf v = M →
      ∃ a : SL(2, ℤ), ((a 1 0 : ℤ) : ZMod M) = v.1 ∧ ((a 1 1 : ℤ) : ZMod M) = v.2) ∧
    (∀ a : SL(2, ℤ), addOrderOf ((((a 1 0 : ℤ) : ZMod M), ((a 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M) = M) ∧
    (∀ a b : SL(2, ℤ),
      {w : ZMod M × ZMod M | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
          w = (u : ZMod M).val • ((((a 1 0 : ℤ) : ZMod M), ((a 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M)} =
        {w : ZMod M × ZMod M | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
          w = (u : ZMod M).val • ((((b 1 0 : ℤ) : ZMod M), ((b 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M)} ↔
      b * a⁻¹ ∈ CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)) :=
  ⟨exists_row_eq, addOrderOf_row, orb_row_eq_iff H⟩


namespace P2MKcXHCount

section Orb

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M]

omit [NeZero M] in
theorem nsmul_eq_mod_nsmul {P : A} (hP : M • P = 0) (n : ℕ) : n • P = (n % M) • P := by
  conv_lhs => rw [← Nat.mod_add_div n M, add_nsmul, mul_nsmul, hP, nsmul_zero, add_zero]

omit [NeZero M] in
theorem val_natCast_nsmul {P : A} (hP : M • P = 0) (n : ℕ) : ((n : ZMod M).val) • P = n • P := by
  rw [ZMod.val_natCast, ← nsmul_eq_mod_nsmul hP]

omit [NeZero M] in
theorem val_mul_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u * v).val • P = u.val • (v.val • P) := by
  rw [ZMod.val_mul, ← nsmul_eq_mod_nsmul hP, mul_nsmul']

theorem val_add_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u + v).val • P = u.val • P + v.val • P := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul hP, add_nsmul]

theorem val_neg_nsmul {P : A} (hP : M • P = 0) (u : ZMod M) : (-u).val • P = -(u.val • P) := by
  have h : (-u + u).val • P = 0 := by rw [neg_add_cancel, ZMod.val_zero, zero_nsmul]
  rw [val_add_nsmul hP] at h
  exact eq_neg_of_add_eq_zero_left h

theorem val_sub_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u - v).val • P = u.val • P - v.val • P := by
  rw [sub_eq_add_neg, val_add_nsmul hP, val_neg_nsmul hP, ← sub_eq_add_neg]

omit [NeZero M] in
theorem val_one_nsmul {P : A} (hP : M • P = 0) : (1 : ZMod M).val • P = P := by
  have := val_natCast_nsmul hP 1
  rwa [Nat.cast_one, one_nsmul] at this

omit [NeZero M] in
theorem nsmul_of_addOrderOf_eq {P : A} (hP : addOrderOf P = M) : M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

omit [NeZero M] in
theorem nsmul_val_nsmul {P : A} (hP : M • P = 0) (n : ℕ) (u : ZMod M) :
    n • (u.val • P) = ((n : ZMod M) * u).val • P := by
  rw [val_mul_nsmul hP, val_natCast_nsmul (by rw [nsmul_left_comm, hP, nsmul_zero])]

variable (H : Subgroup (ZMod M)ˣ)

abbrev orb (P : A) : Set A :=
  {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}

abbrev XH (A : Type*) [AddCommGroup A] (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Type _ :=
  {s : Set A // ∃ P : A, addOrderOf P = M ∧ s = orb H P}

omit [NeZero M] in
theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ H ⊔ Subgroup.zpowers (-1) :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

set_option linter.unusedSectionVars false in
theorem mem_orb_self {P : A} (hP : M • P = 0) : P ∈ orb H P :=
  ⟨1, Subgroup.one_mem _, by rw [Units.val_one, val_one_nsmul hP]⟩

omit [NeZero M] in
theorem nsmul_mem_orb {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : M • T = 0 := by
  obtain ⟨u, -, rfl⟩ := hT
  rw [nsmul_left_comm, hP, nsmul_zero]

omit [NeZero M] in
theorem orb_eq_of_mem {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : orb H T = orb H P := by
  obtain ⟨u, hu, rfl⟩ := hT
  ext W
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v * u, Subgroup.mul_mem _ hv hu, ?_⟩
    rw [Units.val_mul, val_mul_nsmul hP]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w * u⁻¹, Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hu), ?_⟩
    rw [← val_mul_nsmul hP, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem neg_mem_orb {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : -T ∈ orb H P := by
  obtain ⟨u, hu, rfl⟩ := hT
  refine ⟨-1 * u, Subgroup.mul_mem _ (neg_one_mem_Hpm H) hu, ?_⟩
  rw [Units.val_mul, val_mul_nsmul hP, Units.val_neg, Units.val_one, val_neg_nsmul, val_one_nsmul]
  all_goals rw [nsmul_left_comm, hP, nsmul_zero]

theorem orb_neg {P : A} (hP : M • P = 0) : orb H (-P) = orb H P :=
  orb_eq_of_mem H hP (neg_mem_orb H hP (mem_orb_self H hP))

omit [NeZero M] in
theorem image_orb {B : Type*} [AddCommGroup B] (m : A →+ B) (P : A) :
    m '' orb H P = orb H (m P) := by
  ext W
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨T, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [map_nsmul]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : ZMod M).val • P, ⟨u, hu, rfl⟩, by rw [map_nsmul]⟩

variable {H}

omit [NeZero M] in
theorem XH.nsmul_eq_zero (s : XH A M H) {T : A} (hT : T ∈ s.1) : M • T = 0 := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs] at hT
  exact nsmul_mem_orb H (nsmul_of_addOrderOf_eq hP) hT

set_option linter.unusedSectionVars false in
theorem XH.eq_orb_of_mem (s : XH A M H) {T : A} (hT : T ∈ s.1) : s.1 = orb H T := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs] at hT ⊢
  exact (orb_eq_of_mem H (nsmul_of_addOrderOf_eq hP) hT).symm

theorem XH.neg_mem (s : XH A M H) {T : A} (hT : T ∈ s.1) : -T ∈ s.1 := by
  obtain ⟨P, hP, hs⟩ := s.2
  rw [hs] at hT ⊢
  exact neg_mem_orb H (nsmul_of_addOrderOf_eq hP) hT

omit [NeZero M] in
theorem XH.ext' {s s' : XH A M H} (h : s.1 = s'.1) : s = s' := Subtype.ext h

def mapX {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m) (s : XH A M H) :
    XH B M H :=
  ⟨m '' s.1, by
    obtain ⟨P, hP, hs⟩ := s.2
    exact ⟨m P, by rw [addOrderOf_injective m hm, hP], by rw [hs, image_orb]⟩⟩

omit [NeZero M] in
@[scoped simp] theorem mapX_val {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m)
    (s : XH A M H) : (mapX m hm s).1 = m '' s.1 := rfl

omit [NeZero M] in
theorem mapX_mapX {B C : Type*} [AddCommGroup B] [AddCommGroup C] (m : B →+ C) (m' : A →+ B)
    (hm : Function.Injective m) (hm' : Function.Injective m') (s : XH A M H) :
    mapX m hm (mapX m' hm' s) = mapX (m.comp m') (hm.comp hm') s :=
  XH.ext' (by simp [Set.image_image])

omit [NeZero M] in
theorem mapX_congr {B : Type*} [AddCommGroup B] {m m' : A →+ B} (hm : Function.Injective m)
    (hm' : Function.Injective m') (h : m = m') (s : XH A M H) : mapX m hm s = mapX m' hm' s := by
  subst h; rfl

omit [NeZero M] in
theorem mapX_id' {m : A →+ A} (hm : Function.Injective m) (h : ∀ a, m a = a) (s : XH A M H) :
    mapX m hm s = s := by
  apply XH.ext'
  have : (m : A → A) = id := funext h
  simp [this]

theorem mapX_neg' {m : A →+ A} (hm : Function.Injective m) (h : ∀ a, m a = -a) (s : XH A M H) :
    mapX m hm s = s := by
  apply XH.ext'
  obtain ⟨P, hP, hs⟩ := s.2
  rw [mapX_val, hs, image_orb, h, orb_neg H (nsmul_of_addOrderOf_eq hP)]

theorem mapX_eq_of_forall_mem {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m)
    (s : XH A M H) (s' : XH B M H) (h : ∀ T ∈ s.1, m T ∈ s'.1) : mapX m hm s = s' := by
  apply XH.ext'
  obtain ⟨P, hP, hs⟩ := s.2
  have hPs : P ∈ s.1 := by rw [hs]; exact mem_orb_self H (nsmul_of_addOrderOf_eq hP)
  rw [mapX_val, hs, image_orb, XH.eq_orb_of_mem s' (h P hPs)]

omit [NeZero M] in
theorem mapX_injective {B : Type*} [AddCommGroup B] (m : A →+ B) (hm : Function.Injective m) :
    Function.Injective (mapX (M := M) (H := H) m hm) := fun _s _s' h =>
  XH.ext' ((Set.image_injective.mpr hm) (congrArg Subtype.val h))

end Orb

section Level

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev V (M : ℕ) : Type := ZMod M × ZMod M

abbrev ent (M : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : ZMod M := ((g i j : ℤ) : ZMod M)

abbrev row (M : ℕ) (g : SL(2, ℤ)) : V M := (ent M g 1 0, ent M g 1 1)

def ract (v : V M) (g : SL(2, ℤ)) : V M :=
  (v.1 * ent M g 0 0 + v.2 * ent M g 1 0, v.1 * ent M g 0 1 + v.2 * ent M g 1 1)

omit [NeZero M] in
theorem ent_mul (g h : SL(2, ℤ)) (i j : Fin 2) :
    ent M (g * h) i j = ent M g i 0 * ent M h 0 j + ent M g i 1 * ent M h 1 j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

omit [NeZero M] in
theorem ent_one (i j : Fin 2) : ent M 1 i j = if i = j then 1 else 0 := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  split_ifs <;> simp

omit [NeZero M] in
theorem ent_neg (g : SL(2, ℤ)) (i j : Fin 2) : ent M (-g) i j = -ent M g i j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_neg]
  rw [Matrix.neg_apply]
  push_cast
  rfl

omit [NeZero M] in
theorem ract_one (v : V M) : ract v 1 = v := by
  simp only [ract, ent_one]
  simp

omit [NeZero M] in
theorem ract_mul (v : V M) (g h : SL(2, ℤ)) : ract v (g * h) = ract (ract v g) h := by
  simp only [ract, ent_mul]
  ext <;> ring

omit [NeZero M] in
theorem ract_neg_one (v : V M) : ract v (-1) = -v := by
  simp only [ract, ent_neg, ent_one]
  ext <;> simp

omit [NeZero M] in
theorem row_eq_ract (g : SL(2, ℤ)) : row M g = ract ((0 : ZMod M), (1 : ZMod M)) g := by
  simp [ract]

omit [NeZero M] in
theorem row_one : row M 1 = ((0 : ZMod M), (1 : ZMod M)) := by
  rw [row_eq_ract, ract_one]

def ractHom (M : ℕ) (g : SL(2, ℤ)) : V M →+ V M where
  toFun v := ract v g
  map_zero' := by simp [ract]
  map_add' v w := by simp only [ract]; ext <;> simp <;> ring

omit [NeZero M] in
@[scoped simp] theorem ractHom_apply (g : SL(2, ℤ)) (v : V M) : ractHom M g v = ract v g := rfl

omit [NeZero M] in
theorem ract_injective (g : SL(2, ℤ)) : Function.Injective (fun v : V M => ract v g) := by
  intro v w h
  have := congrArg (fun z => ract z g⁻¹) h
  simpa only [← ract_mul, mul_inv_cancel, ract_one] using this

set_option linter.unusedSectionVars false in
theorem ractHom_injective (g : SL(2, ℤ)) : Function.Injective (ractHom M g) := ract_injective g

omit [NeZero M] in
theorem ractHom_comp (g h : SL(2, ℤ)) :
    (ractHom M h).comp (ractHom M g) = ractHom M (g * h) := by
  ext v <;> simp [ract_mul]

variable (H)

scoped instance actXV : MulAction SL(2, ℤ) (XH (V M) M H) where
  smul g s := mapX (ractHom M g⁻¹) (ractHom_injective g⁻¹) s
  one_smul s := mapX_id' _ (fun v => by simp [ract_one]) s
  mul_smul g h s := by
    show mapX (ractHom M (g * h)⁻¹) _ s = mapX (ractHom M g⁻¹) _ (mapX (ractHom M h⁻¹) _ s)
    rw [mapX_mapX]
    exact mapX_congr _ _ (by rw [ractHom_comp, mul_inv_rev]) s

variable {H}

theorem smul_def (g : SL(2, ℤ)) (s : XH (V M) M H) :
    g • s = mapX (ractHom M g⁻¹) (ractHom_injective g⁻¹) s := rfl

theorem smul_val (g : SL(2, ℤ)) (s : XH (V M) M H) :
    (g • s).1 = (fun v => ract v g⁻¹) '' s.1 := rfl

theorem neg_one_smul' (s : XH (V M) M H) : (-1 : SL(2, ℤ)) • s = s := by
  rw [smul_def]
  refine mapX_neg' _ (fun v => ?_) s
  rw [ractHom_apply]
  have : (-1 : SL(2, ℤ))⁻¹ = -1 := by rw [inv_eq_iff_mul_eq_one, neg_mul_neg, one_mul]
  rw [this, ract_neg_one]

theorem neg_smul' (g : SL(2, ℤ)) (s : XH (V M) M H) : (-g) • s = g • s := by
  rw [← neg_one_mul, mul_smul, neg_one_smul']

section WithLevel

variable (hL1 : ∀ v : V M, addOrderOf v = M →
      ∃ a : SL(2, ℤ), ((a 1 0 : ℤ) : ZMod M) = v.1 ∧ ((a 1 1 : ℤ) : ZMod M) = v.2)
  (hL2 : ∀ a : SL(2, ℤ), addOrderOf (row M a) = M)
  (hL3 : ∀ a b : SL(2, ℤ), orb H (row M a) = orb H (row M b) ↔
      b * a⁻¹ ∈ CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1))

def X0 (H : Subgroup (ZMod M)ˣ) (hL2 : ∀ a : SL(2, ℤ), addOrderOf (row M a) = M) : XH (V M) M H :=
  ⟨orb H ((0 : ZMod M), (1 : ZMod M)), _, by simpa [row_one] using hL2 1, rfl⟩

set_option linter.unusedSectionVars false in
theorem X0_val : (X0 H hL2).1 = orb H (row M 1) := by rw [row_one]; rfl

theorem smul_X0_val (g : SL(2, ℤ)) : (g • X0 H hL2).1 = orb H (row M g⁻¹) := by
  rw [smul_val, show (X0 H hL2).1 = orb H ((0 : ZMod M), 1) from rfl,
    show (fun v : V M => ract v g⁻¹) = ractHom M g⁻¹ from rfl, image_orb, ractHom_apply, ← row_eq_ract]

include hL1 in
theorem exists_smul_X0_eq (s : XH (V M) M H) : ∃ g : SL(2, ℤ), g • X0 H hL2 = s := by
  obtain ⟨v, hv, hs⟩ := s.2
  obtain ⟨a, ha1, ha2⟩ := hL1 v hv
  refine ⟨a⁻¹, XH.ext' ?_⟩
  rw [smul_X0_val, inv_inv, hs]
  congr 1
  exact Prod.ext ha1 ha2

include hL3 in
theorem stabilizer_X0 :
    MulAction.stabilizer SL(2, ℤ) (X0 H hL2) = CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1) := by
  ext g
  have h3 := hL3 1 g⁻¹
  rw [inv_one, mul_one] at h3
  rw [MulAction.mem_stabilizer_iff, ← Subgroup.inv_mem_iff (x := g), ← h3, ← X0_val (hL2 := hL2),
    ← smul_X0_val (hL2 := hL2)]
  exact ⟨fun h => congrArg Subtype.val h.symm, fun h => (XH.ext' h).symm⟩

include hL1 hL2 hL3 in

theorem natCard_XV :
    Nat.card (XH (V M) M H) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by
  have : MulAction.IsPretransitive SL(2, ℤ) (XH (V M) M H) := ⟨fun s t => by
    obtain ⟨g, rfl⟩ := exists_smul_X0_eq hL1 hL2 s
    obtain ⟨h, rfl⟩ := exists_smul_X0_eq hL1 hL2 t
    exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩⟩
  rw [Subgroup.index_eq_card, ← stabilizer_X0 hL2 hL3]
  have e1 : XH (V M) M H ≃ MulAction.orbit SL(2, ℤ) (X0 H hL2) :=
    (Equiv.Set.univ _).symm.trans (Set.equivOfEq (MulAction.orbit_eq_univ SL(2, ℤ) (X0 H hL2)).symm)
  exact Nat.card_congr (e1.trans (MulAction.orbitEquivQuotientStabilizer SL(2, ℤ) (X0 H hL2)))

end WithLevel

end Level

section Transport

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
  (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)

def iota : V M →+ A :=
  ((Submodule.torsionBy ℤ A M).subtype.toAddMonoidHom).comp e.toAddMonoidHom

omit [NeZero M] in
theorem iota_apply (c : V M) : iota e c = ((e c : Submodule.torsionBy ℤ A M) : A) := rfl

omit [NeZero M] in
theorem iota_injective : Function.Injective (iota e) := by
  intro c d h
  rw [iota_apply, iota_apply] at h
  exact e.injective (Subtype.ext h)

omit [NeZero M] in
theorem exists_iota_eq (T : A) (hT : M • T = 0) : ∃ c : V M, iota e c = T := by
  have hT' : T ∈ Submodule.torsionBy ℤ A M := by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hT
  refine ⟨e.symm ⟨T, hT'⟩, ?_⟩
  rw [iota_apply, AddEquiv.apply_symm_apply]

def theta (s : XH (V M) M H) : XH A M H := mapX (iota e) (iota_injective e) s

set_option linter.unusedSectionVars false in
theorem theta_bijective : Function.Bijective (theta (H := H) e) := by
  refine ⟨mapX_injective (iota e) (iota_injective e), fun t => ?_⟩
  obtain ⟨Q, hQ, ht⟩ := t.2
  obtain ⟨c, rfl⟩ := exists_iota_eq e Q (nsmul_of_addOrderOf_eq hQ)
  refine ⟨⟨orb H c, c, ?_, rfl⟩, XH.ext' ?_⟩
  · rwa [addOrderOf_injective _ (iota_injective e)] at hQ
  · show iota e '' orb H c = t.1
    rw [image_orb, ht]

include e in
theorem natCard_XH_eq : Nat.card (XH A M H) = Nat.card (XH (V M) M H) :=
  (Nat.card_eq_of_bijective _ (theta_bijective (H := H) e)).symm

end Transport

end P2MKcXHCount

open P2MKcXHCount in
theorem AddCommGroup.natCard_torsionOrbit_gammaH_eq_index
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {A : Type*} [AddCommGroup A]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M) :
    Nat.card {s : Set A // ∃ P : A, addOrderOf P = M ∧
        s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} =
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by
  obtain ⟨hL1, hL2, hL3⟩ := CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff M H
  have hXV : Nat.card (XH (V M) M H) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index :=
    natCard_XV hL1 hL2 hL3
  have h := natCard_XH_eq (H := H) e
  rw [hXV] at h
  exact h

end


