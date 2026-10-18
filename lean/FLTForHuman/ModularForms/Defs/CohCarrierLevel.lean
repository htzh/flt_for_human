/-
  The cohomological Hecke operators on `Γ_H(M)`: the transfer algebra they are
  built from, the upper-triangular conjugation `Γ_HUpper(M,ℓ) → Γ_H(M)` with its
  operator `heckeT`, and the level maps `ι_d`, `iDeg`, `jDeg` (precomposition and
  the transfer) between two levels.

  FLT provenance, pinned `aa2d8b3`: `Definitions/Def_CohCarrier_Level.lean`, the
  whole module except the twelve declarations already homed in
  `ModularForms/Defs/GammaH.lean` (`Gamma0_d_mul_a`, `gamma0Units`,
  `val_gamma0Units`, `GammaH`, `mem_GammaH_iff`, `GammaH_le_Gamma0`,
  `GammaH_top`, `H1`, `GammaH_normal_in_Gamma0`, `conj_mem_GammaH`, `conjHom`,
  `diamondRaw`). The pin's `Carrier` section is an `instance` probe on `H1`
  (`Module R (H1 M H A)` from `AddCommGroup`+`Module`), which has no declaration
  to port; the instance exists in the port for the same reason.

  Statements are transcribed verbatim. The proofs are the pin's, with one API
  adaptation for mathlib `v4.34.0`: `MonoidHom.transfer_def` now takes its
  transversal before the group element, i.e. `transfer_def ϕ T [FiniteIndex] g`
  (the pin could write `transfer_def _ default`).
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Transfer
import Mathlib.Algebra.Module.Hom
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import FLTForHuman.ModularForms.Defs.GammaH

set_option autoImplicit false

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CohCarrier

/-! ### The transfer as an additive construction -/

section TransferAdd

variable {G : Type*} [Group G] {K : Subgroup G} {C : Type*} [CommGroup C]

open Subgroup Subgroup.leftTransversals in
theorem transfer_diff_one [K.FiniteIndex] (S T : K.LeftTransversal) :
    diff (1 : K →* C) S T = 1 := by
  simp [diff]

open Subgroup Subgroup.leftTransversals in
theorem transfer_diff_mul [K.FiniteIndex] (ϕ ψ : K →* C)
    (S T : K.LeftTransversal) : diff (ϕ * ψ) S T = diff ϕ S T * diff ψ S T := by
  simp only [diff, MonoidHom.mul_apply, Finset.prod_mul_distrib]

theorem transfer_one [K.FiniteIndex] : MonoidHom.transfer (1 : K →* C) = 1 := by
  ext g
  rw [MonoidHom.transfer_def (1 : K →* C) default g, transfer_diff_one]
  rfl

theorem transfer_mul [K.FiniteIndex] (ϕ ψ : K →* C) :
    MonoidHom.transfer (ϕ * ψ) = MonoidHom.transfer ϕ * MonoidHom.transfer ψ := by
  ext g
  rw [MonoidHom.mul_apply, MonoidHom.transfer_def (ϕ * ψ) default g,
    MonoidHom.transfer_def ϕ default g, MonoidHom.transfer_def ψ default g,
    transfer_diff_mul]

theorem toMultiplicativeRight_zero {α β : Type*} [MulOneClass α] [AddCommGroup β] :
    AddMonoidHom.toMultiplicativeRight (0 : Additive α →+ β) = 1 := by
  ext a
  simp

theorem toMultiplicativeRight_add {α β : Type*} [MulOneClass α] [AddCommGroup β]
    (φ ψ : Additive α →+ β) :
    AddMonoidHom.toMultiplicativeRight (φ + ψ) =
      AddMonoidHom.toMultiplicativeRight φ * AddMonoidHom.toMultiplicativeRight ψ := by
  ext a
  simp [ofAdd_add]

theorem toAdditiveLeft_one {α β : Type*} [MulOneClass α] [AddCommGroup β] :
    MonoidHom.toAdditiveLeft (1 : α →* Multiplicative β) = 0 := by
  ext a
  simp

theorem toAdditiveLeft_mul {α β : Type*} [MulOneClass α] [AddCommGroup β]
    (f g : α →* Multiplicative β) :
    MonoidHom.toAdditiveLeft (f * g) = MonoidHom.toAdditiveLeft f + MonoidHom.toAdditiveLeft g := by
  ext a
  simp [toAdd_mul]

/-- The transfer of an additive homomorphism out of a finite-index subgroup,
pushed back to the ambient group. -/
noncomputable def coresAdd (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B]
    (φ : Additive ↥K →+ B) : Additive G →+ B :=
  MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ))

theorem coresAdd_zero (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B] :
    coresAdd K (0 : Additive ↥K →+ B) = 0 := by
  simp only [coresAdd, toMultiplicativeRight_zero, transfer_one,
    toAdditiveLeft_one]

theorem coresAdd_add (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B]
    (φ ψ : Additive ↥K →+ B) : coresAdd K (φ + ψ) = coresAdd K φ + coresAdd K ψ := by
  simp only [coresAdd, toMultiplicativeRight_add, transfer_mul,
    toAdditiveLeft_mul]

theorem coresAdd_smul (K : Subgroup G) [K.FiniteIndex] {R B : Type*} [Semiring R] [AddCommGroup B]
    [Module R B] (r : R) (φ : Additive ↥K →+ B) : coresAdd K (r • φ) = r • coresAdd K φ := by
  apply AddMonoidHom.ext; intro g
  simp only [coresAdd, MonoidHom.toAdditiveLeft_apply_apply, AddMonoidHom.smul_apply]
  rw [MonoidHom.transfer_def (AddMonoidHom.toMultiplicativeRight (r • φ)) default (Additive.toMul g),
      MonoidHom.transfer_def (AddMonoidHom.toMultiplicativeRight φ) default (Additive.toMul g)]
  simp only [Subgroup.leftTransversals.diff, toAdd_prod,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, Finset.smul_sum,
    AddMonoidHom.smul_apply]

end TransferAdd

/-! ### The upper-triangular level -/

section UpperLevel

/-- `Γ⁰(ℓ)`, the subgroup of `SL(2, ℤ)` whose upper-right entry vanishes mod `ℓ`. -/
def Gamma0Upper (ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g | (g 0 1 : ZMod ℓ) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    have h := (Matrix.two_mul_expl a.1 b.1).2.1
    simp only [coe_mul] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [SL2_inv_expl a]
    simp only [cons_val_zero, cons_val_one, Int.cast_neg, neg_eq_zero] at *
    exact ha

@[simp]
theorem mem_Gamma0Upper {ℓ : ℕ} {A : SL(2, ℤ)} : A ∈ Gamma0Upper ℓ ↔ (A 0 1 : ZMod ℓ) = 0 :=
  Iff.rfl

end UpperLevel

section Operators

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

/-- Divide the upper-right entry by `ℓ`, multiplying the lower-left one by `ℓ`:
the conjugate `diag(ℓ,1) γ diag(ℓ,1)⁻¹` of an upper-`Γ⁰(ℓ)` matrix. -/
def conjUpperMat (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) : SL(2, ℤ) :=
  ⟨!![A 0 0, A 0 1 / ℓ; A 1 0 * ℓ, A 1 1], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hbc : A 0 1 / ℓ * (A 1 0 * ℓ) = A 0 1 * A 1 0 := by
      rw [mul_comm (A 1 0) _, ← mul_assoc, Int.ediv_mul_cancel h]
    rw [hbc]
    exact hdet⟩

theorem conjUpperMat_mul (A B : SL(2, ℤ)) (hA : (ℓ : ℤ) ∣ A 0 1) (hB : (ℓ : ℤ) ∣ B 0 1)
    (hAB : (ℓ : ℤ) ∣ (A * B) 0 1) :
    conjUpperMat ℓ (A * B) hAB = conjUpperMat ℓ A hA * conjUpperMat ℓ B hB := by
  have h1 : A 0 1 / ℓ * (B 1 0 * ℓ) = A 0 1 * B 1 0 := by
    rw [mul_comm (B 1 0) _, ← mul_assoc, Int.ediv_mul_cancel hA]
  have h2 : (A 0 0 * B 0 1 + A 0 1 * B 1 1) / ℓ = A 0 0 * (B 0 1 / ℓ) + A 0 1 / ℓ * B 1 1 := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_right hA _), Int.mul_ediv_assoc _ hB,
      mul_comm (A 0 1) (B 1 1), Int.mul_ediv_assoc _ hA, mul_comm (B 1 1)]
  have h3 : A 1 0 * ℓ * (B 0 1 / ℓ) = A 1 0 * B 0 1 := by
    rw [mul_assoc, Int.mul_ediv_cancel' hB]
  have hmul : ∀ i j, (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [show ((conjUpperMat ℓ A hA * conjUpperMat ℓ B hB : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (!![A 0 0, A 0 1 / ℓ; A 1 0 * ℓ, A 1 1] : Matrix (Fin 2) (Fin 2) ℤ)
        * !![B 0 0, B 0 1 / ℓ; B 1 0 * ℓ, B 1 1] from by
    rw [Matrix.SpecialLinearGroup.coe_mul]; rfl]
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [conjUpperMat, hmul, h2]
  · exact h1.symm
  · ring
  · exact h3.symm

@[simp] theorem conjUpperMat_apply_11 (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 1 1 = A 1 1 := by
  simp [conjUpperMat]

@[simp] theorem conjUpperMat_apply_10 (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 1 0 = A 1 0 * ℓ := by
  simp [conjUpperMat]

/-- `Γ_HUpper(M,ℓ) = Γ⁰(ℓ) ∩ Γ_H(M)`. -/
abbrev GammaHUpper : Subgroup ↥(GammaH M H) := (Gamma0Upper ℓ).subgroupOf (GammaH M H)

theorem dvd_of_mem_GammaHUpper (γ : ↥(GammaHUpper M H ℓ)) : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := by
  have h : ((γ : ↥(GammaH M H)) : SL(2, ℤ)) ∈ Gamma0Upper ℓ := Subgroup.mem_subgroupOf.mp γ.2
  rw [mem_Gamma0Upper] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

theorem conjUpperMat_mem (γ : ↥(GammaHUpper M H ℓ)) :
    conjUpperMat ℓ (γ : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M H ℓ γ) ∈ GammaH M H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp (γ : ↥(GammaH M H)).2
  rw [mem_GammaH_iff]
  refine ⟨?_, ?_⟩
  · rw [Gamma0_mem, conjUpperMat_apply_10, Int.cast_mul, Gamma0_mem.mp hγ0, zero_mul]
  ·
    convert hγH using 1
    ext
    simp only [val_gamma0Units, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, conjUpperMat_apply_11]

/-- Conjugation by the upper-triangular matrix `diag(ℓ,1)`, as a homomorphism
`Γ_HUpper(M,ℓ) → Γ_H(M)` (the pin's `conjL`). -/
def conjL : ↥(GammaHUpper M H ℓ) →* ↥(GammaH M H) where
  toFun γ := ⟨conjUpperMat ℓ (γ : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M H ℓ γ),
    conjUpperMat_mem M H ℓ γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjUpperMat]
  map_mul' γ δ :=
    Subtype.ext (conjUpperMat_mul ℓ (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M H ℓ γ)
      (dvd_of_mem_GammaHUpper M H ℓ δ) (dvd_of_mem_GammaHUpper M H ℓ (γ * δ)))

variable (A : Type*) [AddCommGroup A]

theorem Gamma0Upper_isCongruenceSubgroup [NeZero ℓ] : IsCongruenceSubgroup (Gamma0Upper ℓ) := by
  refine ⟨ℓ, NeZero.ne _, fun A hA => ?_⟩
  rw [mem_Gamma0Upper]
  exact (Gamma_mem.mp hA).2.1

instance Gamma0Upper_finiteIndex [NeZero ℓ] : (Gamma0Upper ℓ).FiniteIndex :=
  (Gamma0Upper_isCongruenceSubgroup ℓ).finiteIndex

/-- The Hecke operator `T_ℓ` on `H1 M H A`: transfer along `Γ_HUpper(M,ℓ) → Γ_H(M)`. -/
noncomputable def heckeT [NeZero ℓ] : H1 M H A →+ H1 M H A where
  toFun φ :=
    MonoidHom.toAdditiveLeft
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ)))
  map_zero' := by
    simp only [toMultiplicativeRight_zero, MonoidHom.one_comp,
      transfer_one, toAdditiveLeft_one]
  map_add' φ ψ := by
    simp only [toMultiplicativeRight_add, MonoidHom.mul_comp,
      transfer_mul, toAdditiveLeft_mul]

end Operators

/-! ### The level maps `ι_d`, `iDeg`, `jDeg` -/

section LevelMaps

variable (M M' : ℕ) (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ) (d : ℕ)

/-- Divide the lower-left entry by `d`, multiplying the upper-right one by `d`. -/
def conjLowerMat (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) : SL(2, ℤ) :=
  ⟨!![A 0 0, A 0 1 * d; A 1 0 / d, A 1 1], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hbc : A 0 1 * d * (A 1 0 / d) = A 0 1 * A 1 0 := by
      rw [mul_assoc, mul_comm (d : ℤ) _, Int.ediv_mul_cancel h]
    rw [hbc]
    exact hdet⟩

theorem conjLowerMat_mul (A B : SL(2, ℤ)) (hA : (d : ℤ) ∣ A 1 0) (hB : (d : ℤ) ∣ B 1 0)
    (hAB : (d : ℤ) ∣ (A * B) 1 0) :
    conjLowerMat d (A * B) hAB = conjLowerMat d A hA * conjLowerMat d B hB := by
  have h1 : A 0 1 * d * (B 1 0 / d) = A 0 1 * B 1 0 := by
    rw [mul_assoc, Int.mul_ediv_cancel' hB]
  have h2 : (A 1 0 * B 0 0 + A 1 1 * B 1 0) / d = A 1 0 / d * B 0 0 + A 1 1 * (B 1 0 / d) := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_left hB _), Int.mul_ediv_assoc _ hB,
      mul_comm (A 1 0) (B 0 0), Int.mul_ediv_assoc _ hA, mul_comm (B 0 0)]
  have h3 : A 1 0 / d * (B 0 1 * d) = A 1 0 * B 0 1 := by
    rw [mul_comm (B 0 1) _, ← mul_assoc, Int.ediv_mul_cancel hA]
  have hmul : ∀ i j, (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [show ((conjLowerMat d A hA * conjLowerMat d B hB : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (!![A 0 0, A 0 1 * d; A 1 0 / d, A 1 1] : Matrix (Fin 2) (Fin 2) ℤ)
        * !![B 0 0, B 0 1 * d; B 1 0 / d, B 1 1] from by
    rw [Matrix.SpecialLinearGroup.coe_mul]; rfl]
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [conjLowerMat, hmul, h2]
  all_goals first | exact h1.symm | exact h3.symm | ring

/-- `Γ_H(M') ≤ Γ_H(M)` at level gain `d`: `M ∣ M'`, `d ∣ M'/M`, and `H'` maps
into `H` under `ZMod.unitsMap`. -/
structure LevelLE : Prop where
  dvd : M ∣ M'
  ddvd : d ∣ M' / M
  red : ∀ u : (ZMod M')ˣ, u ∈ H' → ZMod.unitsMap dvd u ∈ H

variable {M M' H H' d}

theorem LevelLE.exists_eq (h : LevelLE M M' H H' d) : ∃ e : ℕ, M' = M * (d * e) := by
  obtain ⟨e, he⟩ := h.ddvd
  refine ⟨e, ?_⟩
  rw [← he, Nat.mul_div_cancel' h.dvd]

theorem LevelLE.dvd_entry (h : LevelLE M M' H H' d) (γ : ↥(GammaH M' H')) :
    (d : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  obtain ⟨hγ0, _⟩ := mem_GammaH_iff.mp γ.2
  have hM' : ((M' : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ0)
  obtain ⟨e, he⟩ := h.exists_eq
  refine dvd_trans ?_ hM'
  rw [he]
  push_cast
  exact Dvd.intro_left ((M : ℤ) * e) (by ring)

theorem LevelLE.conjLowerMat_mem [NeZero d] (h : LevelLE M M' H H' d) (γ : ↥(GammaH M' H')) :
    conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ) ∈ GammaH M H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp γ.2
  have hM' : ((M' : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ0)
  obtain ⟨e, he⟩ := h.exists_eq
  obtain ⟨t, ht⟩ := hM'
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hquot : (γ : SL(2, ℤ)) 1 0 / (d : ℤ) = (M : ℤ) * (e * t) := by
    apply Int.ediv_eq_of_eq_mul_right hd0
    rw [ht, he]
    push_cast
    ring
  have h0 : conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ) ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show (((!![(γ : SL(2, ℤ)) 0 0, (γ : SL(2, ℤ)) 0 1 * d; (γ : SL(2, ℤ)) 1 0 / d, (γ : SL(2, ℤ)) 1 1]
      : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [hquot]
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  rw [mem_GammaH_iff]
  refine ⟨h0, ?_⟩
  have hred := h.red _ hγH
  convert hred using 1
  all_goals (ext; simp [gamma0Units, Gamma0Map, conjLowerMat, ZMod.unitsMap])

variable (M M' H H' d)

/-- The level map `Γ_H(M') → Γ_H(M)` given by conjugating by `diag(1,d)`. -/
def iotaDeg [NeZero d] (h : LevelLE M M' H H' d) : ↥(GammaH M' H') →* ↥(GammaH M H) where
  toFun γ := ⟨conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ), h.conjLowerMat_mem γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjLowerMat]
  map_mul' γ δ :=
    Subtype.ext (conjLowerMat_mul d (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) (h.dvd_entry γ) (h.dvd_entry δ)
      (h.dvd_entry (γ * δ)))

variable (A : Type*) [AddCommGroup A]

/-- The pullback `H1 M H A → H1 M' H' A` of `ι_d`. -/
def iDeg' [NeZero d] (h : LevelLE M M' H H' d) : H1 M H A →+ H1 M' H' A where
  toFun φ := φ.comp (MonoidHom.toAdditive (iotaDeg M M' H H' d h))
  map_zero' := by ext; rfl
  map_add' := by intro φ ψ; ext; rfl

/-- `iDeg'` as an `R`-linear map. -/
def iDegL (R : Type*) [Semiring R] [Module R A] [NeZero d] (h : LevelLE M M' H H' d) :
    H1 M H A →ₗ[R] H1 M' H' A where
  toFun φ := φ.comp (MonoidHom.toAdditive (iotaDeg M M' H H' d h))
  map_add' := by intro φ ψ; ext; rfl
  map_smul' := by intro r φ; ext; rfl

theorem conjLowerMat_conjUpperMat [NeZero d] (A : SL(2, ℤ)) (hb : (d : ℤ) ∣ A 0 1)
    (hc : (d : ℤ) ∣ (conjUpperMat d A hb) 1 0) : conjLowerMat d (conjUpperMat d A hb) hc = A := by
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjLowerMat, conjUpperMat, Int.ediv_mul_cancel hb, Int.mul_ediv_cancel _ hd]

theorem Gamma_subgroupOf_le_range_iotaDeg [NeZero M'] [NeZero d] (h : LevelLE M M' H H' d) :
    (Gamma (M' * d)).subgroupOf (GammaH M H) ≤ (iotaDeg M M' H H' d h).range := by
  intro γ hγ
  rw [Subgroup.mem_subgroupOf, Gamma_mem] at hγ
  obtain ⟨_, h01, h10, h11⟩ := hγ
  have hMd : ((M' * d : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
  have hMd' : ((M' * d : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hb : (d : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := dvd_trans (by push_cast; exact Dvd.intro_left _ rfl) hMd
  set A : SL(2, ℤ) := conjUpperMat d (γ : SL(2, ℤ)) hb with hAdef

  have hA0 : A ∈ Gamma0 M' := by
    rw [Gamma0_mem]
    have : A 1 0 = (γ : SL(2, ℤ)) 1 0 * d := by simp [hAdef, conjUpperMat]
    rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Dvd.dvd.mul_right (dvd_trans (by push_cast; exact Dvd.intro _ rfl) hMd') _

  have hA11 : ((A 1 1 : ℤ) : ZMod M') = 1 := by
    have hA : A 1 1 = (γ : SL(2, ℤ)) 1 1 := by simp [hAdef, conjUpperMat]
    rw [hA, ← map_intCast (ZMod.castHom (dvd_mul_right M' d) (ZMod M')), h11, map_one]
  have hAH : gamma0Units M' ⟨A, hA0⟩ ∈ H' := by
    have : gamma0Units M' ⟨A, hA0⟩ = 1 := by
      ext
      simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
      exact hA11
    rw [this]
    exact one_mem H'
  have hc : (d : ℤ) ∣ (conjUpperMat d (γ : SL(2, ℤ)) hb) 1 0 := by
    rw [conjUpperMat_apply_10]; exact dvd_mul_left _ _
  refine ⟨⟨A, mem_GammaH_iff.mpr ⟨hA0, hAH⟩⟩, Subtype.ext ?_⟩
  exact conjLowerMat_conjUpperMat d (γ : SL(2, ℤ)) hb hc

set_option linter.style.haveILetI false in
instance iotaDeg_range_finiteIndex [NeZero M'] [NeZero d] (h : LevelLE M M' H H' d) :
    ((iotaDeg M M' H H' d h).range).FiniteIndex := by
  haveI : NeZero (M' * d) := ⟨mul_ne_zero (NeZero.ne M') (NeZero.ne d)⟩
  haveI : ((Gamma (M' * d)).subgroupOf (GammaH M H)).FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (Gamma_subgroupOf_le_range_iotaDeg M M' H H' d h)

theorem iotaDeg_injective [NeZero d] (h : LevelLE M M' H H' d) :
    Function.Injective (iotaDeg M M' H H' d h) := by
  intro γ δ hγδ
  have hmat : conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ) =
      conjLowerMat d (δ : SL(2, ℤ)) (h.dvd_entry δ) := congrArg Subtype.val hγδ
  have e : ∀ i j, (conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ)) i j =
      (conjLowerMat d (δ : SL(2, ℤ)) (h.dvd_entry δ)) i j := fun i j => by rw [hmat]
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [conjLowerMat] using e 0 0
  · have h01 := e 0 1
    simp only [conjLowerMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h01
    exact mul_right_cancel₀ hd h01
  · have h10 := e 1 0
    simp only [conjLowerMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h10
    calc (γ : SL(2, ℤ)) 1 0 = d * ((γ : SL(2, ℤ)) 1 0 / d) := (Int.mul_ediv_cancel' (h.dvd_entry γ)).symm
      _ = d * ((δ : SL(2, ℤ)) 1 0 / d) := by rw [h10]
      _ = (δ : SL(2, ℤ)) 1 0 := Int.mul_ediv_cancel' (h.dvd_entry δ)
  · simpa [conjLowerMat] using e 1 1

/-- `φ` transported to the range of `ι_d`. -/
noncomputable def pushChar [NeZero d] (h : LevelLE M M' H H' d) (φ : H1 M' H' A) :
    Additive ↥((iotaDeg M M' H H' d h).range) →+ A :=
  φ.comp (MonoidHom.toAdditive
    ((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm.toMonoidHom)

/-- The degeneracy map `jDeg`: transfer along `ι_d`, i.e. the dual of the pullback. -/
noncomputable def jDeg [NeZero M'] [NeZero d] (h : LevelLE M M' H H' d) : H1 M' H' A →+ H1 M H A where
  toFun φ := coresAdd _ (pushChar M M' H H' d A h φ)
  map_zero' := by
    have : pushChar M M' H H' d A h 0 = 0 := by ext; rfl
    rw [this, coresAdd_zero]
  map_add' φ ψ := by
    have : pushChar M M' H H' d A h (φ + ψ) = pushChar M M' H H' d A h φ + pushChar M M' H H' d A h ψ := by
      ext; rfl
    rw [this, coresAdd_add]

/-- `jDeg` as an `R`-linear map. -/
noncomputable def jDegL (R : Type*) [Semiring R] [Module R A] [NeZero M'] [NeZero d]
    (h : LevelLE M M' H H' d) : H1 M' H' A →ₗ[R] H1 M H A where
  toFun φ := coresAdd _ (pushChar M M' H H' d A h φ)
  map_add' φ ψ := by
    have : pushChar M M' H H' d A h (φ + ψ) = pushChar M M' H H' d A h φ + pushChar M M' H H' d A h ψ := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : pushChar M M' H H' d A h (r • φ) = r • pushChar M M' H H' d A h φ := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

end LevelMaps

end CohCarrier
