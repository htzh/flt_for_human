/-
  The upper-triangular congruence subgroup `Γ⁰(ℓ)` — the matrices of `SL(2, ℤ)` whose
  upper-right entry vanishes modulo `ℓ` — and the inclusion `Γ(p * N) ≤ Γ⁰(p)` that the
  level arguments consume.

  Mathlib has `Γ₀` (lower-left), `Γ₁` and `Γ`, but not the transpose-conjugate of `Γ₀`;
  this module is that missing piece and nothing else. Two layers need it: the
  cohomological `Γ_HUpper` (`ModularForms/Defs/CohCarrierLevel.lean`) and the analytic
  engine's `Λ = Γ₁(N) ⊓ Γ⁰(p)` (`ModularForms/Analytic/PeterssonHecke.lean`), so it is
  homed once here, with no dependency beyond mathlib.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_CohCarrier_Level.lean:90–106` — `Gamma0Upper`, `mem_Gamma0Upper`.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup

open scoped MatrixGroups

namespace ModularForm.Level

/-- `Γ⁰(ℓ)`: the subgroup of `SL(2, ℤ)` whose upper-right entry vanishes modulo `ℓ`. -/
def Gamma0Upper (ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g | (g 0 1 : ZMod ℓ) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    have h := (Matrix.two_mul_expl a.1 b.1).2.1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simpa using ha

@[simp]
theorem mem_Gamma0Upper {ℓ : ℕ} {A : SL(2, ℤ)} : A ∈ Gamma0Upper ℓ ↔ (A 0 1 : ZMod ℓ) = 0 :=
  Iff.rfl

/-- `Γ⁰(ℓ)`-membership in the divisibility spelling, which is how the Hecke layer writes the
upper-right vanishing condition. -/
theorem mem_Gamma0Upper_iff_dvd {ℓ : ℕ} {A : SL(2, ℤ)} :
    A ∈ Gamma0Upper ℓ ↔ (ℓ : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
  rw [mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- `Γ⁰` is antitone in the level, in the direction the level arguments consume: the principal
congruence subgroup at a multiple of `ℓ` is upper-triangular modulo `ℓ`. -/
theorem Gamma_le_Gamma0Upper {m n : ℕ} (h : m ∣ n) : Gamma n ≤ Gamma0Upper m := by
  intro A hA
  rw [mem_Gamma0Upper_iff_dvd]
  exact (Int.natCast_dvd_natCast.mpr h).trans
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma_mem.mp hA).2.1)

end ModularForm.Level
