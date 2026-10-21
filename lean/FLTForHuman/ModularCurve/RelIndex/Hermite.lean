/-
The Hermite normal form of `Γ₀(N)`-cosets of `SL(2, ℤ)`.

For `N ≠ 0` every `γ : SL(2, ℤ)` has a unique Hermite datum
`dMul N γ = δ · !![a, b; 0, d]` with `0 < a`, `0 ≤ b < d`, `a * d = N`; the
datum parametrises `Γ₀(N)`-cosets, because two elements with the same datum
differ by an element of `Γ₀(N)` (`mul_inv_mem_Gamma0_of_hermite_eq`).

This is the `RelIndex` body's `Groups` section
(`P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean:122-220`)
with the matrix transport of the same section (`hP`, `heckeDiag_mul_eq`,
`heckeDiag_smul_smul`, `coe_hP_smul`, `hP_smul_heckeDiag_smul`) split off into
`ModularCurve/RelIndex/LevelRaise.lean`, whose subject is the `GL (Fin 2) ℝ`
side.

Dedup. The one premise is imported, not re-proved:
`Matrix.exists_specialLinearGroup_mul_upperTriangular`
(`LinearAlgebra/Matrix/SpecialLinearGroupHermite.lean`), which is the pin's
`Theorems/Thm_Matrix_…` wrapper statement. `Gamma0_mem` and
`ZMod.intCast_zmod_eq_zero_iff_dvd` are mathlib's. Nothing else in the port
states a Hermite form for `!![N * γ 0 0, N * γ 0 1; γ 1 0, γ 1 1]` — this is new
ground, not a lift.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean
-/
import FLTForHuman.LinearAlgebra.Matrix.SpecialLinearGroupHermite
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups

open CongruenceSubgroup Matrix

namespace ModularCurve

namespace RelIndex

/-! ## The Hermite form of `dMul N γ` -/

variable (N : ℕ) [NeZero N]

/-- `!![N * γ 0 0, N * γ 0 1; γ 1 0, γ 1 1]`, the matrix whose Hermite reduction
parametrises the cosets of `Γ₀(N)` in `SL(2, ℤ)`. -/
def dMul (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(N : ℤ) * γ 0 0, (N : ℤ) * γ 0 1; γ 1 0, γ 1 1]

theorem det_dMul (γ : SL(2, ℤ)) : (dMul N γ).det = N := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  rw [dMul, Matrix.det_fin_two_of]
  linear_combination (N : ℤ) * hdet

theorem dMul_eq (γ : SL(2, ℤ)) :
    dMul N γ = !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMul, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_hermite (γ : SL(2, ℤ)) :
    ∃ (δ : SL(2, ℤ)) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < d ∧ 0 < d ∧ a * d = N ∧
      dMul N γ = (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] := by
  obtain ⟨B, a, b, d, ha, hb, hbd, had, hM⟩ :=
    Matrix.exists_specialLinearGroup_mul_upperTriangular (dMul N γ)
      (by rw [det_dMul]; exact_mod_cast NeZero.ne N)
  rw [det_dMul] at had
  have hd : 0 < d := by
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    rw [← had] at hN
    exact pos_of_mul_pos_right hN ha.le
  refine ⟨B, a, b, d, ha, hb, ?_, hd, had, hM⟩
  rwa [abs_of_pos hd] at hbd

def hδ (γ : SL(2, ℤ)) : SL(2, ℤ) := (exists_hermite N γ).choose
def hA (γ : SL(2, ℤ)) : ℤ := (exists_hermite N γ).choose_spec.choose
def hB (γ : SL(2, ℤ)) : ℤ := (exists_hermite N γ).choose_spec.choose_spec.choose
def hD (γ : SL(2, ℤ)) : ℤ := (exists_hermite N γ).choose_spec.choose_spec.choose_spec.choose

theorem hermite_spec (γ : SL(2, ℤ)) :
    0 < hA N γ ∧ 0 ≤ hB N γ ∧ hB N γ < hD N γ ∧ 0 < hD N γ ∧ hA N γ * hD N γ = N ∧
      dMul N γ = (hδ N γ : Matrix (Fin 2) (Fin 2) ℤ) * !![hA N γ, hB N γ; 0, hD N γ] :=
  (exists_hermite N γ).choose_spec.choose_spec.choose_spec.choose_spec

theorem hA_pos (γ : SL(2, ℤ)) : 0 < hA N γ := (hermite_spec N γ).1
theorem hB_nonneg (γ : SL(2, ℤ)) : 0 ≤ hB N γ := (hermite_spec N γ).2.1
theorem hB_lt (γ : SL(2, ℤ)) : hB N γ < hD N γ := (hermite_spec N γ).2.2.1
theorem hD_pos (γ : SL(2, ℤ)) : 0 < hD N γ := (hermite_spec N γ).2.2.2.1
theorem hA_mul_hD (γ : SL(2, ℤ)) : hA N γ * hD N γ = N := (hermite_spec N γ).2.2.2.2.1

theorem dMul_eq_hermite (γ : SL(2, ℤ)) :
    dMul N γ = (hδ N γ : Matrix (Fin 2) (Fin 2) ℤ) * !![hA N γ, hB N γ; 0, hD N γ] :=
  (hermite_spec N γ).2.2.2.2.2

/-! ## The same datum as natural numbers -/

def nA (γ : SL(2, ℤ)) : ℕ := (hA N γ).toNat
def nB (γ : SL(2, ℤ)) : ℕ := (hB N γ).toNat
def nD (γ : SL(2, ℤ)) : ℕ := (hD N γ).toNat

theorem nA_cast (γ : SL(2, ℤ)) : (nA N γ : ℤ) = hA N γ :=
  Int.toNat_of_nonneg (hA_pos N γ).le
theorem nB_cast (γ : SL(2, ℤ)) : (nB N γ : ℤ) = hB N γ :=
  Int.toNat_of_nonneg (hB_nonneg N γ)
theorem nD_cast (γ : SL(2, ℤ)) : (nD N γ : ℤ) = hD N γ :=
  Int.toNat_of_nonneg (hD_pos N γ).le

theorem nA_ne_zero (γ : SL(2, ℤ)) : nA N γ ≠ 0 := by
  intro h; have := nA_cast N γ; rw [h] at this; have := hA_pos N γ; omega

theorem nD_ne_zero (γ : SL(2, ℤ)) : nD N γ ≠ 0 := by
  intro h; have := nD_cast N γ; rw [h] at this; have := hD_pos N γ; omega

theorem nB_lt_nD (γ : SL(2, ℤ)) : nB N γ < nD N γ := by
  have h1 := nB_cast N γ; have h2 := nD_cast N γ; have := hB_lt N γ; omega

theorem nA_mul_nD (γ : SL(2, ℤ)) : nA N γ * nD N γ = N := by
  have h1 := nA_cast N γ; have h2 := nD_cast N γ; have := hA_mul_hD N γ
  have : ((nA N γ * nD N γ : ℕ) : ℤ) = N := by push_cast; rw [h1, h2, this]
  exact_mod_cast this

/-! ## The datum separates `Γ₀(N)`-cosets -/

theorem mul_inv_mem_Gamma0_of_hermite_eq {γ₁ γ₂ : SL(2, ℤ)} (ha : hA N γ₁ = hA N γ₂)
    (hb : hB N γ₁ = hB N γ₂) (hd : hD N γ₁ = hD N γ₂) : γ₂ * γ₁⁻¹ ∈ Gamma0 N := by
  set H : Matrix (Fin 2) (Fin 2) ℤ := !![hA N γ₁, hB N γ₁; 0, hD N γ₁] with hH
  have h1 : dMul N γ₁ = (hδ N γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * H := dMul_eq_hermite N γ₁
  have h2 : dMul N γ₂ = (hδ N γ₂ : Matrix (Fin 2) (Fin 2) ℤ) * H := by
    rw [dMul_eq_hermite N γ₂, hH, ha, hb, hd]
  set Dm : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ), 0; 0, 1] with hDm
  have hX : Dm * ((γ₂ * γ₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((hδ N γ₂ * (hδ N γ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Dm := by
    have e1 : Dm * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) = (hδ N γ₁ : Matrix _ _ ℤ) * H := by
      rw [← dMul_eq]; exact h1
    have e2 : Dm * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) = (hδ N γ₂ : Matrix _ _ ℤ) * H := by
      rw [← dMul_eq]; exact h2
    have hinv1 : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ₁⁻¹ : SL(2, ℤ)) : Matrix _ _ ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hinv2 : (((hδ N γ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (hδ N γ₁ : Matrix _ _ ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have eH : H = (((hδ N γ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (Dm * (γ₁ : Matrix _ _ ℤ)) := by
      rw [e1, ← Matrix.mul_assoc, hinv2, Matrix.one_mul]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc,
      e2, eH]
    simp only [Matrix.mul_assoc]
    rw [hinv1, Matrix.mul_one]
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) hX
  simp only [hDm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h10
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨((hδ N γ₂ * (hδ N γ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0, ?_⟩
  linarith

end RelIndex

end ModularCurve
