/-
  m3 — the `Γ₀` coset permutation, the `SL₂` diagonal transport, and the
  `Δ`-ratio invariance.

  * `exists_perm_gamma0_cosetReps` — for a prime `ℓ`, the `ℓ + 1` coset
    representatives `1`, `S * T^b` are permuted by right multiplication up to
    `Γ₀(ℓ)`.
  * `exists_sl2_heckeDiagMatrix_smul_eq` — a `Γ₀(N)`-element can be pushed
    through `heckeDiagMatrix N`, with the denominator matching.
  * `discriminant_div_discriminant_heckeDiagMatrix_smul` — the resulting
    `Γ₀(N)`-invariance of `Δ(τ)/Δ(heckeDiagMatrix N • τ)`.

  FLT provenance, pinned `aa2d8b3`:
  * `P2M/Sol/S_ModularCurve_exists_perm_gamma0_cosetReps.lean` (134 lines)
  * `P2M/Sol/S_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq.lean` (68 lines)
  * `P2M/Sol/S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul.lean` (55 lines)

  All helpers are `private`; only the three wrapper statements are public.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Group
import FLTForHuman.ModularForms.Defs.HeckeOperator

set_option autoImplicit false

-- `exists_perm_gamma0_cosetReps` needs `NeZero ℓ` (from `Fact (Nat.Prime ℓ)`) as a
-- local instance to call the private `exists_perm`; the style linter's `have`
-- suggestion cannot be taken. Disable it as in `QParamUnique.lean`.
set_option linter.style.haveILetI false

noncomputable section

open CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace ModularCurve

namespace QexpN

open Matrix.SpecialLinearGroup ModularForm

private def rep (ℓ : ℕ) (i : Fin (ℓ + 1)) : SL(2, ℤ) :=
  Fin.cases 1 (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i

private theorem rep_zero (ℓ : ℕ) : rep ℓ 0 = 1 := by simp [rep]

private theorem rep_succ (ℓ : ℕ) (b : Fin ℓ) :
    rep ℓ b.succ = ModularGroup.S * ModularGroup.T ^ (b : ℕ) := by simp [rep]

private theorem val_mk {n v : ℕ} (h : v < n) : ((⟨v, h⟩ : Fin n) : ℕ) = v := rfl

private theorem coe_S_mul_T_pow (b : ℕ) :
    ((ModularGroup.S * ModularGroup.T ^ b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![0, -1; 1, (b : ℤ)] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ← zpow_natCast,
    ModularGroup.coe_T_zpow, Matrix.mul_fin_two]
  norm_num

private theorem coe_S_mul_T_pow_inv (b : ℕ) :
    (((ModularGroup.S * ModularGroup.T ^ b)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(b : ℤ), 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_S_mul_T_pow, Matrix.adjugate_fin_two]
  norm_num

private theorem S_T_apply_one_zero (v : ℕ) :
    (ModularGroup.S * ModularGroup.T ^ v : SL(2, ℤ)) 1 0 = 1 :=
  (congrFun (congrFun (coe_S_mul_T_pow v) 1) 0).trans rfl

private theorem S_T_apply_one_one (v : ℕ) :
    (ModularGroup.S * ModularGroup.T ^ v : SL(2, ℤ)) 1 1 = (v : ℤ) :=
  (congrFun (congrFun (coe_S_mul_T_pow v) 1) 1).trans rfl

private theorem S_T_inv_apply_zero_zero (v : ℕ) :
    ((ModularGroup.S * ModularGroup.T ^ v)⁻¹ : SL(2, ℤ)) 0 0 = (v : ℤ) :=
  (congrFun (congrFun (coe_S_mul_T_pow_inv v) 0) 0).trans rfl

private theorem S_T_inv_apply_one_zero (v : ℕ) :
    ((ModularGroup.S * ModularGroup.T ^ v)⁻¹ : SL(2, ℤ)) 1 0 = -1 :=
  (congrFun (congrFun (coe_S_mul_T_pow_inv v) 1) 0).trans rfl

private theorem mul_apply_one_zero (A B : SL(2, ℤ)) :
    (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := by
  rw [congrFun (congrFun (Matrix.SpecialLinearGroup.coe_mul A B) 1) 0, Matrix.mul_apply,
    Fin.sum_univ_two]

private def slot (ℓ : ℕ) [NeZero ℓ] [Fact (Nat.Prime ℓ)] (δ : SL(2, ℤ)) : Fin (ℓ + 1) :=
  if ((δ 1 0 : ℤ) : ZMod ℓ) = 0 then 0
  else Fin.succ ⟨(((δ 1 1 : ℤ) : ZMod ℓ) / ((δ 1 0 : ℤ) : ZMod ℓ)).val, ZMod.val_lt _⟩

private theorem mul_rep_slot_inv_mem (ℓ : ℕ) [NeZero ℓ] [Fact (Nat.Prime ℓ)] (δ : SL(2, ℤ)) :
    δ * (rep ℓ (slot ℓ δ))⁻¹ ∈ Gamma0 ℓ := by
  unfold slot
  split_ifs with hc
  · rw [rep_zero, inv_one, mul_one, Gamma0_mem]
    exact hc
  · set y : ZMod ℓ := ((δ 1 1 : ℤ) : ZMod ℓ) / ((δ 1 0 : ℤ) : ZMod ℓ) with hy
    have hcy : ((δ 1 0 : ℤ) : ZMod ℓ) * y = ((δ 1 1 : ℤ) : ZMod ℓ) := by
      rw [hy]; exact mul_div_cancel₀ _ hc
    rw [rep_succ, Gamma0_mem, mul_apply_one_zero, S_T_inv_apply_zero_zero,
      S_T_inv_apply_one_zero, val_mk]
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination hcy

private theorem eq_of_mul_inv_mem (ℓ : ℕ) [NeZero ℓ] [Fact (Nat.Prime ℓ)] {i k : Fin (ℓ + 1)}
    (h : rep ℓ i * (rep ℓ k)⁻¹ ∈ Gamma0 ℓ) : i = k := by
  induction i using Fin.cases with
  | zero =>
    induction k using Fin.cases with
    | zero => rfl
    | succ b' =>
      exfalso
      rw [rep_zero, rep_succ, one_mul, Gamma0_mem, S_T_inv_apply_one_zero] at h
      rw [Int.cast_neg, Int.cast_one, neg_eq_zero] at h
      exact one_ne_zero h
  | succ b =>
    induction k using Fin.cases with
    | zero =>
      exfalso
      rw [rep_succ, rep_zero, inv_one, mul_one, Gamma0_mem, S_T_apply_one_zero] at h
      rw [Int.cast_one] at h
      exact one_ne_zero h
    | succ b' =>
      rw [rep_succ, rep_succ, Gamma0_mem, mul_apply_one_zero, S_T_apply_one_zero,
        S_T_apply_one_one, S_T_inv_apply_zero_zero, S_T_inv_apply_one_zero] at h
      push_cast at h
      have hb : ((b' : ℕ) : ZMod ℓ) = ((b : ℕ) : ZMod ℓ) := by linear_combination h
      have hval := congrArg ZMod.val hb
      rw [ZMod.val_cast_of_lt b'.isLt, ZMod.val_cast_of_lt b.isLt] at hval
      exact congrArg Fin.succ (Fin.ext hval.symm)

private theorem exists_perm (ℓ : ℕ) [NeZero ℓ] [Fact (Nat.Prime ℓ)]
    (γ : SL(2, ℤ)) :
    ∃ e : Equiv.Perm (Fin (ℓ + 1)), ∀ i : Fin (ℓ + 1),
      rep ℓ i * γ * (rep ℓ (e i))⁻¹ ∈ Gamma0 ℓ := by
  have hinj : Function.Injective fun i : Fin (ℓ + 1) => slot ℓ (rep ℓ i * γ) := by
    intro i k hik
    have hi := mul_rep_slot_inv_mem ℓ (rep ℓ i * γ)
    have hk := mul_rep_slot_inv_mem ℓ (rep ℓ k * γ)
    rw [show slot ℓ (rep ℓ i * γ) = slot ℓ (rep ℓ k * γ) from hik] at hi
    have hmem := (Gamma0 ℓ).mul_mem hi ((Gamma0 ℓ).inv_mem hk)
    have hgrp : rep ℓ i * γ * (rep ℓ (slot ℓ (rep ℓ k * γ)))⁻¹
        * (rep ℓ k * γ * (rep ℓ (slot ℓ (rep ℓ k * γ)))⁻¹)⁻¹ = rep ℓ i * (rep ℓ k)⁻¹ := by
      group
    rw [hgrp] at hmem
    exact eq_of_mul_inv_mem ℓ hmem
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj),
    fun i => mul_rep_slot_inv_mem ℓ (rep ℓ i * γ)⟩

end QexpN

theorem exists_perm_gamma0_cosetReps (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ e : Equiv.Perm (Fin (ℓ + 1)), ∀ i : Fin (ℓ + 1),
      (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i :
          Matrix.SpecialLinearGroup (Fin 2) ℤ) * γ *
        (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)
          (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) (e i) :
            Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ ∈ CongruenceSubgroup.Gamma0 ℓ := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact QexpN.exists_perm ℓ γ

namespace QexpN

open Matrix.SpecialLinearGroup ModularForm

private theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private def conjSL {p : ℕ} (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) : SL(2, ℤ) :=
  ⟨!![g 0 0, p * g 0 1; e, g 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination det_eq g + g 0 1 * he⟩

-- v4.34 drift: `SpecialLinearGroup.map`'s coercion to `Matrix` no longer reduces
-- under `simp`, so the matrix of `mapGL ℝ (conjSL …)` is stated once here.
private theorem mapGL_conjSL {p : ℕ} (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ((mapGL ℝ (conjSL g e he) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(g 0 0 : ℝ), (p : ℝ) * (g 0 1 : ℝ); (e : ℝ), (g 1 1 : ℝ)] := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  change Matrix.map (conjSL g e he : Matrix (Fin 2) (Fin 2) ℤ) (Int.castRingHom ℝ) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, conjSL]

private theorem heckeDiagMatrix_mul_mapGL {p : ℕ} (hp : p ≠ 0) (g : SL(2, ℤ)) (e : ℤ)
    (he : g 1 0 = p * e) :
    heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ (conjSL g e he) * heckeDiagMatrix p := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    mapGL_conjSL g e he, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, hp]
  all_goals first
    | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
    | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
    | ring1

private theorem conjSL_apply_one_zero {p : ℕ} (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    conjSL g e he 1 0 = e := rfl

private theorem conjSL_apply_one_one {p : ℕ} (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    conjSL g e he 1 1 = g 1 1 := rfl

end QexpN

theorem exists_sl2_heckeDiagMatrix_smul_eq (N : ℕ) [NeZero N]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (∀ τ : UpperHalfPlane, ModularForm.heckeDiagMatrix N • γ • τ = γ' • ModularForm.heckeDiagMatrix N • τ) ∧
      ∀ τ : UpperHalfPlane,
        UpperHalfPlane.denom (γ' : Matrix.GeneralLinearGroup (Fin 2) ℝ)
          (((ModularForm.heckeDiagMatrix N • τ : UpperHalfPlane)) : ℂ)
        = UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨e, he⟩ : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  refine ⟨QexpN.conjSL γ e he, fun τ => ?_, fun τ => ?_⟩
  · have h1 : ModularForm.heckeDiagMatrix N • γ • τ
        = (ModularForm.heckeDiagMatrix N * Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ := by
      rw [mul_smul]; rfl
    rw [h1, QexpN.heckeDiagMatrix_mul_mapGL hN γ e he, mul_smul]; rfl
  · rw [ModularGroup.denom_apply, ModularGroup.denom_apply,
      ModularForm.coe_heckeDiagMatrix_smul hN]
    have heC := congrArg (Int.cast : ℤ → ℂ) he
    push_cast at heC
    rw [QexpN.conjSL_apply_one_zero, QexpN.conjSL_apply_one_one]
    linear_combination (-(τ : ℂ)) * heC

namespace QexpN

open Matrix.SpecialLinearGroup ModularForm

private theorem discriminant_div_discriminant_heckeDiagMatrix_smul' (N : ℕ) [NeZero N]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (τ : UpperHalfPlane) :
    ModularForm.discriminant (γ • τ)
        / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • γ • τ)
      = ModularForm.discriminant τ
        / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) := by
  obtain ⟨γ', hact, hden⟩ := exists_sl2_heckeDiagMatrix_smul_eq N γ hγ
  have hγSL : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hγ'SL : (mapGL ℝ γ' : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ', rfl⟩
  have hΔγ : ModularForm.discriminant (γ • τ)
      = UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) ^ (12 : ℤ)
        * ModularForm.discriminant τ := by
    have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγSL τ
    simp [CuspForm.coe_discriminant] at h
    exact h
  have hΔγ' : ModularForm.discriminant (γ' • ModularForm.heckeDiagMatrix N • τ)
      = UpperHalfPlane.denom (γ' : Matrix.GeneralLinearGroup (Fin 2) ℝ)
          (((ModularForm.heckeDiagMatrix N • τ : UpperHalfPlane)) : ℂ) ^ (12 : ℤ)
        * ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) := by
    have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ'SL
        (ModularForm.heckeDiagMatrix N • τ)
    simp [CuspForm.coe_discriminant] at h
    exact h
  rw [hact τ, hΔγ, hΔγ', hden τ,
    mul_div_mul_left _ _ (zpow_ne_zero 12 (UpperHalfPlane.denom_ne_zero _ _))]

end QexpN

theorem discriminant_div_discriminant_heckeDiagMatrix_smul (N : ℕ) [NeZero N]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (τ : UpperHalfPlane) :
    ModularForm.discriminant (γ • τ) / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • γ • τ) =
      ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) :=
  QexpN.discriminant_div_discriminant_heckeDiagMatrix_smul' N γ hγ τ

end ModularCurve

end
