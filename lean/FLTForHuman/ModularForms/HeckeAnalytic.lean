/-
  Analytic regularity of the Hecke operators `U_p`/`T_p`.

  FLT carries this block in **ten** 353-line `S_` files, byte-identical through
  the analytic head (pin lines 23–154): six of them are the regularity targets
  (`mdifferentiable_*`, `isBoundedAtImInfty_*`, `periodic_*_comp_ofComplex`) and
  four are the `q`-coefficient tail (deferred, SET 3). This module ports the head
  **once** and lands the seven public targets verbatim from their `Theorems/`
  wrappers (pinned `aa2d8b3`):

  - `ModularForm.mdifferentiable_heckeU`, `ModularForm.mdifferentiable_heckeT`;
  - `ModularForm.mdifferentiable_slash_heckeDiagMatrix` (its own 9-line pin file);
  - `ModularForm.periodic_heckeU_comp_ofComplex`,
    `ModularForm.periodic_heckeT_comp_ofComplex`;
  - `ModularForm.isBoundedAtImInfty_heckeU`,
    `ModularForm.isBoundedAtImInfty_heckeT`.

  The block-internal helpers (`heckeMatrix_one_zero`, `heckeDiagMatrix_one_zero`,
  the two `isZeroAtImInfty_*`, and the `vadd`/periodicity machinery) have no
  `Thm_` wrapper and stay `private`. The pin's `q`-coefficient tail (lines
  158–345: `qExpansion_coeff_unique'`, `hasSum_*`, `qCoeff_*`) is **not** ported
  here — it is SET 3's.

  FLT provenance: `P2M/Sol/S_ModularForm_<target>.lean` lines 18–154 (the shared
  head; imports `Mathlib`, `Def_ModularForm_HeckeOperator`,
  `Def_FLTPrelim_Modularity`, `P2M.Util`) and
  `P2M/Sol/S_ModularForm_mdifferentiable_slash_heckeDiagMatrix.lean`.
-/
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import FLTForHuman.ModularForms.Defs.HeckeOperator

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

namespace ModularForm

section Matrices

variable (p j : ℕ)

/-- `!![1, j; 0, p]` is upper triangular. Block helper (no wrapper). -/
private theorem heckeMatrix_one_zero :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeMatrix hp]; rfl

/-- `!![p, 0; 0, 1]` is upper triangular. Block helper (no wrapper). -/
private theorem heckeDiagMatrix_one_zero :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeDiagMatrix hp]; rfl

end Matrices

/-! ### Block helpers (no wrappers) -/

section Regularity

variable {f : ℍ → ℂ} (k : ℤ) (p : ℕ)

/-- `U_p` preserves vanishing at `∞`. Block helper (no wrapper). -/
private theorem isZeroAtImInfty_heckeU (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsZeroAtImInfty g)
    (fun _ _ ha hb => ha.add hb) (zero_zeroAtFilter atImInfty)
    (fun j _ => hf.slash k (heckeMatrix_one_zero p j))

/-- `T_p` preserves vanishing at `∞`. Block helper (no wrapper). -/
private theorem isZeroAtImInfty_heckeT (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeT k p f) :=
  (isZeroAtImInfty_heckeU k p hf).add (hf.slash k (heckeDiagMatrix_one_zero p))

/-- A `1`-periodic function on `ℍ` is constant along integer real shifts. -/
private theorem apply_eq_of_coe_eq_add_nat (hf : Periodic (f ∘ ofComplex) 1) {τ₁ τ₂ : ℍ} (m : ℕ)
    (h : (τ₁ : ℂ) = τ₂ + m) : f τ₁ = f τ₂ := by
  have h1 : (f ∘ ofComplex) ((τ₂ : ℂ) + m) = (f ∘ ofComplex) (τ₂ : ℂ) := by
    have := hf.nat_mul m
    rw [mul_one] at this
    exact this (τ₂ : ℂ)
  simp only [comp_apply] at h1
  rw [← h, ofComplex_apply, ofComplex_apply] at h1
  exact h1

variable {p} in

/-- `(1 +ᵥ τ)` shifts the upper-triangular index `j ↦ j + 1`. -/
private theorem heckeMatrix_smul_vadd (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    heckeMatrix p j • ((1 : ℝ) +ᵥ τ) = heckeMatrix p (j + 1) • τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeMatrix_smul hp, coe_heckeMatrix_smul hp, coe_vadd]
  push_cast
  ring

variable {p} in

/-- `j = p` wraps to `j = 0` after a real shift by `1`. -/
private theorem coe_heckeMatrix_smul_self (hp : p ≠ 0) (τ : ℍ) :
    ((heckeMatrix p p • τ : ℍ) : ℂ) = (heckeMatrix p 0 • τ : ℍ) + (1 : ℕ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [coe_heckeMatrix_smul hp, coe_heckeMatrix_smul hp]
  field_simp
  push_cast
  ring

variable {p} in

/-- The diagonal Hecke matrix shifts the argument by `p`. -/
private theorem coe_heckeDiagMatrix_smul_vadd (hp : p ≠ 0) (τ : ℍ) :
    ((heckeDiagMatrix p • ((1 : ℝ) +ᵥ τ) : ℍ) : ℂ) = (heckeDiagMatrix p • τ : ℍ) + (p : ℕ) := by
  rw [coe_heckeDiagMatrix_smul hp, coe_heckeDiagMatrix_smul hp, coe_vadd]
  push_cast
  ring

variable {p} in
/-- The `range p` reindex making the `U_p` sum invariant under `τ ↦ 1 +ᵥ τ`. -/
private theorem sum_heckeMatrix_smul_vadd (hp : p ≠ 0) (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    ∑ j ∈ Finset.range p, f (heckeMatrix p j • ((1 : ℝ) +ᵥ τ))
      = ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) := by
  simp only [heckeMatrix_smul_vadd hp]
  have h0 := Finset.sum_range_succ' (fun j => f (heckeMatrix p j • τ)) p
  have h1 := Finset.sum_range_succ (fun j => f (heckeMatrix p j • τ)) p
  rw [apply_eq_of_coe_eq_add_nat hf 1 (coe_heckeMatrix_smul_self hp τ)] at h1
  exact add_right_cancel (h0.symm.trans h1)

/-- `U_p f` is invariant under `τ ↦ 1 +ᵥ τ` when `f` is `1`-periodic. -/
private theorem heckeU_vadd (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    heckeU k p f ((1 : ℝ) +ᵥ τ) = heckeU k p f τ := by
  by_cases hp : p = 0
  · simp only [hp, heckeU_zero_left, Pi.zero_apply]
  · rw [heckeU_apply k hp, heckeU_apply k hp, sum_heckeMatrix_smul_vadd hp hf]

/-- `T_p f` is invariant under `τ ↦ 1 +ᵥ τ` when `f` is `1`-periodic. -/
private theorem heckeT_vadd (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    heckeT k p f ((1 : ℝ) +ᵥ τ) = heckeT k p f τ := by
  by_cases hp : p = 0
  · simp only [hp, heckeT_zero_left]
    exact apply_eq_of_coe_eq_add_nat hf 1 (by rw [coe_vadd]; push_cast; ring)
  · rw [heckeT_apply k hp, heckeT_apply k hp, sum_heckeMatrix_smul_vadd hp hf,
      apply_eq_of_coe_eq_add_nat hf p (coe_heckeDiagMatrix_smul_vadd hp τ)]

/-- A `vadd`-invariant function is periodic over `ofComplex`. -/
private theorem periodic_comp_ofComplex_of_vadd {g : ℍ → ℂ} (hg : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) :
    Periodic (g ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < im w
  · have hw' : 0 < im (w + 1) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    convert hg ⟨w, hw⟩ using 2
    apply UpperHalfPlane.ext
    simp [add_comm]
  · have hw1 : im (w + 1) ≤ 0 := by simpa using hw
    have hw0 : im w ≤ 0 := not_lt.mp hw
    simp only [comp_apply, ofComplex_apply_eq_of_im_nonpos hw1 hw0]

end Regularity

/-! ### The public targets

The statements are written with the wrappers' explicit binders (the checker is
textual), not with the pin's section variables. -/

/-- `U_p` preserves holomorphy. Stated verbatim from
`Theorems/Thm_ModularForm_mdifferentiable_heckeU.lean`. -/
theorem mdifferentiable_heckeU {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => MDiff g) (fun _ _ ha hb => ha.add hb)
    mdifferentiable_const (fun _ _ => hf.slash k _)

/-- `T_p` preserves holomorphy. Stated verbatim from
`Theorems/Thm_ModularForm_mdifferentiable_heckeT.lean`. -/
theorem mdifferentiable_heckeT {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeT k p f) :=
  (mdifferentiable_heckeU hf k p).add (hf.slash k _)

/-- `U_p` preserves boundedness at `∞`. Stated verbatim from
`Theorems/Thm_ModularForm_isBoundedAtImInfty_heckeU.lean`. -/
theorem isBoundedAtImInfty_heckeU {f : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) (p : ℕ) :
    UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsBoundedAtImInfty g)
    (fun _ _ ha hb => ha.add hb) UpperHalfPlane.zero_form_isBoundedAtImInfty
    (fun j _ => hf.slash k (heckeMatrix_one_zero p j))

/-- `T_p` preserves boundedness at `∞`. Stated verbatim from
`Theorems/Thm_ModularForm_isBoundedAtImInfty_heckeT.lean`. -/
theorem isBoundedAtImInfty_heckeT {f : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) (p : ℕ) :
    UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeT k p f) :=
  (isBoundedAtImInfty_heckeU hf k p).add (hf.slash k (heckeDiagMatrix_one_zero p))

/-- `U_p` preserves `1`-periodicity. Stated verbatim from
`Theorems/Thm_ModularForm_periodic_heckeU_comp_ofComplex.lean`. -/
theorem periodic_heckeU_comp_ofComplex {f : UpperHalfPlane → ℂ}
    (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (k : ℤ) (p : ℕ) :
    Function.Periodic (ModularForm.heckeU k p f ∘ UpperHalfPlane.ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd (heckeU_vadd k p hf)

/-- `T_p` preserves `1`-periodicity. Stated verbatim from
`Theorems/Thm_ModularForm_periodic_heckeT_comp_ofComplex.lean`. -/
theorem periodic_heckeT_comp_ofComplex {f : UpperHalfPlane → ℂ}
    (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (k : ℤ) (p : ℕ) :
    Function.Periodic (ModularForm.heckeT k p f ∘ UpperHalfPlane.ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd (heckeT_vadd k p hf)

/-- `MDifferentiable.slash` for the diagonal Hecke matrix. Stated verbatim from
`Theorems/Thm_ModularForm_mdifferentiable_slash_heckeDiagMatrix.lean`; its pin
`S_` file is nine lines. -/
theorem mdifferentiable_slash_heckeDiagMatrix (d : ℕ) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (SlashAction.map k (ModularForm.heckeDiagMatrix d) f) :=
  MDifferentiable.slash hf k (ModularForm.heckeDiagMatrix d)

end ModularForm

end
