/-
  The Hecke matrices `heckeMatrix`/`heckeDiagMatrix` and their action on `ℍ`.

  These are the two substitutions `τ ↦ (τ + b)/ℓ` and `τ ↦ ℓτ` that generate the
  `ℓ + 1` cosets of the Hecke correspondence at `ℓ`. mathlib has **no** Hecke
  operator: `grep -rln heckeMatrix Mathlib/` is empty, and there is no
  `ModularForm.heckeU`/`heckeT`. FLT defines them in
  `Definitions/Def_ModularForm_HeckeOperator.lean` (204 lines, 38 declarations);
  the port takes the subset the Φ_p cone uses, which is what the T8 work order's
  `grep -c` survey found: `heckeMatrix` (3 of T8's 5 pin files),
  `heckeDiagMatrix` (3), `coe_heckeMatrix_smul` (1), `coe_heckeDiagMatrix_smul`
  (1) — and nothing else.

  **Dropped block (with counts).** `heckeU`, `heckeT`, `coeffHeckeT`,
  `coeffHeckeU`, `slash_hecke*`, `σ_hecke*`: **0 occurrences** in T8's five pin
  files. Across the cone's other 44 node files, `heckeU`/`heckeT` appear only in
  the doc-site toolchain's `attribute [-simp] ModularForm.heckeU_zero …` pragma
  (5 files: `ModularPolynomialData_eq_of_prime`, `PhiGen_splits_of_prime`,
  `PhiGen_splits_prime_at_slot`, `exists_phiIrreducible_evalSymm`,
  `finrank_adjoin_jqN_eq_of_prime`), never mathematically;
  `coeffHeckeT`/`coeffHeckeU`/`slash_hecke*`/`σ_hecke*` are 0. So the block is
  not ported; a later cone piece that needs the Hecke *operators* extends this
  module then.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularForm_HeckeOperator.lean` lines 11–70. The declarations
  kept are verbatim; `upperTriangularGL`, the `val_*`/`det_*`/`denom_*` helpers
  are private here because only `heckeMatrix`/`heckeDiagMatrix` and the two
  `coe_*_smul` facts are consumed outside.
-/
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ModularForm

/-- `!![a, b; 0, d]` as an element of `GL (Fin 2) ℝ`, for `a * d ≠ 0`. -/
private def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] private theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] :=
  rfl

/-- The Hecke matrix `!![1, j; 0, p]` (the substitution `τ ↦ (τ + j)/p`). -/
def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

/-- The diagonal Hecke matrix `!![p, 0; 0, 1]` (the substitution `τ ↦ pτ`). -/
def heckeDiagMatrix (p : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp)

@[simp] private theorem val_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)] := by
  simp [heckeMatrix, hp]

@[simp] private theorem val_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; 0, 1] := by
  simp [heckeDiagMatrix, hp]

@[simp] private theorem heckeMatrix_zero (j : ℕ) : heckeMatrix 0 j = 1 := by simp [heckeMatrix]

@[simp] private theorem heckeDiagMatrix_zero : heckeDiagMatrix 0 = 1 := by simp [heckeDiagMatrix]

private theorem det_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) : ((heckeMatrix p j).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeMatrix hp, Matrix.det_fin_two_of]
  ring

private theorem det_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) : ((heckeDiagMatrix p).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeDiagMatrix hp, Matrix.det_fin_two_of]
  ring

private theorem det_heckeMatrix_pos (p j : ℕ) : 0 < ((heckeMatrix p j).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

private theorem det_heckeDiagMatrix_pos (p : ℕ) : 0 < ((heckeDiagMatrix p).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeDiagMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

private theorem denom_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeMatrix p j) τ = p := by
  simp [UpperHalfPlane.denom, val_heckeMatrix hp]

private theorem denom_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeDiagMatrix p) τ = 1 := by
  simp [UpperHalfPlane.denom, val_heckeDiagMatrix hp]

/-- The action of the Hecke matrix on `ℍ`: `(heckeMatrix p j) • τ = (τ + j)/p`. -/
theorem coe_heckeMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    ((heckeMatrix p j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeMatrix hp]

/-- The action of the diagonal Hecke matrix on `ℍ`: `(heckeDiagMatrix p) • τ = pτ`. -/
theorem coe_heckeDiagMatrix_smul {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    ((heckeDiagMatrix p • τ : UpperHalfPlane) : ℂ) = (p : ℂ) * (τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeDiagMatrix_pos p)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeDiagMatrix hp]

end ModularForm

end
