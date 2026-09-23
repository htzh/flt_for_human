/-
  The Hecke matrices `heckeMatrix`/`heckeDiagMatrix` and their action on `ℍ`.

  These are the two substitutions `τ ↦ (τ + b)/ℓ` and `τ ↦ ℓτ` that generate the
  `ℓ + 1` cosets of the Hecke correspondence at `ℓ`. mathlib has **no** Hecke
  operator: `grep -rln heckeMatrix Mathlib/` is empty, and there is no
  `ModularForm.heckeU`/`heckeT`. FLT defines them in
  `Definitions/Def_ModularForm_HeckeOperator.lean` (204 lines, 41 declarations);
  the port first took only the 60-line subset the Φ_p cone used
  (`heckeMatrix`/`heckeDiagMatrix` and the two `coe_*_smul` facts), and the
  Hecke-operator topic (2026-09) extends it with the operator block, lines
  72–200, in full: `σ_hecke*`, `slash_hecke*_apply`, `heckeU`/`heckeT`, the
  three definitional rewrites, the `_zero_left`/`_zero`/`_apply` displays, the
  linearity algebra (`add`/`smul`/`neg`/`sub`) and `coeffHecke*` with its nine
  lemmas. This makes the file the verbatim subset of the pin's definition module
  that the port needs; the Tier-1 invariance results live in
  `FLTForHuman/ModularForms/HeckeInvariance.lean`.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularForm_HeckeOperator.lean` lines 11–200. All declarations
  are verbatim (including the pin's `@[simp]` attributes); only `heckeMatrix_zero`,
  `heckeDiagMatrix_zero` and the `det_*`/`denom_*` helpers are private here.
  `val_heckeMatrix` is public because the Fricke pair consumes it,
  `val_heckeDiagMatrix` because the analytic layer does, and
  `upperTriangularGL`/`val_upperTriangularGL` because the cusp-class layer's
  rational model needs them (the pin has all of these public too).
-/
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ModularForm

/-- `!![a, b; 0, d]` as an element of `GL (Fin 2) ℝ`, for `a * d ≠ 0`. -/
def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] :=
  rfl

/-- The Hecke matrix `!![1, j; 0, p]` (the substitution `τ ↦ (τ + j)/p`). -/
def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

/-- The diagonal Hecke matrix `!![p, 0; 0, 1]` (the substitution `τ ↦ pτ`). -/
def heckeDiagMatrix (p : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp)

@[simp] theorem val_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)] := by
  simp [heckeMatrix, hp]

@[simp] theorem val_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) :
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

/-! ## The operators `U_p` and `T_p`

FLT's `Def_ModularForm_HeckeOperator.lean` lines 72–200, verbatim: the `σ`-twists,
the two slash displays, the `Finset.range` operators, their `simp`/linearity
algebra, and the coefficient maps. -/

theorem σ_heckeMatrix (p j : ℕ) : UpperHalfPlane.σ (heckeMatrix p j) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, ite_eq_left (det_heckeMatrix_pos p j)]

theorem σ_heckeDiagMatrix (p : ℕ) : UpperHalfPlane.σ (heckeDiagMatrix p) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, ite_eq_left (det_heckeDiagMatrix_pos p)]

theorem slash_heckeMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeMatrix p j • τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [ModularForm.slash_apply, σ_heckeMatrix, det_heckeMatrix hp, denom_heckeMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hp', show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]

theorem slash_heckeDiagMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeDiagMatrix p) τ = (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [ModularForm.slash_apply, σ_heckeDiagMatrix, det_heckeDiagMatrix hp, denom_heckeDiagMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast, one_zpow, mul_one]
  rw [mul_comm]

def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

def heckeT (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p

theorem heckeU_def (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeU k p f = ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j := rfl

theorem heckeT_eq_heckeU_add (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeT k p f = heckeU k p f + f ∣[k] heckeDiagMatrix p := rfl

theorem heckeT_def (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeT k p f = (∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j) + f ∣[k] heckeDiagMatrix p := rfl

@[simp] theorem heckeU_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeU k 0 f = 0 := by
  simp [heckeU]

@[simp] theorem heckeT_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by
  simp [heckeT]

theorem heckeU_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeU k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) := by
  simp only [heckeU, Finset.sum_apply, slash_heckeMatrix_apply k hp, Finset.mul_sum]

theorem heckeT_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeT k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)
      + (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [heckeT, Pi.add_apply, heckeU_apply k hp, slash_heckeDiagMatrix_apply k hp]

@[simp] theorem heckeU_zero (k : ℤ) (p : ℕ) : heckeU k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeU]

@[simp] theorem heckeT_zero (k : ℤ) (p : ℕ) : heckeT k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeT]

theorem heckeU_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeU k p (f + g) = heckeU k p f + heckeU k p g := by
  simp [heckeU, Finset.sum_add_distrib]

theorem heckeT_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeT k p (f + g) = heckeT k p f + heckeT k p g := by
  simp only [heckeT, heckeU_add, SlashAction.add_slash]
  abel

theorem heckeU_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) :
    heckeU k p (c • f) = c • heckeU k p f := by
  simp only [heckeU, ModularForm.smul_slash, σ_heckeMatrix, ContinuousAlgEquiv.refl_apply,
    Finset.smul_sum]

theorem heckeT_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) :
    heckeT k p (c • f) = c • heckeT k p f := by
  rw [heckeT, heckeT, heckeU_smul, ModularForm.smul_slash, σ_heckeDiagMatrix,
    ContinuousAlgEquiv.refl_apply, smul_add]

theorem heckeU_neg (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : heckeU k p (-f) = -heckeU k p f := by
  simp [heckeU, Finset.sum_neg_distrib]

theorem heckeT_neg (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : heckeT k p (-f) = -heckeT k p f := by
  simp only [heckeT, heckeU_neg, SlashAction.neg_slash, neg_add]

theorem heckeU_sub (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeU k p (f - g) = heckeU k p f - heckeU k p g := by
  rw [sub_eq_add_neg, heckeU_add, heckeU_neg, ← sub_eq_add_neg]

theorem heckeT_sub (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeT k p (f - g) = heckeT k p f - heckeT k p g := by
  rw [sub_eq_add_neg, heckeT_add, heckeT_neg, ← sub_eq_add_neg]

def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)

theorem coeffHeckeT_apply (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT k p a n = a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 := rfl

theorem coeffHeckeU_apply (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : coeffHeckeU p a n = a (n * p) := rfl

theorem coeffHeckeT_of_dvd (k : ℤ) {p n : ℕ} (h : p ∣ n) (a : ℕ → ℂ) :
    coeffHeckeT k p a n = a (n * p) + (p : ℂ) ^ (k - 1) * a (n / p) := by
  rw [coeffHeckeT, ite_eq_left h]

theorem coeffHeckeT_of_not_dvd (k : ℤ) {p n : ℕ} (h : ¬ p ∣ n) (a : ℕ → ℂ) :
    coeffHeckeT k p a n = a (n * p) := by
  rw [coeffHeckeT, ite_eq_right h, add_zero]

theorem coeffHeckeT_eq_coeffHeckeU_add (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT k p a n = coeffHeckeU p a n + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 := rfl

theorem coeffHeckeT_add (k : ℤ) (p : ℕ) (a b : ℕ → ℂ) :
    coeffHeckeT k p (a + b) = coeffHeckeT k p a + coeffHeckeT k p b := by
  funext n
  simp only [coeffHeckeT, Pi.add_apply]
  split_ifs <;> ring

theorem coeffHeckeT_smul (k : ℤ) (p : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeT k p (c • a) = c • coeffHeckeT k p a := by
  funext n
  simp only [coeffHeckeT, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem coeffHeckeU_add (p : ℕ) (a b : ℕ → ℂ) :
    coeffHeckeU p (a + b) = coeffHeckeU p a + coeffHeckeU p b := rfl

theorem coeffHeckeU_smul (p : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeU p (c • a) = c • coeffHeckeU p a := rfl

end ModularForm

end
