/-
  The Atkin–Lehner datum, and the slash it acts by.

  ## What the module is

  `AtkinLehnerDatum M q` packages a Fricke-type involution at level `M` for a prime `q`:
  the decomposition `M = q * R`, a Bézout pair `(a, b)` with `q * a - R * b = 1`, and the
  integer matrix `!![q * a, b; q * R, q]` of determinant `q`, whose square is a scalar
  multiple of a matrix in `Γ₀ M`. The slash by its `GL₂(ℝ)` image is `alSlash W k f`.

  This is the general object the port's `HeckeNebentypusFricke.lean` had been building by
  hand for the single Fricke matrix (`frickeGL M`, the case `q = M`): the datum carries the
  Bézout data that makes `mat` invertible mod `q` and `sqUnit` a unit, so `alGL` exists for
  every `q` and the two lemmas `alSlash_add` / `alSlash_smul` are the `slash`-calculus
  identities the weight-one nebentypus chain needs. `sigma_alGL_apply` is the reason the
  slash preserves the nebentypus: `σ` acts trivially on the half-plane because `alGL` has
  positive determinant.

  Nothing here is a theorem about cusp forms; it is the substrate for
  `ModularForm.alSlash_isZeroAt` / `…_mdifferentiable_alSlash` and for the two `CuspForm`
  headlines that consume them.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`, verbatim:
  `Definitions/Def_ModularForm_AtkinLehnerDatum.lean` (157 lines).
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_AtkinLehnerDatum.lean>

  spec-pin: Definitions/Def_ModularForm_AtkinLehnerDatum.lean
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions

open Matrix UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularForm

variable (M q : ℕ)

/-- The Atkin–Lehner datum at level `M` for `q`: the decomposition `M = q * R` and a Bézout
pair making the Fricke matrix invertible with determinant `q`. -/
structure AtkinLehnerDatum : Type where

  R : ℕ

  hM : M = q * R

  a : ℤ

  b : ℤ

  bezout : (q : ℤ) * a - (R : ℤ) * b = 1

namespace AtkinLehnerDatum

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

lemma hM_int : (M : ℤ) = (q : ℤ) * (W.R : ℤ) := by exact_mod_cast W.hM

include W in

lemma q_pos [NeZero M] : 0 < q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inl h))) (NeZero.ne M)
  · exact h

include W in

lemma R_pos [NeZero M] : 0 < W.R := by
  rcases Nat.eq_zero_or_pos W.R with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inr h))) (NeZero.ne M)
  · exact h

/-- The Fricke matrix `!![q * a, b; q * R, q]`, of determinant `q`. -/
def mat : Matrix (Fin 2) (Fin 2) ℤ := !![(q : ℤ) * W.a, W.b; (q : ℤ) * (W.R : ℤ), (q : ℤ)]

@[simp] lemma det_mat : W.mat.det = (q : ℤ) := by
  rw [mat, Matrix.det_fin_two_of]
  linear_combination (q : ℤ) * W.bezout

lemma mat_lowerLeft : W.mat 1 0 = (M : ℤ) := by
  rw [mat, W.hM_int]
  simp

/-- `mat * mat = q • sqUnit`: the square of the Fricke matrix is a scalar multiple of the
matrix `sqUnit` below, which is what lands `Γ₀ M`. -/
def sqUnit : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a ^ 2 + (W.R : ℤ) * W.b, W.b * (W.a + 1);
     (q : ℤ) * (W.R : ℤ) * (W.a + 1), (W.R : ℤ) * W.b + (q : ℤ)]

theorem mat_sq : W.mat * W.mat = (q : ℤ) • W.sqUnit := by
  rw [mat, sqUnit, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · show (q : ℤ) * W.a * ((q : ℤ) * W.a) + W.b * ((q : ℤ) * (W.R : ℤ))
      = (q : ℤ) * ((q : ℤ) * W.a ^ 2 + (W.R : ℤ) * W.b)
    ring
  · show (q : ℤ) * W.a * W.b + W.b * (q : ℤ) = (q : ℤ) * (W.b * (W.a + 1))
    ring
  · show (q : ℤ) * (W.R : ℤ) * ((q : ℤ) * W.a) + (q : ℤ) * ((q : ℤ) * (W.R : ℤ))
      = (q : ℤ) * ((q : ℤ) * (W.R : ℤ) * (W.a + 1))
    ring
  · show (q : ℤ) * (W.R : ℤ) * W.b + (q : ℤ) * (q : ℤ)
      = (q : ℤ) * ((W.R : ℤ) * W.b + (q : ℤ))
    ring

@[simp] lemma det_sqUnit : W.sqUnit.det = 1 := by
  rw [sqUnit, Matrix.det_fin_two_of]
  linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout

def sqUnitSL : SL(2, ℤ) := ⟨W.sqUnit, W.det_sqUnit⟩

@[simp] lemma sqUnitSL_coe : (W.sqUnitSL : Matrix (Fin 2) (Fin 2) ℤ) = W.sqUnit := rfl

lemma sqUnitSL_mem : W.sqUnitSL ∈ Gamma0 M := by
  rw [Gamma0_mem]
  show (((W.sqUnit 1 0 : ℤ) : ZMod M) = 0)
  have h : W.sqUnit 1 0 = (M : ℤ) * (W.a + 1) := by
    rw [sqUnit, W.hM_int]; simp
  rw [h]
  push_cast
  simp

/-- The datum's element of `GL₂(ℝ)`, whose slash is `alSlash`. -/
def alGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℝ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using W.q_pos.ne')

@[simp] lemma alGL_coe [NeZero M] :
    (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) = (W.mat).map (algebraMap ℤ ℝ) := rfl

lemma alGL_entry [NeZero M] (i j : Fin 2) :
    W.alGL i j = algebraMap ℤ ℝ (W.mat i j) := by
  show ((W.alGL : Matrix (Fin 2) (Fin 2) ℝ)) i j = _
  rw [alGL_coe, Matrix.map_apply]

lemma val_det_alGL [NeZero M] : ((W.alGL).det : ℝ) = (q : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, alGL_coe]
  have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h, W.det_mat]
  simp

lemma det_alGL_pos [NeZero M] : 0 < ((W.alGL).det : ℝ) := by
  rw [val_det_alGL]
  exact_mod_cast W.q_pos

/-- `σ` is the identity on the half-plane at positive determinant, so the Atkin–Lehner
slash does not conjugate the nebentypus — this is why `alSlash` commutes with `phi`. -/
lemma σ_alGL_apply [NeZero M] (z : ℂ) : σ W.alGL z = z := by
  rw [UpperHalfPlane.σ, ite_eq_left W.det_alGL_pos]
  simp

def alGLQ [NeZero M] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℚ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℚ)).det = (algebraMap ℤ ℚ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using W.q_pos.ne')

lemma alGLQ_map_castHom [NeZero M] : (W.alGLQ).map (Rat.castHom ℝ) = W.alGL := by
  apply Units.ext
  show (Rat.castHom ℝ).mapMatrix ((W.alGLQ : Matrix (Fin 2) (Fin 2) ℚ))
      = (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
  show (Rat.castHom ℝ).mapMatrix ((W.mat).map (algebraMap ℤ ℚ))
      = (W.mat).map (algebraMap ℤ ℝ)
  rw [RingHom.mapMatrix_apply, Matrix.map_map]
  congr 1

end AtkinLehnerDatum

/-- The Atkin–Lehner slash: `f ↦ f ∣[k] W.alGL`. -/
def alSlash {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M] (f : ℍ → ℂ) : ℍ → ℂ :=
  f ∣[k] W.alGL

lemma alSlash_def {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M] (f : ℍ → ℂ) :
    alSlash W k f = f ∣[k] W.alGL := rfl

lemma alSlash_add {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M] (f g : ℍ → ℂ) :
    alSlash W k (f + g) = alSlash W k f + alSlash W k g := by
  simp only [alSlash, SlashAction.add_slash]

lemma alSlash_smul {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M] (c : ℂ) (f : ℍ → ℂ) :
    alSlash W k (c • f) = c • alSlash W k f := by
  simp only [alSlash, ModularForm.smul_slash, AtkinLehnerDatum.σ_alGL_apply]

end ModularForm

end
