/-
  A Hermite-type coset representative for the upper triangular subgroup of `SL(2, ℤ)`:
  every `M ∈ M₂(ℤ)` with `M.det ≠ 0` factors as

      `M = B · !![a, b; 0, d]` with `B ∈ SL(2, ℤ)`, `0 < a`, `0 ≤ b < |d|`, `a * d = M.det`.

  The port of the pin leaf

      `Matrix.exists_specialLinearGroup_mul_upperTriangular`

  (`P2M/Sol/S_Matrix_exists_specialLinearGroup_mul_upperTriangular.lean`
  — 76 pin lines; the pin's `S_` development is `namespace Matrix` and its
  `S06W2` sub-namespace, kept here under the pin's own namespace and its short names
  untouched), together with the statement of its `Theorems/` wrapper

      `Theorems/Thm_Matrix_exists_specialLinearGroup_mul_upperTriangular.lean`.

  It is a faithful transcription: no statement is weakened, no route is generalised, and
  the pin's proof is carried verbatim (`spec/check_port.py` diffs both public
  declarations below against the two files named here).

  The mathematics: `g = gcd(M 0 0, M 1 0) > 0` with Bézout coefficients `u`, `v`
  (`Int.gcdA`, `Int.gcdB`), so `B₀ = !![u, v; -y', x'] ∈ SL(2, ℤ)` clears the first
  column: `B₀ * M = !![g, b'; 0, d]` with `g * d = M.det ≠ 0`. Dividing `b'` by `d`
  (`Int.mul_ediv_add_emod`) gives the bound `0 ≤ r < |d|`, and the unipotent
  `T = !![1, q; 0, 1]` moves `!![g, r; 0, d]` to `!![g, b'; 0, d]`. Hence
  `M = (B₀⁻¹ * T) · !![g, r; 0, d]`.

  The statement is the wrapper's, not the `S_` file's: it names
  `Matrix.SpecialLinearGroup`, where the `S_` copy says `SpecialLinearGroup` inside
  `namespace Matrix` (the two differ; `port_advise` ratio 0.982). The `S_` file's own
  `S06W2.exists_specialLinearGroup_mul_upperTriangular` is kept public at the pin's name,
  since its proof body is the verified surface.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  spec-pin: Theorems/Thm_Matrix_exists_specialLinearGroup_mul_upperTriangular.lean
  spec-pin: P2M/Sol/S_Matrix_exists_specialLinearGroup_mul_upperTriangular.lean
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Matrix

namespace S06W2

/-- The pin's `S_`-file copy: Hermite reduction of `M` by `B ∈ SL(2, ℤ)`. -/
theorem exists_specialLinearGroup_mul_upperTriangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    ∃ (B : SpecialLinearGroup (Fin 2) ℤ) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < |d| ∧ a * d = M.det ∧
      M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] := by

  set x := M 0 0 with hx
  set y := M 1 0 with hy
  have hxy : ¬ (x = 0 ∧ y = 0) := by
    rintro ⟨h0, h1⟩
    apply hM
    rw [det_fin_two, ← hx, ← hy, h0, h1, zero_mul, mul_zero, sub_zero]
  set g : ℤ := (Int.gcd x y : ℤ) with hg
  have hg0 : 0 < g := by
    rw [hg, Int.natCast_pos, Int.gcd_pos_iff]
    tauto
  obtain ⟨x', hx'⟩ : (g : ℤ) ∣ x := Int.gcd_dvd_left x y
  obtain ⟨y', hy'⟩ : (g : ℤ) ∣ y := Int.gcd_dvd_right x y

  set u := Int.gcdA x y
  set v := Int.gcdB x y
  have hbez : x * u + y * v = g := (Int.gcd_eq_gcd_ab x y).symm
  have hbez' : x' * u + y' * v = 1 := by
    rw [hx', hy'] at hbez
    have h0 : g * (x' * u + y' * v - 1) = 0 := by linear_combination hbez
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hg0.ne'
    · linear_combination h

  let B₀ : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![u, v; -y', x'], by rw [det_fin_two_of]; linear_combination hbez'⟩
  set b' := u * M 0 1 + v * M 1 1 with hb'
  set d := -y' * M 0 1 + x' * M 1 1 with hd
  have hkey : (B₀ : Matrix (Fin 2) (Fin 2) ℤ) * M = !![g, b'; 0, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B₀, Matrix.mul_apply, Fin.sum_univ_two, ← hx, ← hy, hx', hy', hb', hd] <;> ring_nf
    · linear_combination (g : ℤ) * hbez'

  have hdet : g * d = M.det := by
    have := congrArg Matrix.det hkey
    rw [det_mul, B₀.prop, one_mul, det_fin_two_of, mul_zero, sub_zero] at this
    exact this.symm
  have hd0 : d ≠ 0 := by intro h0; exact hM (by rw [← hdet, h0, mul_zero])

  set q := b' / d
  set r := b' % d
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hd0
  have hrd : r < |d| := Int.emod_lt_abs _ hd0
  have hbqr : b' = r + d * q := by
    have := Int.mul_ediv_add_emod b' d
    linear_combination -this
  let T : SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, q; 0, 1], by rw [det_fin_two_of]; ring⟩
  have hT : (T : Matrix (Fin 2) (Fin 2) ℤ) * !![g, r; 0, d] = !![g, b'; 0, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two, hbqr]
    ring
  refine ⟨B₀⁻¹ * T, g, r, d, hg0, hr0, hrd, hdet, ?_⟩
  rw [SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hT, ← hkey, ← Matrix.mul_assoc,
    ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one, Matrix.one_mul]

end S06W2

/-- The pin's headline, at the wrapper's name: Hermite reduction in `M₂(ℤ)`. -/
theorem exists_specialLinearGroup_mul_upperTriangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < |d| ∧ a * d = M.det ∧ M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] :=
  S06W2.exists_specialLinearGroup_mul_upperTriangular M hM

end Matrix
