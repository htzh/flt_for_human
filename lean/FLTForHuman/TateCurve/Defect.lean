/-
The defect coefficients of the Tate curve's point coordinates.

Transcribed from the pin's `Definitions/Def_TateCurve_Defect.lean` (182 lines), pinned `aa2d8b3`:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_TateCurve_Defect.lean>

Three layers, in the pin's own order:

* the **Cauchy product** of `q`-series (`cauchyMul` and its mul/summability lemmas), the ring structure
  the point coordinates' identities are computed in;
* the **full coefficient sequences** `xCoeffFull`/`yCoeffFull` (the `0`-th term is the `q`-free part) and
  the **Weierstrass coefficients** `a₄Coeff`/`a₆Coeff` as divisor sums, with their growth bounds against
  `growthBound`/`seriesBound`;
* the **defect coefficients** `defectCoeff`, the `q`-series of the Weierstrass-defect of a point.

It is the definition layer the two defect rows are stated in: `defect_qExpansion` writes the defect of
`(pointX q u, pointY q u)` as `∑' N, defectCoeff u N * q ^ N`, and `defectCoeff_zero` is its `0`-th term.

The pin's bare `import Mathlib` is replaced by the specific mathlib module the file uses
(`Mathlib.Analysis.Normed.Ring.InfiniteSum`); names, statements, the `private` marking of
`antidiagonal_sum_mul_pow` and the top-level `TateCurve` namespace are the pin's. Section-variable
placement is adjusted so the module builds with 0 warnings; no declaration statement is changed.

spec-pin: Definitions/Def_TateCurve_Defect.lean
-/
import FLTForHuman.TateCurve.PointSeries
import FLTForHuman.TateCurve.Tails
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

section CauchyProduct

variable {K : Type*} [NontriviallyNormedField K] {q : K}

noncomputable def cauchyMul (c d : ℕ → K) (N : ℕ) : K :=
  ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal N, c kl.1 * d kl.2

@[simp] theorem cauchyMul_zero (c d : ℕ → K) : cauchyMul c d 0 = c 0 * d 0 := by
  simp [cauchyMul]

theorem cauchyMul_one (c d : ℕ → K) : cauchyMul c d 1 = c 0 * d 1 + c 1 * d 0 := by
  rw [cauchyMul, Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.Nat.antidiagonal_zero,
    Finset.sum_map, Finset.sum_singleton]
  rfl

private theorem antidiagonal_sum_mul_pow (c d : ℕ → K) (N : ℕ) :
    ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal N, (c kl.1 * q ^ kl.1) * (d kl.2 * q ^ kl.2)
      = cauchyMul c d N * q ^ N := by
  rw [cauchyMul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hsum : kl.1 + kl.2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  rw [← hsum, pow_add]
  ring

theorem qSeries_mul {c d : ℕ → K} [CompleteSpace K]
    (hc : Summable fun N => ‖c N * q ^ N‖) (hd : Summable fun N => ‖d N * q ^ N‖) :
    (∑' N : ℕ, c N * q ^ N) * (∑' N : ℕ, d N * q ^ N)
      = ∑' N : ℕ, cauchyMul c d N * q ^ N := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hc hd]
  exact tsum_congr fun N => antidiagonal_sum_mul_pow c d N

theorem summable_norm_cauchyMul {c d : ℕ → K}
    (hc : Summable fun N => ‖c N * q ^ N‖) (hd : Summable fun N => ‖d N * q ^ N‖) :
    Summable fun N => ‖cauchyMul c d N * q ^ N‖ := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hc hd
  refine h.congr fun N => ?_
  rw [antidiagonal_sum_mul_pow]

theorem summable_norm_qSeries {c : ℕ → K} {B C : ℝ} (hC0 : 0 ≤ C)
    (hb : ∀ N, ‖c N‖ ≤ B * C ^ N) (hqC : ‖q‖ * C < 1) :
    Summable fun N => ‖c N * q ^ N‖ := by
  have hCq0 : 0 ≤ C * ‖q‖ := mul_nonneg hC0 (norm_nonneg q)
  have hCq1 : C * ‖q‖ < 1 := by rwa [mul_comm] at hqC
  have hgeom : Summable fun N : ℕ => B * (C * ‖q‖) ^ N :=
    (summable_geometric_of_lt_one hCq0 hCq1).mul_left B
  refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_) hgeom
  rw [norm_mul, norm_pow]
  calc ‖c N‖ * ‖q‖ ^ N ≤ (B * C ^ N) * ‖q‖ ^ N :=
        mul_le_mul_of_nonneg_right (hb N) (pow_nonneg (norm_nonneg q) N)
    _ = B * (C * ‖q‖) ^ N := by rw [mul_pow]; ring

end CauchyProduct

section Coefficients

variable {K : Type*} [NontriviallyNormedField K]

noncomputable def xCoeffFull (u : K) : ℕ → K
  | 0 => xfun u
  | (N + 1) => xCoeff u (N + 1)

@[simp] theorem xCoeffFull_zero (u : K) : xCoeffFull u 0 = xfun u := rfl

@[simp] theorem xCoeffFull_succ (u : K) (N : ℕ) : xCoeffFull u (N + 1) = xCoeff u (N + 1) := rfl

noncomputable def yCoeffFull (u : K) : ℕ → K
  | 0 => yfun u
  | (N + 1) => yCoeff u (N + 1)

@[simp] theorem yCoeffFull_zero (u : K) : yCoeffFull u 0 = yfun u := rfl

@[simp] theorem yCoeffFull_succ (u : K) (N : ℕ) : yCoeffFull u (N + 1) = yCoeff u (N + 1) := rfl

noncomputable def a₄Coeff : ℕ → K
  | 0 => 0
  | (N + 1) => -(∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K))

@[simp] theorem a₄Coeff_zero : a₄Coeff (K := K) 0 = 0 := rfl

@[simp] theorem a₄Coeff_succ (N : ℕ) :
    a₄Coeff (K := K) (N + 1) = -(∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K)) := rfl

noncomputable def a₆Coeff : ℕ → K
  | 0 => 0
  | (N + 1) => -(∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K))

@[simp] theorem a₆Coeff_zero : a₆Coeff (K := K) 0 = 0 := rfl

@[simp] theorem a₆Coeff_succ (N : ℕ) :
    a₆Coeff (K := K) (N + 1) = -(∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K)) := rfl

section Ultra
variable [IsUltrametricDist K]

theorem norm_xCoeff_le (u : K) (N : ℕ) : ‖xCoeff u N‖ ≤ growthBound u ^ N := by
  rw [xCoeff]
  refine norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (growthBound_nonneg u) N)
    (fun d hd => ?_)
  exact (norm_xDivTerm_le u d).trans
    (pow_le_pow_right₀ (one_le_growthBound u) (Nat.divisor_le hd))

theorem norm_yCoeff_le (u : K) (N : ℕ) : ‖yCoeff u N‖ ≤ growthBound u ^ N := by
  rw [yCoeff]
  refine norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (growthBound_nonneg u) N)
    (fun d hd => ?_)
  exact (norm_yDivTerm_le u d).trans
    (pow_le_pow_right₀ (one_le_growthBound u) (Nat.divisor_le hd))

end Ultra

noncomputable def seriesBound (u : K) : ℝ := max (max ‖xfun u‖ ‖yfun u‖) 1

theorem one_le_seriesBound (u : K) : 1 ≤ seriesBound u := le_max_right _ _

theorem seriesBound_nonneg (u : K) : 0 ≤ seriesBound u :=
  zero_le_one.trans (one_le_seriesBound u)

section UltraCoeff
variable [IsUltrametricDist K]

theorem norm_xCoeffFull_le (u : K) (N : ℕ) :
    ‖xCoeffFull u N‖ ≤ seriesBound u * growthBound u ^ N := by
  cases N with
  | zero =>
      simp only [xCoeffFull_zero, pow_zero, mul_one]
      exact (le_max_left _ _).trans (le_max_left _ _)
  | succ n =>
      rw [xCoeffFull_succ]
      calc ‖xCoeff u (n + 1)‖ ≤ growthBound u ^ (n + 1) := norm_xCoeff_le u (n + 1)
        _ = 1 * growthBound u ^ (n + 1) := (one_mul _).symm
        _ ≤ seriesBound u * growthBound u ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (one_le_seriesBound u)
              (pow_nonneg (growthBound_nonneg u) _)

theorem norm_yCoeffFull_le (u : K) (N : ℕ) :
    ‖yCoeffFull u N‖ ≤ seriesBound u * growthBound u ^ N := by
  cases N with
  | zero =>
      simp only [yCoeffFull_zero, pow_zero, mul_one]
      exact (le_max_right _ _).trans (le_max_left _ _)
  | succ n =>
      rw [yCoeffFull_succ]
      calc ‖yCoeff u (n + 1)‖ ≤ growthBound u ^ (n + 1) := norm_yCoeff_le u (n + 1)
        _ = 1 * growthBound u ^ (n + 1) := (one_mul _).symm
        _ ≤ seriesBound u * growthBound u ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (one_le_seriesBound u)
              (pow_nonneg (growthBound_nonneg u) _)

theorem norm_a₄Coeff_le (N : ℕ) : ‖a₄Coeff (K := K) N‖ ≤ 1 := by
  cases N with
  | zero => simp
  | succ n =>
      rw [a₄Coeff_succ, norm_neg]
      exact norm_sum_le_of_forall_le_of_nonneg zero_le_one
        (fun d _ => IsUltrametricDist.norm_natCast_le_one K _)

theorem norm_a₆Coeff_le (N : ℕ) : ‖a₆Coeff (K := K) N‖ ≤ 1 := by
  cases N with
  | zero => simp
  | succ n =>
      rw [a₆Coeff_succ, norm_neg]
      exact norm_sum_le_of_forall_le_of_nonneg zero_le_one
        (fun d _ => IsUltrametricDist.norm_natCast_le_one K _)

end UltraCoeff

end Coefficients

section Defect

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

noncomputable def defectCoeff (u : K) (N : ℕ) : K :=
  cauchyMul (yCoeffFull u) (yCoeffFull u) N + cauchyMul (xCoeffFull u) (yCoeffFull u) N
    - (cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
        + cauchyMul a₄Coeff (xCoeffFull u) N + a₆Coeff N)

end Defect

end TateCurve
