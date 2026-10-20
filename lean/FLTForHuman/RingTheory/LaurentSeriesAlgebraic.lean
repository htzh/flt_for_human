/-
  Algebraic elements of `K⸨X⸩` are constant:

      `IsAlgebraic K x → x = HahnSeries.C (x.coeff 0)`.

  The port of the pin leaf `LaurentSeries.eq_C_coeff_zero_of_isAlgebraic`
  (`P2M/Sol/S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic.lean`, 77 pin lines),
  together with the statement of its `Theorems/` wrapper.

  The mathematics: a nonconstant Laurent series has a least exponent `x.order`,
  and if `x.order < 0` then for the leading-degree term `d` of an annihilating
  polynomial `p` the coefficient `p.coeff d * (x ^ d).coeff (d • x.order)` of
  `aeval x p` is nonzero — because every other term `x ^ i` (`i < d`) has order
  `i • x.order > d • x.order`.  Applying the same argument to `x⁻¹` gives
  `x.order = 0`; then `x - C (x.coeff 0)` is again algebraic and nonzero of
  order `0`, whose own constant coefficient vanishes — contradiction.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has no form of this statement —
  `rg -n "eq_C_coeff_zero|order_nonneg_of_isAlgebraic|isAlgebraic.*LaurentSeries"`
  over `Mathlib/` hits only `Polynomial.eq_C_coeff_zero_iff_natDegree_eq_zero`
  (a different, polynomial-level statement) and the `HahnSeries.order_*` API.
  One of the pin's helpers *is* mathlib's: the pin's `algebraMap_eq_C` is
  `LaurentSeries.algebraMap_apply` (`Mathlib/RingTheory/LaurentSeries.lean:1069`),
  so it is imported, not transcribed (see drift below).

  The pin's inner namespace `LaurentSeries.AlgClosedPort` is folded into the object's own
  `LaurentSeries` (the three declarations are `LaurentSeries.order_*` facts; no label is left),
  and the module is homed beside mathlib's `RingTheory/LaurentSeries.lean`.

  spec-pin: Theorems/Thm_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic.lean
  spec-pin: P2M/Sol/S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic.lean
-/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Algebraic.Basic

set_option autoImplicit false

namespace LaurentSeries

open HahnSeries Polynomial

variable {K : Type*} [Field K]

-- Dropped from the pin: the pin's `algebraMap_eq_C` is mathlib's
-- `LaurentSeries.algebraMap_apply`.

theorem order_nonneg_of_isAlgebraic {x : LaurentSeries K} (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    0 ≤ x.order := by
  by_contra hneg
  push Not at hneg
  obtain ⟨p, hp0, hpx⟩ := hx
  set d := p.natDegree with hd
  have hne : (x ^ d).coeff (d • x.order) ≠ 0 := by
    rw [← HahnSeries.order_pow x d]
    exact (HahnSeries.coeff_order_eq_zero.not.mpr (pow_ne_zero d hx0))
  have key : (Polynomial.aeval x p).coeff (d • x.order)
      = p.coeff d * (x ^ d).coeff (d • x.order) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    simp only [HahnSeries.coeff_sum, LaurentSeries.algebraMap_apply, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hpi : p.coeff i = 0
    · rw [hpi, zero_mul]
    · have hlt : d • x.order < (x ^ i).order := by
        rw [HahnSeries.order_pow, nsmul_eq_mul, nsmul_eq_mul]
        have hi' : (i : ℤ) < (d : ℤ) := by exact_mod_cast hi
        nlinarith
      rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, mul_zero]
  have hlead : p.coeff d ≠ 0 := by
    rw [hd]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have h : (Polynomial.aeval x p).coeff (d • x.order) ≠ 0 := by
    rw [key]; exact mul_ne_zero hlead hne
  apply h
  rw [hpx]
  rfl

theorem order_eq_zero_of_isAlgebraic {x : LaurentSeries K} (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    x.order = 0 := by
  have h1 := order_nonneg_of_isAlgebraic hx hx0
  have h2 := order_nonneg_of_isAlgebraic hx.inv (inv_ne_zero hx0)
  have h3 : x.order + x⁻¹.order = 0 := by
    rw [← HahnSeries.order_mul hx0 (inv_ne_zero hx0), mul_inv_cancel₀ hx0, HahnSeries.order_one]
  omega

end LaurentSeries

open LaurentSeries in
theorem LaurentSeries.eq_C_coeff_zero_of_isAlgebraic {K : Type*} [Field K] {x : LaurentSeries K}
    (hx : IsAlgebraic K x) :
    x = HahnSeries.C (x.coeff 0) := by
  set y : LaurentSeries K := x - HahnSeries.C (x.coeff 0) with hy
  have hyalg : IsAlgebraic K y := by
    refine hx.sub ?_
    rw [← LaurentSeries.algebraMap_apply]
    exact isAlgebraic_algebraMap _
  by_cases hy0 : y = 0
  · exact sub_eq_zero.mp hy0
  · exfalso
    have hord := order_eq_zero_of_isAlgebraic hyalg hy0
    have hc : y.coeff y.order ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hy0
    rw [hord] at hc
    apply hc
    simp [hy]
