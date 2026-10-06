/-
Characteristic-free principal divisors on the function field of a Weierstrass curve.

Canonical sources: the pinned FLT `aa2d8b3` wrappers

* `Theorems/Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField_of_two_ne_zero_or.lean`,
* `Theorems/Thm_WeierstrassCurve_hasPrincipalDivisors_functionField_of_isElliptic.lean`,

with their `S_` files
`P2M/Sol/S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField_of_two_ne_zero_or.lean`
(147 lines) and
`P2M/Sol/S_WeierstrassCurve_hasPrincipalDivisors_functionField_of_isElliptic.lean`
(34 lines).  The statements are the wrappers' verbatim text; the proofs are the
`S_` files' bodies adapted to mathlib `v4.34.0`.

The mathematics: `yCoord` generates the function field over `RatFunc F`
(`adjoin_yCoord_eq_top`) and satisfies the quadratic `weierstrassQuadratic`.  The
element `yCoord` is separable over `RatFunc F` as soon as `2 ≠ 0 ∨ a₁ ≠ 0 ∨ a₃ ≠ 0`
(the derivative of its minimal polynomial — which divides the quadratic — is then
nonzero), so `RatFunc F → W.FunctionField` is separable and the ported generic
characteristic-free transfer `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`
supplies `HasPrincipalDivisors`.  The discriminant case reduces to it through
`(2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0` for `W.Δ ≠ 0`.

Assumes from lower modules: `FunctionFieldQuadratic.lean` (`yCoord`,
`weierstrassQuadratic` and its monicity/degree/annihilation facts),
`FunctionFieldFinite.lean` (`adjoin_yCoord_eq_top`,
`finiteDimensional_ratFunc_functionField`), `PrincipalDivisors.lean` (the
`CharZero` headline) and `AlgebraicCurve/PrincipalDivisors/IsSeparable.lean` (the
characteristic-free transfer `hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`,
which this module uses directly rather than the `ratFunc` alias, to keep the module
DAG a tree).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField_of_two_ne_zero_or.lean>
-/
import FLTForHuman.WeierstrassCurve.FunctionFieldQuadratic
import FLTForHuman.WeierstrassCurve.FunctionFieldFinite
import FLTForHuman.WeierstrassCurve.PrincipalDivisors
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.IsSeparable

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

private theorem natDegree_weierstrassQuadratic : (weierstrassQuadratic W).natDegree = 2 := by
  rw [weierstrassQuadratic, Polynomial.natDegree_add_eq_left_of_degree_lt]
  · exact Polynomial.natDegree_X_pow 2
  · rw [Polynomial.degree_X_pow]
    exact weierstrassQuadratic_sub_degree_lt

private theorem natDegree_minpoly_yCoord_le' :
    (minpoly (RatFunc F) (yCoord W)).natDegree ≤ 2 := by
  have hdvd : minpoly (RatFunc F) (yCoord W) ∣ weierstrassQuadratic W :=
    minpoly.dvd _ _ aeval_yCoord_weierstrassQuadratic
  exact (Polynomial.natDegree_le_of_dvd hdvd weierstrassQuadratic_monic.ne_zero).trans
    natDegree_weierstrassQuadratic.le

private theorem derivative_weierstrassQuadratic :
    derivative (weierstrassQuadratic W)
      = C (2 : RatFunc F) * X + C (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) := by
  rw [weierstrassQuadratic, derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X,
    derivative_C, sub_zero]
  norm_num

private theorem coeff_derivative_weierstrassQuadratic_zero :
    (derivative (weierstrassQuadratic W)).coeff 0
      = algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃) := by
  rw [derivative_weierstrassQuadratic, coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add,
    coeff_C_zero]

private theorem isSeparable_yCoord_of_or (h : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0) :
    IsSeparable (RatFunc F) (yCoord W) := by
  have hint : _root_.IsIntegral (RatFunc F) (yCoord W) := isIntegral_yCoord
  set m := minpoly (RatFunc F) (yCoord W) with hm
  have hirr : Irreducible m := minpoly.irreducible hint
  have hmon : m.Monic := minpoly.monic hint
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hint
  have hle : m.natDegree ≤ 2 := natDegree_minpoly_yCoord_le'

  have hcoeff : (derivative m).coeff (m.natDegree - 1) = (m.natDegree : RatFunc F) := by
    have h1 : m.natDegree - 1 + 1 = m.natDegree := by omega
    rw [Polynomial.coeff_derivative, h1, hmon.coeff_natDegree, one_mul]
    have : ((m.natDegree - 1 : ℕ) : RatFunc F) + 1 = (m.natDegree : RatFunc F) := by
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, h1]
    exact this
  have hder : derivative m ≠ 0 := by
    intro h0
    interval_cases hn : m.natDegree
    ·
      have := hcoeff
      rw [h0, Polynomial.coeff_zero] at this
      exact one_ne_zero (by exact_mod_cast this.symm)
    ·
      rcases h with h2 | h13
      · have h2' : (2 : RatFunc F) ≠ 0 := by
          rw [← map_ofNat (algebraMap F (RatFunc F)) 2]
          exact (_root_.map_ne_zero _).mpr h2
        have := hcoeff
        rw [h0, Polynomial.coeff_zero] at this
        exact h2' (by exact_mod_cast this.symm)
      · have hmQ : m = weierstrassQuadratic W :=
          (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon weierstrassQuadratic_monic
            (minpoly.dvd _ _ aeval_yCoord_weierstrassQuadratic)
            (by rw [natDegree_weierstrassQuadratic, hn])).symm
        have hc := coeff_derivative_weierstrassQuadratic_zero (W := W)
        rw [← hmQ, h0, Polynomial.coeff_zero] at hc
        have hpoly : (C W.a₁ * X + C W.a₃ : F[X]) ≠ 0 := by
          intro hz
          rcases h13 with h1 | h3
          · apply h1
            simpa using congrArg (fun p : F[X] => p.coeff 1) hz
          · apply h3
            simpa using congrArg (fun p : F[X] => p.coeff 0) hz
        exact hpoly ((map_eq_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mp hc.symm)
  show m.Separable
  exact (Polynomial.separable_iff_derivative_ne_zero hirr).mpr hder

private theorem algebra_isSeparable_ratFunc_functionField_of_or
    (h : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0) :
    Algebra.IsSeparable (RatFunc F) W.FunctionField := by
  have h1 : Algebra.IsSeparable (RatFunc F)
      (IntermediateField.adjoin (RatFunc F) ({yCoord W} : Set W.FunctionField)) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
        (F := RatFunc F) (E := W.FunctionField)).mpr
      (isSeparable_yCoord_of_or h)
  rw [adjoin_yCoord_eq_top] at h1
  exact AlgEquiv.Algebra.isSeparable
    (IntermediateField.topEquiv (F := RatFunc F) (E := W.FunctionField))

private theorem two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero (W : Affine F)
    (hΔ : W.Δ ≠ 0) :
    (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨h2, h1, h3⟩ := h
  apply hΔ
  have hb2 : W.b₂ = 0 := by
    rw [WeierstrassCurve.b₂, h1]; linear_combination (2 * W.a₂) * h2
  have hb4 : W.b₄ = 0 := by
    rw [WeierstrassCurve.b₄, h1]; linear_combination W.a₄ * h2
  have hb6 : W.b₆ = 0 := by
    rw [WeierstrassCurve.b₆, h3]; linear_combination (2 * W.a₆) * h2
  rw [WeierstrassCurve.Δ, hb2, hb4, hb6]; ring

/-- **Principal divisors when `2 ≠ 0 ∨ a₁ ≠ 0 ∨ a₃ ≠ 0`.**  Verbatim from
`Theorems/Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField_of_two_ne_zero_or.lean`. -/
theorem hasPrincipalDivisors_functionField_of_two_ne_zero_or {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F)
    (h : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0) :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField := by
  haveI : FiniteDimensional (RatFunc F) W.FunctionField := finiteDimensional_ratFunc_functionField W
  haveI : Algebra.IsSeparable (RatFunc F) W.FunctionField :=
    algebra_isSeparable_ratFunc_functionField_of_or h
  exact AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable (K := F)
    W.FunctionField

end Affine

/-- **Principal divisors on an elliptic curve's function field.**  Verbatim from
`Theorems/Thm_WeierstrassCurve_hasPrincipalDivisors_functionField_of_isElliptic.lean`. -/
theorem hasPrincipalDivisors_functionField_of_isElliptic
    {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    AlgebraicCurve.HasPrincipalDivisors F W.toAffine.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_two_ne_zero_or W.toAffine
    (WeierstrassCurve.Affine.two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero W.toAffine
      W.isUnit_Δ.ne_zero)

end WeierstrassCurve

end
