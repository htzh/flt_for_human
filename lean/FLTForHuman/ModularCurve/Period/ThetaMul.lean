/-
  The Leibniz rule for `θ = q d/dq` on `LaurentSeries`.

  With `θ` written out as `single 1 1 * derivative`, the normalized derivation
  satisfies the product rule

      `θ (f * g) = f * θ g + g * θ f`.

  The port of the pin leaf `ModularCurve.theta_mul`
  (`Theorems/Thm_ModularCurve_theta_mul.lean` and
  `P2M/Sol/S_ModularCurve_theta_mul.lean`, pinned `aa2d8b3`).  The statement is the
  wrapper's verbatim; the proof is the `S_` file's `theta_mul` body (its
  coefficient computation `hθ : (θ h).coeff m = m • h.coeff m` and the support
  inclusion `θ h`'s support in `h`'s, then coefficientwise the Leibniz identity).
  The pin's `solution` wrapper is not ported, and the `S_` file's other
  declarations are `private` helpers of *its* later nodes (`theta_qExpand`,
  `theta_qTwist`, `PhiGen.weightTwo_*`) which this node's proof does not use, so
  they are not transcribed; nor are the `S_` file's `example` blocks.  The pin's
  own `ModularCurve.theta_coeff` (used by those helpers) is already homed, public,
  in `ModularCurve/Period/QExpansionDerivative.lean`.

  This is the one declaration group C's `omegaRow_T2` needed and the port lacked;
  it is not the D-S cone's node but a real pin leaf, so it lands as its own module
  (no existing module is edited).

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_theta_mul.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_theta_mul.lean>

  spec-pin: Theorems/Thm_ModularCurve_theta_mul.lean
  spec-pin: P2M/Sol/S_ModularCurve_theta_mul.lean
-/

import Mathlib.RingTheory.LaurentSeries

set_option autoImplicit false

noncomputable section

namespace ModularCurve

theorem theta_mul {R : Type*} [CommRing R] (f g : LaurentSeries R) :
    (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R (f * g) =
      f * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R g) +
        g * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f) := by
  have hθ : ∀ (h : LaurentSeries R) (m : ℤ),
      ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R h).coeff m
        = m • h.coeff m := by
    intro h m
    rw [HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
      LaurentSeries.hasseDeriv_coeff]
    simp
  have hsupp : ∀ h : LaurentSeries R,
      ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R h).support
        ⊆ h.support := by
    intro h m hm
    rw [HahnSeries.mem_support] at hm ⊢
    intro h0
    exact hm (by rw [hθ, h0, smul_zero])
  ext k
  rw [HahnSeries.coeff_add, hθ, mul_comm g, HahnSeries.coeff_mul_right' g.isPWO_support (hsupp g),
    HahnSeries.coeff_mul_left' f.isPWO_support (hsupp f), HahnSeries.coeff_mul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  obtain ⟨-, -, hk⟩ := Finset.mem_antidiagonal.mp hij
  rw [hθ, hθ, ← hk, add_smul, mul_smul_comm, smul_mul_assoc, add_comm]

end ModularCurve

end
