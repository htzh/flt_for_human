/-
  Layer 0a — the unit twist `q ↦ u q`.

  `qTwistFun u` rescales the coefficient of `q ^ k` by `u ^ k`; `qTwist u` is
  that function packaged as a ring endomorphism. It is the second of the two
  transport maps (the first being `qExpand`), and `qTwist_qExpand` records that
  the two commute into the substitution `q ↦ u q ^ N`.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_PhiGen.lean` lines 18–96.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PhiGen.lean

  Names are FLT's verbatim; `LaurentSeries`, `HahnSeries` and `Finset` are
  mathlib's. Assumes `qExpand` and its coefficient lemmas from
  `FLTForHuman.ModularCurve.Defs.Laurent`.
-/
import FLTForHuman.ModularCurve.Defs.Laurent

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField

namespace ModularCurve

section QTwist

variable {R : Type*} [CommRing R]

/-- The twist `q ↦ u q` on coefficients: the coefficient of `q ^ k` is rescaled
by `u ^ k`. -/
def qTwistFun (u : Rˣ) (f : LaurentSeries R) : LaurentSeries R where
  coeff k := (u ^ k : Rˣ) * f.coeff k
  isPWO_support' := f.isPWO_support'.mono fun k hk => by
    simp only [Function.mem_support] at hk ⊢
    exact fun h => hk (by rw [h, mul_zero])

@[simp]
theorem qTwistFun_coeff (u : Rˣ) (f : LaurentSeries R) (k : ℤ) :
    (qTwistFun u f).coeff k = (u ^ k : Rˣ) * f.coeff k := rfl

/-- A unit twist rescales coefficients, so it does not change which exponents
occur: the support is unchanged. -/
theorem support_qTwistFun (u : Rˣ) (f : LaurentSeries R) :
    (qTwistFun u f).support = f.support := by
  ext k
  rw [HahnSeries.mem_support, HahnSeries.mem_support, qTwistFun_coeff]
  exact not_congr (Units.mul_right_eq_zero _)

open Finset renaming antidiagonal → pwoAntidiagonal, mem_antidiagonal → mem_pwoAntidiagonal in
/-- `qTwistFun u` as a ring endomorphism of Laurent series: the substitution
`q ↦ u q`. -/
def qTwist (u : Rˣ) : LaurentSeries R →+* LaurentSeries R where
  toFun := qTwistFun u
  map_one' := by
    ext k
    rw [qTwistFun_coeff, HahnSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · rw [mul_zero]
  map_mul' f g := by
    ext k

    have hset : pwoAntidiagonal (qTwistFun u f).isPWO_support
        (qTwistFun u g).isPWO_support k =
        pwoAntidiagonal f.isPWO_support g.isPWO_support k := by
      ext ij
      simp only [mem_pwoAntidiagonal, support_qTwistFun]
    rw [qTwistFun_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, hset, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    obtain ⟨-, -, hsum⟩ := mem_pwoAntidiagonal.mp hij
    rw [qTwistFun_coeff, qTwistFun_coeff, mul_mul_mul_comm, ← Units.val_mul, ← zpow_add,
      hsum]
  map_zero' := by
    ext k
    rw [qTwistFun_coeff, HahnSeries.coeff_zero, mul_zero]
  map_add' f g := by
    ext k
    rw [HahnSeries.coeff_add]
    show (qTwistFun u (f + g)).coeff k = (qTwistFun u f).coeff k + (qTwistFun u g).coeff k
    rw [qTwistFun_coeff, qTwistFun_coeff, qTwistFun_coeff, HahnSeries.coeff_add, mul_add]

@[simp]
theorem qTwist_coeff (u : Rˣ) (f : LaurentSeries R) (k : ℤ) :
    (qTwist u f).coeff k = (u ^ k : Rˣ) * f.coeff k := rfl

theorem support_qTwist (u : Rˣ) (f : LaurentSeries R) : (qTwist u f).support = f.support :=
  support_qTwistFun u f

@[simp]
theorem qTwist_single (u : Rˣ) (k : ℤ) (r : R) :
    qTwist u (HahnSeries.single k r) = HahnSeries.single k ((u ^ k : Rˣ) * r) := by
  ext m
  rw [qTwist_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs with h
  · subst h; rfl
  · rw [mul_zero]

theorem qTwist_one_apply (f : LaurentSeries R) : qTwist (1 : Rˣ) f = f := by
  ext k
  rw [qTwist_coeff, one_zpow, Units.val_one, one_mul]

/-- Twisting by `u` after `v` is twisting by `u * v`. -/
theorem qTwist_qTwist (u v : Rˣ) (f : LaurentSeries R) :
    qTwist u (qTwist v f) = qTwist (u * v) f := by
  ext k
  rw [qTwist_coeff, qTwist_coeff, qTwist_coeff, ← mul_assoc, ← Units.val_mul, ← mul_zpow]

theorem qTwist_injective (u : Rˣ) : Function.Injective (qTwist u) := by
  intro f g h
  have := congrArg (qTwist u⁻¹) h
  rwa [qTwist_qTwist, qTwist_qTwist, inv_mul_cancel, qTwist_one_apply, qTwist_one_apply]
    at this

/-- `qTwist` and `qExpand` commute into the substitution `q ↦ u q ^ N`: twisting
after expanding by `N` is expanding by `N` after twisting by `u ^ N`. -/
theorem qTwist_qExpand (v : Rˣ) (N : ℕ) [NeZero N] (f : LaurentSeries R) :
    qTwist v (qExpand R N f) = qExpand R N (qTwist (v ^ (N : ℤ)) f) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qTwist_coeff, qExpand_coeff_mul, qExpand_coeff_mul, qTwist_coeff, ← zpow_mul]
  · rw [qTwist_coeff, qExpand_coeff_of_not_dvd N f hk, mul_zero,
      qExpand_coeff_of_not_dvd N _ hk]

end QTwist

end ModularCurve

end
