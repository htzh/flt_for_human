/-
  One unreachable helper of the weak-approximation node, kept as a reading copy: the
  order of a unit of `v`'s valuation subring at a place `w` whose valuation subring
  contains `v`'s.  In the pin its only consumer is the `S_` file's own proof of
  `exists_mem_and_not_mem`; the port carries that separation lemma publicly in
  `Place/OrdCalculus.lean` with a different proof, so nothing here reaches this lemma.

  Cut from `FLTForHuman/AlgebraicCurve/Place/Approximation.lean` on 2026-10-23
  (`tools/deps/move_dead.py`), at the pin's statement and `private` as the pin has it.
  It imports the port's public `Defs` API and never the module it came from.  No
  `spec-pin:` wire: a shelf in `Reserve`, built so that it stays green, diffed by nothing.

  Pin source (pinned `aa2d8b3`): `P2M/Sol/S_AlgebraicCurve_Place_exists_forall_ord_eq.lean`
  lines 85–101, public there as `AlgebraicCurve.Place.ord_coe_unit_eq_zero_of_le`.
-/
import FLTForHuman.AlgebraicCurve.Defs.PushPull

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A unit of `v`'s valuation subring, viewed in `w`, has order zero at `w`
whenever `w`'s valuation subring contains `v`'s. -/
private theorem ord_coe_unit_eq_zero_of_le {v w : Place K F}
    (h : v.toValuationSubring ≤ w.toValuationSubring) (u : v.toValuationSubringˣ) :
    w.ord ((u : v.toValuationSubring) : F) = 0 := by
  have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 := by
    simp [ne_eq, ZeroMemClass.coe_eq_zero]
  have hui0 : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) ≠ 0 := by
    simp [ne_eq, ZeroMemClass.coe_eq_zero]
  have h1 : 0 ≤ w.ord ((u : v.toValuationSubring) : F) :=
    (w.mem_iff_ord_nonneg hu0).mp (h (u : v.toValuationSubring).2)
  have h2 : 0 ≤ w.ord (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) :=
    (w.mem_iff_ord_nonneg hui0).mp (h ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).2)
  have hprod : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
      * ((u : v.toValuationSubring) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, OneMemClass.coe_one]
  have hsum := congrArg w.ord hprod
  rw [w.ord_mul hui0 hu0, ord_one] at hsum
  omega

end Place

end AlgebraicCurve
