/-
  Layer 0b — a primitive `N`-th root of unity in `CyclotomicField N ℚ`.

  Both T13's `splits_of_prime` and the FFG spine need a chosen primitive `N`-th
  root in the cyclotomic field; the pin repeats the five declarations in
  `S_ModularCurve_PhiGen_splits_of_prime.lean` (188–203) and
  `S_ModularCurve_PhiGen_splits_prime_at_slot.lean` (123–133, 188–203 in the
  sibling copies) and the FFG `S_ModularCurve_functionFieldGeneration.lean`. The
  port writes them once here and imports them from both.

  `cycUnit_pow` is the `cycUnit N ^ N = 1` form the cone's integrality input
  wants; `isPrimitiveRoot_pow_div` is the `p ∣ N` root-of-a-power step.

  Assumes only mathlib (`CyclotomicField`, `IsCyclotomicExtension`,
  `IsPrimitiveRoot`).
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

set_option autoImplicit false
-- The cyclotomic instances are installed with `haveI`; the style linter prefers
-- `have`, but they are consumed by instance search, so `haveI` is the faithful
-- spelling (the same local disable the cone's modules use).
set_option linter.style.haveILetI false

noncomputable section

namespace ModularCurve

/-- `CyclotomicField N ℚ` contains a primitive `N`-th root of unity. -/
theorem exists_isPrimitiveRoot_cyclotomicField (N : ℕ) [NeZero N] :
    ∃ z : CyclotomicField N ℚ, IsPrimitiveRoot z N := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  exact IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField N ℚ)
    (Set.mem_singleton N) (NeZero.ne N)

/-- A chosen primitive `N`-th root of unity in `CyclotomicField N ℚ`, as a unit. -/
def cycUnit (N : ℕ) [NeZero N] : (CyclotomicField N ℚ)ˣ :=
  ((exists_isPrimitiveRoot_cyclotomicField N).choose_spec.isUnit (NeZero.ne N)).unit

/-- The chosen root is primitive. -/
theorem cycUnit_spec (N : ℕ) [NeZero N] :
    IsPrimitiveRoot ((cycUnit N : (CyclotomicField N ℚ)ˣ) : CyclotomicField N ℚ) N := by
  rw [cycUnit, IsUnit.unit_spec]
  exact (exists_isPrimitiveRoot_cyclotomicField N).choose_spec

/-- The chosen root satisfies `ζ ^ N = 1`. -/
theorem cycUnit_pow (N : ℕ) [NeZero N] : cycUnit N ^ N = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, (cycUnit_spec N).pow_eq_one, Units.val_one])

variable {K : Type*} [Field K]

/-- If `ζ` is a primitive `N`-th root and `p ∣ N`, then `ζ ^ (N / p)` is a
primitive `p`-th root. -/
theorem isPrimitiveRoot_pow_div {N : ℕ} [NeZero N] {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N)
    {p : ℕ} (hpN : p ∣ N) : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := by
  have hN : N ≠ 0 := NeZero.ne N
  have hd0 : N / p ≠ 0 := by
    intro h0
    have hc := Nat.div_mul_cancel hpN
    rw [h0, zero_mul] at hc
    exact hN hc.symm
  have h := hζ.pow_of_dvd hd0 (Nat.div_dvd_of_dvd hpN)
  rw [Nat.div_div_self hpN hN] at h
  rwa [← Units.val_pow_eq_pow_val] at h

end ModularCurve

end
