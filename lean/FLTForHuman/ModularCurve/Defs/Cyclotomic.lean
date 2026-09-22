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

  The **statements are the pin's verbatim; the proofs are mathlib's**, per the
  2026-09-22 bridge audit (`logs/audit-prelude-bridges.md` a.1). The pin
  re-proves `IsCyclotomicExtension.exists_isPrimitiveRoot` for the `CyclotomicField`
  instance; here the existence and the chosen root come straight from mathlib's
  `IsCyclotomicExtension.zeta`/`zeta_spec`. The `p ∣ N` step is
  `IsPrimitiveRoot.pow` + `Nat.div_mul_cancel` in place of the pin's
  `pow_of_dvd`/`div_div_self` chain. `cycUnit_pow` keeps the
  `IsPrimitiveRoot.pow_eq_one` two-liner; `IsCyclotomicExtension.zeta_pow` is the
  equally short alternative the audit records. The pin's
  `haveI : NeZero ((N : ℕ) : ℚ)` is likewise dropped: mathlib synthesizes it from
  `[NeZero N]`, so only the `IsCyclotomicExtension` instance is installed.

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
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  exact ⟨IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ),
    IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)⟩

/-- A chosen primitive `N`-th root of unity in `CyclotomicField N ℚ`, as a unit. -/
def cycUnit (N : ℕ) [NeZero N] : (CyclotomicField N ℚ)ˣ :=
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  ((IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)).isUnit (NeZero.ne N)).unit

/-- The chosen root is primitive. -/
theorem cycUnit_spec (N : ℕ) [NeZero N] :
    IsPrimitiveRoot ((cycUnit N : (CyclotomicField N ℚ)ˣ) : CyclotomicField N ℚ) N := by
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  rw [cycUnit, IsUnit.unit_spec]
  exact IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)

/-- The chosen root satisfies `ζ ^ N = 1`. -/
theorem cycUnit_pow (N : ℕ) [NeZero N] : cycUnit N ^ N = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, (cycUnit_spec N).pow_eq_one, Units.val_one])

variable {K : Type*} [Field K]

/-- If `ζ` is a primitive `N`-th root and `p ∣ N`, then `ζ ^ (N / p)` is a
primitive `p`-th root. -/
theorem isPrimitiveRoot_pow_div {N : ℕ} [NeZero N] {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N)
    {p : ℕ} (hpN : p ∣ N) : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := by
  have h := hζ.pow (Nat.pos_of_ne_zero (NeZero.ne N)) (Nat.div_mul_cancel hpN).symm
  rwa [← Units.val_pow_eq_pow_val] at h

end ModularCurve

end
