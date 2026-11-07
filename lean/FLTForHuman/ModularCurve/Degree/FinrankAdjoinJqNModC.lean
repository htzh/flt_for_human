/-
  The Tate curve's `j`, `c₄` and `c₆` in terms of `jqModC`.

  `tateLaurent K` is `tatePowerSeries.map (laurentOfInt K)`, so its invariants are the
  integral power series of `Defs/TateFormal.lean`; the coefficient computations here turn
  `c₄ ^ 3 = jqModC · Δ` into a cancellation of the units `Δ` and `q` rather than an
  analytic statement. The live consumer is `TateSlots/ToricPointDictionary.lean`
  (`c6_tatePowerSeries`).

  ## What moved out

  Until the shelving this module also carried the socket-route degree development — the
  `finrank`/`NonAdjoin`/`Pkg` block fed by
  `FunctionFieldGeneration/PrimePowerStepAnyField.lean`. Nothing in the tree reaches that
  route (`finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero` had no consumer), so it is now
  `Reserve/ModularCurve/Degree/FinrankAdjoinJqNModCDead.lean`, together with the whole
  `C`-layer island it rests on (`Reserve/ModularCurve/FunctionFieldGeneration/`).
  spec-pin: P2M/Sol/S_ModularCurve_j_tateLaurent.lean
  spec-pin: Theorems/Thm_ModularCurve_Delta_tatePowerSeries.lean
  spec-pin: Theorems/Thm_ModularCurve_c4_pow_three_tateLaurent.lean
  spec-pin: Theorems/Thm_ModularCurve_c4_tatePowerSeries.lean
  spec-pin: Theorems/Thm_ModularCurve_c6_tatePowerSeries.lean
  spec-pin: Theorems/Thm_ModularCurve_j_tateLaurent.lean
-/
import FLTForHuman.ModularCurve.Defs.QExpandCharP
import FLTForHuman.ModularCurve.Degree.PrimeNonAdjoin
import FLTForHuman.ModularCurve.FunctionFieldGeneration.ModularPolynomialExistence
import FLTForHuman.ModularCurve.X1.IntegralityJqNModC
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false
-- The pin installs the `Fact (Nat.Prime (ringChar K))` and `NeZero ((d : ℕ) : K)`
-- instances of the two headlines with `haveI`; both are consumed by typeclass
-- search (`CharP.char_prime_of_ne_zero`, `HasEnoughRootsOfUnity`), so the style
-- linter's `have` preference does not apply. Same local disable as
-- `PrimePowerStepAnyField.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

variable {K : Type*} [Field K]

/-! ## The Tate `j`

`tateLaurent K` is `tatePowerSeries.map (laurentOfInt K)`, so its invariants are
the integral power series of `Defs/TateFormal.lean`; the three coefficient
computations below are what turn `c₄ ^ 3 = jqModC · Δ` into a cancellation of the
units `Δ` and `q` rather than an analytic statement. -/

/-- `c₄` of the formal Tate curve in terms of `tateA4`: `1 - 48 A₄`. Verbatim from
`S_ModularCurve_j_tateLaurent.lean:16`. -/
theorem c4_tatePowerSeries_eq_one_sub :
    tatePowerSeries.c₄ = 1 - PowerSeries.C 48 * tateA4 := by
  rw [show (PowerSeries.C (48 : ℤ)) = (48 : PowerSeries ℤ) from map_ofNat _ 48]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tatePowerSeries_a₁,
    tatePowerSeries_a₂, tatePowerSeries_a₃, tatePowerSeries_a₄]
  ring

/-- `c₆` of the formal Tate curve in terms of `tateA4`/`tateA6`: `-1 + 72 A₄ - 864 A₆`.
Verbatim from `S_ModularCurve_j_tateLaurent.lean:23`. -/
theorem c6_tatePowerSeries_eq :
    tatePowerSeries.c₆ = -1 + PowerSeries.C 72 * tateA4 - PowerSeries.C 864 * tateA6 := by
  rw [show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72,
    show (PowerSeries.C (864 : ℤ)) = (864 : PowerSeries ℤ) from map_ofNat _ 864]
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃, tatePowerSeries_a₄,
    tatePowerSeries_a₆]
  ring

/-- `c₄` of the formal Tate curve is the weight-`4` Eisenstein series. Verbatim
from `S_ModularCurve_j_tateLaurent.lean:32`. -/
theorem c4_tatePowerSeries : tatePowerSeries.c₄ = eisenstein4 := by
  rw [c4_tatePowerSeries_eq_one_sub]
  ext n
  rw [eisenstein4, PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    coeff_tateA4]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [ite_eq_right hn.ne', mul_neg, Finset.mul_sum]
    rw [show (∑ d ∈ n.divisors, (48 : ℤ) * (5 * (d : ℤ) ^ 3))
        = ∑ d ∈ n.divisors, 240 * (d : ℤ) ^ 3 from
      Finset.sum_congr rfl fun d _ => by ring]
    ring

/-- `c₆` of the formal Tate curve is `-eisenstein6`. Verbatim from
`S_ModularCurve_j_tateLaurent.lean:45`. -/
theorem c6_tatePowerSeries : tatePowerSeries.c₆ = -eisenstein6 := by
  rw [c6_tatePowerSeries_eq]
  ext n
  rw [map_neg, eisenstein6, PowerSeries.coeff_mk, map_sub, map_add, map_neg,
    PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_tateA4,
    coeff_tateA6]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [ite_eq_right hn.ne', mul_neg, neg_zero, zero_add, sub_neg_eq_add, Finset.mul_sum]
    have hSb : (∑ d ∈ n.divisors, (864 : ℤ) * tateB d)
        = (∑ d ∈ n.divisors, 72 * (5 * (d : ℤ) ^ 3)) + ∑ d ∈ n.divisors, 504 * (d : ℤ) ^ 5 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      have h := twelve_mul_tateB d
      linarith
    have hE6 : (∑ d ∈ n.divisors, (-504 : ℤ) * (d : ℤ) ^ 5)
        = -∑ d ∈ n.divisors, 504 * (d : ℤ) ^ 5 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    linarith [hSb, hE6]

/-- `q⁻¹` times `PowerSeries.X` is `1` in the Laurent series ring: the inverse of
`laurentOfInt K X` is the single-term series at `-1`. Verbatim from
`S_ModularCurve_j_tateLaurent.lean:74`. -/
theorem single_neg_one_mul_laurentOfInt_X (K : Type*) [CommRing K] :
    (HahnSeries.single (-1 : ℤ) (1 : K)) * laurentOfInt K PowerSeries.X = 1 := by
  rw [laurentOfInt_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X, HahnSeries.single_mul_single,
    neg_add_cancel, mul_one, HahnSeries.single_zero_one]

/-- The two `laurentOfInt`-images of `Δ` and `Δ⁻¹` multiply to `1`. Verbatim from
`S_ModularCurve_j_tateLaurent.lean:79`. -/
theorem laurentOfInt_dedekindEtaUnitInv_mul (K : Type*) [CommRing K] :
    laurentOfInt K dedekindEtaUnitInv * laurentOfInt K dedekindEtaUnit = 1 := by
  rw [← map_mul, mul_comm, dedekindEtaUnit_mul_inv, map_one]

/-- `Δ` of the formal Tate curve is `q · η ^ 24` — the coefficient identity
`c₄ ^ 3 - c₆ ^ 2 = 1728 · q · η ^ 24` (`eisenstein4_cube_sub_mk_sq`) divided by
`1728`. Verbatim from `S_ModularCurve_j_tateLaurent.lean:83`, and from
`Theorems/Thm_ModularCurve_Delta_tatePowerSeries.lean`. -/
theorem Delta_tatePowerSeries :
    tatePowerSeries.Δ = PowerSeries.X * dedekindEtaUnit := by
  have hc : (1728 : PowerSeries ℤ) * tatePowerSeries.Δ
      = 1728 * (PowerSeries.X * dedekindEtaUnit) := by
    rw [WeierstrassCurve.c_relation, c4_tatePowerSeries, c6_tatePowerSeries, neg_pow,
      neg_one_pow_two, one_mul]
    simpa only [eisenstein6] using eisenstein4_cube_sub_mk_sq
  have h1728 : (1728 : PowerSeries ℤ) ≠ 0 := fun h => by
    have := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this; exact absurd this (by decide)
  exact mul_left_cancel₀ h1728 hc

/-- **`c₄ ^ 3 = jqModC · Δ`** for the formal Tate curve over any `CommRing K`: the
two sides differ by the unit pair `(q⁻¹, q)` times `(Δ⁻¹, Δ)`, both of which are
`1`. Verbatim from `S_ModularCurve_j_tateLaurent.lean:94`, and from
`Theorems/Thm_ModularCurve_c4_pow_three_tateLaurent.lean`. -/
theorem c4_pow_three_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ ^ 3 = jqModC K * (tateLaurent K).Δ := by
  rw [tateLaurent, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, c4_tatePowerSeries,
    Delta_tatePowerSeries, ← map_pow, jqModC]
  rw [← laurentOfInt_apply, show jNum = eisenstein4 ^ 3 * dedekindEtaUnitInv from rfl, map_mul,
    map_mul]
  calc laurentOfInt K (eisenstein4 ^ 3)
      = laurentOfInt K (eisenstein4 ^ 3)
          * (laurentOfInt K dedekindEtaUnitInv * laurentOfInt K dedekindEtaUnit)
          * (HahnSeries.single (-1 : ℤ) (1 : K) * laurentOfInt K PowerSeries.X) := by
        rw [laurentOfInt_dedekindEtaUnitInv_mul K, single_neg_one_mul_laurentOfInt_X K, mul_one,
          mul_one]
    _ = HahnSeries.single (-1 : ℤ) (1 : K)
          * (laurentOfInt K (eisenstein4 ^ 3) * laurentOfInt K dedekindEtaUnitInv)
          * (laurentOfInt K PowerSeries.X * laurentOfInt K dedekindEtaUnit) := by ring

/-- **The Tate curve's `j`-invariant is `jqModC`**: `(tateLaurent K).j = jqModC K`
over any `CommRing K`. Verbatim from
`Theorems/Thm_ModularCurve_j_tateLaurent.lean:6` (the pin's `S_` copy is
`private`, at `S_ModularCurve_j_tateLaurent.lean:108`). -/
theorem j_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).j = jqModC K := by
  rw [WeierstrassCurve.j, c4_pow_three_tateLaurent K, ← WeierstrassCurve.coe_Δ',
    mul_comm (jqModC K), Units.inv_mul_cancel_left]

end ModularCurve

end
