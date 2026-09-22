/-
  The low coefficients of `jq`: `j(q) = q⁻¹ + 744 + 196884 q + ⋯`.

  This is the first *proof* module of the `functionFieldGeneration` effort: it closes
  the two `jq.coeff` claims that sat in Zone C of `spec/ModularCurveConsumer.lean`
  since Layer 0.

  Source of the *statement* — `base/004-the-j-invariant.md` (and the consumer's
  Zone C): the regular coefficients of `j` are `744` at `q ^ 0` and `196884` at
  `q ^ 1`. FLT has no declaration for these two facts — `hasSum_jq_qParam` is a
  different statement, reached a different way — so there is no FLT name to keep.
  The names follow the port's own convention in `Defs/Jq.lean`, next to
  `coeff_jq_neg_one` and `coeff_jq_of_lt`.

  The *proof* is a deliberate divergence from FLT's route. FLT reaches the
  coefficients of `η` through `S_ModularCurve_StarBank_deltaNorm.lean`
  (`rescale_tprod_one_sub_X_pow`, `expand_tprod_one_sub_X_pow`) and the modular-form
  q-expansion cluster (44 nodes, ~11k lines) inside the deferred `Φ_p` subtree.
  Here we use mathlib's pentagonal number theorem instead: `Defs/Jq.lean` defines
  `etaProd` as exactly `∏' n, (1 - X ^ (n + 1))`, and mathlib's
  `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` identifies that product with
  `pentagonalSeries`, whose coefficients are given by
  `coeff_pentagonalSeries_pentagonal` / `coeff_pentagonalSeries_eq_zero`. The
  computation is then finite and low-order:

      E₄³  = 1 + 720 q + 179280 q² + ⋯
      η²⁴  = 1 - 24 q +   252 q² + ⋯
      Δ⁻¹  = 1 + 24 q +   324 q² + ⋯
      jNum = 1 + 744 q + 196884 q² + ⋯

  Nothing of the modular-form cluster is ported. `PowerSeries`, `HahnSeries`,
  `pentagonalSeries` and `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` are
  mathlib's; the two exported theorems are ours.

  Assumes `eisenstein4`, `etaProd`, `dedekindEtaUnit{,_inv}`, `jNum`, `jNumQ`, `jq`
  and their constant-term/`invOfUnit` lemmas from `Defs/Jq.lean`.
-/
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import FLTForHuman.ModularCurve.Defs.Jq

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

/-! ## `etaProd` is mathlib's pentagonal product

`Defs/Jq.lean` defines `etaProd` as a topological product; mathlib proves the same
product equals `pentagonalSeries`, whose coefficients are explicit. The next three
constants are all the `η` data the computation needs: `1`, `-1`, `-1`. -/

private theorem etaProd_eq_pentagonalSeries : etaProd = PowerSeries.pentagonalSeries ℤ := by
  rw [etaProd]
  exact PowerSeries.WithPiTopology.tprod_one_sub_X_pow ℤ

private theorem coeff_etaProd_zero : etaProd.coeff 0 = 1 := by
  rw [etaProd_eq_pentagonalSeries, PowerSeries.coeff_zero_eq_constantCoeff]
  have h := PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℤ) 0
  norm_num [pentagonal] at h
  exact h

private theorem coeff_etaProd_one : etaProd.coeff 1 = -1 := by
  rw [etaProd_eq_pentagonalSeries]
  have h := PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℤ) 1
  norm_num [pentagonal] at h
  exact h

private theorem coeff_etaProd_two : etaProd.coeff 2 = -1 := by
  rw [etaProd_eq_pentagonalSeries]
  have h := PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℤ) (-1)
  norm_num [pentagonal] at h
  exact h

/-! ## Low-order coefficient algebra

`PowerSeries.coeff_mul` is a `Finset` sum over `antidiagonal n`; for `n = 2` it is
the three-term formula below (mathlib rewrites the antidiagonal as `range 3` via
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ`). `coeff_two_pow` is the resulting
closed form for the second coefficient of a power, by induction on the exponent,
using mathlib's `coeff_one_pow` for the first coefficient. -/

private theorem coeff_two_mul (φ ψ : PowerSeries ℤ) :
    (φ * ψ).coeff 2 =
      φ.coeff 0 * ψ.coeff 2 + φ.coeff 1 * ψ.coeff 1 + φ.coeff 2 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (PowerSeries.coeff i) φ * (PowerSeries.coeff j) ψ) 2]
  norm_num [Finset.sum_range_succ]

private theorem coeff_two_pow (φ : PowerSeries ℤ) (h0 : constantCoeff φ = 1) (n : ℕ) :
    (φ ^ n).coeff 2 =
      (n.choose 2 : ℤ) * (φ.coeff 1) ^ 2 + (n : ℤ) * φ.coeff 2 := by
  have h0' : φ.coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact h0
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow0 : (φ ^ n).coeff 0 = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, h0, one_pow]
      rw [pow_succ, coeff_two_mul, ih, PowerSeries.coeff_one_pow, hpow0, h0', h0]
      simp only [mul_one, one_mul]
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      ring

/-! ## The numerator `jNum = E₄ ^ 3 · Δ⁻¹` -/

private theorem coeff_eisenstein4_one : eisenstein4.coeff 1 = 240 := by
  rw [eisenstein4, PowerSeries.coeff_mk, ite_eq_right (by norm_num : ¬ (1 : ℕ) = 0),
    Nat.divisors_one]
  norm_num

private theorem coeff_eisenstein4_two : eisenstein4.coeff 2 = 2160 := by
  rw [eisenstein4, PowerSeries.coeff_mk, ite_eq_right (by norm_num : ¬ (2 : ℕ) = 0)]
  decide

private theorem coeff_dedekindEtaUnit_zero : dedekindEtaUnit.coeff 0 = 1 := by
  rw [dedekindEtaUnit, PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_etaProd,
    one_pow]

private theorem coeff_dedekindEtaUnit_one : dedekindEtaUnit.coeff 1 = -24 := by
  rw [dedekindEtaUnit, PowerSeries.coeff_one_pow, coeff_etaProd_one, constantCoeff_etaProd]
  norm_num

private theorem coeff_dedekindEtaUnit_two : dedekindEtaUnit.coeff 2 = 252 := by
  rw [dedekindEtaUnit, coeff_two_pow _ constantCoeff_etaProd, coeff_etaProd_one, coeff_etaProd_two]
  decide

/-- `Δ⁻¹`'s coefficients come from `Δ * Δ⁻¹ = 1` rather than from
`PowerSeries.coeff_invOfUnit`'s recursion: multiply out and solve. -/
private theorem coeff_dedekindEtaUnitInv_zero : dedekindEtaUnitInv.coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  exact constantCoeff_dedekindEtaUnitInv

private theorem coeff_dedekindEtaUnitInv_one : dedekindEtaUnitInv.coeff 1 = 24 := by
  have h := congrArg (PowerSeries.coeff 1) dedekindEtaUnit_mul_inv
  rw [PowerSeries.coeff_one_mul, PowerSeries.coeff_one, coeff_dedekindEtaUnit_one,
    constantCoeff_dedekindEtaUnit, constantCoeff_dedekindEtaUnitInv] at h
  norm_num at h
  linarith

private theorem coeff_dedekindEtaUnitInv_two : dedekindEtaUnitInv.coeff 2 = 324 := by
  have h := congrArg (PowerSeries.coeff 2) dedekindEtaUnit_mul_inv
  rw [coeff_two_mul, PowerSeries.coeff_one, coeff_dedekindEtaUnit_zero,
    coeff_dedekindEtaUnit_one, coeff_dedekindEtaUnit_two, coeff_dedekindEtaUnitInv_zero,
    coeff_dedekindEtaUnitInv_one] at h
  norm_num at h
  linarith

private theorem coeff_eisenstein4Pow3_zero : (eisenstein4 ^ 3).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_eisenstein4, one_pow]

private theorem coeff_eisenstein4Pow3_one : (eisenstein4 ^ 3).coeff 1 = 720 := by
  rw [PowerSeries.coeff_one_pow, coeff_eisenstein4_one, constantCoeff_eisenstein4]
  norm_num

private theorem coeff_eisenstein4Pow3_two : (eisenstein4 ^ 3).coeff 2 = 179280 := by
  rw [coeff_two_pow _ constantCoeff_eisenstein4, coeff_eisenstein4_one, coeff_eisenstein4_two]
  decide

private theorem constantCoeff_eisenstein4Pow3 : constantCoeff (eisenstein4 ^ 3) = 1 := by
  rw [map_pow, constantCoeff_eisenstein4, one_pow]

private theorem coeff_jNum_one : jNum.coeff 1 = 744 := by
  rw [jNum, PowerSeries.coeff_one_mul, coeff_eisenstein4Pow3_one, constantCoeff_dedekindEtaUnitInv,
    coeff_dedekindEtaUnitInv_one, constantCoeff_eisenstein4Pow3]
  norm_num

private theorem coeff_jNum_two : jNum.coeff 2 = 196884 := by
  rw [jNum, coeff_two_mul, coeff_eisenstein4Pow3_zero, coeff_eisenstein4Pow3_one,
    coeff_eisenstein4Pow3_two, coeff_dedekindEtaUnitInv_zero, coeff_dedekindEtaUnitInv_one,
    coeff_dedekindEtaUnitInv_two]
  norm_num

/-! ## Push to `ℚ` and read off the coefficients of `jq` -/

private theorem coeff_jNumQ_one : jNumQ.coeff 1 = 744 := by
  rw [jNumQ, PowerSeries.coeff_map, coeff_jNum_one]
  norm_num

private theorem coeff_jNumQ_two : jNumQ.coeff 2 = 196884 := by
  rw [jNumQ, PowerSeries.coeff_map, coeff_jNum_two]
  norm_num

/-- The constant coefficient of the `j`-invariant, `j(q) = q⁻¹ + 744 + ⋯`:
`744`. The statement is base/004's; the proof is mathlib's pentagonal route. -/
theorem coeff_jq_zero : jq.coeff 0 = 744 := by
  rw [jq, HahnSeries.coeff_single_mul, one_mul]
  rw [show (0 : ℤ) - -1 = ((1 : ℕ) : ℤ) by norm_num]
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  exact coeff_jNumQ_one

/-- The `q`-coefficient of the `j`-invariant, `j(q) = q⁻¹ + 744 + 196884 q + ⋯`:
`196884`. The statement is base/004's; the proof is mathlib's pentagonal route. -/
theorem coeff_jq_one : jq.coeff 1 = 196884 := by
  rw [jq, HahnSeries.coeff_single_mul, one_mul]
  rw [show (1 : ℤ) - -1 = ((2 : ℕ) : ℤ) by norm_num]
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  exact coeff_jNumQ_two

end ModularCurve

end
