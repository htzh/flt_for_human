/-
  Layer 0a — the explicit `q`-expansion of the `j`-invariant.

  `jq` is assembled as `E₄ ^ 3 / Δ`, where `Δ` is written as a unit times its
  inverse so that only its constant term `1` is needed. The module then records
  the shape that matters for the field theory: `jq = q⁻¹ + ⋯`, i.e. a simple
  pole at `q = 0` with leading coefficient `1`. Finally it defines `jqN`, the
  Dedekind psi function, and evaluation `Polynomial ℤ → LaurentSeries ℚ` at `jq`.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_X0.lean` lines 111–212.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean

  The regular coefficients of `jq` (`744`, `196884`) are *not* available here:
  `etaProd` is a topological product, so `jNum` is not an evaluable expression.
  See `spec/ModularCurveConsumer.lean` Zone C.

  Names are FLT's verbatim; `PowerSeries`, `HahnSeries`, `Finset` are mathlib's.
  Assumes `qExpand` and its coefficient lemmas from `FLTForHuman.ModularCurve.Defs.Laurent`.
-/
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree
import FLTForHuman.ModularCurve.Defs.Laurent

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

section JFunction

/-- The weight-`4` Eisenstein series as a `q`-expansion with integer
coefficients: `1 + 240 ∑_{d ∣ n} d ^ 3` in degree `n`. -/
def eisenstein4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3

@[simp]
theorem constantCoeff_eisenstein4 : PowerSeries.constantCoeff eisenstein4 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [eisenstein4]

/-- The eta product `∏_{n ≥ 1} (1 - q ^ n)`, as a topological product. -/
def etaProd : PowerSeries ℤ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))

theorem constantCoeff_etaProd : PowerSeries.constantCoeff etaProd = 1 := by
  rw [etaProd]
  simp [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod _
    (PowerSeries.WithPiTopology.continuous_constantCoeff ℤ)]

/-- The modular discriminant `Δ = η ^ 24`, as a unit of the power series ring. -/
def dedekindEtaUnit : PowerSeries ℤ := etaProd ^ 24

theorem constantCoeff_dedekindEtaUnit : PowerSeries.constantCoeff dedekindEtaUnit = 1 := by
  rw [dedekindEtaUnit, map_pow, constantCoeff_etaProd, one_pow]

/-- The inverse of `Δ`, via `invOfUnit` with constant term `1`. -/
def dedekindEtaUnitInv : PowerSeries ℤ := dedekindEtaUnit.invOfUnit 1

theorem dedekindEtaUnit_mul_inv : dedekindEtaUnit * dedekindEtaUnitInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_dedekindEtaUnit]; rfl)

theorem constantCoeff_dedekindEtaUnitInv :
    PowerSeries.constantCoeff dedekindEtaUnitInv = 1 := by
  have h := congrArg (PowerSeries.constantCoeff (R := ℤ)) dedekindEtaUnit_mul_inv
  rwa [map_mul, constantCoeff_dedekindEtaUnit, one_mul, map_one] at h

/-- The numerator of `j`: `E₄ ^ 3 / Δ`, with `Δ` normalised to constant term
`1`. -/
def jNum : PowerSeries ℤ := eisenstein4 ^ 3 * dedekindEtaUnitInv

@[simp]
theorem constantCoeff_jNum : PowerSeries.constantCoeff jNum = 1 := by
  rw [jNum, map_mul, map_pow, constantCoeff_eisenstein4, constantCoeff_dedekindEtaUnitInv,
    one_pow, one_mul]

/-- `jNum` with coefficients pushed to `ℚ`. -/
def jNumQ : PowerSeries ℚ := jNum.map (Int.castRingHom ℚ)

@[simp]
theorem constantCoeff_jNumQ : PowerSeries.constantCoeff jNumQ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, jNumQ, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum]
  simp

/-- The `j`-invariant as a Laurent series in `q`: `q⁻¹ · jNum(q)`, i.e.
`j(q) = q⁻¹ + ⋯`. -/
def jq : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ

theorem ofPowerSeries_coeff_of_neg {R : Type*} [Semiring R] (f : PowerSeries R) {k : ℤ}
    (hk : k < 0) : (HahnSeries.ofPowerSeries ℤ R f).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨m, rfl⟩
  exact absurd hk (not_lt.mpr (Int.natCast_nonneg m))

/-- The `n`-th power of `jq` is `q ^ (-n)` times `jNumQ ^ n`: the pole is
exactly `q ^ (-n)`. -/
theorem jq_pow (n : ℕ) :
    jq ^ n = HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℚ (jNumQ ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jq, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

theorem coeff_jq_pow_self (n : ℕ) : (jq ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNumQ, one_pow]

theorem coeff_jq_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : (jq ^ n).coeff m = 0 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

/-- The pole of `jq` at `q = 0` is simple with residue `1`. -/
@[simp]
theorem coeff_jq_neg_one : jq.coeff (-1 : ℤ) = 1 := by
  have h := coeff_jq_pow_self 1
  simpa using h

theorem coeff_jq_of_lt {k : ℤ} (hk : k < -1) : jq.coeff k = 0 := by
  have h := coeff_jq_pow_of_lt (n := 1) (m := k) (by simpa using hk)
  simpa using h

theorem jq_ne_zero : jq ≠ 0 := fun h => by simpa [h] using coeff_jq_neg_one

end JFunction

/-- `j(q ^ N)`, the `q ^ N`-substitution of `jq`. -/
def jqN (N : ℕ) [NeZero N] : LaurentSeries ℚ := qExpand ℚ N jq

@[simp]
theorem jqN_one : jqN 1 = jq := qExpand_one_apply jq

section NamedInputs

/-- The Dedekind psi function: `ψ(N) = ∑_{d ∣ N, d squarefree} N / d`, which
equals `N ∏_{p ∣ N} (1 + 1/p)`. -/
def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d

@[simp]
theorem dedekindPsi_one : dedekindPsi 1 = 1 := by
  rw [dedekindPsi, Nat.divisors_one, Finset.filter_singleton, ite_eq_left squarefree_one]
  simp

/-- Evaluation of an integer polynomial at `jq`, as a ring hom into the Laurent
series over `ℚ`. -/
def evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) jq).toRingHom

@[simp]
theorem evalAtJ_X : evalAtJ Polynomial.X = jq := by
  simp [evalAtJ]

end NamedInputs

end ModularCurve

end
