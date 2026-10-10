/-
  Layer 0a — the explicit `q`-expansion of the `j`-invariant.

  `jq` is assembled as `E₄ ^ 3 / Δ`, where `Δ` is written as a unit times its
  inverse so that only its constant term `1` is needed. The module then records
  the shape that matters for the field theory: `jq = q⁻¹ + ⋯`, i.e. a simple
  pole at `q = 0` with leading coefficient `1`. Finally it defines `jqN` and the
  evaluation `Polynomial ℤ → LaurentSeries ℚ` at `jq`.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_X0.lean` lines 111–212.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean

  The regular coefficients of `jq` (`744`, `196884`) are *not* available here:
  `etaProd` is a topological product, so `jNum` is not an evaluable expression.
  See `spec/ModularCurveConsumer.lean` Zone C (they are proved in
  `FLTForHuman/ModularCurve/JqCoefficients.lean`).

  This module also carries the part of the cone's **outbound interface** stated
  over `jq`: `aeval_jq_eq_zero` and `transcendental_jq`, transcribed verbatim from
  their `Theorems/Thm_ModularCurve_*` wrappers in the pin and public.

  The `dedekindPsi` block used to sit here too — `dedekindPsi_prime`,
  `dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime`, and the two out-of-cone ψ
  facts `dedekindPsi_mul_prime` and `dedekindPsi_pos` (indegrees 72, 33, 46, 20, 76;
  see `logs/ffg-port.md` §2e). It moved on 2026-10-09 to
  `FLTForHuman/NumberTheory/DedekindPsi.lean`: `ψ` is generic number theory with no
  `jq` content, and its `ArithmeticFunction` view was `private` here, which forced
  `Gamma0Index.lean` to re-derive it. The pin's `ModularCurve` spelling of those
  names is kept by `FLTForHuman/ModularCurve/Defs/DedekindPsi.lean`.

  Names are FLT's verbatim; `PowerSeries`, `HahnSeries`, `Finset` are mathlib's.
  Assumes `qExpand` and its coefficient lemmas from `FLTForHuman.ModularCurve.Defs.Laurent`.
-/
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.IntervalCases
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

/-! ## `jq` is transcendental

`jq` has a simple pole at `q = 0` with residue `1`; that alone forces it to be
transcendental over `ℚ`, since a nonzero polynomial relation would make a
leading coefficient vanish at the pole. FLT's `transcendental_jq` (indeg 56) is
part of the cone's outbound interface. -/

/-- Triangularity of `aeval jq`: for `m ≥ P.natDegree`, the `q ^ (-m)` coefficient
of `P(jq)` is the `m`-th coefficient of `P`. This is the shared form of the
`q`-expansion triangularity that the cone's integrality and pole-bound topics
(`PhiGenDescends.intCoeffs`, `aeval_jq_intCoeffs_descent`, the 328-block) all use;
FLT repeats it privately in nine of its `S_` files. -/
theorem coeff_aeval_jq_neg (P : Polynomial ℚ) {m : ℕ} (hm : P.natDegree ≤ m) :
    (Polynomial.aeval jq P).coeff (-(m : ℤ)) = P.coeff m := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
    Finset.sum_eq_single m]
  · rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_self,
      mul_one]
  · intro i hi hin
    have hilt : i < m :=
      lt_of_le_of_ne (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hm) hin
    rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
      coeff_jq_pow_of_lt (by omega), mul_zero]
  · intro hm'
    rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simp only [Finset.mem_range, not_lt] at hm'; omega),
      zero_mul]

/-- There is no nonzero rational polynomial relation satisfied by `jq`: the
`q ^ (-natDegree)` coefficient of `p(jq)` is the leading coefficient of `p`. -/
theorem aeval_jq_eq_zero {p : Polynomial ℚ} (hp : Polynomial.aeval jq p = 0) : p = 0 := by
  by_contra hp0
  have hcoeff := coeff_aeval_jq_neg p le_rfl
  rw [hp] at hcoeff
  simp only [HahnSeries.coeff_zero] at hcoeff
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hcoeff.symm)

/-- `jq` is transcendental over `ℚ`. -/
theorem transcendental_jq : Transcendental ℚ jq :=
  transcendental_iff.mpr fun _ hp => aeval_jq_eq_zero hp

/-- `j(q ^ N)`, the `q ^ N`-substitution of `jq`. -/
def jqN (N : ℕ) [NeZero N] : LaurentSeries ℚ := qExpand ℚ N jq

@[simp]
theorem jqN_one : jqN 1 = jq := qExpand_one_apply jq

/-- `jqN` depends only on the value of `N`: equal levels give equal series. The
pin repeats this `private` in the FFG spine and in
`S_ModularCurve_jqN_prime_not_mem_full.lean`; T14 promotes it here. -/
theorem jqN_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) : jqN n = jqN m := by
  subst h; rfl

section NamedInputs

/-- Evaluation of an integer polynomial at `jq`, as a ring hom into the Laurent
series over `ℚ`. -/
def evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) jq).toRingHom

@[simp]
theorem evalAtJ_X : evalAtJ Polynomial.X = jq := by
  simp [evalAtJ]

/-- The bridge from the integer evaluation `evalAtJ` to mathlib's `ℚ`-algebra
evaluation `aeval jq` after the coefficient map `ℤ → ℚ`. FLT repeats it privately
in the 328 block, the assembly file and the 895 block (`evalAtJ_eq_aeval_map_rat`);
the port writes it once here, beside `evalAtJ`, and T11/T12 import it. -/
theorem evalAtJ_eq_aeval_map (Q : Polynomial ℤ) :
    evalAtJ Q = Polynomial.aeval jq (Q.map (Int.castRingHom ℚ)) := by
  have hcomp : (algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ)
      = algebraMap ℤ (LaurentSeries ℚ) := Subsingleton.elim _ _
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  rfl

end NamedInputs

end ModularCurve

end
