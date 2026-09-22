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
  See `spec/ModularCurveConsumer.lean` Zone C (they are proved in
  `FLTForHuman/ModularCurve/JqCoefficients.lean`).

  This module also carries the part of the cone's **outbound interface** stated
  over `jq` and `dedekindPsi`: `dedekindPsi_prime`, `dedekindPsi_prime_pow`,
  `dedekindPsi_mul_of_coprime` (FLT `S_ModularCurve_dedekindPsi_*`, whose ψ
  section is ~50 lines and whose remaining resultant development is off-path),
  `aeval_jq_eq_zero` and `transcendental_jq`. They are transcribed verbatim from
  their `Theorems/Thm_ModularCurve_*` wrappers in the pin and are public; the
  indegrees in FLT's graph are 72, 33, 46, 2 and 56. See
  `logs/ffg-port.md` §2e.

  Names are FLT's verbatim; `PowerSeries`, `HahnSeries`, `Finset`,
  `ArithmeticFunction` are mathlib's.
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

section NamedInputs

/-- The Dedekind psi function: `ψ(N) = ∑_{d ∣ N, d squarefree} N / d`, which
equals `N ∏_{p ∣ N} (1 + 1/p)`. -/
def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d

@[simp]
theorem dedekindPsi_one : dedekindPsi 1 = 1 := by
  rw [dedekindPsi, Nat.divisors_one, Finset.filter_singleton, ite_eq_left squarefree_one]
  simp

/-- `ψ(p) = p + 1` for a prime `p`. Part of the cone's outbound interface
(indeg 72). -/
theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by
  rw [dedekindPsi, Finset.sum_filter, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp [hp.squarefree, Nat.div_self hp.pos]

/-- `ψ(p ^ k) = p ^ k + p ^ (k - 1)` for a prime `p` and `k ≠ 0`. Part of the
cone's outbound interface (indeg 33). -/
theorem dedekindPsi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    dedekindPsi (p ^ k) = p ^ k + p ^ (k - 1) := by
  have hsqfree : ∀ j, Squarefree (p ^ j) ↔ j ≤ 1 := fun j => by
    constructor
    · intro hsq
      by_contra hj
      exact hp.one_lt.ne'
        (Nat.isUnit_iff.mp (hsq p (by rw [← pow_two]; exact pow_dvd_pow p (by omega))))
    · intro hj
      interval_cases j
      · simp
      · simpa using hp.prime.squarefree
  have hfilter : {d ∈ (p ^ k).divisors | Squarefree d} = {1, p} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hsq⟩
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have : j ≤ 1 := (hsqfree j).mp hsq
      interval_cases j
      · exact Or.inl (pow_zero p)
      · exact Or.inr (pow_one p)
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, pow_ne_zero _ hp.pos.ne'⟩, squarefree_one⟩
      · exact ⟨⟨dvd_pow_self _ hk, pow_ne_zero _ hp.pos.ne'⟩, hp.prime.squarefree⟩
  have hdiv : p ^ k / p = p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ hp.pos
  rw [dedekindPsi, hfilter, Finset.sum_pair hp.one_lt.ne, Nat.div_one, hdiv]

/-- The squarefree indicator as an arithmetic function. -/
private def squarefreeIndicator : ArithmeticFunction ℕ :=
  ⟨fun n => if Squarefree n then 1 else 0, by simp [not_squarefree_zero]⟩

@[simp]
private theorem squarefreeIndicator_apply {n : ℕ} :
    squarefreeIndicator n = if Squarefree n then 1 else 0 :=
  rfl

private theorem isMultiplicative_squarefreeIndicator :
    squarefreeIndicator.IsMultiplicative := by
  refine ⟨by simp, fun {m n} h => ?_⟩
  simp only [squarefreeIndicator_apply, Nat.squarefree_mul h]
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;> simp [hm, hn]

private theorem dedekindPsi_eq_mul_apply (N : ℕ) :
    dedekindPsi N = (squarefreeIndicator * ArithmeticFunction.id) N :=
  calc dedekindPsi N
      = ∑ d ∈ N.divisors, squarefreeIndicator d * ArithmeticFunction.id (N / d) := by
        rw [dedekindPsi, Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        by_cases hd : Squarefree d <;> simp [hd]
    _ = ∑ x ∈ N.divisorsAntidiagonal, squarefreeIndicator x.1 * ArithmeticFunction.id x.2 :=
        (Nat.sum_divisorsAntidiagonal fun d e =>
          squarefreeIndicator d * ArithmeticFunction.id e).symm
    _ = (squarefreeIndicator * ArithmeticFunction.id) N := ArithmeticFunction.mul_apply.symm

private theorem isMultiplicative_squarefreeIndicator_mul_id :
    (squarefreeIndicator * ArithmeticFunction.id).IsMultiplicative :=
  isMultiplicative_squarefreeIndicator.mul ArithmeticFunction.isMultiplicative_id

/-- `ψ` is multiplicative: `ψ(mn) = ψ(m)ψ(n)` for coprime `m`, `n`. Part of the
cone's outbound interface (indeg 46). -/
theorem dedekindPsi_mul_of_coprime (M N : ℕ) (h : Nat.Coprime M N) :
    dedekindPsi (M * N) = dedekindPsi M * dedekindPsi N := by
  simp only [dedekindPsi_eq_mul_apply]
  exact isMultiplicative_squarefreeIndicator_mul_id.map_mul_of_coprime h

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
