/-
  The twisted power sum over a residue class of `ℤ`: for `2 ≤ k` and `a : ZMod N`,

      `∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹
         = -(2 π i)^k / (k ! N) * ∑ r : ZMod N, stdAddChar (-(r a)) * B_k (r.val / N)`,

  with `B_k` the periodic Bernoulli function `bernoulliFun`.

  The port of the pin leaf `ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun`
  (`P2M/Sol/S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun.lean` — 101 pin lines;
  the pin's `S_` development is `namespace ZMod
namespace BernoulliTsum`, kept here under the pin's own
  namespace and its short names untouched), together with the statement of its
  `Theorems/` wrapper `Theorems/Thm_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun.lean`.

  It is a faithful transcription: no statement is weakened, no route is generalised,
  and the pin's proofs are carried verbatim (`spec/check_port.py` diffs every public
  declaration below against the two files named here).

  The mathematics is the Fourier expansion of the periodic Bernoulli function: the
  residue-class indicator is a root-of-unity filter
  (`indicator_eq_sum`, from primitivity of `ZMod.stdAddChar`), which turns the
  restricted sum into the full `ℤ`-sum `∑ d, stdAddChar (r d) / d ^ k`; that one is
  mathlib's `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` in disguise, and
  `bernoulliFun k (r.val / N)` is the value of the periodised Bernoulli polynomial at
  `r d / N ≡ r.val / N`.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  spec-pin: Theorems/Thm_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun.lean
  spec-pin: P2M/Sol/S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun.lean
-/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false

open Real Complex
open scoped Nat

namespace ZMod
namespace BernoulliTsum

variable {N : ℕ} [NeZero N] {k : ℕ}

/-- The twisted power sum `∑ d, stdAddChar (r d) / d^k` converges to
`-(2 π i)^k / k ! * B_k (r.val / N)`. -/
lemma hasSum_twisted (hk : 2 ≤ k) (r : ZMod N) :
    HasSum (fun d : ℤ => ZMod.stdAddChar (r * (d : ZMod N)) * ((d : ℂ) ^ k)⁻¹)
      (-(2 * π * I) ^ k / k ! * (bernoulliFun k ((r.val : ℝ) / N) : ℂ)) := by
  have hx : ((r.val : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by exact_mod_cast NeZero.pos N)]
    exact_mod_cast (ZMod.val_lt r).le
  have h := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx
  refine h.congr_fun fun d => ?_
  rw [fourier_coe_apply, one_div, mul_comm]
  congr 1
  have : (r * (d : ZMod N) : ZMod N) = (((r.val : ℤ) * d : ℤ) : ZMod N) := by
    simp
  rw [this, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- The power sum `∑ d : ℤ, 1 / d^k` converges for `2 ≤ k`. -/
lemma summable_inv_pow (hk : 2 ≤ k) : Summable fun d : ℤ => ((d : ℂ) ^ k)⁻¹ := by
  have : Summable fun d : ℤ => (1 : ℝ) / (d : ℝ) ^ k := Real.summable_one_div_int_pow.mpr (by omega)
  have := (this.map Complex.ofRealCLM Complex.ofRealCLM.continuous)
  refine this.congr fun d => ?_
  simp

/-- `ZMod.stdAddChar` has unit norm. -/
lemma norm_stdAddChar (x : ZMod N) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- The twisted power sum is summable. -/
lemma summable_twisted (hk : 2 ≤ k) (r : ZMod N) :
    Summable fun d : ℤ => ZMod.stdAddChar (r * (d : ZMod N)) * ((d : ℂ) ^ k)⁻¹ := by
  refine Summable.of_norm_bounded (g := fun d : ℤ => ‖((d : ℂ) ^ k)⁻¹‖) (summable_inv_pow hk).norm ?_
  intro d
  rw [norm_mul, norm_stdAddChar, one_mul]

/-- The residue-class indicator as a root-of-unity filter: for `a b : ZMod N`,
`[b = a] = N⁻¹ ∑ r, stdAddChar (-(r a)) * stdAddChar (r b)`. -/
lemma indicator_eq_sum (a b : ZMod N) :
    (if b = a then (1 : ℂ) else 0) =
      (N : ℂ)⁻¹ * ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * ZMod.stdAddChar (r * b) := by
  have h := AddChar.sum_mulShift (b - a) (ZMod.isPrimitive_stdAddChar N)
  simp only [ZMod.card, sub_eq_zero] at h
  have h2 : ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * ZMod.stdAddChar (r * b) =
      ∑ r : ZMod N, ZMod.stdAddChar (r * (b - a)) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [h2, h]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  split_ifs <;> simp [hN]

/-- The `k`-th power sum over the residue class `a mod N`, as a finite sum of
periodised Bernoulli values. -/
private theorem main (hk : 2 ≤ k) (a : ZMod N) :
    ∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹ =
      -(2 * π * I) ^ k / (k ! * N) *
        ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * (bernoulliFun k ((r.val : ℝ) / N) : ℂ) := by

  have h1 : ∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹ =
      ∑' d : ℤ, (if (d : ZMod N) = a then (1 : ℂ) else 0) * ((d : ℂ) ^ k)⁻¹ := by
    rw [show (∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹) =
        ∑' d : ({d : ℤ | (d : ZMod N) = a} : Set ℤ), ((d : ℂ) ^ k)⁻¹ from rfl,
      tsum_subtype {d : ℤ | (d : ZMod N) = a} (fun d : ℤ => ((d : ℂ) ^ k)⁻¹)]
    refine tsum_congr fun d => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  rw [h1]

  have h2 : ∀ d : ℤ, (if (d : ZMod N) = a then (1 : ℂ) else 0) * ((d : ℂ) ^ k)⁻¹ =
      ∑ r : ZMod N, ((N : ℂ)⁻¹ * ZMod.stdAddChar (-(r * a))) *
        (ZMod.stdAddChar (r * (d : ZMod N)) * ((d : ℂ) ^ k)⁻¹) := by
    intro d
    rw [indicator_eq_sum a, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp_rw [h2]
  rw [Summable.tsum_finsetSum (fun r _ => (summable_twisted hk r).mul_left _)]
  simp_rw [tsum_mul_left]

  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [(hasSum_twisted hk r).tsum_eq]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

end BernoulliTsum
end ZMod

theorem ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun (N : ℕ) [NeZero N] (k : ℕ) (hk : 2 ≤ k)
    (a : ZMod N) :
    ∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹ =
      -(2 * π * I) ^ k / (k ! * N) *
        ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * (bernoulliFun k ((r.val : ℝ) / N) : ℂ) :=
  ZMod.BernoulliTsum.main hk a
