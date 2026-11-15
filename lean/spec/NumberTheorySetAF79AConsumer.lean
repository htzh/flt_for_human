/-
  SET-AF79A consumer: the Euler product of the Dedekind zeta function at `K = ℚ`, read at the
  rational prime `(2)` and at `s = 2`.

  **The zone.** Both rows of the order, hence both headlines of
  `FLTForHuman/NumberTheory/LSeries/DedekindZetaEuler.lean`:

  * A1 — `NumberField.ZetaEuler.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta`, the Euler
    product `∏'_𝔭 (1 - |𝔭|^{-s})⁻¹ = ζ_K(s)` over the height-one spectrum;
  * A2 — `NumberField.ZetaEuler.dedekindZeta_ne_zero_of_one_lt_re`, `ζ_K(s) ≠ 0` for `re s > 1`.

  **The data.** `K = ℚ`, so `𝓞 ℚ` is the ring of integers of the rational field
  (`Rat.ringOfIntegersEquiv` identifies it with `ℤ`, and `Module.finrank ℤ (𝓞 ℚ) = 1` is
  `RingOfIntegers.rank`), the prime is `𝔭 = (2)`, and the point is `s = 2`, with `re 2 = 2 > 1`
  discharging both hypotheses.

  **The readings.**

  * Zone 1 — `|𝔭|` at `𝔭 = (2)`: `Ideal.absNorm_span_natCast` and the rank `1` give
    `|(2)| = 2 ^ 1 = 2`, and `Ideal.isPrime_of_irreducible_absNorm` (with `Nat.prime_two`) makes
    `(2)` prime, so it really is an element of the height-one spectrum.
  * Zone 2 — the Euler factor at `s = 2`: `(1 - |𝔭|^{-2})⁻¹ = (1 - 4⁻¹)⁻¹ = 4/3`, computed with
    `Complex.cpow_neg` and `Complex.cpow_two`.
  * Zone 3 — the product, truncated to the singleton prime set `{(2)}`: the partial product is the
    single Euler factor `4/3`, and the headline's `HasProd` is exactly the statement that these
    partial products tend to `ζ_ℚ(2)`.
  * Zone 4 — A2 at `s = 2`: `dedekindZeta ℚ 2 ≠ 0`.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.NumberTheory.LSeries.DedekindZetaEuler

set_option autoImplicit false

noncomputable section

open Filter Finset Topology IsDedekindDomain NumberField NumberField.ZetaEuler

namespace AF79AConsumer

/-- The ring of integers of `ℚ` has `ℤ`-rank one: `RingOfIntegers.rank` at `K = ℚ`. -/
theorem finrank_ringOfIntegers_rat : Module.finrank ℤ (𝓞 ℚ) = 1 := by
  rw [RingOfIntegers.rank]
  simp

/-- Zone 1: `|𝔭|` at the rational prime `𝔭 = (2)` is `2`. -/
theorem absNorm_span_two : Ideal.absNorm (Ideal.span {((2 : ℕ) : 𝓞 ℚ)}) = 2 := by
  rw [Ideal.absNorm_span_natCast, finrank_ringOfIntegers_rat, pow_one]

/-- Zone 1: `(2)` is a nonzero prime ideal of `𝓞 ℚ`, hence a point of the height-one spectrum. The
ideal norm being the prime `2` is what makes it irreducible. -/
theorem prime_span_two : Prime (Ideal.span {((2 : ℕ) : 𝓞 ℚ)}) := by
  refine Ideal.prime_of_isPrime ?_ (Ideal.isPrime_of_irreducible_absNorm ?_)
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  · rw [absNorm_span_two]
    exact Nat.prime_two

/-- The rational prime `(2)` as a height-one prime of `𝓞 ℚ`. -/
def v2 : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.ofPrime prime_span_two

/-- Zone 1, read on the spectrum: the prime's ideal norm is `2`. -/
theorem absNorm_v2 : Ideal.absNorm v2.asIdeal = 2 := absNorm_span_two

/-- Zone 2: the Euler factor `1 - |𝔭|^{-s}` at `𝔭 = (2)` and `s = 2`, inverted, is `4/3`. -/
theorem eulerFactor_two :
    (1 - ((Ideal.absNorm v2.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹ = (4 / 3 : ℂ) := by
  rw [absNorm_v2, Complex.cpow_neg, Complex.cpow_two]
  norm_num

/-- Zone 3: A1 at `K = ℚ` and `s = 2` — the Euler product over the height-one spectrum of `ℚ`,
converging to `ζ_ℚ(2)`. -/
theorem hasProd_euler_rat_two :
    HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) =>
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹) (dedekindZeta ℚ 2) :=
  hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta ℚ 2 (by norm_num)

/-- Zone 3, truncated: the partial product over the singleton prime set `{(2)}` is the single
Euler factor `4/3`. -/
theorem prod_singleton_v2 :
    ∏ v ∈ ({v2} : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹ = (4 / 3 : ℂ) := by
  rw [Finset.prod_singleton, eulerFactor_two]

/-- Zone 3, the limit form of the headline: the truncated Euler products tend to `ζ_ℚ(2)`. -/
theorem tendsto_prod_rat_two :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 ℚ)) =>
      ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹)
      atTop (𝓝 (dedekindZeta ℚ 2)) :=
  hasProd_euler_rat_two

/-- Zone 4: A2 at `s = 2`, where `re 2 = 2 > 1`. -/
theorem dedekindZeta_rat_two_ne_zero : dedekindZeta ℚ 2 ≠ 0 :=
  dedekindZeta_ne_zero_of_one_lt_re ℚ (by norm_num)

end AF79AConsumer
