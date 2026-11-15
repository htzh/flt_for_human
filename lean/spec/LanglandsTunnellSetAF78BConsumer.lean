/-
  Cross-module wire test for the real measure of a valued ball (`AF78B`).

  A `spec/` probe, not a library module. The whole zone is at the base field `K = ℚ` and the
  concrete place `v = 2`, where the row's abstract objects have concrete shapes:

  * `𝓞 ℚ = ℤ`, and the height-one prime `(2)` of `𝓞 ℚ` is the place `vTwo` below, its primality
    transported from `Int.prime_two` along the ring equivalence `𝓞 ℚ ≃+* ℤ`
    (`Rat.ringOfIntegersEquiv`);
  * `vTwo.adicCompletion ℚ` is `ℚ₂`, carrying the chosen additive Haar measure
    `Measure.addHaar` (its `BorelSpace` structure supplied locally, as the row's statement
    assumes both it and `IsAddHaarMeasure`);
  * `WithZero.exp (k : ℤ)` is the value-group element `k` of the discrete valuation, so the ball
    `{x | Valued.v x ≤ WithZero.exp k}` is the set of points of valuation at least `-k`;
    at `k = 0` it is exactly the completed integer ring
    (`HeightOneSpectrum.mem_adicCompletionIntegers`).

  Every zone is a real composition — no `#check` — so deleting the module (or leaving a hole in
  it) breaks this file:

  * `vTwo` is the row's place `v = 2`, built from the ring of integers' own data;
  * `ball_zero_eq_adicCompletionIntegers` reads the ball at `k = 0` as the integer ring;
  * `measureReal_ball_zero` is the row at `k = 0`: both sides are the same real number
    `μ.real 𝓞̂`, since `|𝔭|⁰ = 1`;
  * `measureReal_ball_one` is the row at `k = 1`, where the right side keeps the factor
    `|𝔭| = Ideal.absNorm (2)`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF78BConsumer.lean` and never enters the build.
-/
import FLTForHuman.LanglandsTunnell.TateLocal.BallVolume

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum Topology
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnellSetAF78BConsumer

/-! ### The place `v = 2` of `ℚ` -/

/-- The ideal `(2) ⊆ 𝓞 ℚ` is prime: it is the image of the prime `(2) ⊆ ℤ` under the ring
equivalence `𝓞 ℚ ≃+* ℤ`. -/
theorem span_two_isPrime : (Ideal.span ({(2 : 𝓞 ℚ)} : Set (𝓞 ℚ))).IsPrime := by
  have htwo : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (p := (2 : ℤ)) (by norm_num)).mpr Int.prime_two
  have hmap : Ideal.map (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ)
        (Ideal.span ({(2 : ℤ)} : Set ℤ))
      = Ideal.span ({(2 : 𝓞 ℚ)} : Set (𝓞 ℚ)) := by
    rw [Ideal.map_span, Set.image_singleton]
    norm_num
  rw [← hmap]
  refine Ideal.map_isPrime_of_surjective (I := Ideal.span ({(2 : ℤ)} : Set ℤ))
    Rat.ringOfIntegersEquiv.symm.surjective ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).mp Rat.ringOfIntegersEquiv.symm.injective]
  exact bot_le

/-- `(2) ≠ 0` in `𝓞 ℚ`: the rational prime is not zero. -/
theorem span_two_ne_bot : Ideal.span ({(2 : 𝓞 ℚ)} : Set (𝓞 ℚ)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  norm_num

/-- The place `v = 2` of `ℚ`: the height-one prime `(2)` of `𝓞 ℚ`. -/
def vTwo : HeightOneSpectrum (𝓞 ℚ) :=
  ⟨Ideal.span ({(2 : 𝓞 ℚ)} : Set (𝓞 ℚ)), span_two_isPrime, span_two_ne_bot⟩

/-! ### `ℚ₂` as a measure space with a Haar measure -/

instance : MeasurableSpace (vTwo.adicCompletion ℚ) := borel _

instance : BorelSpace (vTwo.adicCompletion ℚ) := ⟨rfl⟩

/-- The chosen additive Haar measure on `ℚ₂`.  An `abbrev`, so that instance search sees the
Haar measure's `IsAddHaarMeasure` instance through it. -/
abbrev μTwo : Measure (vTwo.adicCompletion ℚ) := Measure.addHaar

instance : μTwo.IsAddHaarMeasure := inferInstance

/-! ### The row at `k = 0` and at `k = 1` -/

/-- At `k = 0` the ball is the completed integer ring: `Valued.v x ≤ 1` is membership. -/
theorem ball_zero_eq_adicCompletionIntegers :
    {x : vTwo.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (0 : ℤ)}
      = (vTwo.adicCompletionIntegers ℚ : Set (vTwo.adicCompletion ℚ)) := by
  ext x
  simp only [Set.mem_ofPred_eq, WithZero.exp_zero]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) (v := vTwo) (x := x)).symm

/-- The row at `k = 0`: the two sides are the same real number, since `|𝔭|⁰ = 1`. -/
theorem measureReal_ball_zero :
    μTwo.real {x : vTwo.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (0 : ℤ)}
      = (Ideal.absNorm vTwo.asIdeal : ℝ) ^ (0 : ℤ) *
          μTwo.real (vTwo.adicCompletionIntegers ℚ : Set (vTwo.adicCompletion ℚ)) :=
  LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp ℚ vTwo μTwo 0

/-- Consequently both sides of the row at `k = 0` are `μ.real 𝓞̂`, the measure of the integer ring
read by `ball_zero_eq_adicCompletionIntegers`. -/
theorem measureReal_ball_zero_eq_integers :
    μTwo.real {x : vTwo.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (0 : ℤ)}
      = μTwo.real (vTwo.adicCompletionIntegers ℚ : Set (vTwo.adicCompletion ℚ)) := by
  rw [measureReal_ball_zero, zpow_zero, one_mul]

/-- The row at `k = 1`: the right side keeps the single factor `|𝔭| = Ideal.absNorm (2)`. -/
theorem measureReal_ball_one :
    μTwo.real {x : vTwo.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}
      = (Ideal.absNorm vTwo.asIdeal : ℝ) *
          μTwo.real (vTwo.adicCompletionIntegers ℚ : Set (vTwo.adicCompletion ℚ)) := by
  rw [LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp ℚ vTwo μTwo 1, zpow_one]

end LanglandsTunnellSetAF78BConsumer
