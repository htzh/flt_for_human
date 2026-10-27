/-
Membership in the integral closure at a place, from orders on the fibre.

Given a finite separable extension `F ⊆ F'` and a place `v` of `F`, an element `f` of `F'`
whose order is non-negative at every place of the fibre of `v` lies in the integral closure
`Place.integralClosureAt F' v` of `v`'s valuation subring.  The proof is the ideal-norm
count: the fibre centres of `v` are the prime factors of `Ideal.span {c}` with the exponents
given by the orders, and non-negativity puts `f` in every one of them.

This is the pin's `Place.exists_integralClosureAt_of_ord_fiber_nonneg`; it lives above the
norm block because its proof counts normalised factors (`Place.count_normalizedFactors_span_singleton`)
and the fibre dictionary, neither of which is available in the `Defs` layer below.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence
import FLTForHuman.AlgebraicCurve.Defs.PlaceDictionary

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open Place UniqueFactorizationMonoid IsDedekindDomain

theorem Place.exists_integralClosureAt_of_ord_fiber_nonneg {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F}
    [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0)
    (hord : ∀ w ∈ v.fiber F', 0 ≤ w.ord f) :
    ∃ c : Place.integralClosureAt F' v, algebraMap (Place.integralClosureAt F' v) F' c = f := by
  classical

  obtain ⟨⟨c₀, s₀⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt F' v)) f
  have hs0 : (s₀ : integralClosureAt F' v) ≠ 0 := nonZeroDivisors.coe_ne_zero s₀
  have hsF : algebraMap (integralClosureAt F' v) F' (s₀ : integralClosureAt F' v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hs0
  have hcF : algebraMap (integralClosureAt F' v) F' c₀ ≠ 0 := by
    rw [← hcs]; exact mul_ne_zero hf hsF
  have hc0 : c₀ ≠ 0 := fun h => hcF (by rw [h, map_zero])

  have hdom : ∀ (w : Place K F') (hw : w.restrict F = v),
      w.ord (algebraMap (integralClosureAt F' v) F' (s₀ : integralClosureAt F' v))
        ≤ w.ord (algebraMap (integralClosureAt F' v) F' c₀) := by
    intro w hw
    have h1 : w.ord (algebraMap (integralClosureAt F' v) F' c₀)
        = w.ord f + w.ord (algebraMap (integralClosureAt F' v) F' (s₀ :
            integralClosureAt F' v)) := by
      rw [← hcs]; exact w.ord_mul hf hsF
    have h2 := hord w (mem_fiber.mpr hw)
    omega

  have hle : Ideal.span {c₀} ≤ Ideal.span {(s₀ : integralClosureAt F' v)} := by
    have hspan_c : (Ideal.span {c₀} : Ideal (integralClosureAt F' v)) ≠ ⊥ := fun h =>
      hc0 (Ideal.span_singleton_eq_bot.mp h)
    have hspan_s : (Ideal.span {(s₀ : integralClosureAt F' v)} :
        Ideal (integralClosureAt F' v)) ≠ ⊥ := fun h => hs0 (Ideal.span_singleton_eq_bot.mp h)
    rw [← Ideal.dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors hspan_s hspan_c,
      Multiset.le_iff_count]
    intro P
    by_cases hP : P ∈ normalizedFactors
      (Ideal.span {(s₀ : integralClosureAt F' v)} : Ideal (integralClosureAt F' v))
    ·
      have hPprime : Prime P := prime_of_normalized_factor P hP
      have hPisPrime : P.IsPrime := Ideal.isPrime_of_prime hPprime
      have hres := restrict_placeOfPrime
        (⟨P, hPisPrime, hPprime.ne_zero⟩ : HeightOneSpectrum (integralClosureAt F' v))
      have hPeq : (fiberCenter F' v hres).asIdeal = P := congrArg HeightOneSpectrum.asIdeal
        (fiberCenter_placeOfPrime
          (⟨P, hPisPrime, hPprime.ne_zero⟩ : HeightOneSpectrum (integralClosureAt F' v)))
      rw [← hPeq, count_normalizedFactors_span_singleton hres hs0,
        count_normalizedFactors_span_singleton hres hc0]
      exact Int.toNat_le_toNat (hdom _ hres)
    · rw [Multiset.count_eq_zero_of_notMem hP]
      exact Nat.zero_le _

  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hle (Ideal.mem_span_singleton_self c₀))
  refine ⟨d, ?_⟩
  have hmapped := congrArg (algebraMap (integralClosureAt F' v) F') hd
  rw [map_mul] at hmapped
  refine mul_left_cancel₀ hsF ?_
  rw [← hmapped, ← hcs]
  ring

end AlgebraicCurve
