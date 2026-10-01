/-
The `InlineSpecific` uniformizer slice at a discrete place: `completionIdeal`, the
unit-ball description of its powers, and the uniformizer facts for the completed
integers, after FLT's
`Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean` (pin 104,
299–551)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean>).

Sets 3.3a/3.3c/3.4 transcribed these `private` into `Tate/CommFinite.lean`,
`Tate/Agreement.lean` and `Tate/CompletionTraceSum.lean` because the pin module was
not ported. The P3.2 refactor round (R8) hoists the union here once, publicly, at the
pin's names and with the pin's section/`variable` structure (so the checker diffs the
statements verbatim); the three Tate modules import this file and their `private`
copies are deleted. The pin's `DVR`/`Ring.DimensionLEOne`/`IsPrincipalIdealRing`
instances in the same slice are not needed and are not transcribed, and the v4.34
`Valued` adapter `isUnit_adicCompletionIntegers_of_valued_eq_one` stays `private`.
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceCompletion
import Mathlib.Algebra.Group.Int.TypeTags

set_option autoImplicit false

noncomputable section

open IsLocalRing IsDedekindDomain.HeightOneSpectrum
open WithZero Multiplicative

namespace ValuationSubring

theorem valued_eq_one_of_isUnit {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : IsUnit x) : Valued.v x.val = 1 := by
  simpa only [ValuationSubring.algebraMap_apply] using
    Valuation.Integers.one_of_isUnit (Valuation.valuationSubring.integers hv.v) hx

theorem isUnit_of_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : Valued.v x.val = 1) : IsUnit x := by
  refine Valuation.Integers.isUnit_of_one' (Valuation.valuationSubring.integers hv.v) ?_
  simpa only [ValuationSubring.algebraMap_apply] using hx

theorem isUnit_iff_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring) :
    IsUnit x ↔ Valued.v x.val = 1 := by
  rw [Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.valuationSubring.integers hv.v)]
  simp only [ValuationSubring.algebraMap_apply]

end ValuationSubring

namespace IsDedekindDomain.HeightOneSpectrum

section Multiplicative

lemma exists_ofAdd_natCast_lt {x : ℤᵐ⁰} (hx : x ≠ 0) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) < x := by
  lift x to Multiplicative ℤ using hx
  refine ⟨x.toAdd.natAbs + 1, ?_⟩
  rw [WithZero.coe_lt_coe, ← ofAdd_toAdd x, ofAdd_lt]
  simp only [toAdd_ofAdd]
  have h : x.toAdd ≤ (x.toAdd.natAbs : ℤ) := Int.le_natAbs
  omega

end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

noncomputable abbrev completionIdeal : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (adicCompletionIntegers K v)

lemma mem_completionIdeal_iff (x : v.adicCompletionIntegers K) :
    x ∈ completionIdeal K v ↔ Valued.v x.val < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

namespace adicCompletion

open scoped algebraMap in
theorem exists_uniformizer (v : HeightOneSpectrum A) :
    ∃ π : v.adicCompletionIntegers K, Valued.v π.1 = Multiplicative.ofAdd (- 1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  use π
  rw [← WithZero.exp, ← hπ, ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]

variable {K} in
theorem uniformizer_ne_zero {v : HeightOneSpectrum A}
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    π ≠ 0 := by
  contrapose! hπ
  simp [hπ]

set_option backward.isDefEq.respectTransparency false in
variable {K} in
open scoped Multiplicative in
theorem uniformizer_not_isUnit {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ¬IsUnit (π : v.adicCompletionIntegers K) := by
  rw [ValuationSubring.isUnit_iff_valued_eq_one, ← WithZero.coe_one, ← ofAdd_zero, hπ]
  apply ne_of_lt
  rw [WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
  omega

/-- v4.34 adapter: `HeightOneSpectrum.adicCompletionIntegers` is a `def`, so the
`ValuationSubring.isUnit_of_valued_eq_one` rewrite needs the valuation-subring type
ascribed. Port-only, hence `private`. -/
private theorem isUnit_adicCompletionIntegers_of_valued_eq_one {x : v.adicCompletionIntegers K}
    (hx : Valued.v x.val = 1) : IsUnit x :=
  ValuationSubring.isUnit_of_valued_eq_one (show Valued.v.valuationSubring from x) hx

theorem eq_pow_uniformizer_mul_unit {x : v.adicCompletionIntegers K} (hx : x ≠ 0)
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers K)ˣ), x = π ^ n * u := by
  have hx' : Valued.v x.1 ≠ 0 := by simp [hx]
  let m := - Multiplicative.toAdd (WithZero.unzero hx')
  have hm₀ : 0 ≤ m := by
    simp_rw [m, Right.nonneg_neg_iff, ← toAdd_one, Multiplicative.toAdd_le]
    rw [← WithZero.coe_le_coe]; exact (WithZero.coe_unzero _).symm ▸ x.2
  have hpow : Valued.v (π ^ (-m) * x.val) = 1 := by
    rw [Valued.v.map_mul, map_zpow₀, hπ, ofAdd_neg, WithZero.coe_inv,
      inv_zpow', neg_neg, ← WithZero.coe_zpow, ← Int.ofAdd_mul, one_mul, ofAdd_neg,
      ofAdd_toAdd, WithZero.coe_inv, WithZero.coe_unzero, inv_mul_cancel₀ hx']
  let a : v.adicCompletionIntegers K :=
    ⟨π ^ (-m) * x.val, by
      show Valued.v (π ^ (-m) * x.val) ≤ 1
      exact hpow.le⟩
  have hunit : IsUnit a := isUnit_adicCompletionIntegers_of_valued_eq_one K v hpow
  refine ⟨m.toNat, hunit.unit, Subtype.ext ?_⟩
  simp only [zpow_neg, IsUnit.unit_spec, MulMemClass.coe_mul, SubmonoidClass.coe_pow, a,
    ← zpow_natCast, m.toNat_of_nonneg hm₀, ← mul_assoc]
  rw [mul_inv_cancel₀ (zpow_ne_zero _ <| (by simp [uniformizer_ne_zero hπ])), one_mul]

open scoped algebraMap in
theorem maximalIdeal_eq_span_uniformizer {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {(π : v.adicCompletionIntegers K)} := by
  refine (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
    (Ideal.span_singleton_ne_top (uniformizer_not_isUnit v hπ)) (fun x hx => ?_)
  by_cases hx₀ : x = 0
  · simp only [hx₀, Ideal.zero_mem]
  · obtain ⟨n, ⟨u, hu⟩⟩ := eq_pow_uniformizer_mul_unit K v hx₀ hπ
    have hn : ¬(IsUnit x) := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx h)
    replace hn : n ≠ 0 := fun h => by {rw [hu, h, pow_zero, one_mul] at hn; exact hn u.isUnit}
    simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using dvd_pow_self π hn

instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    let ⟨π, hπ⟩ := exists_uniformizer K v
    rw [maximalIdeal_eq_span_uniformizer K v hπ]
    intro h
    simp only [Ideal.span_singleton_eq_bot] at h
    exact uniformizer_ne_zero hπ h

lemma mem_completionIdeal_pow {n : ℕ} (x : v.adicCompletionIntegers K) :
    x ∈ (v.completionIdeal K) ^ n ↔ Valued.v x.val ≤ ↑(Multiplicative.ofAdd (-(n : ℤ))) := by
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  unfold completionIdeal
  rw [maximalIdeal_eq_span_uniformizer K v hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hvalπ_pow : (Valued.v π.val) ^ n = (Multiplicative.ofAdd (-n : ℤ)) := by
    rw [hπ]
    norm_num
    norm_cast
    rw [← ofAdd_nsmul, Nat.smul_one_eq_cast]
  constructor
  · rintro ⟨a, rfl⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ofAdd_neg,
      WithZero.coe_inv]
    apply mul_le_of_le_one_of_le a.prop <| le_of_eq hvalπ_pow
  · intro hx
    set a := x.val / (π ^ n) with ha'
    have ha : Valued.v a ≤ 1 := by
      rwa [ha', Valuation.map_div, Valuation.map_pow, hvalπ_pow,
        div_le_one₀ (WithZero.zero_lt_coe _)]
    use ⟨a, ha⟩
    apply Subtype.val_injective
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, ha']
    rw [div_mul_eq_mul_div₀, mul_div_cancel_right₀]
    apply pow_ne_zero n
    norm_cast
    exact uniformizer_ne_zero hπ

end adicCompletion

end IsDedekindDomain.HeightOneSpectrum
