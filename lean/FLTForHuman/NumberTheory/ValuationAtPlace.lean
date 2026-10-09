/-
  Places of `ℚ̄` and the integral elements: the shared membership lemma
  `ValuationSubring.mem_of_isIntegral` (an element integral over `ℤ` lies in the
  valuation ring, because the ring of integers is integrally closed), together
  with `ValuationSubring.exists_integral_mul_eq_of_liesOverPrime`: an element of
  a place `A` over the prime `q` becomes integral after multiplying by a unit of
  `A` (the "clear the denominator" step).

  Ported from `P2M/Sol/S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.lean`
  (pinned `aa2d8b3`, 184 lines). The pin proves `IsIntegral ℤ b → b ∈ A` twice —
  as the local `int_mem` here and as `PlaceTransitivity.coe_mem` in
  `S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean` (lines 17–28) —
  so it is written once, publicly, and used by both. The pin's private
  `exists_div_rep_or_inv_div_rep_of_ne_bot` block is transcribed `private`. The
  mathematics is math/018 §1.4.
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import FLTForHuman.GaloisRep.Defs.Ramification

set_option autoImplicit false

-- The pin's proofs introduce instances with `haveI` in `Prop` goals; they are
-- transcribed verbatim, as in the other ported proof files.
set_option linter.style.haveILetI false

open scoped NumberField

/-- An element of `ℚ̄` integral over `ℤ` lies in every valuation ring of `ℚ̄`.

This is the pin's `int_mem`, promoted public so that the two copies in
`S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.lean` and
`S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean` become one. -/
theorem ValuationSubring.mem_of_isIntegral (A : ValuationSubring (AlgebraicClosure ℚ))
    (b : AlgebraicClosure ℚ) (hb : IsIntegral ℤ b) : b ∈ A := by
  have hbA : IsIntegral A b := by
    obtain ⟨p, hp, hpb⟩ := hb
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A)
        = algebraMap ℤ (AlgebraicClosure ℚ) := RingHom.ext_int _ _
    rw [this]
    exact hpb
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hbA
  rw [← hy]
  exact y.2

/-- At a nonzero prime `P` of `𝓞 F` and `x ≠ 0`, either `x` or `x⁻¹` has a
`P`-integral presentation `a / s` with `s ∉ P` — and in the second case the
numerator also lies in `P`. This is the localisation choice the pin makes before
passing to the place. -/
private theorem exists_div_rep_or_inv_div_rep_of_ne_bot {F : Type*} [Field F] [NumberField F]
    (P : Ideal (𝓞 F)) [P.IsPrime]
    (hP : P ≠ ⊥) (x : F) (hx : x ≠ 0) :
    (∃ a s : 𝓞 F, s ∉ P ∧ x = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F s) ∨
      ∃ a s : 𝓞 F, a ∈ P ∧ s ∉ P ∧ x⁻¹ = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F s := by
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hφ : Function.Injective (algebraMap (𝓞 F) F) := IsFractionRing.injective (𝓞 F) F
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hnd
    exact hx hnd.symm
  have hnF : algebraMap (𝓞 F) F n ≠ 0 := fun h0 => hn0 (hφ (by rw [h0, map_zero]))
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := fun h0 => hd0 (hφ (by rw [h0, map_zero]))
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_of_local_atPrime ‹P.IsPrime›
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) hP _
  obtain ⟨c, hc | hc⟩ :=
    ValuationRing.cond (algebraMap (𝓞 F) (Localization.AtPrime P) n)
      (algebraMap (𝓞 F) (Localization.AtPrime P) d)
  ·
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    have hsP : (s : 𝓞 F) ∉ P := s.2
    have hsF : algebraMap (𝓞 F) F (s : 𝓞 F) ≠ 0 := fun h0 =>
      hsP (by rw [show (s : 𝓞 F) = 0 from hφ (by rw [h0, map_zero])]; exact P.zero_mem)
    have key : algebraMap (𝓞 F) (Localization.AtPrime P) (n * a)
        = algebraMap (𝓞 F) (Localization.AtPrime P) (d * s) := by
      rw [map_mul, map_mul, ← IsLocalization.mk'_spec (Localization.AtPrime P) a s, ← hc]
      ring
    obtain ⟨t, ht⟩ :=
      (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).mp key
    have ht0 : (t : 𝓞 F) ≠ 0 :=
      nonZeroDivisors.ne_zero (P.primeCompl_le_nonZeroDivisors t.2)
    have hEq : n * a = d * (s : 𝓞 F) := mul_left_cancel₀ ht0 ht
    have hF : algebraMap (𝓞 F) F n * algebraMap (𝓞 F) F a
        = algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F (s : 𝓞 F) := by
      rw [← map_mul, ← map_mul, hEq]
    have hxinv : x⁻¹ = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F (s : 𝓞 F) := by
      rw [← hnd, inv_div, div_eq_div_iff hnF hsF]
      linear_combination -hF
    by_cases haP : a ∈ P
    · exact Or.inr ⟨a, s, haP, hsP, hxinv⟩
    · refine Or.inl ⟨(s : 𝓞 F), a, haP, ?_⟩
      rw [← inv_inv x, hxinv, inv_div]
  ·
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    have hsP : (s : 𝓞 F) ∉ P := s.2
    have hsF : algebraMap (𝓞 F) F (s : 𝓞 F) ≠ 0 := fun h0 =>
      hsP (by rw [show (s : 𝓞 F) = 0 from hφ (by rw [h0, map_zero])]; exact P.zero_mem)
    have key : algebraMap (𝓞 F) (Localization.AtPrime P) (d * a)
        = algebraMap (𝓞 F) (Localization.AtPrime P) (n * s) := by
      rw [map_mul, map_mul, ← IsLocalization.mk'_spec (Localization.AtPrime P) a s, ← hc]
      ring
    obtain ⟨t, ht⟩ :=
      (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).mp key
    have ht0 : (t : 𝓞 F) ≠ 0 :=
      nonZeroDivisors.ne_zero (P.primeCompl_le_nonZeroDivisors t.2)
    have hEq : d * a = n * (s : 𝓞 F) := mul_left_cancel₀ ht0 ht
    have hF : algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F a
        = algebraMap (𝓞 F) F n * algebraMap (𝓞 F) F (s : 𝓞 F) := by
      rw [← map_mul, ← map_mul, hEq]
    refine Or.inl ⟨a, s, hsP, ?_⟩
    rw [← hnd, div_eq_div_iff hdF hsF]
    linear_combination -hF

theorem ValuationSubring.exists_integral_mul_eq_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ),
      (s : AlgebraicClosure ℚ) ∉ A.nonunits ∧ a * s = x := by
  classical

  haveI halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h

  by_cases ha0 : a = 0
  · refine ⟨0, 1, ?_, by simp [ha0]⟩
    rw [OneMemClass.coe_one, ValuationSubring.mem_nonunits_iff, map_one]
    exact lt_irrefl 1

  have haint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {a}
  haveI hFfd : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional haint
  haveI : NumberField F :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
      to_finiteDimensional := hFfd }

  have hOA : ∀ b : 𝓞 F, algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b) ∈ A := fun b =>
    ValuationSubring.mem_of_isIntegral A _
      (map_isIntegral_int (algebraMap F (AlgebraicClosure ℚ))
        (NumberField.RingOfIntegers.isIntegral_coe b))
  let φ : 𝓞 F →+* A :=
    ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)).codRestrict A.toSubring (fun b => hOA b)
  have hφ : ∀ b : 𝓞 F, (φ b : (AlgebraicClosure ℚ)) = algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b) := fun b => rfl
  let P : Ideal (𝓞 F) := Ideal.comap φ (IsLocalRing.maximalIdeal A)
  haveI hPprime : P.IsPrime := Ideal.IsPrime.comap φ
  have hmemP : ∀ b : 𝓞 F, b ∈ P ↔ algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b) ∈ A.nonunits := by
    intro b
    rw [← hφ, ValuationSubring.coe_mem_nonunits_iff]
    rfl

  have hqP : (q : 𝓞 F) ∈ P := by
    rw [hmemP, map_natCast, map_natCast]
    exact hA
  have hPbot : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at hqP
    exact hq.ne_zero (Nat.cast_eq_zero.mp hqP)

  have hval1 : ∀ s : 𝓞 F, s ∉ P → A.valuation (algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s)) = 1 := by
    intro s hs
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (hOA s)) (not_lt.mp fun hlt => hs ?_)
    rw [hmemP, ValuationSubring.mem_nonunits_iff]
    exact hlt

  let a' : F := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ a⟩
  have ha' : algebraMap F (AlgebraicClosure ℚ) a' = a := rfl
  have ha'0 : a' ≠ 0 := fun h => ha0 (by rw [← ha', h, map_zero])

  have hint : ∀ b : 𝓞 F, IsIntegral ℤ (algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b)) := fun b =>
    map_isIntegral_int (algebraMap F (AlgebraicClosure ℚ)) (NumberField.RingOfIntegers.isIntegral_coe b)
  rcases exists_div_rep_or_inv_div_rep_of_ne_bot P hPbot a' ha'0 with
    ⟨b, s, hs, hrep⟩ | ⟨b, s, hb, hs, hrep⟩
  ·
    have hsK : algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s) ≠ 0 := by
      intro h0
      have := hval1 s hs
      rw [h0, map_zero] at this
      exact zero_ne_one this
    refine ⟨⟨_, hint b⟩, ⟨_, hint s⟩, ?_, ?_⟩
    · change algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s) ∉ A.nonunits
      rw [ValuationSubring.mem_nonunits_iff, hval1 s hs]
      exact lt_irrefl 1
    · change a * algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s) = algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b)
      rw [← ha', hrep, map_div₀, div_mul_cancel₀ _ hsK]
  ·
    exfalso
    have hlt : A.valuation a⁻¹ < 1 := by
      have : a⁻¹ = algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b) / algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s) := by
        rw [← ha', ← map_inv₀, hrep, map_div₀]
      rw [this, map_div₀, hval1 s hs, div_one, ← ValuationSubring.mem_nonunits_iff, ← hmemP]
      exact hb
    have hle : A.valuation a ≤ 1 := (A.valuation_le_one_iff a).mpr ha
    have hone : A.valuation a * A.valuation a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
    have hprod : A.valuation a * A.valuation a⁻¹ < 1 := by
      calc A.valuation a * A.valuation a⁻¹ ≤ A.valuation a⁻¹ := mul_le_of_le_one_left' hle
        _ < 1 := hlt
    exact absurd hone (ne_of_lt hprod)

/-! ## The residue field of a place over `q`

The opening `ValuationSubring` block of the pin's
`Definitions/Def_WeierstrassCurve_ReductionMap.lean` (pinned `aa2d8b3`). The pin's
Weierstrass reduction map is ported separately (`WeierstrassCurve/Reduction/Point.lean`,
W4 stages 1–2); this half is homed here because the q-expansion column also needs it —
`ModularCurve/X1/FunctionFieldIsAlgClosed.lean`
and the `isAlgClosed` finrank target both set
`CharP (IsLocalRing.ResidueField A) q` from `A.LiesOverPrime q`. It was carried as
a `private` re-derivation there; it is homed here, publicly, at the pin's names so
both consumers import it. -/

namespace ValuationSubring

variable {L : Type*} [Field L]

lemma liesOverPrime_iff {A : ValuationSubring L} {q : ℕ} :
    A.LiesOverPrime q ↔ (q : L) ∈ A.nonunits :=
  Iff.rfl

lemma natCast_mem' (A : ValuationSubring L) (q : ℕ) : (q : L) ∈ A :=
  natCast_mem A.toSubring q

lemma natCast_mem_maximalIdeal_of_liesOverPrime {A : ValuationSubring L} {q : ℕ}
    (h : A.LiesOverPrime q) : (q : A) ∈ IsLocalRing.maximalIdeal A := by
  have : ((q : A) : L) ∈ A.nonunits := by
    simpa using liesOverPrime_iff.mp h
  exact A.coe_mem_nonunits_iff.mp this

theorem charP_residueField_of_liesOverPrime_def {A : ValuationSubring L} {q : ℕ} (hq : q.Prime)
    (h : A.LiesOverPrime q) : CharP (IsLocalRing.ResidueField A) q := by
  rw [CharP.charP_iff_prime_eq_zero hq]

  have : ((q : ℕ) : IsLocalRing.ResidueField A) = IsLocalRing.residue A ((q : ℕ) : A) := by
    simp
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (natCast_mem_maximalIdeal_of_liesOverPrime h)

theorem exists_liesOverPrime [CharZero L] {q : ℕ} (hq : q.Prime) :
    ∃ A : ValuationSubring L, A.LiesOverPrime q := by

  set R : Subring L := ⊥ with hR

  have hqR : ¬IsUnit ((q : ℕ) : R) := by
    rw [isUnit_iff_exists_inv]
    rintro ⟨y, hy⟩

    have hy' : (q : L) * (y : L) = 1 := by
      have := congrArg (R.subtype) hy
      simpa using this

    obtain ⟨n, hn⟩ := Subring.mem_bot.mp y.2
    rw [← hn] at hy'

    have hqn : (q : ℤ) * n = 1 := by
      have : (((q : ℤ) * n : ℤ) : L) = ((1 : ℤ) : L) := by push_cast; linear_combination hy'
      exact_mod_cast this

    have h1 : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos ⟨n, hqn.symm⟩
    have h2 : 2 ≤ q := hq.two_le
    omega

  obtain ⟨B, -, hB⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (Ideal.span {((q : ℕ) : R)})
      (fun h => hqR (Ideal.span_singleton_eq_top.mp h))
  refine ⟨B, hB ⟨((q : ℕ) : R), Ideal.subset_span rfl, ?_⟩⟩
  simp

variable (K : Type*) [Field K] [Algebra K L]

lemma mem_inertiaSubgroupIn {A : ValuationSubring L} {σ : L ≃ₐ[K] L} :
    σ ∈ A.inertiaSubgroupIn K ↔
      ∃ h : σ ∈ A.decompositionSubgroup K, (⟨σ, h⟩ : A.decompositionSubgroup K) ∈
        A.inertiaSubgroup K := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hτI, rfl⟩
    exact ⟨hτ, hτI⟩
  · rintro ⟨h, hI⟩
    exact ⟨⟨σ, h⟩, hI, rfl⟩

end ValuationSubring

/-! ### The non-unit block and the decomposition/inertia action

The *second* `ValuationSubring` block of the pin's
`Definitions/Def_WeierstrassCurve_ReductionMap.lean` (lines 80–95 and 205–228): that a ring
element times a non-unit of `A` is a non-unit, that `1` is not a non-unit, and that the
decomposition subgroup of a place acts on `A` while its inertia subgroup acts trivially on
the residue field. They are the tools the reduction map is built from, and their natural home
is here beside the file's first `ValuationSubring` block rather than in the reduction module.

Statements are the pin's verbatim text; the pin's `_root_.ValuationSubring.` prefixes are
spelled by the enclosing namespace. -/

namespace ValuationSubring

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem mul_mem_nonunits {a x : L} (ha : a ∈ A) (hx : x ∈ A.nonunits) :
    a * x ∈ A.nonunits := by
  rw [mem_nonunits_iff] at hx ⊢
  calc A.valuation (a * x) = A.valuation a * A.valuation x := map_mul _ _ _
    _ ≤ 1 * A.valuation x := mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
    _ = A.valuation x := one_mul _
    _ < 1 := hx

theorem one_notMem_nonunits : (1 : L) ∉ A.nonunits := by
  simp [mem_nonunits_iff]

end ValuationSubring

section Inertia

open IsLocalRing
open scoped Pointwise

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L)

theorem ValuationSubring.smul_mem_of_mem_decompositionSubgroup {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {z : L} (hz : z ∈ A) : σ z ∈ A := by
  have h1 : σ • z ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ z A hz
  rwa [MulAction.mem_stabilizer_iff.mp hσ, AlgEquiv.smul_def] at h1

theorem ValuationSubring.residue_smul_eq_of_mem_inertiaSubgroup
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K) (a : A) :
    residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • a) = residue A a := by
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A)
      ⟨σ, hσ⟩ = 1 := hσI
  calc residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • a)
      = (⟨σ, hσ⟩ : A.decompositionSubgroup K) • residue A a := rfl
    _ = MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A)
          ⟨σ, hσ⟩ (residue A a) := rfl
    _ = residue A a := by rw [h1]; rfl

end Inertia
