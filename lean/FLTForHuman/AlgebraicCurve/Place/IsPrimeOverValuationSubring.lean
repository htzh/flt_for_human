/-
The place realising a prime over a valuation subring: FLT's
`AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring`, after the pin
`P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean`
(the whole 1,886-line `S_` file) and its statement wrapper
`Theorems/Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean`.

Given an algebraically closed `K`, a finite separable extension `F` of `K(j)` for
a transcendental `j`, a subring `B ≤ F` containing the constants and `j` and
integral over `K[A] ∪ {j}`, and a prime `𝔮` of `B` over the maximal ideal of a
valuation subring `A ≤ K` with `j - a₀ ∈ 𝔮`, the headline produces a place `w` of
`F` with `0 < w.ord (j - a₀)` and with `𝔮` cut out by the nonunits of
`w.toValuationSubring` above the maximal ideal of `A`.

The generic valuation-subring prelude the headline was ported with — the
`Place`-free domination theory and the `Place` value/residue dictionary — now
lives, public, in `AlgebraicCurve/Place/ValueDictionary.lean` (whose `Place`-free
half is `NumberTheory/ValuationSubring/Domination.lean`), which this module
imports; this module declares the headline and nothing else, exactly as the pin
has the single non-`private` declaration `theorem solution`. The pin's
`p2m_export`/`p2m_open`/`p2m_reactivate`/`p2m_alias` scaffolding is not ported;
each declaration sits in its pin namespace under a plain `namespace`/`end`.

Deviations from the pin are API drift only (playbook §4); no statement changes.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean
-/

import FLTForHuman.AlgebraicCurve.Place.ValueDictionary
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Int.CharZero
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

open Polynomial

-- pin: exists_of_isPrime_over_valuationSubring (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1841)
theorem AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] (A : ValuationSubring K) {j : F}
    (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({j} : Set F)) F]
    {B : Subring F} (hconst : ∀ a : A, algebraMap K F a ∈ B) (hjB : j ∈ B)
    (hint : ∀ b : B,
      IsIntegral (Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {j})) (b : F))
    (𝔮 : Ideal B) [𝔮.IsPrime]
    (h𝔮A : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → (⟨algebraMap K F a, hconst a⟩ : B) ∈ 𝔮)
    (a₀ : A) (hja : (⟨j, hjB⟩ : B) - ⟨algebraMap K F a₀, hconst a₀⟩ ∈ 𝔮) :
    ∃ w : AlgebraicCurve.Place K F,
      0 < w.ord (j - algebraMap K F a₀) ∧
      ∀ b : B, b ∈ 𝔮 ↔ ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
        ((b : F) - algebraMap K F a) ∈ w.toValuationSubring.nonunits := by

  have h𝔮A' : ∀ a : A, (⟨algebraMap K F a, hconst a⟩ : B) ∈ 𝔮 ↔
      a ∈ IsLocalRing.maximalIdeal A := by
    intro a
    refine ⟨fun ha => ?_, h𝔮A a⟩
    by_contra hu
    have hunit : IsUnit a := (IsLocalRing.notMem_maximalIdeal.mp hu)
    obtain ⟨u, rfl⟩ := hunit
    apply (inferInstance : 𝔮.IsPrime).ne_top
    rw [Ideal.eq_top_iff_one]
    have hinv : (⟨algebraMap K F ((u⁻¹ : Aˣ) : A), hconst _⟩ : B) *
        ⟨algebraMap K F ((u : Aˣ) : A), hconst _⟩ = 1 := by
      apply Subtype.ext
      show algebraMap K F ((u⁻¹ : Aˣ) : A) * algebraMap K F ((u : Aˣ) : A) = 1
      rw [← map_mul, ← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one, map_one]
    rw [← hinv]
    exact 𝔮.mul_mem_left _ ha
  obtain ⟨w, hB, hcent, hval⟩ := AlgebraicCurve.Place.exists_place_centre_comap_eq (K := K)
    (F := F) A hj
    hconst hjB hint 𝔮 h𝔮A' a₀ hja
  refine ⟨w, ?_, fun b => ?_⟩
  · have hne : j ≠ algebraMap K F (a₀ : K) := fun h =>
      hj (h ▸ isAlgebraic_algebraMap (a₀ : K))
    exact (w.hasValueAt_iff_ord_pos hne).mp hval
  · rw [← hcent, Ideal.mem_comap]
    constructor
    · intro hb
      exact ⟨w.value A (Subring.inclusion hB b), (w.mem_centre_iff _).mp hb,
        w.hasValueAt_value A (Subring.inclusion hB b)⟩
    · rintro ⟨a, ha, hba⟩
      have hba' : w.HasValueAt (Subring.inclusion hB b : F) (a : K) := hba
      exact (w.mem_centre_iff_of_hasValueAt hba').mpr ha
