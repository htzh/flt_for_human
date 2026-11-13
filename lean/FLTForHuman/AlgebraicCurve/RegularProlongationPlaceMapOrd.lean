/-
  The place map of a chart is the ord map.

  On a finite chart whose residue map is surjective onto the integral closure, the place
  `Q` produced by the chart's uniqueness theorem maps along `mapDomain` to the place of the
  function field with the same `ord`: for an integral element `f`, `Q.ord (R.residue f)` is
  the order of `f` at the corresponding place. This is the dictionary between the residue
  field's place and the function field's, and the step the constant-reduction argument uses.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective.lean`
  (375 lines), with the statement from the wrapper
  `Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective.lean`.

  Assumes from earlier modules: the reduced place and its uniqueness
  (`RegularProlongationReducedPlace.lean`), the ord equality of AF52
  (`RegularProlongationOrdResidueEquality.lean`, which also owns `Red`), the inverse-adjoin
  dictionary of `RegularProlongationReducedPlace.lean`, and the `Place`/ord calculus.

  spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective.lean
-/
import FLTForHuman.AlgebraicCurve.RegularProlongation
import FLTForHuman.AlgebraicCurve.RegularProlongationFinrank
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueSpan
import FLTForHuman.AlgebraicCurve.RegularProlongationGaussBasis
import FLTForHuman.AlgebraicCurve.RegularProlongationReducedPlace
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueIntegralClosure
import FLTForHuman.AlgebraicCurve.RegularProlongationSumOrdResidue
import FLTForHuman.AlgebraicCurve.RegularProlongationOrdResidueEquality
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueBasis
import FLTForHuman.AlgebraicCurve.DeuringMultiplicity
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.Repartitions
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Place.Approximation
import FLTForHuman.FieldTheory.ValuationSubringComposite
import FLTForHuman.FieldTheory.ValuationSubringResidueField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing
open AlgebraicCurve.RegularProlongation.OrdResidueEquality AlgebraicCurve.RegularProlongation.ReducedPlace

namespace AlgebraicCurve
namespace RegularProlongation
namespace PlaceMapOrd
open AlgebraicCurve.RegularProlongation AlgebraicCurve
section abstract

variable {ι κ : Type*}

theorem exists_map_of_two_charts (Dom₁ Dom₂ : ι → Prop) (Red₁ Red₂ : ι → κ → Prop)
    (Fin : κ → Prop)
    (hcover : ∀ P, Dom₁ P ∨ Dom₂ P)
    (E₁ : ∀ P, Dom₁ P → ∃! Q, Red₁ P Q) (E₂ : ∀ P, Dom₂ P → ∃! Q, Red₂ P Q)
    (hfin₁ : ∀ P Q, Dom₁ P → Red₁ P Q → Fin Q)
    (hinf₂ : ∀ P Q, ¬ Dom₁ P → Dom₂ P → Red₂ P Q → ¬ Fin Q)
    (hboth : ∀ P Q, Dom₁ P → Dom₂ P → Red₂ P Q → Fin Q) :
    ∃ r : ι → κ, (∀ P Q, Fin Q → (r P = Q ↔ Dom₁ P ∧ Red₁ P Q)) ∧
      (∀ P Q, ¬ Fin Q → (r P = Q ↔ Dom₂ P ∧ Red₂ P Q)) := by
  classical
  let r : ι → κ := fun P =>
    if h : Dom₁ P then (E₁ P h).exists.choose
    else (E₂ P ((hcover P).resolve_left h)).exists.choose
  have hr₁ : ∀ P (h : Dom₁ P), Red₁ P (r P) := fun P h => by
    simp only [r, dite_eq_left h]
    exact (E₁ P h).exists.choose_spec
  have hr₂ : ∀ P (h : ¬ Dom₁ P), Red₂ P (r P) := fun P h => by
    simp only [r, dite_eq_right h]
    exact (E₂ P ((hcover P).resolve_left h)).exists.choose_spec
  refine ⟨r, fun P Q hQ => ⟨fun hPQ => ?_, fun ⟨hd, hred⟩ => ?_⟩,
    fun P Q hQ => ⟨fun hPQ => ?_, fun ⟨hd, hred⟩ => ?_⟩⟩
  · by_cases h : Dom₁ P
    · exact ⟨h, hPQ ▸ hr₁ P h⟩
    · exact absurd hQ (hinf₂ P Q h ((hcover P).resolve_left h) (hPQ ▸ hr₂ P h))
  · exact (E₁ P hd).unique (hr₁ P hd) hred
  · by_cases h : Dom₁ P
    · exact absurd (hfin₁ P _ h (hr₁ P h)) (hPQ ▸ hQ)
    · exact ⟨(hcover P).resolve_left h, hPQ ▸ hr₂ P h⟩
  · by_cases h : Dom₁ P
    · exact absurd (hboth P Q h hd hred) hQ
    · exact (E₂ P ((hcover P).resolve_left h)).unique (hr₂ P h) hred

theorem mapDomain_eq_sum_filter [DecidableEq κ] (r : ι → κ) (D : ι →₀ ℤ) (Q : κ) :
    Finsupp.mapDomain r D Q = ∑ P ∈ D.support with r P = Q, D P := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [Finsupp.single_apply]

theorem mapDomain_eq_of_chart (r : ι → κ) (D : ι →₀ ℤ) (Q : κ) (Dom : ι → Prop)
    (Red : ι → κ → Prop) (hfib : ∀ P, r P = Q ↔ Dom P ∧ Red P Q) (n : ℤ)
    (hM : ∀ T : Finset ι, (∀ P, P ∈ T ↔ (D P ≠ 0 ∧ Dom P ∧ Red P Q)) → ∑ P ∈ T, D P = n) :
    Finsupp.mapDomain r D Q = n := by
  classical
  rw [mapDomain_eq_sum_filter]
  refine hM _ fun P => ?_
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hfib]

end abstract

section places

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem valuation_algebraMap_eq_one (P : Place L F) {c : L} (hc : c ≠ 0) :
    P.toValuationSubring.valuation (algebraMap L F c) = 1 := by
  let u : (P.toValuationSubring)ˣ :=
    ⟨algebraMap L P.toValuationSubring c, algebraMap L P.toValuationSubring c⁻¹,
      by rw [← map_mul, mul_inv_cancel₀ hc, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hc, map_one]⟩
  exact P.toValuationSubring.valuation_unit u

theorem const_unique (P : Place L F) {h : F} {c c' : L}
    (hc : h - algebraMap L F c ∈ P.toValuationSubring.nonunits)
    (hc' : h - algebraMap L F c' ∈ P.toValuationSubring.nonunits) : c = c' := by
  by_contra hne
  rw [ValuationSubring.mem_nonunits_iff] at hc hc'
  have hlt : P.toValuationSubring.valuation (algebraMap L F (c' - c)) < 1 := by
    have : algebraMap L F (c' - c) = (h - algebraMap L F c) + -(h - algebraMap L F c') := by
      rw [map_sub]; ring
    rw [this]
    refine Valuation.map_add_lt _ hc ?_
    rwa [Valuation.map_neg]
  rw [valuation_algebraMap_eq_one P (sub_ne_zero.mpr (Ne.symm hne))] at hlt
  exact lt_irrefl _ hlt

theorem inv_sub_inv_mem_nonunits (P : Place L F) {x : F} {c : L} (hc0 : c ≠ 0)
    (hc : x - algebraMap L F c ∈ P.toValuationSubring.nonunits) :
    x⁻¹ - algebraMap L F c⁻¹ ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hc ⊢
  have hvc : P.toValuationSubring.valuation (algebraMap L F c) = 1 :=
    valuation_algebraMap_eq_one P hc0
  have hvx : P.toValuationSubring.valuation x = 1 := by
    have := Valuation.map_add_eq_of_lt_left P.toValuationSubring.valuation
      (x := algebraMap L F c) (y := x - algebraMap L F c) (by rwa [hvc])
    rwa [add_sub_cancel, hvc] at this
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hvx; exact zero_ne_one hvx
  have hc0' : algebraMap L F c ≠ 0 := by simpa using hc0
  have heq : x⁻¹ - algebraMap L F c⁻¹ =
      -(x⁻¹ * (algebraMap L F c)⁻¹ * (x - algebraMap L F c)) := by
    rw [map_inv₀]; field_simp; ring
  rw [heq, Valuation.map_neg, map_mul, map_mul, map_inv₀, map_inv₀, hvx, hvc]
  simpa using hc

theorem exists_sub_algebraMap_mem_nonunits [IsAlgClosed L] [IsCurveOver L F] (P : Place L F)
    {h : F} (hh : h ∈ P.toValuationSubring) :
    ∃ c : L, h - algebraMap L F c ∈ P.toValuationSubring.nonunits := by
  have : Module.Finite L P.ResidueField := IsCurveOver.finiteResidue P
  have : Algebra.IsIntegral L P.ResidueField := Algebra.IsIntegral.of_finite L P.ResidueField
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := P.ResidueField)).2
      (IsLocalRing.residue P.toValuationSubring ⟨h, hh⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨h, hh⟩ : P.toValuationSubring) - algebraMap L P.toValuationSubring c ∈
      maximalIdeal P.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc]
    exact (IsScalarTower.algebraMap_apply L P.toValuationSubring P.ResidueField c).symm
  have := ValuationSubring.coe_mem_nonunits_iff.mpr hmem
  simpa using this

theorem exists_inv_sub_mem_nonunits [IsAlgClosed L] [IsCurveOver L F] (A : ValuationSubring L)
    (P : Place L F) (x : F)
    (hnot : ¬ ∃ a : A, x - algebraMap L F a ∈ P.toValuationSubring.nonunits) :
    ∃ a : A, x⁻¹ - algebraMap L F a ∈ P.toValuationSubring.nonunits := by
  by_cases hxV : x ∈ P.toValuationSubring
  · obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_nonunits P hxV
    have hcA : c ∉ A := fun h => hnot ⟨⟨c, h⟩, hc⟩
    have hc0 : c ≠ 0 := by rintro rfl; exact hcA A.zero_mem
    have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    exact ⟨⟨c⁻¹, hcinv⟩, inv_sub_inv_mem_nonunits P hc0 hc⟩
  · refine ⟨0, ?_⟩
    have hxinv : x⁻¹ ∈ P.toValuationSubring :=
      (P.toValuationSubring.mem_or_inv_mem x).resolve_left hxV
    rw [show ((0 : A) : L) = 0 from rfl, map_zero, sub_zero, ValuationSubring.mem_nonunits_iff]
    rw [← P.toValuationSubring.valuation_le_one_iff, not_le] at hxV
    have hx0 : x ≠ 0 := by rintro rfl; simp at hxV
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hxV

theorem inv_const_eq (P : Place L F) {x : F} (hx0 : x ≠ 0) {a a' : L}
    (ha : x - algebraMap L F a ∈ P.toValuationSubring.nonunits)
    (ha' : x⁻¹ - algebraMap L F a' ∈ P.toValuationSubring.nonunits) : a ≠ 0 ∧ a' = a⁻¹ := by
  have hmem : x⁻¹ ∈ P.toValuationSubring := by
    have h1 : x⁻¹ - algebraMap L F a' ∈ P.toValuationSubring :=
      ValuationSubring.nonunits_subset ha'
    have h2 : algebraMap L F a' ∈ P.toValuationSubring := P.algebraMap_mem' a'
    simpa using add_mem h1 h2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero, ValuationSubring.mem_nonunits_iff] at ha
    rw [← P.toValuationSubring.valuation_le_one_iff, map_inv₀] at hmem
    have hvx0 : 0 < P.toValuationSubring.valuation x :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
    exact absurd hmem (not_le.mpr ((one_lt_inv₀ hvx0).mpr ha))
  exact ⟨ha0, const_unique P ha' (inv_sub_inv_mem_nonunits P ha0 ha)⟩

end places

section main

variable {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

def Dom (P : Place L F) (y : F) : Prop :=
  ∃ a : A, y - algebraMap L F a ∈ P.toValuationSubring.nonunits

variable {A}

theorem isIntegral_self (y : F) : IsIntegral (Algebra.adjoin L {y}) y :=
  isIntegral_algebraMap (x := (⟨y, Algebra.self_mem_adjoin_singleton L y⟩ : Algebra.adjoin L {y}))

theorem residue_mem_of_red (R : RegularProlongation A F Fbar) (y : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hd : Dom A P (y : F)) (hred : Red A R y P Q) :
    R.residue y ∈ Q.toValuationSubring := by
  obtain ⟨a, ha⟩ := hd
  have h1 := ValuationSubring.nonunits_subset (hred y (isIntegral_self (y : F)) a ha)
  have h2 := Q.algebraMap_mem' (IsLocalRing.residue A a)
  simpa using add_mem h1 h2

variable [IsAlgClosed L] [IsCurveOver L F] [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

theorem main (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart :
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h)) :
    ∃ r : Place L F → Place (IsLocalRing.ResidueField A) Fbar,
      ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f) := by
  classical

  have hx0 : R.residue x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  obtain ⟨ux, hux⟩ := R.isUnit_of_residue_ne_zero hx0
  have hxF0 : (x : F) ≠ 0 := by
    intro h
    exact hx0 (by rw [show x = 0 from Subtype.ext h, map_zero])
  obtain ⟨xi, hxxi⟩ : ∃ xi : R.integers, x * xi = 1 := ⟨(ux⁻¹ : R.integersˣ), hux ▸ ux.mul_inv⟩
  have hxiF : (xi : F) = (x : F)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by exact_mod_cast congrArg Subtype.val hxxi)
  have hxires : R.residue xi = (R.residue x)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, hxxi, map_one])
  have hxiF0 : (xi : F) ≠ 0 := by rw [hxiF]; exact inv_ne_zero hxF0
  have hx' : Transcendental (IsLocalRing.ResidueField A) (R.residue xi) := by
    rw [hxires]; exact fun h => hx (IsAlgebraic.inv_iff.mp h)
  have hadjK : IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue xi} : Set Fbar) =
      IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar) := by
    rw [hxires]; exact inv_adjoin_eq _
  have hadjL : IntermediateField.adjoin L ({(xi : F)} : Set F) =
      IntermediateField.adjoin L ({(x : F)} : Set F) := by
    rw [hxiF]; exact inv_adjoin_eq _
  have hfin' : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue xi} : Set Fbar)) Fbar := by
    rw [hadjK]; exact hfin
  have hdeg' : Module.finrank (IntermediateField.adjoin L ({(xi : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue xi} : Set Fbar))
          Fbar := by
    rw [hadjK, hadjL]; exact hdeg
  have hchart' : ∀ h : Fbar,
      IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue xi}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(xi : F)}) (f : F) ∧ R.residue f = h := by
    rw [hxires, hxiF]; exact hchart.2

  have hcover : ∀ P : Place L F, Dom A P (x : F) ∨ Dom A P (xi : F) := fun P =>
    or_iff_not_imp_left.mpr fun h => by
      rw [hxiF]; exact exists_inv_sub_mem_nonunits A P (x : F) h
  have E₁ : ∀ P : Place L F, Dom A P (x : F) → ∃! Q, Red A R (x : F) P Q := fun P hP =>
    RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits
      A R x hx hfin hdeg hchart.1 P hP
  have E₂ : ∀ P : Place L F, Dom A P (xi : F) → ∃! Q, Red A R (xi : F) P Q := fun P hP =>
    RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits
      A R xi hx' hfin' hdeg' hchart' P hP
  have hfin₁ : ∀ P Q, Dom A P (x : F) → Red A R (x : F) P Q →
      R.residue x ∈ Q.toValuationSubring := fun P Q hd hred =>
    residue_mem_of_red R x P Q hd hred
  have hinf₂ : ∀ P Q, ¬ Dom A P (x : F) → Dom A P (xi : F) → Red A R (xi : F) P Q →
      R.residue x ∉ Q.toValuationSubring := by
    intro P Q hnd hd hred hfinQ
    obtain ⟨a', ha'⟩ := hd
    have hres := hred xi (isIntegral_self (xi : F)) a' ha'
    by_cases hunit : IsUnit a'
    ·
      obtain ⟨u, hu⟩ := hunit
      apply hnd
      refine ⟨(u⁻¹ : Aˣ), ?_⟩
      have ha'0 : ((a' : A) : L) ≠ 0 := fun h =>
        (hu ▸ u.isUnit).ne_zero (Subtype.ext h)
      have hcoe : (((u⁻¹ : Aˣ) : A) : L) = ((a' : A) : L)⁻¹ := by
        refine eq_inv_of_mul_eq_one_right ?_
        rw [← hu]
        exact_mod_cast congrArg Subtype.val u.mul_inv
      have := inv_sub_inv_mem_nonunits P ha'0 ha'
      rwa [hxiF, inv_inv, ← hcoe] at this
    ·
      have hmax : a' ∈ maximalIdeal A :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunit)
      have hzero : IsLocalRing.residue A a' = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
      rw [hzero, map_zero, sub_zero, hxires, ValuationSubring.mem_nonunits_iff, map_inv₀] at hres
      rw [← Q.toValuationSubring.valuation_le_one_iff] at hfinQ
      have hv0 : 0 < Q.toValuationSubring.valuation (R.residue x) :=
        zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
      exact absurd hfinQ (not_le.mpr ((inv_lt_one₀ hv0).mp hres))
  have hboth : ∀ P Q, Dom A P (x : F) → Dom A P (xi : F) → Red A R (xi : F) P Q →
      R.residue x ∈ Q.toValuationSubring := by
    intro P Q hd hd' hred
    obtain ⟨a, ha⟩ := hd
    obtain ⟨a', ha'⟩ := hd'
    obtain ⟨ha0, haa'⟩ := inv_const_eq P hxF0 ha (hxiF ▸ ha')
    have hres := hred xi (isIntegral_self (xi : F)) a' ha'

    have hunit : IsUnit a' := by
      refine isUnit_iff_exists_inv.mpr ⟨a, Subtype.ext ?_⟩
      show ((a' : A) : L) * ((a : A) : L) = 1
      rw [haa', inv_mul_cancel₀ ha0]
    have hres0 : IsLocalRing.residue A a' ≠ 0 := fun h0 =>
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0))
        hunit
    have hc0 : algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a') ≠ 0 := by
      simpa using hres0
    have hvc : Q.toValuationSubring.valuation
        (algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a')) = 1 :=
      valuation_algebraMap_eq_one Q hres0
    rw [ValuationSubring.mem_nonunits_iff] at hres
    have hvxi : Q.toValuationSubring.valuation (R.residue xi) = 1 := by
      have := Valuation.map_add_eq_of_lt_left Q.toValuationSubring.valuation
        (x := algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a'))
        (y := R.residue xi - algebraMap (IsLocalRing.ResidueField A) Fbar
          (IsLocalRing.residue A a')) (by rwa [hvc])
      rwa [add_sub_cancel, hvc] at this
    rw [← Q.toValuationSubring.valuation_le_one_iff, show R.residue x = (R.residue xi)⁻¹ by
      rw [hxires, inv_inv], map_inv₀, hvxi, inv_one]

  obtain ⟨r, hr₁, hr₂⟩ := exists_map_of_two_charts
    (fun P : Place L F => Dom A P (x : F)) (fun P : Place L F => Dom A P (xi : F))
    (Red A R (x : F)) (Red A R (xi : F))
    (fun Q : Place (IsLocalRing.ResidueField A) Fbar => R.residue x ∈ Q.toValuationSubring)
    hcover E₁ E₂ hfin₁ hinf₂ hboth
  refine ⟨r, fun f hf D hD Q => ?_⟩
  by_cases hQ : R.residue x ∈ Q.toValuationSubring
  ·
    exact mapDomain_eq_of_chart r D Q (fun P => Dom A P (x : F)) (Red A R (x : F))
      (fun P => hr₁ P Q hQ) _ fun T hT =>
        RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
          A R x hx hfin hdeg hchart.1 f hf Q hQ D hD T hT
  ·
    have hQ' : R.residue xi ∈ Q.toValuationSubring := by
      rw [hxires]; exact (Q.toValuationSubring.mem_or_inv_mem _).resolve_left hQ
    exact mapDomain_eq_of_chart r D Q (fun P => Dom A P (xi : F)) (Red A R (xi : F))
      (fun P => hr₂ P Q hQ) _ fun T hT =>
        RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
          A R xi hx' hfin' hdeg' hchart' f hf Q hQ' D hD T hT

end main


end PlaceMapOrd
end RegularProlongation
end AlgebraicCurve

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart :
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h)) :
    ∃ r : Place L F → Place (IsLocalRing.ResidueField A) Fbar,
      ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f) :=
  AlgebraicCurve.RegularProlongation.PlaceMapOrd.main R x hx hfin hdeg hchart

