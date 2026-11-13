/-
  SET-AF48A consumer: the reduced place of a chart, read at the three places where the
  existence-and-uniqueness headline can actually be *executed*.

  **The zone.** `FLTForHuman/AlgebraicCurve/RegularProlongationReducedPlace.lean`'s headline
  `existsUnique_place_forall_residue_sub_mem_nonunits` (the pin's `solution`, its `main` body) is an
  `∃!` over places `Q` of the residue field `Fbar` of a regular prolongation, characterized by the
  residue condition

      `h - a` a `P`-non-unit  ⟹  `R.residue h - ā` a `Q`-non-unit

  for every *integral* `h` of the integers and every constant `a` of `A`. Discharging the chart
  hypotheses (`hx`, `hfin`, `hdeg`, `hchart`) at a concrete curve would mean constructing a regular
  prolongation with all four properties, which is the *next* wave's business; so, as the work order
  allows, the hypotheses are stated and the two halves of the `∃!` are executed:

  * **Zone A** — the uniqueness half: two places satisfying the residue condition are equal
    (`(huniq Q hQ).trans (huniq Q' hQ').symm`).
  * **Zone B** — the existence half *and* one real consequence: at the chart point `x` itself
    (`isIntegral_self`) and a witness `a₀` of `hP`, the reduced difference
    `R.residue x - algebraMap _ Fbar (residue A a₀)` is a `Q`-non-unit, and then
    `ne_top_of_mem_nonunits` (this module's own lemma, applied to transcendence for the nonzero side
    condition `residue x - c ≠ 0`) makes `Q.toValuationSubring` a *proper* valuation subring. That is
    the composition: `main`'s witness ∘ `ne_top_of_mem_nonunits` ∘ `Transcendental`.
  * **Zone C** — a genuine `Place` from a *different* module, `Place.ofHeightOneSpectrum`, plugged
    into the uniqueness half: a place `Q` with the residue condition and the concrete place of a
    height-one spectrum `w` with the residue condition are the same place, and the identification of
    their valuation subrings follows by rewriting with `ofHeightOneSpectrum_toValuationSubring`.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.AlgebraicCurve.RegularProlongationReducedPlace

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace AlgebraicCurve.RegularProlongation.ReducedPlace

namespace AF48AConsumer

/-- The residue condition of the headline, as a predicate on places, so that the three rows below
can name the two halves of the `∃!` without restating the statement. It is the headline's conclusion
with the chart data `R`, `x`, `P` made explicit; `main`'s statement is definitionally
`∃! Q, ResidueCond R x P Q`. -/
def ResidueCond {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) : Prop :=
  ∀ h : R.integers, IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (h : F) →
    ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
      R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
        Q.toValuationSubring.nonunits

/-- **Zone A.** The uniqueness half of the headline: two places of `Fbar` with the residue condition
coincide. Read through `ResidueCond`, so `main`'s conclusion and `hQ`/`hQ'` are the *same*
proposition. -/
theorem consumer_zoneA_unique {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar,
      IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (P : Place L F)
    (hP : ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits)
    (Q Q' : Place (IsLocalRing.ResidueField A) Fbar)
    (hQ : ResidueCond R x P Q) (hQ' : ResidueCond R x P Q') : Q = Q' := by
  obtain ⟨Q₀, -, huniq⟩ := main R x hx hfin hdeg hchart P hP
  exact (huniq Q hQ).trans (huniq Q' hQ').symm

/-- **Zone B.** The existence half, composed with this module's `ne_top_of_mem_nonunits` and the
transcendence of `R.residue x`: at the chart point `x` and a witness `a₀` of `hP`, the reduced
difference is a non-unit of the produced place, and that place's valuation subring is *proper*. -/
theorem consumer_zoneB_exists_nontrivial {L : Type*} [Field L] [IsAlgClosed L]
    {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar,
      IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (P : Place L F)
    (hP : ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits)
    (a₀ : A) (ha₀ : (x : F) - algebraMap L F a₀ ∈ P.toValuationSubring.nonunits) :
    ∃ Q : Place (IsLocalRing.ResidueField A) Fbar,
      ResidueCond R x P Q ∧
        R.residue x - algebraMap (IsLocalRing.ResidueField A) Fbar
            (IsLocalRing.residue A a₀) ∈ Q.toValuationSubring.nonunits ∧
          Q.toValuationSubring ≠ ⊤ := by
  obtain ⟨Q, hQ, -⟩ := main R x hx hfin hdeg hchart P hP
  have hmem := hQ x (isIntegral_self (x : F)) a₀ ha₀
  refine ⟨Q, hQ, hmem, ne_top_of_mem_nonunits hmem ?_⟩
  intro h0
  apply hx
  rw [sub_eq_zero] at h0
  rw [h0]
  exact isAlgebraic_algebraMap _

/-- **Zone C.** A `Place` built by a *different* module's constructor (`Place.ofHeightOneSpectrum`)
with the residue condition is the same place as any place with the residue condition, and their
valuation subrings agree by the constructor's own projection lemma. -/
theorem consumer_zoneC_heightOneSpectrum {L : Type*} [Field L] [IsAlgClosed L]
    {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar,
      IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (P : Place L F)
    (hP : ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : ResidueCond R x P Q)
    {R₀ : Type*} [CommRing R₀] [IsDedekindDomain R₀] [Algebra R₀ Fbar] [IsFractionRing R₀ Fbar]
    [Algebra (IsLocalRing.ResidueField A) R₀]
    [IsScalarTower (IsLocalRing.ResidueField A) R₀ Fbar]
    (w : IsDedekindDomain.HeightOneSpectrum R₀)
    (hw : ResidueCond R x P (Place.ofHeightOneSpectrum (K := IsLocalRing.ResidueField A) w)) :
    Q = Place.ofHeightOneSpectrum (K := IsLocalRing.ResidueField A) w ∧
      Q.toValuationSubring = (w.valuation Fbar).valuationSubring := by
  obtain ⟨Q₀, -, huniq⟩ := main R x hx hfin hdeg hchart P hP
  have h1 : Q = Q₀ := huniq Q hQ
  have h2 : Place.ofHeightOneSpectrum (K := IsLocalRing.ResidueField A) w = Q₀ := huniq _ hw
  refine ⟨h1.trans h2.symm, ?_⟩
  rw [h1, h2.symm, Place.ofHeightOneSpectrum_toValuationSubring]

end AF48AConsumer

end AlgebraicCurve.RegularProlongation.ReducedPlace
