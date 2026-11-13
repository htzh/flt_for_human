/-
  SET-AF50B consumer: the residue map is surjective onto the integral closure at equal genus.

  **The zone.** One row, hence one composition, read off
  `FLTForHuman/AlgebraicCurve/RegularProlongationResidueIntegralClosure.lean`'s headline
  `AlgebraicCurve.RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq`:

    `∀ y ∈ integralClosure (ResidueField A) Fbar, ∃ f : R.integers, R.residue f = y`,

  in the two charts the headline states it for, `{R.residue x}` and `{(R.residue x)⁻¹}`.

  **The reading.** The consumer extracts the witness element of the chart dictionary — the
  `R.integers` element whose residue is a prescribed `h` — as a `private` definition
  (`chartWitness`), and then *reads its two defining properties back* (`chartWitness_spec`):
  integrality over `L⟮x⟯`, and the residue equation. That is a genuine composition: the
  witness is consumed, not restated.

  Zone B reads the same headline as an image statement: the set of elements of `Fbar` integral
  over `ResidueField A⟮R.residue x⟯` is contained in the residue image of the elements of
  `R.integers` integral over `L⟮x⟯`. The proof is the headline's first conjunct applied to the
  membership hypothesis, so the composition is executed and no hypothesis is added.

  Zone C composes the headline's *second* (inverse-chart) conjunct with the module's
  `ResidueIntegralClosure.adjoin_inv_eq`: an element integral over
  `ResidueField A⟮(R.residue x)⁻¹⟯` is the residue of an element integral over `L⟮x⟯` — the two
  charts are the same chart, and the substitution is discharged through `adjoin_inv_eq` and
  `isIntegral_of_subring_le`, not assumed.

  The chart data (`hx`, `hfin`, `hdeg`, `hgood`) cannot be instantiated concretely — they are
  properties of an arbitrary regular prolongation — so they enter in hypothesis form, which is
  the legitimate reading for this row. Any named carrier in the zone is `private`, so this file
  cannot leak into a port.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueIntegralClosure

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing Polynomial IntermediateField

namespace AlgebraicCurve.RegularProlongation

namespace AF50BConsumer

section Headline

variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
variable [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

/-- The witness of the chart dictionary at `h`: the element of `R.integers` whose residue is the
element `h` of the residue field's integral closure, extracted from the headline's first conjunct. -/
private noncomputable def chartWitness (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F)
    (h : Fbar) (hh : IsIntegral
      (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h) : R.integers :=
  ((residue_integralClosure_surjective_of_genusFF_eq A R x hx hfin hdeg hgood).1 h hh).choose

/-- **Zone A.** The witness is integral over `L⟮x⟯` and has residue `h`: the two conjuncts of the
extracted element, read back from the headline. -/
theorem consumer_zoneA_witness_spec (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F)
    (h : Fbar) (hh : IsIntegral
      (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h) :
    IsIntegral (Algebra.adjoin L {(x : F)}) ((chartWitness A R x hx hfin hdeg hgood h hh : R.integers) : F) ∧
      R.residue (chartWitness A R x hx hfin hdeg hgood h hh) = h :=
  ((residue_integralClosure_surjective_of_genusFF_eq A R x hx hfin hdeg hgood).1 h hh).choose_spec

/-- **Zone B.** The residue map's image contains every element of `Fbar` integral over
`ResidueField A⟮R.residue x⟯` and landing in `L⟮x⟯`-integral elements: the headline as an image
statement, applied to the membership hypothesis. -/
theorem consumer_zoneB_image_subset (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F) :
    {h : Fbar | IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h} ⊆
      R.residue '' {f : R.integers | IsIntegral (Algebra.adjoin L {(x : F)}) (f : F)} := by
  rintro h hh
  exact ⟨chartWitness A R x hx hfin hdeg hgood h hh,
    (consumer_zoneA_witness_spec A R x hx hfin hdeg hgood h hh).1,
    (consumer_zoneA_witness_spec A R x hx hfin hdeg hgood h hh).2⟩

end Headline

section ChartData

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

/-- **Zone C.** The chart data are invariant under `x ↦ x⁻¹`: the two adjoins `L⟮x⁻¹⟯` and `L⟮x⟯`
have the same codimension in `F`, and likewise `ResidueField A⟮(R.residue x)⁻¹⟯` and
`ResidueField A⟮R.residue x⟯` in `Fbar`. This is the substitution the headline's second conjunct
rests on, discharged through the module's `adjoin_inv_eq` composed with `finrank_congr_of_eq`. -/
theorem consumer_zoneC_chart_data_inv (R : RegularProlongation A F Fbar) (x : R.integers) :
    (Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({(R.residue x)⁻¹} : Set Fbar)) Fbar =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar) ∧
    (Module.finrank (IntermediateField.adjoin L ({(x : F)⁻¹} : Set F)) F =
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F) :=
  ⟨ResidueIntegralClosure.finrank_congr_of_eq
      (ResidueIntegralClosure.adjoin_inv_eq (R.residue x)),
    ResidueIntegralClosure.finrank_congr_of_eq
      (ResidueIntegralClosure.adjoin_inv_eq (x : F))⟩

end ChartData

section Headline

variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
variable [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

/-- **Zone D.** The inverse chart, with its hypotheses supplied in the inverse-chart form: Zone C
transfers `hfin` and `hdeg` back to the `x` chart, and the headline's second conjunct then delivers
an element of `R.integers` integral over `L⟮x⁻¹⟯` and with residue `h`. -/
theorem consumer_zoneD_inverse_chart (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin_inv : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R.residue x)⁻¹} : Set Fbar)) Fbar)
    (hdeg_inv : Module.finrank (IntermediateField.adjoin L ({(x : F)⁻¹} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({(R.residue x)⁻¹} : Set Fbar)) Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F)
    (h : Fbar) (hh : IsIntegral
      (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h) :
    ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h := by
  have hdata := consumer_zoneC_chart_data_inv R x
  have hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar := by
    rw [← hdata.1]
    exact hfin_inv
  have hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    hdata.2.symm.trans (hdeg_inv.trans hdata.1)
  exact (residue_integralClosure_surjective_of_genusFF_eq A R x hx hfin hdeg hgood).2 h hh

end Headline

end AF50BConsumer

end AlgebraicCurve.RegularProlongation
