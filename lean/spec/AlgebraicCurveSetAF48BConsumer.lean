/-
  SET-AF48B consumer: Deuring's multiplicity inequality read at the empty chart divisor.

  **The zone.** One row, hence one composition, read off
  `FLTForHuman/AlgebraicCurve/DeuringMultiplicity.lean`'s headline
  `AlgebraicCurve.RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin`:

    `Q.ord (R.residue f) ≤ ∑ P ∈ T, D P`,

  where `T` is the finite set of places of `F` on the chart that the residue map sends
  into `Q`'s nonunits and that carry a pole of `f`.

  **The reading.** The consumer substitutes `T = ∅` and `D = 0`, and *discharges* — rather
  than assumes — both substitution obligations:

  * `hT`, the defining property `∀ P, P ∈ T ↔ (D P ≠ 0 ∧ …)`, is not a hypothesis: with
    `D = 0` its right-hand side is `0 ≠ 0 ∧ …`, so it holds at every place, and the proof is
    `simp`;
  * `hD`, the identity `∀ P, D P = P.ord (f : F)`, is the single real hypothesis
    `hf0 : ∀ P, P.ord (f : F) = 0` — `f` is a chart integral element with no order anywhere,
    the chart analogue of a unit.

  What comes back is the inequality with its right-hand side collapsed: the empty sum is
  `0`, so the statement reads `Q.ord (R.residue f) ≤ 0` — Deuring's bound says a chart
  integral `f` that is nowhere a pole outside `T` cannot have a pole at `Q` either. This is
  the shape the residue-degree argument of the level-lowering step consumes, at the
  degenerate end where no place of `F` survives the chart.

  The chart hypotheses (`hx`, `hfin`, `hdeg`, `hchart`, `hfi`, `hf`, `hQ`) are carried as
  hypotheses of the consumer: it is a composition check, not a new theorem about curves.
  Any named instance in the zone is `private`, so this file cannot leak into a port.

  This module is outside every library: it is a spec-side composition check, not part of
  the port's import graph.
-/
import FLTForHuman.AlgebraicCurve.DeuringMultiplicity

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace AlgebraicCurve.RegularProlongation

namespace AF48BConsumer

/-- **Zone A.** The inequality at `T = ∅`, `D = 0`: both substitution obligations are
discharged, so the conclusion is `Q.ord (R.residue f) ≤ 0` with no divisor and no finite
set of places left. -/
theorem consumer_ord_residue_le_zero_of_forall_ord_eq_zero
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [IsCurveOver (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0)
    (Q : Place (ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (hf0 : ∀ P : Place L F, P.ord (f : F) = 0) :
    Q.ord (R.residue f) ≤ 0 := by
  classical
  -- the substitution `D = 0`
  have hzero : ∀ P : Place L F, (0 : Divisor L F) P = P.ord (f : F) := by
    intro P
    rw [Finsupp.zero_apply, hf0 P]
  -- the substitution `T = ∅`: the defining property of `T` holds vacuously, because
  -- `D = 0` kills its first conjunct
  have hempty : ∀ P : Place L F, P ∈ (∅ : Finset (Place L F)) ↔
      ((0 : Divisor L F) P ≠ 0 ∧
        (∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
        ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
          ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
            R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈
              Q.toValuationSubring.nonunits) := by
    intro P
    simp [hzero P, hf0 P]
  -- the composition: the port's headline, instantiated
  have h := ord_residue_le_sum_ord_of_isIntegral_adjoin A R x hx hfin hdeg hchart f hfi hf
    Q hQ (0 : Divisor L F) hzero (∅ : Finset (Place L F)) hempty
  simpa using h

end AF48BConsumer

end AlgebraicCurve.RegularProlongation
