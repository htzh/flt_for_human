/-
  SET-AF50A consumer: the sum of the orders of an element and of its residue.

  **The zone.** One row, hence one composition, read off
  `FLTForHuman/AlgebraicCurve/RegularProlongationSumOrdResidue.lean`'s headline
  `AlgebraicCurve.RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin`:

    `∑ P ∈ TP, D P = ∑ Q ∈ TQ, Dbar Q`,

  with `D` the order divisor of `f` and `Dbar` the order divisor of `R.residue f`, restricted to
  the chart's places (`Dom R x`) and to the residue field's places above `R.residue x` (`Fnt R x`).

  **The reading.** The headline is stated for an arbitrary pair of divisors `(D, Dbar)` together
  with pointwise identification hypotheses `hD`/`hDbar`. The consumer *instantiates* those
  hypotheses at the canonical pair `(divOf L (f : F), divOf (ResidueField A) (R.residue f))` and
  discharges them with the module's `divOf_apply` — so the composition is executed, not restated:
  `consumer_zoneA_canonical_divisor` is the headline applied to the divisors that actually occur
  in the level-lowering argument, and `consumer_zoneB_zsum` then reads that equality back in the
  `zsum` notation the rest of the chart dictionary is phrased in.

  The chart data (`hx`, `hfin`, `hdeg`, `hchart`) cannot be instantiated concretely — they are
  properties of an arbitrary regular prolongation — so they enter in hypothesis form, which is the
  legitimate reading for this row. Any named carrier in the zone is `private`, so this file cannot
  leak into a port.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AlgebraicCurve.RegularProlongationSumOrdResidue

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing Polynomial
open scoped Classical

namespace AlgebraicCurve.RegularProlongation

namespace AF50AConsumer

open AlgebraicCurve.RegularProlongation.SumOrdResidue

variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
variable [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

/-- **Zone A.** The headline applied to the canonical divisors: the order divisor of `f` filtered
to the chart's places, and the order divisor of `R.residue f` filtered to the residue places over
`R.residue x`. The two identifications the headline asks for are `divOf_apply`, so the composition
is a genuine instantiation of the hypothesis-form headline. -/
theorem consumer_zoneA_canonical_divisor (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0) :
    ∑ P ∈ (divOf L (f : F)).support.filter (Dom R x), P.ord (f : F) =
      ∑ Q ∈ (divOf (IsLocalRing.ResidueField A) (R.residue f)).support.filter (Fnt R x),
        Q.ord (R.residue f) := by
  have hmain := sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin A R x hx hfin hdeg hchart f hfi hf
    (divOf L (f : F)) (fun P => divOf_apply _ _)
    (divOf (IsLocalRing.ResidueField A) (R.residue f)) (fun Q => divOf_apply _ _)
    ((divOf L (f : F)).support.filter (Dom R x)) (fun P => by
      rw [Finset.mem_filter, Finsupp.mem_support_iff, divOf_apply]
      exact Iff.rfl)
    ((divOf (IsLocalRing.ResidueField A) (R.residue f)).support.filter (Fnt R x)) (fun Q => by
      rw [Finset.mem_filter, Finsupp.mem_support_iff, divOf_apply]
      exact Iff.rfl)
  calc ∑ P ∈ (divOf L (f : F)).support.filter (Dom R x), P.ord (f : F)
      = ∑ P ∈ (divOf L (f : F)).support.filter (Dom R x), divOf L (f : F) P :=
        Finset.sum_congr rfl fun P _ => (divOf_apply _ _).symm
    _ = ∑ Q ∈ (divOf (IsLocalRing.ResidueField A) (R.residue f)).support.filter (Fnt R x),
          divOf (IsLocalRing.ResidueField A) (R.residue f) Q := hmain
    _ = ∑ Q ∈ (divOf (IsLocalRing.ResidueField A) (R.residue f)).support.filter (Fnt R x),
          Q.ord (R.residue f) :=
        Finset.sum_congr rfl fun Q _ => divOf_apply _ _

/-- **Zone B.** The same equality read back through the `zsum` abbreviation the chart dictionary is
phrased in: `zsum (Dom R x) f = zsum (Fnt R x) (R.residue f)`. This composes the headline (via
Zone A) with the definition of `zsum`, so the consumed statement is the headline's divisors, not
the `zsum` form. -/
theorem consumer_zoneB_zsum (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0) :
    zsum (Dom R x) (f : F) = zsum (Fnt R x) (R.residue f) := by
  have hA := consumer_zoneA_canonical_divisor A R x hx hfin hdeg hchart f hfi hf
  have hL : zsum (Dom R x) (f : F) =
      ∑ P ∈ (divOf L (f : F)).support.filter (Dom R x), P.ord (f : F) := rfl
  have hR : zsum (Fnt R x) (R.residue f) =
      ∑ Q ∈ (divOf (IsLocalRing.ResidueField A) (R.residue f)).support.filter (Fnt R x),
        Q.ord (R.residue f) := rfl
  rw [hL, hR, hA]

end AF50AConsumer

end AlgebraicCurve.RegularProlongation
