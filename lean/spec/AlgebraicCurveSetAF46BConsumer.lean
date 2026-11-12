/-
  SET-AF46B consumer: the Gauss basis of the residue map, read at the two sharpest non-degenerate
  instances.

  **The zone.** Two rows, hence two compositions, both read off
  `FLTForHuman/AlgebraicCurve/RegularProlongationGaussBasis.lean`'s two headlines.

  Row A (`exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq`) carries three
  conjuncts: integrality of the family `z` at every valuation, **uniqueness of the representation**
  (two polynomial families with the same residues of one and the same `z` are equal), and the spanning
  property. Read at `ι = Fin 1` — the smallest family that is not empty — the degree hypothesis
  `∑ i, finrank (adjoin (ResidueField A) {residue f}) (Fb i) = finrank (adjoin L {f}) F` collapses to its
  one term (by `Fin.sum_univ_one`), and the antichain hypothesis `hR : Function.Injective fun i =>
  (R i).integers` is *discharged*, not assumed: over `Fin 1` it is `Subsingleton.elim`. The consumer
  supplies the *single-place* degree equality and returns the uniqueness conjunct itself, so the
  composition produces the residue-basis uniqueness statement of a single prolongation.

  Row B (`coe_minpoly_adjoin_coeff_mem_integers`) says the `j`-th coefficient of the `minpoly` over
  `L[x]` of an element satisfying the row's valuation hypothesis lies in the prolongation's integers.
  The consumer reads it at the concrete element `f = x` (the trace element of the row) and the concrete
  coefficient `j = 0`, and *discharges* both hypotheses rather than assuming them: `x` is integral over
  `L[x]` because it is in it (`isIntegral_algebraMap`), and the valuation hypothesis at `f = x` is the
  triviality that `x ∈ R.integers` and `x ∈ L[x]` put `x` in every valuation subring that contains
  `L[x]`'s integers. What comes back is a statement about `R` alone — the constant coefficient of
  `minpoly_{L[x]} x` is integral, with no free `f` left.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.AlgebraicCurve.RegularProlongationGaussBasis

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace AlgebraicCurve.RegularProlongation

namespace W10XK3ER2BConsumer

/-- **Zone A.** The uniqueness conjunct at the singleton family `ι = Fin 1`: the degree hypothesis is
the one-place equality (the `Fin 1` sum is one term) and the antichain hypothesis is
`Subsingleton.elim`. The conclusion is the statement itself — uniqueness of the residue representation
in the Gauss basis of a single prolongation. -/
theorem consumer_zoneA_uniqueRepr_singleton
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : Fin 1 → RegularProlongation A F Fbar)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (hcomplete : ∀ W : ValuationSubring F,
      (∀ e ∈ IntermediateField.adjoin L ({f} : Set F), e ∈ W ↔ e ∈ (R 0).integers) →
      ∃ j, W = (R j).integers)
    (hdeg : Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R 0).residue ⟨f, hf 0⟩} : Set Fbar)) Fbar
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (d' : ℕ) (z : Fin d' → F) (hzO : ∀ σ i, z σ ∈ (R i).integers),
      ∀ q q' : Fin d' → Polynomial (ResidueField A),
        (∀ i, ∑ σ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q σ)
            * (R i).residue ⟨z σ, hzO σ i⟩
          = ∑ σ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q' σ)
            * (R i).residue ⟨z σ, hzO σ i⟩) →
        q = q' := by
  have hdeg' : ∑ i : Fin 1, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set Fbar)) Fbar
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
    rw [Fin.sum_univ_one]; exact hdeg
  obtain ⟨d', z, hzO, -, huniq, -⟩ :=
    exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq (Fb := fun _ => Fbar)
      A R (fun i _ _ => Subsingleton.elim i _) f hf htrL hfd htr 0 hcomplete hdeg'
  exact ⟨d', z, hzO, huniq⟩

/-- **Zone B.** The coefficient criterion at the concrete element `f = x` and the concrete coefficient
`j = 0`: both the integrality hypothesis and the valuation hypothesis of the row are discharged, so the
conclusion mentions `R` and `x` only. -/
theorem consumer_zoneB_minpoly_coeff_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x)) :
    (((minpoly (Algebra.adjoin L ({(x : F)} : Set F)) (x : F)).coeff 0 :
      Algebra.adjoin L ({(x : F)} : Set F)) : F) ∈ R.integers := by
  have hxS : (x : F) ∈ Algebra.adjoin L ({(x : F)} : Set F) :=
    Algebra.self_mem_adjoin_singleton L (x : F)
  have hxK : (x : F) ∈ IntermediateField.adjoin L ({(x : F)} : Set F) :=
    IntermediateField.mem_adjoin_simple_self L (x : F)
  refine coe_minpoly_adjoin_coeff_mem_integers A R x hx (x : F) ?_ ?_ 0
  · simpa using isIntegral_algebraMap (R := Algebra.adjoin L ({(x : F)} : Set F)) (A := F)
      (x := (⟨(x : F), hxS⟩ : Algebra.adjoin L ({(x : F)} : Set F)))
  · intro V hV
    exact (hV (x : F) hxK).mpr x.2

end W10XK3ER2BConsumer

end AlgebraicCurve.RegularProlongation
