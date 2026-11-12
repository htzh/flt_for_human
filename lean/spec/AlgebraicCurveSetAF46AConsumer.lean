/-
  SET-AF46A consumer: the residue span's rank and its comparison with the `L²` span, read at the two
  sharpest non-degenerate instances.

  **The zone.** Two rows, hence two compositions, both read off
  `FLTForHuman/AlgebraicCurve/RegularProlongationResidueSpan.lean`'s two headlines.

  Row A (`finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq`) says the residue span of an
  *arbitrary* subspace `V` of `F` has, over a family of prolongations, exactly `V`'s `L`-dimension.
  Read at `ι = Fin 1` — the smallest family that is not empty — the hypothesis
  `∑ i, finrank (adjoin (ResidueField A) {residue f}) (Fb i) = finrank (adjoin L {f}) F` collapses
  to its one term `finrank (adjoin (ResidueField A) {residue f}) Fbar = finrank (adjoin L {f}) F`
  (by `Fin.sum_univ_one`), so the consumer supplies the *single-place* degree equality and gets back
  the equality at a single prolongation. The antichain hypothesis
  `hR : Function.Injective fun i => (R i).integers` is *discharged*, not assumed: over `Fin 1` it is
  `Subsingleton.elim`.

  Row B (`span_residue_lSpace_le_residueSpan_inf`) says the residue span of `LSpace (M • D)` sits
  inside the intersection of the two *integrality* residue spans — the one read at the places
  containing `f`, and the one read at the places containing `f⁻¹` twisted by `(f ^ M)⁻¹`. Read at
  `M = 0`, the twisting factor is `(f ^ 0)⁻¹ = 1`, so the second branch *is* the plain
  "integral at every place containing `f⁻¹`" branch. That is the point of the composition: the
  `L²` inclusion is untwisted at `M = 0`, and a member of the left span is landed in both branches
  explicitly.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueSpan

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace AlgebraicCurve.RegularProlongation

namespace W10XK3ER2Consumer

/-- **Zone A.** The rank equality at the singleton family `ι = Fin 1`: the hypothesis is the
one-place degree equality (the `Fin 1` sum is one term), the antichain hypothesis is
`Subsingleton.elim`, and the conclusion is the exact-dimension statement for a single
prolongation. -/
theorem consumer_zoneA_single_finrank_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : Fin 1 → RegularProlongation A F Fbar)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (hdeg : Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R 0).residue ⟨f, hf 0⟩} : Set Fbar)) Fbar
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (ResidueField A) (Submodule.span (ResidueField A)
        {h : Fin 1 → Fbar | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) =
      Module.finrank L V := by
  have hdeg' : ∑ i : Fin 1, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set Fbar)) Fbar
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
    rw [Fin.sum_univ_one]; exact hdeg
  exact finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq (Fb := fun _ => Fbar) A R
    (fun i _ _ => Subsingleton.elim i _) f hf htr hdeg' V

/-- **Zone B.** The `L²` inclusion read at `M = 0`: the two branches of the intersection, with the
second one untwisted because `(f ^ 0)⁻¹ = 1`. -/
theorem consumer_zoneB_lSpace_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (D : Divisor L F) (hD : ∀ v : Place L F, D v = max 0 (-v.ord f))
    (h : ∀ i, Fb i)
    (hh : h ∈ Submodule.span (ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        u ∈ LSpace ((0 : ℕ) • D) ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) :
    h ∈ Submodule.span (ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ∧
      h ∈ Submodule.span (ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by
  have hinc := span_residue_lSpace_le_residueSpan_inf (Fb := Fb) (M := 0) A R f hf hfd D hD
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp (hinc hh)
  refine ⟨h1, ?_⟩
  refine Submodule.span_mono ?_ h2
  rintro x ⟨u, hu, hV, hres⟩
  exact ⟨u, hu, fun V hVL hfi => by simpa using hV V hVL hfi, hres⟩

end W10XK3ER2Consumer

end AlgebraicCurve.RegularProlongation
