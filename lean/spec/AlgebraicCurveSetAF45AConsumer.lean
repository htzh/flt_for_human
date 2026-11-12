/-
  SET-AF45A consumer: the regular prolongation's residue calculus, read at one place.

  **The zone.** Two rows, hence two compositions, both read off
  `FLTForHuman/AlgebraicCurve/RegularProlongationFinrank.lean`'s two new headlines.

  Row A1 (`sum_finrank_adjoin_residue_le`) bounds a *sum* of residue degrees over a family of
  prolongations `R : ∀ i, RegularProlongation A F (Fb i)` by the single degree
  `finrank (adjoin L {f}) F`. Read at `ι = Fin 1` — the smallest family that is not empty — the sum
  is one term: the `Fin 1` sum collapses by `Fin.sum_univ_one`, and the conclusion becomes the
  one-step statement for a *single* prolongation `R 0`, namely that the residue degree
  `finrank (adjoin (ResidueField A) {residue f}) Fbar` is finite and no larger than the degree of
  `L(f)`. The antichain hypothesis `hR : Function.Injective fun i => (R i).integers` is
  *discharged*, not assumed: over `Fin 1` it is `Subsingleton.elim`. So the row is read at its
  sharpest non-degenerate instance.

  Row A2 (`exists_forall_residue_eq`) prescribes a residue at every member of a finite family and
  returns one element `z : F` that is integral at every member and whose residue is the prescribed
  one. Read at the singleton family `ι = Fin 1` with a prescribed nonzero residue `a₀`, it produces
  `z` integral at the single place `R 0` with `residue z = a₀` — and then *composes with
  the prolongation's own unit dictionary*: a nonzero residue makes `⟨z, h⟩` a unit of
  `R.integers` (`isUnit_of_residue_ne_zero`). That second leg is the point of the composition: the
  prescribed residue is not merely attained, it is attained by an integer that is invertible in the
  integers, which is what the residue calculus is used for (a unit in the integers divides every
  other integer).

  Again `hR` is discharged by `Subsingleton.elim`, since `Fin 1` is a subsingleton and `Finite _`
  is `Fin 1`'s own instance.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AlgebraicCurve.RegularProlongationFinrank

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace AlgebraicCurve.RegularProlongation

namespace W7XK3FIConsumer

/-- **Zone A.** Row A1 at `ι = Fin 1`: the family bound read at a single prolongation, where the
`Fin 1` sum is one term `finrank (adjoin (ResidueField A) {residue f}) Fbar`. The antichain
hypothesis is discharged by `Subsingleton.elim` on `Fin 1`. -/
theorem consumer_zoneA_single_finrank_le
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : Fin 1 → RegularProlongation A F Fbar)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F] :
    FiniteDimensional (IntermediateField.adjoin (ResidueField A)
        ({(R 0).residue ⟨f, hf 0⟩} : Set Fbar)) Fbar ∧
    Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R 0).residue ⟨f, hf 0⟩} : Set Fbar)) Fbar
      ≤ Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
  obtain ⟨hfin, hsum⟩ :=
    sum_finrank_adjoin_residue_le (ι := Fin 1) (Fb := fun _ => Fbar) A R
      (fun i _ _ => Subsingleton.elim i _) f hf htr
  refine ⟨hfin 0, ?_⟩
  simpa using hsum

/-- **Zone B.** Row A2 at the singleton family `ι = Fin 1` and a prescribed nonzero residue `a₀`:
one `z : F` is integral at the single place and `residue z = a₀`; composed with the prolongation's
unit dictionary, `⟨z, h⟩` is moreover a *unit* of the integers. -/
theorem consumer_zoneB_prescribed_residue_unit
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : Fin 1 → RegularProlongation A F Fbar)
    (a₀ : Fbar) (ha₀ : a₀ ≠ 0) :
    ∃ z : F, ∃ h : z ∈ (R 0).integers,
      (R 0).residue ⟨z, h⟩ = a₀ ∧ IsUnit (⟨z, h⟩ : (R 0).integers) := by
  obtain ⟨z, hz⟩ :=
    exists_forall_residue_eq (ι := Fin 1) (Fb := fun _ => Fbar) A R
      (fun i _ _ => Subsingleton.elim i _) (fun _ => a₀)
  obtain ⟨h, hres⟩ := hz 0
  exact ⟨z, h, hres, (R 0).isUnit_of_residue_ne_zero (by rw [hres]; exact ha₀)⟩

end W7XK3FIConsumer

end AlgebraicCurve.RegularProlongation
