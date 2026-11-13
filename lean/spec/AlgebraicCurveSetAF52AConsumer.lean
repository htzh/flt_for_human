/-
  SET-AF52A consumer: the ord equality from residue surjectivity, and the residue basis.

  **The zone.** Three rows, hence three compositions, read off the two modules of the set:

  * `FLTForHuman/AlgebraicCurve/RegularProlongationOrdResidueEquality.lean`:
    `AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective`;
  * `FLTForHuman/AlgebraicCurve/RegularProlongationResidueBasis.lean`:
    `…exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq` and
    `…finiteDimensional_adjoin_residue_of_sum_finrank_eq`.

  **The readings.**

  * Zone A. The ord equality is stated for an arbitrary divisor `D` together with the
    pointwise identification `hD : D P = P.ord (f : F)` and an arbitrary place set
    `T` filtered by the chart predicates `Dom`/`Red`. The consumer *instantiates* both: it
    takes `D` to be the principal divisor of `f` (`HasPrincipalDivisors.exists_divisor`,
    the canonical object of the theory) and `T` to be that divisor's support cut by
    `Dom ∧ Red`, discharging `hD` with the divisor's own specification. Zone A' then reads
    the headline in the degenerate case the level-lowering argument actually uses: when no
    chart place above `Q` carries the divisor, the residue has order zero at `Q`.
  * Zone B. The residue-basis headline is instantiated at `u = f` inside an arbitrary
    finite-dimensional `V ∋ f`: its spanning conjunct then produces an honest
    `A`-coefficient representation of `f` in a residue-independent family of `V`-elements.
  * Zone C. The finiteness headline supplies the missing `FiniteDimensional` instance for
    the residue extension at each `i`, which the consumer then *spends* by producing a
    `k`-basis of `Fb i` of the stated rank.

  The chart data (`hx`, `hfin`, `hdeg`, `hchart`) and the degree hypothesis `heq` cannot be
  instantiated concretely — they are properties of an arbitrary regular prolongation under
  the residue-surjectivity hypothesis — so they enter in hypothesis form, which is the
  legitimate reading for these rows. Every carrier in the zone is `private`, so this file
  cannot leak into a port.

  This module is outside every library: it is a spec-side composition check, not part of
  the port's import graph.
-/
import FLTForHuman.AlgebraicCurve.RegularProlongationOrdResidueEquality
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueBasis

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing Polynomial
open scoped Classical

namespace AlgebraicCurve.RegularProlongation

namespace AF52AConsumer

/-! ### Zone A: the ord equality at the principal divisor of `f` -/

section zoneA

variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
variable [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

/-- **Zone A.** The ord equality of a chart, read at the canonical divisor: `D` is the
principal divisor of `f` (so its `hD` is the divisor's specification, not an assumption),
and `T` is its support cut by the chart predicates `Dom`/`Red`. -/
theorem consumer_zoneA_canonical_divisor (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hf : R.residue f ≠ 0)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring) :
    ∃ D : Divisor L F, (∀ P, D P = P.ord (f : F)) ∧
      ∑ P ∈ D.support.filter (fun P => OrdResidueEquality.Dom A (x : F) P ∧
          OrdResidueEquality.Red A R (x : F) P Q), D P = Q.ord (R.residue f) := by
  have hf0 : (f : F) ≠ 0 := fun h => hf (by rw [show f = 0 from Subtype.ext h, map_zero])
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (f : F) hf0
  refine ⟨D, hD, ?_⟩
  exact sum_ord_eq_ord_residue_of_residue_integralClosure_surjective A R x hx hfin hdeg hchart
    f hf Q hQ D hD _
    (fun P => by rw [Finset.mem_filter, Finsupp.mem_support_iff]; exact Iff.rfl)

/-- **Zone A'.** The degenerate reading: if no chart place above `Q` occurs in the support of
`f`'s principal divisor, then `R.residue f` has order zero at `Q`. This is the form in which
the equality is consumed when the residue lands in the units at `Q`. -/
theorem consumer_zoneA_empty_support (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hf : R.residue f ≠ 0)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (hempty : ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
      D.support.filter (fun P => OrdResidueEquality.Dom A (x : F) P ∧
        OrdResidueEquality.Red A R (x : F) P Q) = ∅) :
    Q.ord (R.residue f) = 0 := by
  obtain ⟨D, hD, hsum⟩ :=
    consumer_zoneA_canonical_divisor A R x hx hfin hdeg hchart f hf Q hQ
  rw [hempty D hD, Finset.sum_empty] at hsum
  exact hsum.symm

end zoneA

/-! ### Zone B: the residue basis read at the chart element -/

section zoneBC

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]

/-- **Zone B.** The residue-basis headline instantiated at `u = f`: an `L`-basis `w` of a
finite-dimensional `V ∋ f`, whose joint residues are `k`-independent and all of whose members
lie in every integer ring, represents `f` with coefficients in `A`. The spanning conjunct of
the headline is what is *executed* here, at the one element the level-lowering argument
needs to be integral. -/
theorem consumer_zoneB_combination (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (V : Submodule L F) [FiniteDimensional L V] (hVf : f ∈ V) :
    ∃ w : Fin (Module.finrank L V) → F, ∃ hwO : ∀ a i, w a ∈ (R i).integers,
      (∀ a, w a ∈ V) ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun a => fun i => (R i).residue ⟨w a, hwO a i⟩) ∧
      ∃ c : Fin (Module.finrank L V) → A, f = ∑ a, (c a : L) • w a := by
  obtain ⟨w, hwO, hwV, hwLI, hspan⟩ :=
    exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq A Fb R hR f hf htr
      heq V
  exact ⟨w, hwO, hwV, hwLI, hspan f hf hVf⟩

/-! ### Zone C: the residue extension is finite, spent on a basis -/

/-- **Zone C.** The finiteness headline *supplies* the `FiniteDimensional` instance for the
residue extension at `i`; the consumer spends it by producing a `k`-basis of the prescribed
rank. This is the finiteness the residue-span rows consume, used, not restated. -/
theorem consumer_zoneC_basis (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (i : ι) :
    Nonempty (Module.Basis
      (Fin (Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)))
      (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)) := by
  have hfin : FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) :=
    finiteDimensional_adjoin_residue_of_sum_finrank_eq A Fb R hR f hf htr heq i
  exact ⟨Module.finBasis _ _⟩

end zoneBC

end AF52AConsumer

end AlgebraicCurve.RegularProlongation
