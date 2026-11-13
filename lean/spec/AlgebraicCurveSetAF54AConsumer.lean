/-
  SET-AF54A consumer: the place map's ord dictionary, and the non-unit multiple.

  **The zone.** Two rows, hence two compositions, read off the two modules of the set:

  * `FLTForHuman/AlgebraicCurve/RegularProlongationPlaceMapOrd.lean`:
    `AlgebraicCurve.RegularProlongation.exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective`;
  * `FLTForHuman/AlgebraicCurve/RegularProlongationNonunitSmul.lean`:
    `…exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq`.

  **The readings.**

  * Zone A. The headline produces the place map `r : Place L F → Place (ResidueField A) Fbar`
    and asserts `Finsupp.mapDomain r D Q = Q.ord (R.residue f)` for an arbitrary divisor `D`
    carrying the pointwise identification `hD : D P = P.ord (f : F)`. The consumer *executes*
    that at the canonical data — `D` the order divisor of `f` and `hD` its specification — and
    then spends the result twice: Zone A rewrites the map-domain sum through the module's own
    `PlaceMapOrd.mapDomain_eq_sum_filter`, so the identity is read as a *fiber sum*
    `∑ P with r P = Q` over the divisor's support; Zone A' turns that fiber sum into the
    non-emptiness statement the dictionary is used for — a nonzero order of `R.residue f` at `Q`
    forces some place of `D`'s support above `Q`.
  * Zone B. The non-unit-multiple headline produces `a : A` with `¬ IsUnit a` and `u' ∈ V ∩ ⋂ᵢ
    (R i).integers` with `u = (a : L) • u'`. The consumer *spends* the non-unitness: a non-unit
    of the valuation ring `A` has vanishing residue at the maximal ideal, which is exactly what
    the residue-span argument consumes. Zone B' reads the same conclusion when `u ≠ 0`: the
    multiple is a genuine factorization, so `u' ≠ 0` as well.

  The chart data (`hx`, `hfin`, `hdeg`, `hchart`) and the degree hypothesis `heq` cannot be
  instantiated concretely — they are properties of an arbitrary regular prolongation under the
  residue-surjectivity hypothesis — so they enter in hypothesis form, which is the legitimate
  reading for these rows.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AlgebraicCurve.RegularProlongationPlaceMapOrd
import FLTForHuman.AlgebraicCurve.RegularProlongationNonunitSmul

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace AlgebraicCurve.RegularProlongation

namespace AF54AConsumer

/-! ### Zone A: the place map's fibers compute the order -/

section zoneA

variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
variable [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

/-- The fiber sum of the dictionary cuts the divisor's support by a proposition about places, so
the reading needs decidable equality on both families of places. -/
private instance : DecidableEq (Place L F) := Classical.decEq _

private instance : DecidableEq (Place (IsLocalRing.ResidueField A) Fbar) := Classical.decEq _

/-- **Zone A.** The ord dictionary, read at the canonical divisor of `f`: the headline supplies
the place map `r`, and the module's abstract chart lemma turns the map-domain sum into the fiber
sum over `D`'s support. So the order of `R.residue f` at `Q` *is* the sum of the divisor over the
places above `Q`. -/
theorem consumer_zoneA_fiber_sum (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart :
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h))
    (f : R.integers) (hf : R.residue f ≠ 0) (D : Divisor L F)
    (hD : ∀ P, D P = P.ord (f : F)) :
    ∃ r : Place L F → Place (IsLocalRing.ResidueField A) Fbar,
      ∀ Q, ∑ P ∈ D.support with r P = Q, D P = Q.ord (R.residue f) := by
  classical
  obtain ⟨r, hr⟩ :=
    exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective
      A R x hx hfin hdeg hchart
  refine ⟨r, fun Q => ?_⟩
  rw [← hr f hf D hD Q]
  exact (PlaceMapOrd.mapDomain_eq_sum_filter r D Q).symm

/-- **Zone A'.** The fiber sum of Zone A, spent: if the residue has nonzero order at `Q`, then
some place of `D`'s support maps to `Q`. This is the shape in which the dictionary feeds the
level-lowering argument (a vanishing fiber sum forces vanishing order). -/
theorem consumer_zoneA_fiber_nonempty (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart :
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h))
    (f : R.integers) (hf : R.residue f ≠ 0) (D : Divisor L F)
    (hD : ∀ P, D P = P.ord (f : F)) :
    ∃ r : Place L F → Place (IsLocalRing.ResidueField A) Fbar,
      ∀ Q, Q.ord (R.residue f) ≠ 0 → (D.support.filter fun P => r P = Q).Nonempty := by
  obtain ⟨r, hr⟩ := consumer_zoneA_fiber_sum A R x hx hfin hdeg hchart f hf D hD
  refine ⟨r, fun Q hQ => ?_⟩
  have h := hr Q
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  rw [hempty, Finset.sum_empty] at h
  exact hQ h.symm

end zoneA

/-! ### Zone B: the non-unit multiple, spent at the maximal ideal -/

section zoneB

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
  [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]

/-- **Zone B.** The non-unit multiple headline, read at the maximal ideal: the produced `a : A` is
a non-unit of the valuation ring, so its residue vanishes and `u` is a genuine non-unit multiple
of an element of `V` that is integral at every chart. That vanishing residue is what the
residue-span argument consumes. -/
theorem consumer_zoneB_nonunit_residue_zero
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (V : Submodule L F) [FiniteDimensional L V]
    (u : F) (huO : ∀ i, u ∈ (R i).integers) (huV : u ∈ V)
    (hres : ∀ i, (R i).residue ⟨u, huO i⟩ = 0) :
    ∃ a : A, ¬ IsUnit a ∧ IsLocalRing.residue A a = 0 ∧
      ∃ u' : F, (∀ i, u' ∈ (R i).integers) ∧ u' ∈ V ∧ u = (a : L) • u' := by
  obtain ⟨a, u', hnu, hu'O, hu'V, hua⟩ :=
    exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
      A Fb R hR f hf htr heq V u huO huV hres
  refine ⟨a, hnu, ?_, u', hu'O, hu'V, hua⟩
  exact (IsLocalRing.residue_eq_zero_iff a).mpr
    ((IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hnu))

/-- **Zone B'.** The same multiple when `u ≠ 0`: the factorization is genuine, so the cofactor
`u'` is nonzero too — the non-unit multiple does not degenerate to `0 = 0`. -/
theorem consumer_zoneB_cofactor_ne_zero
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (V : Submodule L F) [FiniteDimensional L V]
    (u : F) (huO : ∀ i, u ∈ (R i).integers) (huV : u ∈ V)
    (hres : ∀ i, (R i).residue ⟨u, huO i⟩ = 0) (hu : u ≠ 0) :
    ∃ a : A, ¬ IsUnit a ∧ ∃ u' : F, u' ≠ 0 ∧ (∀ i, u' ∈ (R i).integers) ∧ u' ∈ V ∧
      u = (a : L) • u' := by
  obtain ⟨a, u', hnu, hu'O, hu'V, hua⟩ :=
    exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
      A Fb R hR f hf htr heq V u huO huV hres
  refine ⟨a, hnu, u', ?_, hu'O, hu'V, hua⟩
  rintro rfl
  apply hu
  rw [hua, smul_zero]

end zoneB

end AF54AConsumer

end AlgebraicCurve.RegularProlongation
