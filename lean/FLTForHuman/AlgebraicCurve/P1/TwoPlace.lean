/-
TwoPlace — the atom-2 two-place cancellation tail of the ℙ¹ residue core.

Port of the unique tail of
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero.lean`
(pin `anthropics/fermats-last-theorem@aa2d8b3`), the sibling of the master
ℙ¹ file already ported as the `P1/` chain. The shared engine is imported from
`P1/Core`; only the declarations absent from the port are transcribed, stated
at the pin's `placeInfty` spelling (definitionally the port's `p1PlaceInfty`).
-/
import FLTForHuman.AlgebraicCurve.P1.Core

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open KaehlerDifferential
open scoped IntermediateField
open AlgebraicCurve

namespace AlgebraicCurve

open RationalFunctionField

set_option autoImplicit false

section TwoPlaceCancelMOne

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

/-- The two-place (`finitePlace` + `placeInfty`) cancellation row for the
principal-part atom `p1PrincipalPartAtom K p c 1`. -/
def P1PrincipalPartTwoPlaceCancelMOne {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1))
        (finitePlace K hpirr)
      + kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1))
          (placeInfty K)
      = 0

variable {K}

omit [DecidableEq (RatFunc K)] [∀ v : Place K (RatFunc K), v.DCoordGenerates] in
/-- A residue term whose differential form already lies in the simple-pole
submodule is the trace of its simple-pole residue. -/
theorem kaehlerResidueTerm_eq_of_mem_simplePoleSubmodule
    {ω : Ω[(RatFunc K)⁄K]} {f : RatFunc K} {v : Place K (RatFunc K)}
    (hmem : f * v.differentialCoeff ω ∈ v.simplePoleSubmodule) :
    kaehlerResidueTerm ω (diagonalHom K (RatFunc K) f) v
      = Algebra.trace K v.ResidueField (v.simplePoleResidueAux ⟨_, hmem⟩) := by
  unfold kaehlerResidueTerm
  rw [diagonalHom_apply, v.localResidue_simplePole _ hmem]
  rfl

/-- The two-place cancellation reduces to the one-place (simple-pole)
cancellation plus the two membership facts. -/
theorem p1PrincipalPartTwoPlaceCancelMOne_of_simplePoleCancel
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0)
    (hInfty : (placeInfty K).ordDifferential ω₀ = -2)
    (hSimple : P1PrincipalPartMOneSimplePoleCancel K hω₀) :
    P1PrincipalPartTwoPlaceCancelMOne K hω₀ := by
  intro p c hpmon hpirr hdeg
  have hfmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace K hω₀
    hunit hpirr c hdeg
  have himem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K hω₀
    hInfty hpirr c hdeg
  rw [kaehlerResidueTerm_eq_of_mem_simplePoleSubmodule hfmem,
    kaehlerResidueTerm_eq_of_mem_simplePoleSubmodule himem]
  exact hSimple p c hpmon hpirr hdeg hfmem himem

end TwoPlaceCancelMOne

section TwoPlaceCancelMOnePerfect

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

/-- Two-place cancellation for `dX`, from the placed-at-`∞` Euler value. -/
theorem ag9b12c_p1TwoPlaceCancelMOne_dX_of_inftyEulerValue_of_perfectField
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K) :=
  p1PrincipalPartTwoPlaceCancelMOne_of_simplePoleCancel (dX_ne_zero K)
    (p1DifferentialCoeffUnitFinite_dX_of_perfectField K)
    (ordDifferential_dX_placeInfty_of_perfectField K)
    (ag9b12c_p1MOneSimplePoleCancel_dX_of_inftyEulerValue_of_perfectField K hinf)

/-- Two-place cancellation for `dX`, over a perfect field. -/
theorem ag9b13e_p1TwoPlaceCancelMOne_dX_of_perfectField :
    P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K) :=
  ag9b12c_p1TwoPlaceCancelMOne_dX_of_inftyEulerValue_of_perfectField K
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValue_of_perfectField K)

end TwoPlaceCancelMOnePerfect

namespace RationalFunctionField

/-- The atom-2 headline: the sum of the traces of the `finitePlace` and
`placeInfty` residues of `c/p · dX` vanishes. -/
theorem trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    {p c : K[X]} (hmon : p.Monic) (hp : Irreducible p) (hc : c.degree < p.degree) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.finitePlace K hp).ResidueField
        ((AlgebraicCurve.RationalFunctionField.finitePlace K hp).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.finitePlace K hp).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K))))
      + Algebra.trace K (AlgebraicCurve.RationalFunctionField.placeInfty K).ResidueField
        ((AlgebraicCurve.RationalFunctionField.placeInfty K).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.placeInfty K).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by
  have h := ag9b13e_p1TwoPlaceCancelMOne_dX_of_perfectField K p c hmon hp hc
  simpa only [kaehlerResidueTerm, diagonalHom_apply, p1PrincipalPartAtom, pow_one] using h

end RationalFunctionField

end AlgebraicCurve
