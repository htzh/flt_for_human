/-
PerfectField — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.KaehlerIntegral

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open AlgebraicCurve.RationalFunctionField
open KaehlerDifferential
open AlgebraicCurve.RationalFunctionField KaehlerDifferential
open scoped IntermediateField
open scoped IntermediateField Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
open KaehlerDifferential Module IntermediateField
open AlgebraicCurve

section
section

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField


section PerfectDCoord

variable (K : Type*) [Field K] [PerfectField K]

theorem exists_ne_zero_smul_dX_of_uniformizer (v : Place K (RatFunc K)) :
    ∃ c : RatFunc K, c ≠ 0 ∧
      KaehlerDifferential.D K (RatFunc K) v.uniformizer = c • dX K := by
  classical
  have hord : v.ord v.uniformizer = 1 := v.ord_uniformizer
  have hpi0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨hne, -⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
      (PerfectField.separable_of_irreducible hp) hpi0 hord
    exact ⟨ratFuncDXCoeff K _, hne, D_eq_ratFuncDXCoeff_smul_dX K _⟩
  ·
    obtain ⟨e, he0, -, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hpi0 hord
    exact ⟨e, he0, hDe⟩

namespace RationalFunctionField

scoped instance (priority := low) instDCoordGeneratesPerfectField (v : Place K (RatFunc K)) :
    v.DCoordGenerates := by
  obtain ⟨c, hc0, hDc⟩ := exists_ne_zero_smul_dX_of_uniformizer K v
  refine ⟨?_⟩
  have hdc : v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer := rfl
  rw [hdc, hDc, eq_top_iff, ← span_dX_eq_top K, Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_span_singleton.mpr
    ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

end RationalFunctionField

end PerfectDCoord

section Profile

variable (K : Type*) [Field K]

section PerfectProfileValues

variable [PerfectField K] [DecidableEq (RatFunc K)]

theorem p1DifferentialCoeffUnitFinite_dX_of_perfectField :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp
      (PerfectField.separable_of_irreducible hp)
  · exact absurd rfl hvinf

theorem p1DifferentialCoeffRegularFinite_dX_of_perfectField :
    P1DifferentialCoeffRegularFinite K (dX_ne_zero K) :=
  fun v hv => v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
    (p1DifferentialCoeffUnitFinite_dX_of_perfectField K v hv).ge

theorem ordDifferential_dX_of_ne_placeInfty_of_perfectField {v : Place K (RatFunc K)}
    (hv : v ≠ p1PlaceInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX_of_perfectField K v hv

theorem ordDifferential_dX_placeInfty_of_perfectField :
    (p1PlaceInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K)

theorem exists_divisor_smul_dX_of_perfectField {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (p1PlaceInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (p1PlaceInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty_of_perfectField K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty_of_perfectField K hne,
        Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end PerfectProfileValues

section PerfectInstance

variable [PerfectField K]

scoped instance instHasCanonicalDivisorRatFuncPerfectField :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX_of_perfectField K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

end PerfectInstance

section PerfectExactDivisor

variable [PerfectField K] [DecidableEq (RatFunc K)]

end PerfectExactDivisor

section CharZeroRoutes

variable [CharZero K]

end CharZeroRoutes

end Profile

section FiniteFieldReadings

end FiniteFieldReadings

end AlgebraicCurve

section AxiomAudit

end AxiomAudit

end
end

end

section
section

set_option maxHeartbeats 1600000

noncomputable section


namespace ModularCurve

open AlgebraicCurve

namespace MilneAvAg9bRd13T2CoordIndepChar3



end MilneAvAg9bRd13T2CoordIndepChar3
end ModularCurve
end
end
end
section
section
noncomputable section
namespace AlgebraicCurve

open RationalFunctionField
section ChoiceOpacity
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
namespace Place
section BumpConstruction
variable (v : Place K F)
end BumpConstruction
end Place
end ChoiceOpacity
section CanonicalKResidueTerm
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
section SupportMachinery
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable (K F)
variable {K F}
section Bridge
variable [HasLocalResidue K F] [HasCanonicalLocalResidueKStar K F]
variable [Nontrivial Ω[F⁄K]]
end Bridge
end SupportMachinery
end CanonicalKResidueTerm
section RatFuncPlaceInftyClause
variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]
theorem residueTheoremK_placeInfty_clause_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK) (n : ℕ) :
    kaehlerResidueTermKFam Rfam (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n)) (p1PlaceInfty K) = 0 := by
  rw [kaehlerResidueTermKFam_apply]
  exact canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow K (Rfam (p1PlaceInfty K)) n

end RatFuncPlaceInftyClause

section GenericGates

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

end GenericGates

section AlgClosedGate

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
  [HasCanonicalDivisor (K := K) (F := RatFunc K)]

end AlgClosedGate

end AlgebraicCurve

section AxiomAudit

end AxiomAudit

end

end

end

end
