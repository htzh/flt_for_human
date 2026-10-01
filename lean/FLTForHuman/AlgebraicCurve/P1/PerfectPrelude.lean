/-
PerfectPrelude — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.Adjoin

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

set_option linter.unusedSectionVars false

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField


variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

section NamedRow

variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

def CanonicalLocalResidueKSimplePoleCoordIndep : Prop :=
  ∀ (v : Place K F) (π' : F), v.ord π' = 1 →
    ∀ (R : v.CanonicalLocalResidueDataK),
      R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1

end NamedRow

section SATGate

variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end SATGate

section XInvCoordinate

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1XAtom_mul_differentialCoeff_dX_eq_neg :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      = -((p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹) := by
  show algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
        * (p1PlaceInfty K).differentialCoeff (dX K)
      = -((p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹)
  rw [show (dX K) = KaehlerDifferential.D K (RatFunc K) RatFunc.X from rfl,
    differentialCoeff_placeInfty_D_X_eq K, RatFunc.algebraMap_X, map_one, pow_one, inv_inv,
    one_div]
  field_simp [RatFunc.X_ne_zero (K := K), sq, mul_comm]

end XInvCoordinate

section InftyXDischarge

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem trace_placeInfty_residueField_one :
    Algebra.trace K (p1PlaceInfty K).ResidueField 1 = 1 := by
  rw [show (1 : (p1PlaceInfty K).ResidueField) = algebraMap K _ 1 from (map_one _).symm,
    Algebra.trace_algebraMap, show Module.finrank K (p1PlaceInfty K).ResidueField = 1 from
      deg_placeInfty K, one_smul]

theorem simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    (p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩ = -1 := by

  set R := (p1PlaceInfty K).canonicalLocalResidueDataKOfExtend
  rw [← (p1PlaceInfty K).localResidueData_res_eq_simplePoleResidueAux R.toLocalResidueData himem,
    show R.toLocalResidueData.res = R.res from rfl,
    p1XAtom_mul_differentialCoeff_dX_eq_neg K, _root_.map_neg,
    hsp (p1PlaceInfty K) (RatFunc.X : RatFunc K)⁻¹ (ord_placeInfty_X_inv K) R]

theorem p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K)) :
    P1PlaceInftySimplePoleResidueEulerValueX K := by
  intro himem
  rw [simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one K hsp himem, _root_.map_neg,
    trace_placeInfty_residueField_one K]

end InftyXDischarge

section ComposedEngine

variable (K) [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K)) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyX K hwd hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep K hsp)

end ComposedEngine

section Monotonicity

variable (K) [DecidableEq (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end Monotonicity

end AlgebraicCurve

section AxiomAudit

end AxiomAudit

end
end

end

section
section


namespace IntermediateField

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem adjoin_simple_map_algHom' (e : F →ₐ[K] F') (t : F) :
    (K⟮t⟯).map e = K⟮e t⟯ := by
  rw [adjoin_map, Set.image_singleton]

theorem adjoin_simple_eq_top_of_algEquiv (e : F ≃ₐ[K] F') {t : F}
    (htop : K⟮t⟯ = (⊤ : IntermediateField K F)) :
    K⟮e t⟯ = (⊤ : IntermediateField K F') := by
  have key : K⟮(e : F →ₐ[K] F') t⟯ = (⊤ : IntermediateField K F') := by
    rw [← adjoin_simple_map_algHom' (e : F →ₐ[K] F') t, htop,
      ← AlgHom.fieldRange_eq_map, AlgEquiv.fieldRange_eq_top]
  exact key

end IntermediateField

namespace AlgebraicCurve

open RationalFunctionField

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem IsPurelyTranscendentalSimple.congr (e : F ≃ₐ[K] F')
    (h : IsPurelyTranscendentalSimple K F) : IsPurelyTranscendentalSimple K F' := by
  obtain ⟨t, ht, htop⟩ := h
  refine ⟨e t, ?_, IntermediateField.adjoin_simple_eq_top_of_algEquiv e htop⟩
  unfold Transcendental at ht ⊢
  rw [show (e t : F') = (e : F →ₐ[K] F') t from rfl,
    isAlgebraic_algHom_iff (e : F →ₐ[K] F') e.injective]
  exact ht

end Congr

section RatFuncInstance

variable (K : Type*) [Field K]

theorem isPurelyTranscendentalSimple_ratFunc :
    IsPurelyTranscendentalSimple K (RatFunc K) :=
  (isPurelyTranscendentalSimple_adjoin_simple (RatFunc.transcendental_X (K := K))).congr
    (RatFunc.algEquivOfTranscendental (RatFunc.X : RatFunc K)
      (RatFunc.transcendental_X (K := K))).symm

end RatFuncInstance

section Iff

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isPurelyTranscendentalSimple_of_ratFuncAlgEquiv
    (h : Nonempty (RatFunc K ≃ₐ[K] F)) : IsPurelyTranscendentalSimple K F :=
  (isPurelyTranscendentalSimple_ratFunc K).congr h.some

end Iff

section CharZeroReflection

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end CharZeroReflection

section TowerComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

end TowerComposites

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


variable (N : ℕ) [NeZero N]

end ModularCurve

namespace AlgebraicCurve

open RationalFunctionField

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


end ModularCurve

section AxiomAudits

end AxiomAudits

end

end

section
section


namespace AlgebraicCurve

open RationalFunctionField

section AbstractEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_charZero
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (valSubringKaehlerSpanTop_of_kaehlerFinite_of_charZero hfin) v

end AbstractEngine

section ChainComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

theorem Place.dCoordGenerates_of_isPurelyTranscendentalSimple
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (h : IsPurelyTranscendentalSimple K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_charZero
    (valSubringKaehlerFinite_of_core
      (hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple h)) v

end ChainComposites

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


variable (N : ℕ) [NeZero N]

end ModularCurve

namespace ModularCurve

open AlgebraicCurve


variable (N : ℕ) [NeZero N]

theorem gate_dCoordGenerates_of_ratFunc_sat
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hRat : Nonempty (RatFunc K ≃ₐ[K] F)) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_isPurelyTranscendentalSimple
    (isPurelyTranscendentalSimple_of_ratFuncAlgEquiv hRat) v

end ModularCurve

section AxiomAudits

end AxiomAudits

end

end

section
section

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000


namespace AlgebraicCurve

open RationalFunctionField

namespace RationalFunctionField

variable {K : Type*} [Field K]

scoped instance (priority := low) instDCoordGenerates [CharZero K] (v : Place K (RatFunc K)) :
    v.DCoordGenerates :=
  ModularCurve.gate_dCoordGenerates_of_ratFunc_sat ⟨AlgEquiv.refl⟩ v

end RationalFunctionField

section TransportTwoRoutes

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]

end TransportTwoRoutes

section ConsumerDemonstrations

variable {K : Type*} [Field K] [CharZero K]

end ConsumerDemonstrations

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


section RatBasePinned

end RatBasePinned

section RatBaseCrossing

end RatBaseCrossing

end ModularCurve

section AxiomAudits

end AxiomAudits

end
end

end

end
