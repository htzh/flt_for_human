/-
Adjoin — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.Separating

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open AlgebraicCurve.RationalFunctionField
open KaehlerDifferential
open AlgebraicCurve.RationalFunctionField KaehlerDifferential
open scoped IntermediateField
open scoped IntermediateField Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
open KaehlerDifferential Module IntermediateField

section
section


namespace IntermediateField

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem finiteDimensional_top : FiniteDimensional ↥(⊤ : IntermediateField K E) E :=
  Module.Finite.of_surjective (Algebra.linearMap (↥(⊤ : IntermediateField K E)) E)
    fun x => ⟨⟨x, mem_top⟩, rfl⟩

theorem adjoin_simple_gen_eq_top (α : E) :
    K⟮AdjoinSimple.gen K α⟯ = (⊤ : IntermediateField K ↥K⟮α⟯) :=
  (K⟮α⟯).lift_injective <| by
    rw [lift_adjoin_simple, AdjoinSimple.coe_gen, lift_top]

theorem transcendental_gen {α : E} (hα : Transcendental K α) :
    Transcendental K (AdjoinSimple.gen K α) := by
  rw [show α = algebraMap K⟮α⟯ E (AdjoinSimple.gen K α) from
    (AdjoinSimple.algebraMap_gen K α).symm] at hα
  exact (transcendental_algebraMap_iff (algebraMap K⟮α⟯ E).injective).mp hα

end IntermediateField

namespace AlgebraicCurve

open RationalFunctionField

section PurelyTranscendentalSimple

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def IsPurelyTranscendentalSimple : Prop :=
  ∃ t : F, Transcendental K t ∧ K⟮t⟯ = (⊤ : IntermediateField K F)

variable {K F}

theorem hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple
    (h : IsPurelyTranscendentalSimple K F) :
    HasSeparatingTranscendentalCore K F := by
  obtain ⟨t, ht, htop⟩ := h
  haveI : FiniteDimensional ↥(⊤ : IntermediateField K F) F :=
    IntermediateField.finiteDimensional_top
  exact ⟨t, ht, IntermediateField.finiteDimensional_of_eq htop.symm⟩

end PurelyTranscendentalSimple

section SelfAdjoinInstance

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem isPurelyTranscendentalSimple_adjoin_simple {α : E} (hα : Transcendental K α) :
    IsPurelyTranscendentalSimple K ↥K⟮α⟯ :=
  ⟨AdjoinSimple.gen K α, IntermediateField.transcendental_gen hα,
    IntermediateField.adjoin_simple_gen_eq_top α⟩

end SelfAdjoinInstance

section TowerComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

end TowerComposites

section AdjoinTowerComposites

variable {K E F' : Type*} [Field K] [Field E] [Field F']
variable [Algebra K E] [Algebra K F']

end AdjoinTowerComposites

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

end
