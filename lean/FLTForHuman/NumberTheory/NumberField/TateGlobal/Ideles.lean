/-
  The idèles of a number field and the order/valuation prelude.

  The idèle group `(AdeleRing (𝓞 F) F)ˣ`, its "integral outside `S`" subgroup
  `unitsOutside S` (both the element and its inverse are integral away from `S`),
  the generic discrete-valuation order `ord`, the local
  order `ordAt`, the uniformizer package `Uniformizers`/`unifPow`/`unitPart`, the
  exponent vector `expVec` and the `shell` decomposition, the archimedean unit
  subgroup, and the second-countability instances of the adèlic unit groups.

  Transcribed into the pin's own namespace `NumberField.TateGlobal`, declared
  lines 26–661 of file A,
  pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  The definition layer is imported, never re-derived: `integralOutside`,
  `ideleNorm`, `localChar`, `archLocalChar`, `archUnitHom`,
  `IsUnramifiedCharAt`, `IsFactorizableStandardOutside`, `zetaIntegral` and the
  adelic-completion vocabulary come from
  `FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs` (pin
  `Def_NumberField_TateGlobalZeta.lean`).

  Build notes (mathlib v4.34.0 drift and port adaptations):

  * the pin's `p2m_open`/`p2m_export`/`p2m_reactivate` scaffolding is replaced by
    the `open`/`open scoped` commands in the header; in particular
    `open scoped NumberField.TateGlobal` re-activates the pin's `scoped
    instance`s, which `p2m_open` did through `activateScoped`;
  * the pin's `M4aLocalCFT.ValuationOrd` block **is not here**: it is generic discrete
    valuation ring theory, quantified over an abstract `(A : ValuationSubring L)
    [IsDiscreteValuationRing A]`, and on 2026-10-13 it moved to its own home,
    `FLTForHuman/RingTheory/DiscreteValuationRing/Order.lean` (imported below). It had
    reached this file only because the pin copies it verbatim into sixteen `S_` files and
    this was the first to need it; ten `TateGlobal` modules consume it, always at
    `A := v.adicCompletionIntegers F`;
  * no file-wide option beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.RingTheory.DiscreteValuationRing.Order
-- the adic-completion facts the prelude consumes: the residue-field identification
-- (`ResidueFieldEquivCompletionResidueField`, pin
-- `Def_DedekindDomain_AdicValuation_InlineSpecific.lean`) and the openness/compactness
-- of the completed integers (`isOpenAdicCompletionIntegers`, pin
-- `Def_NumberField_Completion_Finite.lean`).
import FLTForHuman.AlgebraicCurve.Place.AdicCompletion
import FLTForHuman.NumberTheory.NumberField.Completion.Finite

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal NumberField.TateGlobal




section Fold_TateSDecomp



open scoped NNReal

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

-- pin: mem_integralOutside_iff (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:28)
theorem mem_integralOutside_iff (S : Finset (HeightOneSpectrum (𝓞 F))) (x : AdeleRing (𝓞 F) F) :
    x ∈ integralOutside S ↔ ∀ v ∉ S, (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
  Iff.rfl

-- pin: one_mem_integralOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:32)
theorem one_mem_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (1 : AdeleRing (𝓞 F) F) ∈ integralOutside S :=
  fun v _ => (v.adicCompletionIntegers F).one_mem

-- pin: mul_mem_integralOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:36)
theorem mul_mem_integralOutside {S : Finset (HeightOneSpectrum (𝓞 F))} {x y : AdeleRing (𝓞 F) F}
    (hx : x ∈ integralOutside S) (hy : y ∈ integralOutside S) : x * y ∈ integralOutside S :=
  fun v hv => mul_mem (hx v hv) (hy v hv)

-- pin: isOpen_integralOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:40)
theorem isOpen_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOutside (F := F) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    Fact.out (p := fun v => v ∉ S)
  exact h.preimage (continuous_adeleFin (𝓞 F) F)

-- pin: unitsOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:48)
def unitsOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (AdeleRing (𝓞 F) F)ˣ where
  carrier := {x | (x : AdeleRing (𝓞 F) F) ∈ integralOutside S ∧
    ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ integralOutside S}
  one_mem' := ⟨by simpa using one_mem_integralOutside S, by simpa using one_mem_integralOutside S⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨?_, ?_⟩
    · simpa using mul_mem_integralOutside hx hy
    · simpa [mul_inv_rev] using mul_mem_integralOutside hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨hx', by simpa using hx⟩

-- pin: mem_unitsOutside_iff (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:61)
theorem mem_unitsOutside_iff (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) :
    x ∈ unitsOutside S ↔
      (∀ v ∉ S, ((x : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F) ∧
      (∀ v ∉ S, (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
        ∈ v.adicCompletionIntegers F) :=
  Iff.rfl

-- pin: isOpen_unitsOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:68)
theorem isOpen_unitsOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (unitsOutside (F := F) S : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have h1 : IsOpen ((fun x : (AdeleRing (𝓞 F) F)ˣ => (x : AdeleRing (𝓞 F) F)) ⁻¹' integralOutside S) :=
    (isOpen_integralOutside S).preimage Units.continuous_val
  have h2 : IsOpen ((fun x : (AdeleRing (𝓞 F) F)ˣ => ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
      ⁻¹' integralOutside S) :=
    (isOpen_integralOutside S).preimage Units.continuous_coe_inv
  exact h1.inter h2

section CharTriviality

open Filter Topology

variable (x : (AdeleRing (𝓞 F) F)ˣ)

-- pin: inv_val_fst_eq_one (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:83)
theorem inv_val_fst_eq_one (h1 : ((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1) :
    (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 = 1 := by
  have h := congrArg Prod.fst x.mul_inv
  change (x : AdeleRing (𝓞 F) F).1 * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
    = (1 : InfiniteAdeleRing F) at h
  rw [h1, one_mul] at h
  exact h

end CharTriviality

end NumberField.TateGlobal

end

end Fold_TateSDecomp

section Fold_TateSDecomp2



open scoped NNReal

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

-- pin: unitAtHom (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:326)
def unitAtHom (w : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ →* (w.adicCompletion F)ˣ :=
  Units.map (((finAdeleEval (𝓞 F) F w).comp (adeleFin (𝓞 F) F)).toMonoidHom)

-- pin: embUnit (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:329)
def embUnit (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v)

-- pin: embUnit_val_fst (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:332)
theorem embUnit_val_fst (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := rfl

-- pin: unitAtHom_embUnit_self (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:335)
theorem unitAtHom_embUnit_self (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    unitAtHom v (embUnit v t) = t :=
  Units.ext (localUnit_apply_self (𝓞 F) F v t)

-- pin: unitAtHom_embUnit_of_ne (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:339)
theorem unitAtHom_embUnit_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (t : (v.adicCompletion F)ˣ) :
    unitAtHom w (embUnit v t) = 1 :=
  Units.ext (localUnit_apply_of_ne (𝓞 F) F v t hw)

-- pin: ordAt (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:343)
def ordAt (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) : ℤ :=
  IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul t)

-- pin: ordAt_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:346)
theorem ordAt_mul (v : HeightOneSpectrum (𝓞 F)) (s t : (v.adicCompletion F)ˣ) :
    ordAt v (s * t) = ordAt v s + ordAt v t := by
  simp [ordAt, ofMul_mul, map_add]

-- pin: ordAt_inv (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:350)
theorem ordAt_inv (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) : ordAt v t⁻¹ = -ordAt v t := by
  simp [ordAt, ofMul_inv, map_neg]

-- pin: ordAt_zpow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:353)
theorem ordAt_zpow (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) (n : ℤ) :
    ordAt v (t ^ n) = n * ordAt v t := by
  simp [ordAt, ofMul_zpow, map_zsmul]

-- pin: ordAt_eq_zero_iff (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:357)
theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ordAt v t = 0 ↔ (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  rw [ordAt, IsDiscreteValuationRing.ord_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    rw [← hu]
    exact ⟨(u : v.adicCompletionIntegers F).2, ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨⟨_, h⟩, ⟨_, h'⟩, Subtype.ext t.mul_inv, Subtype.ext t.inv_mul⟩, Units.ext rfl⟩

-- pin: Uniformizers (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:368)
structure Uniformizers (F : Type) [Field F] [NumberField F] where
  ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ
  ordAt_eq_one : ∀ v, ordAt v (ϖ v) = 1

-- pin: unifPow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:372)
def unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) : (AdeleRing (𝓞 F) F)ˣ :=
  k.prod fun v n => embUnit v (ϖ.ϖ v) ^ n

-- pin: unitAtHom_unifPow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:375)
theorem unitAtHom_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) (w : HeightOneSpectrum (𝓞 F)) :
    unitAtHom w (unifPow ϖ k) = ϖ.ϖ w ^ k w := by
  classical
  rw [unifPow, Finsupp.prod, map_prod]
  simp_rw [map_zpow]
  rw [Finset.prod_eq_single w]
  · rw [unitAtHom_embUnit_self]
  · intro v _ hvw
    rw [unitAtHom_embUnit_of_ne (Ne.symm hvw), one_zpow]
  · intro hw
    rw [Finsupp.notMem_support_iff.mp hw, zpow_zero]

-- pin: unifPow_val_fst (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:387)
theorem unifPow_val_fst (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ((unifPow ϖ k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  let archU : (AdeleRing (𝓞 F) F)ˣ →* (InfiniteAdeleRing F)ˣ := Units.map (adeleArch (𝓞 F) F).toMonoidHom
  have h1 : ∀ v, archU (embUnit v (ϖ.ϖ v)) = 1 := fun v => Units.ext (embUnit_val_fst v (ϖ.ϖ v))
  have h : archU (unifPow ϖ k) = 1 := by
    rw [unifPow, Finsupp.prod, map_prod]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [map_zpow, h1, one_zpow]
  exact congrArg (fun u : (InfiniteAdeleRing F)ˣ => (u : InfiniteAdeleRing F)) h

-- pin: ordAt_unitAtHom_unifPow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:397)
theorem ordAt_unitAtHom_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ)
    (w : HeightOneSpectrum (𝓞 F)) : ordAt w (unitAtHom w (unifPow ϖ k)) = k w := by
  rw [unitAtHom_unifPow, ordAt_zpow, ϖ.ordAt_eq_one, mul_one]

-- pin: finite_setOf_ordAt_ne_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:401)
theorem finite_setOf_ordAt_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | ordAt v (unitAtHom v x) ≠ 0}.Finite := by
  have h1 := (((x : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F).2)
  have h2 := ((((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F).2)
  have h := Filter.eventually_cofinite.mp (h1.and h2)
  refine h.subset fun v hv => ?_
  intro hv'
  apply hv
  rw [ordAt_eq_zero_iff]
  exact hv'

-- pin: expVec (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:412)
def expVec (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) : HeightOneSpectrum (𝓞 F) →₀ ℤ := by
  classical
  exact Finsupp.ofSupportFinite (fun v => if v ∈ S then 0 else ordAt v (unitAtHom v x))
    ((finite_setOf_ordAt_ne_zero x).subset fun v hv => by
      simp only [Function.mem_support, ne_eq, ite_eq_left_iff, Classical.not_imp] at hv
      exact hv.2)

-- pin: expVec_apply_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:419)
theorem expVec_apply_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AdeleRing (𝓞 F) F)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : expVec S x v = 0 := by
  classical
  simp [expVec, Finsupp.ofSupportFinite_coe, hv]

-- pin: expVec_apply_of_not_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:424)
theorem expVec_apply_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AdeleRing (𝓞 F) F)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : expVec S x v = ordAt v (unitAtHom v x) := by
  classical
  simp [expVec, Finsupp.ofSupportFinite_coe, hv]

-- pin: unitPart (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:429)
def unitPart (ϖ : Uniformizers F) (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) :
    (AdeleRing (𝓞 F) F)ˣ :=
  (unifPow ϖ (expVec S x))⁻¹ * x

-- pin: unifPow_mul_unitPart (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:433)
theorem unifPow_mul_unitPart (ϖ : Uniformizers F) (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) :
    unifPow ϖ (expVec S x) * unitPart ϖ S x = x := by
  rw [unitPart, mul_inv_cancel_left]

-- pin: ordAt_unitAtHom_unitPart_of_not_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:437)
theorem ordAt_unitAtHom_unitPart_of_not_mem (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (x : (AdeleRing (𝓞 F) F)ˣ) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ordAt v (unitAtHom v (unitPart ϖ S x)) = 0 := by
  rw [unitPart, map_mul, map_inv, ordAt_mul, ordAt_inv, ordAt_unitAtHom_unifPow, expVec_apply_of_not_mem x hv]
  ring

-- pin: unitPart_mem_unitsOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:443)
theorem unitPart_mem_unitsOutside (ϖ : Uniformizers F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : (AdeleRing (𝓞 F) F)ˣ) : unitPart ϖ S x ∈ unitsOutside S := by
  rw [mem_unitsOutside_iff]
  have key : ∀ v ∉ S, ((unitAtHom v (unitPart ϖ S x) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v (unitPart ϖ S x))⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        ∈ v.adicCompletionIntegers F :=
    fun v hv => (ordAt_eq_zero_iff v _).mp (ordAt_unitAtHom_unitPart_of_not_mem ϖ x hv)
  refine ⟨fun v hv => (key v hv).1, fun v hv => ?_⟩
  have h := (key v hv).2
  rwa [← map_inv] at h

-- pin: archUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:455)
def archUnits : (AdeleRing (𝓞 F) F)ˣ →* (InfiniteAdeleRing F)ˣ := Units.map (adeleArch (𝓞 F) F).toMonoidHom

-- pin: char_unifPow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:457)
theorem char_unifPow (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    χ (unifPow ϖ k) = k.prod fun v n => localChar χ v (ϖ.ϖ v) ^ n := by
  rw [unifPow, Finsupp.prod, map_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow]
  rfl

end NumberField.TateGlobal

end

end Fold_TateSDecomp2

section Fold_TateSDecomp3



open scoped NNReal Pointwise

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

-- pin: countable_numberField (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:488)
theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F := by
  have e := (Module.finBasis ℚ F).equivFun.toEquiv
  exact (Equiv.countable_iff e).mpr inferInstance

set_option linter.style.haveILetI false in
-- The four `haveI`s below are load-bearing for instance search (each `Countable`
-- is consumed by the next line's `inferInstance`/`Function.Injective.countable`),
-- so `have` would not elaborate; the style linter is disabled for this declaration.
-- pin: countable_heightOneSpectrum (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:492)
theorem countable_heightOneSpectrum (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable F := countable_numberField F
  haveI : Countable (𝓞 F) :=
    Function.Injective.countable (f := ((↑) : 𝓞 F → F)) NumberField.RingOfIntegers.coe_injective
  haveI : Countable (List (𝓞 F)) := inferInstance
  have hsurj : Function.Surjective (fun l : List (𝓞 F) => Ideal.span {x | x ∈ l}) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨s.toList, ?_⟩
    have hset : {x : 𝓞 F | x ∈ s.toList} = (s : Set (𝓞 F)) := Set.ext fun x => Finset.mem_toList
    show Ideal.span {x | x ∈ s.toList} = I
    rw [hset]
    exact hs
  haveI : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

attribute [local instance] countable_heightOneSpectrum

-- pin: ExpIndex (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:511)
def ExpIndex (S : Finset (HeightOneSpectrum (𝓞 F))) : Type :=
  {k : HeightOneSpectrum (𝓞 F) →₀ ℤ // ∀ v ∈ S, k v = 0}

-- pin: instCountableExpIndex (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:514)
scoped instance instCountableExpIndex (S : Finset (HeightOneSpectrum (𝓞 F))) : Countable (ExpIndex (F := F) S) := by
  unfold ExpIndex; infer_instance

-- pin: shell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:517)
def shell (S : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {x | expVec S x = k}

-- pin: expVec_unifPow_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:520)
theorem expVec_unifPow_mul (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    expVec S (unifPow ϖ k * u) = k := by
  have hu' := (mem_unitsOutside_iff S u).mp hu
  ext v
  by_cases hv : v ∈ S
  · rw [expVec_apply_of_mem _ hv, hk v hv]
  · rw [expVec_apply_of_not_mem _ hv, map_mul, ordAt_mul, ordAt_unitAtHom_unifPow]
    have h0 : ordAt v (unitAtHom v u) = 0 := by
      rw [ordAt_eq_zero_iff]
      refine ⟨hu'.1 v hv, ?_⟩
      rw [← map_inv]
      exact hu'.2 v hv
    rw [h0, add_zero]

-- pin: expVec_vanishes (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:535)
theorem expVec_vanishes (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ∀ v ∈ S, expVec S x v = 0 := fun _ hv => expVec_apply_of_mem x hv

-- pin: shell_eq_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:538)
theorem shell_eq_smul (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) :
    shell S k = unifPow ϖ k • (unitsOutside (F := F) S : Set (AdeleRing (𝓞 F) F)ˣ) := by
  ext x
  constructor
  · intro hx
    refine ⟨unitPart ϖ S x, unitPart_mem_unitsOutside ϖ S x, ?_⟩
    show unifPow ϖ k * unitPart ϖ S x = x
    have h := unifPow_mul_unitPart ϖ S x
    rw [show expVec S x = k from hx] at h
    exact h
  · rintro ⟨u, hu, rfl⟩
    exact expVec_unifPow_mul ϖ hk hu

-- pin: isOpen_shell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:552)
theorem isOpen_shell (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) : IsOpen (shell (F := F) S k) := by
  rw [shell_eq_smul ϖ hk]
  exact (isOpen_unitsOutside S).smul _

-- pin: measurableSet_shell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:557)
theorem measurableSet_shell [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) : MeasurableSet (shell (F := F) S k) :=
  (isOpen_shell ϖ hk).measurableSet

-- pin: pairwise_disjoint_shell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:562)
theorem pairwise_disjoint_shell (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Pairwise (Function.onFun Disjoint fun k : ExpIndex (F := F) S => shell S k.1) := by
  intro k k' hne
  refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
  exact Subtype.ext (hx.symm.trans hx')

-- pin: iUnion_shell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:568)
theorem iUnion_shell (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ⋃ k : ExpIndex (F := F) S, shell S k.1 = univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
  exact ⟨⟨expVec S x, expVec_vanishes S x⟩, rfl⟩

section Integral

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

-- pin: setIntegral_smul_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:577)
theorem setIntegral_smul_eq (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    {U : Set (AdeleRing (𝓞 F) F)ˣ} (hU : MeasurableSet U) (g : (AdeleRing (𝓞 F) F)ˣ) (G : (AdeleRing (𝓞 F) F)ˣ → ℂ) :
    ∫ x in g • U, G x ∂ν = ∫ u in U, G (g * u) ∂ν := by
  have hgU : MeasurableSet (g • U) := hU.const_smul g
  rw [← integral_indicator hgU, ← integral_indicator hU, ← integral_mul_left_eq_self _ g]
  congr 1
  funext u
  have hiff : g * u ∈ g • U ↔ u ∈ U := by
    constructor
    · intro h
      obtain ⟨u', hu', h'⟩ := Set.mem_smul_set.mp h
      rw [smul_eq_mul] at h'
      rw [← mul_left_cancel h']
      exact hu'
    · intro hu
      exact Set.mem_smul_set.mpr ⟨u, hu, rfl⟩
  simp only [Set.indicator]
  by_cases hu : u ∈ U
  · rw [ite_eq_left (hiff.mpr hu), ite_eq_left hu]
  · rw [ite_eq_right (mt hiff.mp hu), ite_eq_right hu]

-- pin: hasSum_setIntegral_unitsOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:598)
theorem hasSum_setIntegral_unitsOutside (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    (ϖ : Uniformizers F) (S : Finset (HeightOneSpectrum (𝓞 F))) {G : (AdeleRing (𝓞 F) F)ˣ → ℂ} (hG : Integrable G ν) :
    HasSum (fun k : ExpIndex (F := F) S => ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ), G (unifPow ϖ k.1 * u) ∂ν)
      (∫ x, G x ∂ν) := by
  have h := hasSum_integral_iUnion (μ := ν) (f := G) (s := fun k : ExpIndex (F := F) S => shell S k.1)
    (fun k => measurableSet_shell ϖ k.2) (pairwise_disjoint_shell S)
    (by rw [iUnion_shell]; exact hG.integrableOn)
  rw [iUnion_shell, Measure.restrict_univ] at h
  refine h.congr_fun fun k => ?_
  show _ = ∫ x in shell S k.1, G x ∂ν
  rw [shell_eq_smul ϖ k.2, setIntegral_smul_eq ν (isOpen_unitsOutside S).measurableSet]

end Integral

end NumberField.TateGlobal

end

end Fold_TateSDecomp3

section Fold_TateAssembly



noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

-- pin: instSecondCountableUnitsAdicCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:638)
scoped instance instSecondCountableUnitsAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

-- pin: instSecondCountableCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:642)
scoped instance instSecondCountableCompletion (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

-- pin: instSecondCountableUnitsCompletion (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:645)
scoped instance instSecondCountableUnitsCompletion (w : InfinitePlace F) : SecondCountableTopology (w.Completion)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

-- pin: instSecondCountableInfiniteAdeleRing (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:648)
scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F) :=
  show SecondCountableTopology ((w : InfinitePlace F) → w.Completion) from inferInstance

-- pin: instSecondCountableMulOpposite (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:651)
scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X] [SecondCountableTopology X] :
    SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

-- pin: instSecondCountableUnitsInfiniteAdeleRing (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:655)
scoped instance instSecondCountableUnitsInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F)ˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology

-- pin: instSecondCountableUnitsIntegers (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:658)
scoped instance instSecondCountableUnitsIntegers (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletionIntegers F)ˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology


end NumberField.TateGlobal

end

end Fold_TateAssembly

