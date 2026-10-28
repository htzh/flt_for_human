/-
  Consumer specification for SET MC-7's **definition wave**
  (`lean/FLTForHuman/ModularCurve/Defs/QExpReductionModL.lean`, the port of FLT's
  `Definitions/Def_ModularCurve_QExpReductionModL.lean`).

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the new definition layer, composed across modules, expressed in Lean
  so that each is either bound or not.  It is a deliverable measure, not a proof obligation.
  It is **not part of any library** (`lake build` does not see `spec/`); run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveMC7DefConsumer.lean 2>&1 | grep -c error

  The error count is the metric.  The row modules of the set (MC-7a/b/c) extend this file's
  zones once they land; the brief's §6 is the plan.

  ZONES
  -----
    [single]    ZONE A — the reduction of a single-place divisor difference: the degree-zero
                lift `laurentReductionDegZero` of `single P n - single Q n` is
                `single (r P) n - single (r Q) n`, and its degree is `0` when `P.deg = Q.deg`.
                Composes the definition wave with `Defs/Divisor`'s `degree_single`,
                `degree`-as-`AddMonoidHom` and `Finsupp.mapDomain`.
    [prin]      ZONE B — the reduction of a *principal* divisor is principal: the wave's
                `LaurentReductionInputs` (an existential over `IsLaurentPlaceReduction`)
                consumed through `laurentReductionDiv_apply` and the ported `Divisor.principal`
                of `Defs/Divisor`.  This is the hypothesis the 953 row's `mapDomain_placeMap`
                starts from.
    [charL]     ZONE C — the character-ℓ specialisation: at `Γ = Γ₁(M)` and
                `A : ValuationSubring (AlgebraicClosure ℚ)`, `reductionQExpModL` lands in the
                residue q-expansion field `JOneC M (ResidueField A)` — the def module's own
                `example`, restated as a named use, composed with `JOne`/`JOneC` from
                `X1/Defs.lean`.
-/

import FLTForHuman.ModularCurve.Defs.QExpReductionModL
import FLTForHuman.AlgebraicCurve.ConstantReduction
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import FLTForHuman.ModularCurve.X1.Defs

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve
open ModularCurve

namespace MC7DefConsumer

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
  {k : Type*} [Field k] {π : A →+* k}
  {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {Fbar : IntermediateField k (LaurentSeries k)}

/-! ## Zone A — `[single]` single-place divisors -/

theorem reductionDiv_single_sub (r : Place L (laurentBaseChange L F₀) → Place k Fbar)
    (P Q : Place L (laurentBaseChange L F₀)) (n : ℤ) :
    ModularCurve.laurentReductionDiv r (Finsupp.single P n - Finsupp.single Q n) =
      Finsupp.single (r P) n - Finsupp.single (r Q) n := by
  rw [ModularCurve.laurentReductionDiv_apply, Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single]

theorem degree_reductionDiv_single_sub (r : Place L (laurentBaseChange L F₀) → Place k Fbar)
    (hdeg : ∀ P, (r P).deg = P.deg) (P Q : Place L (laurentBaseChange L F₀))
    (hPQ : P.deg = Q.deg) (n : ℤ) :
    Divisor.degree (ModularCurve.laurentReductionDiv r
      (Finsupp.single P n - Finsupp.single Q n)) = 0 := by
  rw [reductionDiv_single_sub r P Q n, map_sub, Divisor.degree_single,
    Divisor.degree_single, hdeg P, hdeg Q, hPQ, sub_self]

theorem reductionDegZero_single_sub (r : Place L (laurentBaseChange L F₀) → Place k Fbar)
    (hdeg : ∀ P, (r P).deg = P.deg) (P Q : Place L (laurentBaseChange L F₀))
    (n : ℤ)
    (hD : (Finsupp.single P n - Finsupp.single Q n) ∈
      Divisor.degZero (K := L) (F := laurentBaseChange L F₀)) :
    ((ModularCurve.laurentReductionDegZero r hdeg
        ⟨Finsupp.single P n - Finsupp.single Q n, hD⟩ : Divisor.degZero (K := k) (F := Fbar)) :
        Divisor k Fbar) =
      Finsupp.single (r P) n - Finsupp.single (r Q) n := by
  rw [ModularCurve.coe_laurentReductionDegZero]
  exact reductionDiv_single_sub r P Q n

/-! ## Zone B — `[prin]` principal divisors -/

theorem reductionDiv_mem_principal (r : Place L (laurentBaseChange L F₀) → Place k Fbar)
    (h : ModularCurve.IsLaurentPlaceReduction A π F₀ Fbar r)
    (hgen : ModularCurve.LaurentPrincipalGeneratedByIntegral A π F₀ Fbar)
    {D : Divisor L (laurentBaseChange L F₀)}
    (hD : D ∈ Divisor.principal (K := L) (F := laurentBaseChange L F₀)) :
    ModularCurve.laurentReductionDiv r D ∈ Divisor.principal (K := k) (F := Fbar) := by
  rw [ModularCurve.laurentReductionDiv_apply]
  exact h.mapDomain_mem_principal hgen hD

theorem reduction_mem_principal_of_inputs
    (h : ModularCurve.LaurentReductionInputs A π F₀ Fbar)
    {D : Divisor L (laurentBaseChange L F₀)}
    (hD : D ∈ Divisor.principal (K := L) (F := laurentBaseChange L F₀)) :
    ModularCurve.laurentReductionDiv h.choose D ∈ Divisor.principal (K := k) (F := Fbar) :=
  reductionDiv_mem_principal h.choose h.choose_spec.1 h.choose_spec.2 hD

/-! ## Zone C — `[charL]` the character-ℓ specialisation -/

/-- The dichotomy the def module records: a `Γ₁(M)` reduction whose input hypothesis fails is
the zero homomorphism, hence kills every class — read through `reductionQExpModL_of_not` and the
`Pic0` group structure. -/
theorem reductionQExpModL_apply_eq_zero_of_not (M : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (h : ¬ ModularCurve.ReductionInputsQExpModL A (CongruenceSubgroup.Gamma1 M))
    (z : Pic0 (AlgebraicClosure ℚ)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) :
    ModularCurve.reductionQExpModL A (CongruenceSubgroup.Gamma1 M) z = 0 := by
  rw [ModularCurve.reductionQExpModL_of_not h]
  rfl

/-- The def module's own check, as a named use: the character-ℓ reduction of `Γ₁(M)` lands in
the residue `JOneC`. -/
example (M : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (z : ModularCurve.JOne M) :
    ModularCurve.JOneC M (IsLocalRing.ResidueField A) :=
  ModularCurve.reductionQExpModL A (CongruenceSubgroup.Gamma1 M) z

end MC7DefConsumer
