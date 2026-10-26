/-
  Corestriction of a homomorphism out of a finite-index subgroup, written as an
  explicit sum over the cosets, and its identification with `MonoidHom.transfer`.

  This module is deliberately **Mathlib-only** (no `FLTForHuman` import): the
  statements mention no modular vocabulary at all — `(H : Subgroup G)`,
  `Additive H →+ A`, `MonoidHom.transfer` — and the layering rule of the port
  keeps `GroupTheory/` free of `ModularForms/`.

  FLT provenance, pinned `aa2d8b3`: the `Transfer` section of
  `Definitions/Def_Gamma0HeckeOperatorHom.lean` (lines 204–265, transcribed
  verbatim), and

  spec-pin: Theorems/Thm_HeckeEis_coresHom_eq_transfer.lean
  spec-pin: P2M/Sol/S_HeckeEis_coresHom_eq_transfer.lean   -- comparable copy
  spec-pin: Definitions/Def_Gamma0HeckeOperatorHom.lean

  Two spellings of one object, on purpose (the pin's own arrangement, kept by
  this wave's decision D2): `HeckeEis.coresHom` below is the coset sum
  `∑ q : G ⧸ H, φ (transferAux H g q)`, while `CohCarrier.coresAdd`
  (`ModularForms/Defs/CohCarrierLevel.lean`) is the same map defined through
  `MonoidHom.transfer`.  `HeckeEis.coresHom_eq_transfer` is the named bridge
  between them, and no third spelling is to be added.

  API note (mathlib `v4.34.0`): `MonoidHom.transfer_def` now takes its
  transversal before the group element, `transfer_def ϕ T g`.  The proof below
  is the pin's, adapted only in that respect.
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group

set_option autoImplicit false

-- The pin's `letI` walls are kept literal: `letI` inlines its value, which is
-- what makes `coresHom`'s coset sum definitionally the transfer below.
set_option linter.style.haveILetI false

namespace HeckeEis

open Subgroup Subgroup.leftTransversals

section Transfer

variable {G : Type*} [Group G] (H : Subgroup G) {A : Type*} [AddCommGroup A]

/-- Restriction of an additive homomorphism out of `G` to one out of `H`,
as an additive monoid homomorphism. -/
def resHom : (Additive G →+ A) →+ (Additive H →+ A) :=
  AddMonoidHom.mk' (fun φ => φ.comp (MonoidHom.toAdditive H.subtype)) fun _ _ => rfl

@[simp]
theorem resHom_apply (φ : Additive G →+ A) (γ : H) :
    resHom H φ (Additive.ofMul γ) = φ (Additive.ofMul (γ : G)) :=
  rfl

/-- The transfer factor of `g` at the coset `q`, read off a representative. -/
noncomputable def transferAux (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * (g * q.out), by
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq']
    show g • q = ((g * q.out : G) : G ⧸ H)
    rw [show ((g * q.out : G) : G ⧸ H) = g • ((q.out : G) : G ⧸ H) from rfl,
      QuotientGroup.out_eq']⟩

@[simp]
theorem coe_transferAux (g : G) (q : G ⧸ H) :
    (transferAux H g q : G) = (g • q).out⁻¹ * (g * q.out) :=
  rfl

theorem transferAux_mul (g₁ g₂ : G) (q : G ⧸ H) :
    transferAux H (g₁ * g₂) q = transferAux H g₁ (g₂ • q) * transferAux H g₂ q := by
  ext
  push_cast [coe_transferAux]
  rw [mul_smul]
  group

variable [H.FiniteIndex]

/-- Corestriction from a finite-index subgroup, as an explicit sum over the
left cosets of `H` in `G`. -/
noncomputable def coresHom : (Additive H →+ A) →+ (Additive G →+ A) :=
  AddMonoidHom.mk'
    (fun φ =>
      letI := H.fintypeQuotientOfFiniteIndex
      AddMonoidHom.mk'
        (fun g => ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g.toMul q)))
        (fun g₁ g₂ => by
          show ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H (g₁.toMul * g₂.toMul) q)) =
            (∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g₁.toMul q))) +
              ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g₂.toMul q))
          simp_rw [transferAux_mul, ofMul_mul, map_add]
          rw [Finset.sum_add_distrib]
          exact congrArg₂ (· + ·)
            (Fintype.sum_bijective (g₂.toMul • ·) (MulAction.bijective g₂.toMul)
              (fun q => φ (Additive.ofMul (transferAux H g₁.toMul (g₂.toMul • q))))
              (fun q => φ (Additive.ofMul (transferAux H g₁.toMul q))) fun q => rfl) rfl))
    (fun φ ψ => by
      letI := H.fintypeQuotientOfFiniteIndex
      ext g
      exact Finset.sum_add_distrib)

theorem coresHom_apply (φ : Additive H →+ A) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    coresHom H φ (Additive.ofMul g) =
      ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q)) :=
  rfl

end Transfer

/-! ### Pullback along a monoid homomorphism

Not in the workorder's definition tail, but node 1's proof
(`ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU`) needs it: the pin
writes `coresHom (heckeUpper …) (pullbackHom (heckeConj …))`, and the port's
`CohCarrier.heckeT` is literally the `transfer` of
`(toMultiplicativeRight φ).comp (conjL …)`, so `pullbackHom` is the bridge that
lets node 10 rewrite that into the coset sum. Seven lines, Mathlib-only, so it
stays here with the rest of the section. -/

section Pullback

variable {G K : Type*} [Group G] [Group K] {A : Type*} [AddCommGroup A]

def pullbackHom (f : G →* K) : (Additive K →+ A) →+ (Additive G →+ A) :=
  AddMonoidHom.mk' (fun φ => φ.comp (MonoidHom.toAdditive f)) fun _ _ => rfl

@[simp]
theorem pullbackHom_apply (f : G →* K) (φ : Additive K →+ A) (g : G) :
    pullbackHom f φ (Additive.ofMul g) = φ (Additive.ofMul (f g)) :=
  rfl

end Pullback

/-! ### The bridge to `MonoidHom.transfer` -/

section Bridge

variable {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
variable {A : Type*} [AddCommGroup A]

omit [H.FiniteIndex] in
private theorem default_leftQuotientEquiv_apply (q : G ⧸ H) :
    ((default : H.LeftTransversal).2.leftQuotientEquiv q : G) = q.out :=
  IsComplement.leftQuotientEquiv_apply Quotient.out_eq' q

omit [H.FiniteIndex] in
private theorem smul_default_leftQuotientEquiv_apply (g : G) (q : G ⧸ H) :
    ((g • (default : H.LeftTransversal)).2.leftQuotientEquiv q : G) = g * (g⁻¹ • q).out := by
  rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  congr 1
  exact default_leftQuotientEquiv_apply H (g⁻¹ • q)

private theorem coresHom_eq_transfer_aux (φ : Additive H →+ A) :
    coresHom (H := H) φ
      = MonoidHom.toAdditiveLeft
          (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) := by
  letI := H.fintypeQuotientOfFiniteIndex
  ext g
  set g' := Additive.toMul g

  show (∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g' q)))
    = Multiplicative.toAdd
        (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ) g')

  rw [MonoidHom.transfer_def (AddMonoidHom.toMultiplicativeRight φ) (g'⁻¹ • default),
    smul_inv_smul]
  unfold Subgroup.leftTransversals.diff
  simp only [toAdd_prod, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  refine Finset.sum_congr rfl (fun q _ => congr_arg φ (congr_arg Additive.ofMul (Subtype.ext ?_)))
  simp only [coe_transferAux, default_leftQuotientEquiv_apply,
    smul_default_leftQuotientEquiv_apply, inv_inv, mul_inv_rev, mul_assoc]

end Bridge

/-- The pin's coset-sum corestriction equals the group-theoretic transfer, after
transporting the additive target to a multiplicative one. -/
theorem coresHom_eq_transfer {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    {A : Type*} [AddCommGroup A] (φ : Additive ↥H →+ A) :
    HeckeEis.coresHom (H := H) φ
      = MonoidHom.toAdditiveLeft
          (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) :=
  coresHom_eq_transfer_aux H φ

end HeckeEis
