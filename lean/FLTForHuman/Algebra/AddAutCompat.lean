/-
  Mathlib-4.30 compatibility shim, block D: the multiplicative group structure on
  `AddAut`.

  Mathlib `v4.30.0` gave `AddAut A` (i.e. `A ≃+ A`) both a multiplicative `Group`
  structure and the tautological `DistribMulAction (AddAut A) A`; from `v4.33.0` on it
  carries only an *additive* group structure ("We give `AddAut M` the structure of an
  additive group rather than a multiplicative group",
  `Mathlib/Algebra/Group/End.lean`), so `Subgroup (AddAut A)` — the shape the pin's
  `AddAut` nodes state in — no longer elaborates against the current library. The pin
  restores it in `Definitions/Def_Compat_Mathlib430.lean` (block D, its vendored
  `Mathlib/Algebra/Group/End.lean:746-801` plus `GroupWithZero/Action/Basic.lean:89-92`,
  `:104-112` and `Ring/AddAut.lean:32`, names carrying a trailing prime so they do not
  clash with the additive names `v4.33.0`/`v4.34.0` generate).

  This module homes **block D of that pin module, verbatim**: the instance
  `AddAut.instGroup`, the thirteen primed lemmas, the three `example`s asserting
  definitional agreement with mathlib's additive structure, and the "block D
  (continued)" tautological `DistribMulAction`/`FaithfulSMul` together with
  `DistribMulAction.toAddAut'` and `AddAut.mulLeft'`. The pin's blocks A–C
  (vendored `Representation`/`Rep` API) and E (elliptic divisibility sequences) are
  *not* homed here: they are separate subjects, they gate nothing in this group, and
  they vendor a 4.30 API that no current port module consumes. The port therefore homes
  a strict subset of the pin definition module, at the pin's names, and this is recorded
  as a gate landings item in the MG3 phase-2 group D report.

  Mathlib v4.34.0 has no `Group (AddAut A)` (`#check @AddAut.instGroup` fails and
  `example (A : Type*) [Add A] : Group (AddAut A) := inferInstance` does not
  elaborate), and `rg "AddAut" Mathlib/Algebra/Group/End.lean` shows only the additive
  structure; so nothing here duplicates a live mathlib declaration.

  Assumes: mathlib `v4.34.0` only.

  spec-pin: Definitions/Def_Compat_Mathlib430.lean
-/

import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-! ## Block D — AddAut: Mathlib v4.30.0 Mathlib/Algebra/Group/End.lean:746-801 (+ GroupWithZero/Action/Basic.lean:89-92 and :104-112, Ring/AddAut.lean:32), lemma names primed -/

namespace AddAut

section Compat430

variable (A : Type*) [Add A]

instance : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm

/- The following thirteen lemmas are Mathlib v4.30.0 `Mathlib/Algebra/Group/End.lean:758-801`
verbatim except that each name carries a trailing prime. -/

@[simp]
theorem coe_mul' (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one' : ⇑(1 : AddAut A) = id :=
  rfl

@[simp]
theorem coe_inv' (e : AddAut A) : ⇑e⁻¹ = e.symm := rfl

theorem mul_def' (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def' : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl

theorem inv_def' (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl

@[simp]
theorem mul_apply' (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl

@[simp]
theorem one_apply' (a : A) : (1 : AddAut A) a = a :=
  rfl

@[simp]
theorem inv_symm' (e : AddAut A) : e⁻¹.symm = e := rfl

@[simp]
theorem symm_inv' (e : AddAut A) : e.symm⁻¹ = e := rfl

@[simp]
theorem inv_apply' (e : AddAut A) (a : A) : e⁻¹ a = e.symm a := rfl

theorem inv_apply_self' (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  AddEquiv.apply_symm_apply _ _

theorem apply_inv_self' (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  AddEquiv.apply_symm_apply _ _

example (e₁ e₂ : AddAut A) : e₁ * e₂ = e₁ + e₂ := rfl
example : (1 : AddAut A) = 0 := rfl
example (e : AddAut A) : e⁻¹ = -e := rfl

end Compat430

end AddAut

@[simps]
def DistribMulAction.toAddAut' (G A : Type*) [Group G] [AddMonoid A] [DistribMulAction G A] :
    G →* AddAut A where
  toFun := DistribMulAction.toAddEquiv A
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

@[simps! +simpRhs]
def AddAut.mulLeft' {R : Type*} [Semiring R] : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut' _ _

/-! ### Block D (continued) — Mathlib v4.30.0 Mathlib/Algebra/GroupWithZero/Action/Basic.lean:104-112: the tautological `DistribMulAction (AddAut A) A`
(`AddAut.applyDistribMulAction`, its `smul_def` and `apply_faithfulSMul`), dropped in v4.33.0 together with the multiplicative structure;
vendored with primed names on top of the Group instance above. -/

namespace AddAut
instance applyDistribMulAction' {A : Type*} [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add

@[simp] protected theorem smul_def' {A : Type*} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a := rfl

instance apply_faithfulSMul' {A : Type*} [AddMonoid A] : FaithfulSMul (AddAut A) A :=
  ⟨fun h => AddEquiv.ext h⟩
end AddAut
