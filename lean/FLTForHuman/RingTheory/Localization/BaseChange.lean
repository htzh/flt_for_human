/-
  Mathlib supplement: the localization base-change lemmas on tensor products.

  Backported from the pin's
  `Definitions/Def_Mathlib_RingTheory_Localization_BaseChange.lean` (pinned `aa2d8b3`),
  which supplements the mathlib path `Mathlib/RingTheory/Localization/BaseChange.lean`;
  it lives at that path under `FLTForHuman/`.  It adds the tensor-product computation
  rules for mathlib's `IsLocalization.moduleLid`/`moduleTensorEquiv`, the extensionality
  `IsLocalization.tensorProduct_ext`, and `IsLocalization.leftModuleTensorEquiv`, the
  `M'`-linear refinement of `moduleTensorEquiv`, with its `restrictScalars` compatibility.

  Substitutions against mathlib `v4.34.0`: none — `moduleTensorEquiv` and `moduleLid`
  themselves are already mathlib (`Mathlib/RingTheory/Localization/BaseChange.lean`), and
  every declaration of the pin module is absent, so all six are transcribed at the pin's
  name.  The only proof change is that mathlib `v4.34.0` registers
  `TensorProduct.inductionOn` (no `zero` alternative) as the induction eliminator, so the
  pin's separate `zero` case in `leftModuleTensorEquiv` is dropped.
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Module

set_option autoImplicit false

section

namespace IsLocalization

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
  (M₁ : Type*) [AddCommMonoid M₁] [Module R M₁] [Module A M₁] [IsScalarTower R A M₁]

-- pin: moduleLid_symm_apply (Definitions/Def_Mathlib_RingTheory_Localization_BaseChange.lean:13)
@[simp]
lemma moduleLid_symm_apply (m : M₁) : (moduleLid S A M₁).symm m = 1 ⊗ₜ[R] m := rfl

variable (M₂ : Type*) [AddCommMonoid M₂] [Module R M₂] [Module A M₂] [IsScalarTower R A M₂]

-- pin: map_moduleTensorEquiv_tmul (Definitions/Def_Mathlib_RingTheory_Localization_BaseChange.lean:18)
@[simp]
lemma map_moduleTensorEquiv_tmul (m₁ : M₁) (m₂ : M₂) :
    moduleTensorEquiv S A M₁ M₂ (m₁ ⊗ₜ[A] m₂) = m₁ ⊗ₜ[R] m₂ := rfl

-- pin: map_moduleTensorEquiv_symm_tmul (Definitions/Def_Mathlib_RingTheory_Localization_BaseChange.lean:22)
@[simp]
lemma map_moduleTensorEquiv_symm_tmul (m₁ : M₁) (m₂ : M₂) :
    (moduleTensorEquiv S A M₁ M₂).symm (m₁ ⊗ₜ[R] m₂) = m₁ ⊗ₜ[A] m₂ := rfl

end

section

open TensorProduct

variable {A : Type*} [CommSemiring A] (S : Submonoid A)
  (B : Type*) [CommSemiring B] [Algebra A B]
  (K : Type*) [CommSemiring K] [Algebra A K] [IsLocalization S K]
  (L : Type*) [CommSemiring L] [Algebra B L] [Algebra A L] [Algebra K L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsLocalizedModule (M := B) (M' := L) S (Algebra.linearMap B L)]
  (M : Type*) [AddCommMonoid M] [Module K M]
  (P : Type*) [AddCommMonoid P] [Module K P]

include S in
-- pin: tensorProduct_ext (Definitions/Def_Mathlib_RingTheory_Localization_BaseChange.lean:40)
theorem tensorProduct_ext {g h : L ⊗[K] M →ₗ[K] P}
    (H : ∀ (x : B) (y : M), g ((algebraMap _ L x) ⊗ₜ[K] y) = h ((algebraMap _ L x) ⊗ₜ[K] y))
    : g = h := by
  apply TensorProduct.ext'
  intro l m
  obtain ⟨⟨x, s⟩, hl : (s : A) • l = algebraMap B L x⟩ :=
    IsLocalizedModule.surj (M:=B) (M':=L) S (Algebra.linearMap B L) l
  rw [← IsUnit.smul_left_cancel <| map_units K s]
  simpa [← map_smul, TensorProduct.smul_tmul', IsScalarTower.algebraMap_smul K, hl] using H x m

-- pin: leftModuleTensorEquiv (Definitions/Def_Mathlib_RingTheory_Localization_BaseChange.lean:51)
@[simps!]
noncomputable def leftModuleTensorEquiv {R : Type*} (M' : Type*)
    [Semiring M'] [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A]
    [IsLocalization S A] (M₁ : Type*) (M₂ : Type*) [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module M' M₁] [Module R M₁] [Module R M₂] [Module A M₁] [Module A M₂]
    [SMulCommClass A M' M₁] [SMulCommClass R M' M₁] [IsScalarTower R A M₁]
    [IsScalarTower R A M₂] :
    M₁ ⊗[A] M₂ ≃ₗ[M'] M₁ ⊗[R] M₂ where
  __ := IsLocalization.moduleTensorEquiv S A M₁ M₂
  map_smul' r x := by
    induction x with
    | tmul m₁ m₂ => simp [TensorProduct.smul_tmul']
    | add => simp_all

-- pin: leftModuleTensorEquiv_restrictScalars_eq (Definitions/Def_Mathlib_RingTheory_Localization_BaseChange.lean:66)
lemma leftModuleTensorEquiv_restrictScalars_eq {R M' : Type*} [CommSemiring M']
    [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A] [Algebra A M']
    [Algebra M' R] [IsLocalization S A] (M₁ : Type*) (M₂ : Type*) [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module M' M₁] [Module R M₁] [Module R M₂] [Module A M₁]
    [Module A M₂] [IsScalarTower A M' M₁] [IsScalarTower M' R M₁] [IsScalarTower R A M₁]
    [IsScalarTower R A M₂] :
    (IsLocalization.leftModuleTensorEquiv M' S A M₁ M₂).restrictScalars A =
      IsLocalization.moduleTensorEquiv S A M₁ M₂ := by
  rfl

end

end IsLocalization

end
