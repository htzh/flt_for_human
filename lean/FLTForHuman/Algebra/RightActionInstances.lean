/-
  Mathlib supplement: the right-action structures on a tensor product.

  Backported from the pin's `Definitions/Def_Mathlib_RightActionInstances.lean` (pinned
  `aa2d8b3`), which mirrors the mathlib path
  `Mathlib/RingTheory/TensorProduct/RightActionInstances.lean`; it lives at the same path
  under `FLTForHuman/`.  The namespace `TensorProduct.RightActions` carries the scoped
  right `SMul`/`Module`/`Algebra` structures on `M ⊗[R] S` (opened with
  `open scoped TensorProduct.RightActions`), the right-module commutativity
  `Module.TensorProduct.comm`, and the right-hand base-change API.

  Substitutions against mathlib `v4.34.0` (dropped, use the mathlib name):

  * `algebraMap_eval` is `Algebra.TensorProduct.right_algebraMap_apply` (pin line 55);
  * `Algebra.TensorProduct.comm` is `Algebra.TensorProduct.commRight` (pin line 57);
  * `Algebra.TensorProduct.comm_apply_tmul` is `Algebra.TensorProduct.commRight_tmul`
    (pin line 62);
  * `Algebra.TensorProduct.comm_symm_apply_tmul` is `Algebra.TensorProduct.commRight_symm_tmul`
    (pin line 66).

  The scoped `Algebra S (B ⊗[R] S)` instance keeps its pin statement and delegates its
  body to mathlib's `Algebra.TensorProduct.rightAlgebra`.  Everything else is transcribed
  at the pin's name; the proof changes are: mathlib `v4.34.0` registers
  `TensorProduct.inductionOn` (no `zero` alternative) as induction eliminator, so the
  pin's separate `zero` cases in `Module.TensorProduct.comm` are dropped;
  `IsModuleTopology.topologicalAddGroup` is now `isTopologicalAddGroup`; and
  `AlgebraMap.baseChange`'s `commutes'`, which v4.34.0's generalized
  `Algebra.TensorProduct.map` no longer closes by `simp` alone, is closed with
  `Algebra.TensorProduct.right_algebraMap_apply`.  The pin's names
  repeat the `TensorProduct` namespace (`Module.TensorProduct.comm`,
  `Algebra.TensorProduct.basis`), so `linter.dupNamespace` is disabled as mathlib does in
  `Mathlib/RingTheory/TensorProduct/Maps.lean`.
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option autoImplicit false

-- The pin's names repeat the `TensorProduct` namespace (`Module.TensorProduct.comm`,
-- `Algebra.TensorProduct.basis`); mathlib suppresses the same linter in
-- `Mathlib/RingTheory/TensorProduct/Maps.lean`.
set_option linter.dupNamespace false

section

namespace TensorProduct.RightActions

noncomputable section semiring

variable (R S A B M : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M]
    [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B]

scoped instance : SMul S (M ⊗[R] S) where
  smul s e := TensorProduct.comm _ _ _ (s • (TensorProduct.comm _ _ _ e))

-- pin: smul_def (Definitions/Def_Mathlib_RightActionInstances.lean:18)
@[simp]
lemma smul_def (r : S) (m : M ⊗[R] S) :
    r • m = (TensorProduct.comm _ _ _).symm (r • (TensorProduct.comm _ _ _ m)) := rfl

scoped instance : Module S (M ⊗[R] S) where
  one_smul x := by simp_rw [smul_def, one_smul, (TensorProduct.comm R M S).symm_apply_apply]
  mul_smul a b x := by simp_rw [smul_def, mul_smul, (TensorProduct.comm R M S).apply_symm_apply]
  smul_zero := by simp
  smul_add := by simp
  add_smul := by simp [add_smul]
  zero_smul := by simp

scoped instance : Algebra S (B ⊗[R] S) :=
  Algebra.TensorProduct.rightAlgebra

-- pin: Module.TensorProduct.comm (Definitions/Def_Mathlib_RightActionInstances.lean:69)
noncomputable def Module.TensorProduct.comm : A ⊗[R] M ≃ₗ[A] M ⊗[R] A where
  __ := (_root_.TensorProduct.comm R A M).toAddEquiv
  map_smul' a am := by
    induction am with
    | tmul x y =>
        simp only [smul_tmul', smul_eq_mul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, comm_tmul, RingHom.id_apply, smul_def, comm_symm_tmul]
    | add x y _ _ =>
      simp_all only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        RingHom.id_apply, smul_def, smul_add, map_add]

variable {A N} in
-- pin: Module.TensorProduct.comm_apply_tmul (Definitions/Def_Mathlib_RightActionInstances.lean:83)
@[simp] lemma Module.TensorProduct.comm_apply_tmul (a : A) (m : M) :
    Module.TensorProduct.comm R A M (a ⊗ₜ m) = m ⊗ₜ a := rfl

-- pin: Module.TensorProduct.comm_symm_apply_tmul (Definitions/Def_Mathlib_RightActionInstances.lean:86)
@[simp] lemma Module.TensorProduct.comm_symm_apply_tmul (m : M) (a : A) :
    (Module.TensorProduct.comm R A M).symm (m ⊗ₜ a) = a ⊗ₜ m := rfl

scoped instance [Module.Finite R M] : Module.Finite A (M ⊗[R] A) :=
  Module.Finite.equiv (Module.TensorProduct.comm R A M)

scoped instance [Module.Free R M] : Module.Free A (M ⊗[R] A) :=
  Module.Free.of_equiv (Module.TensorProduct.comm R A M)

scoped instance : IsScalarTower R A (M ⊗[R] A) where
  smul_assoc r a ma := by simp

@[nolint unusedArguments]
scoped instance [TopologicalSpace A] [Module.Finite R M] :
    TopologicalSpace (M ⊗[R] A) :=
  moduleTopology A (M ⊗[R] A)

scoped instance [TopologicalSpace A] [Module.Finite R M] :
  IsModuleTopology A (M ⊗[R] A) := ⟨rfl⟩

-- pin: LinearMap.baseChange (Definitions/Def_Mathlib_RightActionInstances.lean:107)
noncomputable abbrev LinearMap.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V →ₗ[R] W) : V ⊗[R] A →ₗ[A] W ⊗[R] A :=
  (Module.TensorProduct.comm R A W) ∘ₗ
    (_root_.LinearMap.baseChange A φ) ∘ₗ
    (Module.TensorProduct.comm R A V).symm

-- pin: LinearMap.baseChange_id (Definitions/Def_Mathlib_RightActionInstances.lean:116)
@[simp]
lemma LinearMap.baseChange_id (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V]
    (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.baseChange R V V A .id = .id := by
  ext
  simp

-- pin: LinearMap.baseChange_comp (Definitions/Def_Mathlib_RightActionInstances.lean:123)
theorem LinearMap.baseChange_comp (R : Type*) [CommRing R]
    (U V W : Type*) [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (A : Type*) [CommRing A] [Algebra R A]
    (φ : U →ₗ[R] V) (ψ : V →ₗ[R] W) :
    LinearMap.baseChange R V W A ψ ∘ₗ LinearMap.baseChange R U V A φ =
    LinearMap.baseChange R U W A (ψ ∘ₗ φ) := by
  ext
  simp [_root_.LinearMap.baseChange_comp]

-- pin: LinearEquiv.baseChange (Definitions/Def_Mathlib_RightActionInstances.lean:135)
noncomputable abbrev LinearEquiv.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V ≃ₗ[R] W) : V ⊗[R] A ≃ₗ[A] W ⊗[R] A where
  __ := LinearMap.baseChange _ _ _ _ φ.toLinearMap
  invFun := LinearMap.baseChange _ _ _ _ φ.symm.toLinearMap
  left_inv := by
    intro x
    calc
    _ = (LinearMap.baseChange R W V A φ.symm ∘ₗ LinearMap.baseChange R V W A φ) x := rfl
    _ = _ := by simp [LinearMap.baseChange_comp]
  right_inv := by
    intro y
    change ((LinearMap.baseChange R V W A φ) ∘ₗ (LinearMap.baseChange R W V A φ.symm)) y = _
    simp [LinearMap.baseChange_comp]

-- pin: AlgebraMap.baseChange (Definitions/Def_Mathlib_RightActionInstances.lean:151)
noncomputable def AlgebraMap.baseChange (R : Type*) [CommRing R]
    (B C : Type*) [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : B →ₐ[R] C) : B ⊗[R] A →ₐ[A] C ⊗[R] A where
  __ := Algebra.TensorProduct.map φ (.id R A)
  commutes' a := by
    rw [Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply]
    simp

-- pin: Algebra.TensorProduct.basis (Definitions/Def_Mathlib_RightActionInstances.lean:158)
def Algebra.TensorProduct.basis {R : Type*} (A : Type*) {M : Type*} {ι : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    (b : Module.Basis ι R M) :
    Module.Basis ι A (M ⊗[R] A) :=
  (_root_.Algebra.TensorProduct.basis A b).map (Module.TensorProduct.comm R A M)

end semiring

noncomputable section ring

variable (R A B M : Type*) [CommRing R]
    [CommRing A] [Algebra R A]
    [Ring B] [Algebra R B]
    [AddCommGroup M] [Module R M]

-- pin: instIsTopologicalAddGroup (Definitions/Def_Mathlib_RightActionInstances.lean:173)
scoped instance [TopologicalSpace A] [Module.Finite R M] :
    IsTopologicalAddGroup (M ⊗[R] A) := IsModuleTopology.isTopologicalAddGroup A (M ⊗[R] A)

end ring

end TensorProduct.RightActions

end
