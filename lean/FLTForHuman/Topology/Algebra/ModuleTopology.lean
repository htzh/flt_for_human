/-
  Mathlib supplement: the module topology of a topological module, the `IsTopologicalModule`
  class, `IsBiscalar` and its `changeScalars` API.

  Backported from the pin's `Definitions/Def_Mathlib_IsModuleTopology.lean` (pinned
  `aa2d8b3`), which supplements the mathlib path
  `Mathlib/Topology/Algebra/Module/ModuleTopology.lean`; it lives at that path under
  `FLTForHuman/`.  Two independent layers live here:

  * `IsTopologicalModule R M` (continuous `•` and `+`; mathlib's `IsModuleTopology R M`
    is the *stronger* statement that the topology *is* the module topology) with its
    subtype and pi instances, and `IsBiscalar` with `LinearMap/AlgHom/AlgEquiv.changeScalars`
    and `AlgEquiv.extendScalars`;
  * additions to mathlib's `IsModuleTopology` API: the `iff` for the module topology,
    `continuous_bilinear_of_finite_free`, `topologicalSemiring`, `Algebra.moduleTopology_le`,
    `moduleTopology.trans`, `continuousLinearEquiv`/`continuousAlgEquivOfIsBiscalar`,
    `t2Space`, `locallyCompactSpaceOfFinite`, `Module.Basis.equivFun_homeo` and
    `Module.Finite.secondCountabletopology`.

  Substitutions against mathlib `v4.34.0` (dropped, use the mathlib name):

  * `IsModuleTopology.continuous_mul'` and `IsModuleTopology.continuous_mul` are
    `IsModuleTopology.continuous_mul_of_finite` (pin lines 179, 202);
  * `IsModuleTopology.Module.topologicalRing` is `IsModuleTopology.isTopologicalRing`
    (pin line 209).

  Every other pin declaration is genuinely absent from `v4.34.0` and is transcribed at
  the pin's name.  The pin's proofs are kept except for API drift: `AlgHom.restrictDomain`
  is now `AlgHom.domRestrict`, `IsTopologicalRing.to_topologicalAddGroup` is
  `IsTopologicalRing.isTopologicalAddGroup`, `IsModuleTopology.topologicalAddGroup` is
  `IsModuleTopology.isTopologicalAddGroup`, and the deprecated
  `Topology.IsQuotientMap.secondCountableTopology` is replaced by its non-deprecated
  `Topology.IsOpenQuotientMap` form in `Module.Finite.secondCountabletopology`.  The pin's
  `letI`/`haveI` on `Prop`-valued instances (pin lines 248-263, 386-437) trigger
  `linter.style.haveILetI`; as in `Topology/Algebra/Valued/WithZeroMulInt.lean`, the linter
  is disabled locally rather than weakening the pin's proofs.
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Bases

set_option autoImplicit false

-- The pin's `letI`/`haveI` install `Prop`-valued instances that typeclass search needs
-- (pin lines 248-263, 386-437); the style linter's `let`/`have` rewrite would drop them.
set_option linter.style.haveILetI false

section IsTopologicalModuleDep

open Topology

variable (R : Type*) [Ring R] [TopologicalSpace R]
  (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]

/-- A topological module: the scalar action and addition are continuous.  This is the pin's
`IsTopologicalModule`, which is weaker than mathlib's `IsModuleTopology` (that one asserts
the topology is *the* module topology). -/
-- pin: IsTopologicalModule (Definitions/Def_Mathlib_IsModuleTopology.lean:10)
class IsTopologicalModule extends ContinuousSMul R M, ContinuousAdd M

variable [IsTopologicalModule R M]

-- pin: Topology.IsInducing.topologicalModule (Definitions/Def_Mathlib_IsModuleTopology.lean:14)
protected theorem Topology.IsInducing.topologicalModule {F : Type*}
    (R : Type*) [Ring R] [TopologicalSpace R]
    {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalModule R M]
    {H : Type*} [AddCommGroup H] [Module R H] [TopologicalSpace H]
    [FunLike F H M] [LinearMapClass F R H M] (f : F) (hf : IsInducing ⇑f) :
    IsTopologicalModule R H where
  continuous_smul := (hf.continuousSMul continuous_id (by intro c x; exact map_smul f c x)).continuous_smul
  continuous_add := (hf.continuousAdd ..).continuous_add

-- pin: Submodule.instIsTopologicalModuleSubtypeMem (Definitions/Def_Mathlib_IsModuleTopology.lean:23)
instance Submodule.instIsTopologicalModuleSubtypeMem (S : Submodule R M) : IsTopologicalModule R S
    := IsInducing.subtypeVal.topologicalModule R S.subtypeL

-- pin: Pi.instTopologicalModule (Definitions/Def_Mathlib_IsModuleTopology.lean:26)
instance Pi.instTopologicalModule {ι : Type*} (R : Type*) [Ring R] [TopologicalSpace R]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsTopologicalModule R (M i)] :
    IsTopologicalModule R ((i : ι) → M i) where
  continuous_smul := by apply continuous_smul
  continuous_add := by apply continuous_add

end IsTopologicalModuleDep

section

-- pin: IsBiscalar (Definitions/Def_Mathlib_IsModuleTopology.lean:37)
class IsBiscalar (R S : Type*) {A B : Type*} [Semiring R] [Semiring S] [AddCommMonoid A]
    [AddCommMonoid B] [Module R A] [Module R B] [Module S A] [Module S B] (f : A → B) where
  map_smul₁ : ∀ (r : R) (a : A), f (r • a) = r • f a
  map_smul₂ : ∀ (s : S) (a : A), f (s • a) = s • f a

section linear

variable {A B : Type*} (S' : Type*) {S : Type*}
    [Semiring S'] [Semiring S] [AddCommMonoid A] [AddCommMonoid B] [Module S A]
    [Module S B] [Module S' A] [Module S' B]

-- pin: LinearMap.changeScalars (Definitions/Def_Mathlib_IsModuleTopology.lean:48)
def LinearMap.changeScalars (f : A →ₗ[S] B) [IsBiscalar S S' f] :
    A →ₗ[S'] B where
  __ := f
  map_smul' s x := by simpa using IsBiscalar.map_smul₂ S s x

-- pin: LinearMap.changeScalars_apply (Definitions/Def_Mathlib_IsModuleTopology.lean:53)
theorem LinearMap.changeScalars_apply (f : A →ₗ[S] B) [IsBiscalar S S' f] (a : A) :
    LinearMap.changeScalars S' f a = f a := by
  simp [changeScalars]

-- pin: LinearEquiv.changeScalars (Definitions/Def_Mathlib_IsModuleTopology.lean:57)
def LinearEquiv.changeScalars (f : A ≃ₗ[S] B) [IsBiscalar S S' f] :
    A ≃ₗ[S'] B where
  __ := LinearMap.changeScalars S' f.toLinearMap
  invFun := f.invFun
  left_inv (a : A) := by simp [LinearMap.changeScalars_apply]
  right_inv (b : B) := by simp [LinearMap.changeScalars_apply]

end linear

section algebra

-- pin: AlgEquiv.extendScalars (Definitions/Def_Mathlib_IsModuleTopology.lean:69)
@[simps! apply symm_apply]
def AlgEquiv.extendScalars {A C D : Type*} (B : Type*) [CommSemiring A] [CommSemiring C]
    [CommSemiring D] [Algebra A C] [Algebra A D] [CommSemiring B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] (f : C ≃ₐ[A] D) :
    letI := (f.toAlgHom.domRestrict B).toRingHom.toAlgebra
    C ≃ₐ[B] D where
  __ := (f.toAlgHom.domRestrict B).toRingHom.toAlgebra
  __ := f
  invFun := f.symm
  commutes' := fun _ => rfl

-- pin: IsBiscalar.commutes (Definitions/Def_Mathlib_IsModuleTopology.lean:79)
theorem IsBiscalar.commutes {S : Type*} (S' : Type*) {A B : Type*} [CommSemiring S']
    [CommSemiring S] [Semiring A] [Semiring B] [Algebra S' A] [Algebra S' B] [Algebra S A]
    [Algebra S B] (f : A →ₐ[S] B) [IsBiscalar S S' f] (s : S') :
    f (algebraMap S' A s) = algebraMap S' B s := by
  simpa [Algebra.algebraMap_eq_smul_one] using IsBiscalar.map_smul₂ (f := f) S s 1

variable {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B]

-- pin: AlgHom.changeScalars (Definitions/Def_Mathlib_IsModuleTopology.lean:89)
def AlgHom.changeScalars (f : A →ₐ[S] B) [IsBiscalar S S' f] :
    A →ₐ[S'] B where
  __ := f
  commutes' (r : _) := by simp [IsBiscalar.commutes]

-- pin: AlgHom.changeScalars_apply (Definitions/Def_Mathlib_IsModuleTopology.lean:94)
theorem AlgHom.changeScalars_apply (f : A →ₐ[S] B) [IsBiscalar S S' f] (a : A) :
    changeScalars S' f a = f a := by
  simp [changeScalars]

-- pin: AlgEquiv.changeScalars (Definitions/Def_Mathlib_IsModuleTopology.lean:98)
def AlgEquiv.changeScalars (f : A ≃ₐ[S] B) [IsBiscalar S S' f.toAlgHom] :
    A ≃ₐ[S'] B where
  __ := AlgHom.changeScalars S' f.toAlgHom
  invFun := f.invFun
  left_inv (a : A) := by simp [AlgHom.changeScalars_apply]
  right_inv (b : B) := by simp [AlgHom.changeScalars_apply]
  commutes' := fun _ => by simp

end algebra

section diamond_checks

example {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) [IsBiscalar S S f] :
    AlgHom.changeScalars S f = f := rfl

example {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B] (f : A →ₐ[S] B) [IsBiscalar S S' f]
    [IsBiscalar S' S (AlgHom.changeScalars S' f)] :
    (AlgHom.changeScalars S' f).changeScalars S = f := rfl

end diamond_checks

end

section

-- pin: ModuleTopology.isModuleTopology (Definitions/Def_Mathlib_IsModuleTopology.lean:126)
theorem ModuleTopology.isModuleTopology (R : Type*) [TopologicalSpace R] (S : Type*) [Add S]
    [SMul R S] : @IsModuleTopology R _ S _ _ (moduleTopology R S) where
  __ := moduleTopology R S
  eq_moduleTopology' := rfl

-- pin: ModuleTopology.iff (Definitions/Def_Mathlib_IsModuleTopology.lean:131)
lemma ModuleTopology.iff (R M : Type*) [Add M] [SMul R M] [TopologicalSpace R]
    [τ : TopologicalSpace M] : IsModuleTopology R M ↔ τ = moduleTopology R M :=
  ⟨fun m ↦ m.eq_moduleTopology', fun a ↦ { eq_moduleTopology' := a }⟩

namespace IsModuleTopology

open ModuleTopology

section semiring_bilinear

variable {R : Type*} [τR : TopologicalSpace R] [CommSemiring R]

variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommMonoid C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

-- pin: Module.continuous_bilinear_of_finite_free (Definitions/Def_Mathlib_IsModuleTopology.lean:147)
theorem Module.continuous_bilinear_of_finite_free [IsTopologicalSemiring R] [Module.Finite R A]
    [Module.Free R A] (bil : A →ₗ[R] B →ₗ[R] C) :
    Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  let ι := Module.Free.ChooseBasisIndex R A
  let hι : Fintype ι := Module.Free.ChooseBasisIndex.fintype R A
  let b : Module.Basis ι R A := Module.Free.chooseBasis R A
  let elinear : A ≃ₗ[R] (ι → R) := b.equivFun
  let bil' : (ι → R) →ₗ[R] B →ₗ[R] C := bil.comp elinear.symm.toLinearMap
  have := continuous_bilinear_of_pi_fintype ι bil'
  have foo : (fun ab ↦ (bil ab.1) ab.2 : A × B → C) = (fun fb ↦ bil' fb.1 fb.2) ∘
    (fun ab ↦ (elinear ab.1, ab.2) : A × B → (ι → R) × B) := by
    ext ⟨a, b⟩
    simp [bil']
  rw [foo]
  apply Continuous.comp this
  apply Continuous.prodMk
  · exact continuous_of_linearMap (elinear.toLinearMap ∘ₗ (LinearMap.fst R A B))
  · fun_prop

end semiring_bilinear

section semiring_algebra

open scoped TensorProduct

variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

open scoped TensorProduct

include R in
-- pin: topologicalSemiring (Definitions/Def_Mathlib_IsModuleTopology.lean:186)
lemma topologicalSemiring : IsTopologicalSemiring D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul_of_finite R D

end semiring_algebra

section algebra

variable (R S : Type*)
  [CommRing R] [TopologicalSpace R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]

-- pin: iff_Continuous_algebraMap (Definitions/Def_Mathlib_IsModuleTopology.lean:222)
lemma iff_Continuous_algebraMap :
    IsTopologicalModule R S ↔ Continuous (algebraMap R S) := by
  refine ⟨fun _ ↦ continuous_algebraMap R S, fun h ↦ ?_⟩
  have : Continuous (fun rs ↦ algebraMap R S rs.1 • rs.2 : R × S → S) := by fun_prop
  simp_rw [← algebra_compatible_smul S] at this
  have : ContinuousSMul R S := ⟨this⟩
  exact IsTopologicalModule.mk

end algebra

section trans

variable (R : Type*) [CommRing R] [TopologicalSpace R]

-- pin: isTopologicalModule (Definitions/Def_Mathlib_IsModuleTopology.lean:236)
theorem isTopologicalModule
    (M : Type*) [AddCommGroup M] [TopologicalSpace M] [Module R M]
    [IsModuleTopology R M] : IsTopologicalModule R M where
      continuous_smul := eq_moduleTopology R M ▸ (continuousSMul R M).1
      continuous_add := eq_moduleTopology R M ▸ (continuousAdd R M).1

variable (S : Type*) [CommRing S] [TopologicalSpace S] [Algebra R S]

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

-- pin: Algebra.moduleTopology_le (Definitions/Def_Mathlib_IsModuleTopology.lean:246)
lemma _root_.Algebra.moduleTopology_le [IsTopologicalModule R S] :
    moduleTopology R M ≤ moduleTopology S M := by
  letI : TopologicalSpace M := moduleTopology S M
  haveI : ContinuousAdd M := continuousAdd S M
  have ⟨cts_smul⟩ : ContinuousSMul S M := continuousSMul S M
  suffices ContinuousSMul R M from _root_.moduleTopology_le R M
  constructor
  suffices Continuous (fun rm ↦ algebraMap R S rm.1 • rm.2 : R × M → M) by
    simpa [← algebra_compatible_smul S]
  fun_prop

-- pin: moduleTopology.trans (Definitions/Def_Mathlib_IsModuleTopology.lean:257)
lemma _root_.moduleTopology.trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S] :
    moduleTopology R M = moduleTopology S M := by
  have := IsModuleTopology.isTopologicalModule
  refine le_antisymm (Algebra.moduleTopology_le _ _ _) ?_
  letI : TopologicalSpace M := moduleTopology R M
  haveI : IsModuleTopology R M := isModuleTopology R M
  haveI : ContinuousAdd M := continuousAdd R M
  have ⟨cts_smul⟩ : ContinuousSMul R M := continuousSMul R M
  suffices ContinuousSMul S M from _root_.moduleTopology_le S M
  constructor
  let bil : S →ₗ[R] M →ₗ[R] M := {
    toFun s := {
      toFun m := s • m
      map_add' := DistribSMul.smul_add s
      map_smul' := smul_comm s
    }
    map_add' s t := by
      ext m
      exact Module.add_smul s t m
    map_smul' r s := by
      ext m
      exact IsScalarTower.smul_assoc r s m
  }
  exact continuous_bilinear_of_finite_left bil

-- pin: trans (Definitions/Def_Mathlib_IsModuleTopology.lean:282)
lemma trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S]
    [τ : TopologicalSpace M] :
    IsModuleTopology R M ↔ IsModuleTopology S M := by
  simp [iff R M, iff S M, moduleTopology.trans R S]

end trans

section opensubring
variable (R S : Type*)
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra R S]

open scoped Topology in

-- pin: of_continuous_isOpenMap_algebraMap (Definitions/Def_Mathlib_IsModuleTopology.lean:297)
theorem of_continuous_isOpenMap_algebraMap (hcont : Continuous (algebraMap R S))
    (hopen : IsOpenMap (algebraMap R S)) : IsModuleTopology R S where
  eq_moduleTopology' := by

    have : ContinuousSMul R S := continuousSMul_of_algebraMap R S hcont

    have hcont_id : Continuous[moduleTopology R S, _] id :=
      continuous_id_iff_le.2 <| moduleTopology_le _ _

    have hcont_alg : Continuous[_, moduleTopology R S] (Algebra.linearMap R S) :=

      letI := moduleTopology R S
      letI : ContinuousAdd S := ModuleTopology.continuousAdd _ _
      letI : ContinuousSMul R S := ModuleTopology.continuousSMul _ _
      IsModuleTopology.continuous_of_linearMap _

    have hopen_mpr {U : Set S} (h : IsOpen U) : IsOpen[moduleTopology R S] U :=
      @Continuous.isOpen_preimage S S (moduleTopology R S) _ id hcont_id U h

    have hopen_mp {U : Set S} (h : IsOpen[moduleTopology R S] U)
        (hUS : U ⊆ Set.range (algebraMap R S)) : IsOpen U :=
      Set.image_preimage_eq_of_subset hUS ▸ hopen _ <|
        @Continuous.isOpen_preimage R S _ (moduleTopology R S) _ hcont_alg U h

    rw [IsTopologicalRing.isTopologicalAddGroup.ext_iff <|

      @IsModuleTopology.isTopologicalAddGroup R _ _ S _ _ (moduleTopology R S) (isModuleTopology R S)]

    apply (nhds_basis_opens 0).ext (@nhds_basis_opens S (moduleTopology R S) 0)
    ·
      exact fun U hU => ⟨U, ⟨⟨hU.1, hopen_mpr hU.2⟩, by simp⟩⟩
    ·
      intro U hU

      refine ⟨Set.range (algebraMap R S) ∩ U, ⟨⟨⟨⟨0, by simp⟩, hU.1⟩, ?_⟩, by simp⟩⟩

      let hopen_range := hopen_mpr hopen.isOpen_range

      exact hopen_mp (@IsOpen.inter _ (moduleTopology R S) _ _ hopen_range hU.2) (by simp)

end opensubring

section quotientMap

variable {R M : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (N : Type*) [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

-- pin: of_isQuotientMap (Definitions/Def_Mathlib_IsModuleTopology.lean:345)
theorem of_isQuotientMap (f : N →ₗ[R] M) (h : Topology.IsQuotientMap f) : IsModuleTopology R M := by
  rw [iff, eq_coinduced_of_surjective h.surjective, h.eq_coinduced]

variable [ContinuousAdd M] [ContinuousSMul R M]

-- pin: of_isOpenMap_surjective (Definitions/Def_Mathlib_IsModuleTopology.lean:350)
theorem of_isOpenMap_surjective (f : N →ₗ[R] M) (h : IsOpenMap f) (hsurj : Function.Surjective f)
    : IsModuleTopology R M := by
  apply of_isQuotientMap N f
  refine IsOpenQuotientMap.isQuotientMap ⟨hsurj, continuous_of_linearMap f, h⟩

-- pin: of_inverse (Definitions/Def_Mathlib_IsModuleTopology.lean:355)
theorem of_inverse (f : N →ₗ[R] M) (g : M → N) (hc : Continuous g) (hi : Function.LeftInverse f g)
    : IsModuleTopology R M := by
  apply of_isQuotientMap N f
  exact Topology.IsQuotientMap.of_inverse hc (continuous_of_linearMap f) hi

end quotientMap

-- pin: continuousLinearEquiv (Definitions/Def_Mathlib_IsModuleTopology.lean:363)
@[simps!]
def continuousLinearEquiv {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [Semiring R] [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₗ[R] B) :
    A ≃L[R] B where
  toFun := e
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

-- pin: continuousLinearEquivOfIsBiscalar (Definitions/Def_Mathlib_IsModuleTopology.lean:377)
def continuousLinearEquivOfIsBiscalar {A B : Type*} (S' : Type*) {S : Type*}
    [Semiring S'] [Semiring S] [AddCommMonoid A] [AddCommMonoid B] [Module S A]
    [Module S B] [Module S' A] [Module S' B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace S'] [IsModuleTopology S' A] [IsModuleTopology S' B] (e : A ≃ₗ[S] B)
    [IsBiscalar S S' e] :
    A ≃L[S] B where
  toLinearEquiv := e
  continuous_toFun := by
    change Continuous (e.changeScalars S')
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (e.changeScalars S').symm
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _

-- pin: continuousAlgEquivOfIsBiscalar (Definitions/Def_Mathlib_IsModuleTopology.lean:393)
def continuousAlgEquivOfIsBiscalar {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S]
    [Algebra S A] [Algebra S B] [Algebra S' A] [Algebra S' B] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace S'] [IsModuleTopology S' A]
    [IsModuleTopology S' B] (e : A ≃ₐ[S] B) [IsBiscalar S S' e.toAlgHom] :
    A ≃A[S] B where
  toAlgEquiv := e
  continuous_toFun := by

    change Continuous (e.changeScalars S').toLinearEquiv

    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (e.changeScalars S').toLinearEquiv.symm
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _

-- pin: continuousAlgEquivOfIsBiscalar_apply (Definitions/Def_Mathlib_IsModuleTopology.lean:412)
@[simp]
theorem continuousAlgEquivOfIsBiscalar_apply {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S]
    [Algebra S A] [Algebra S B] [Algebra S' A] [Algebra S' B]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace S'] [IsModuleTopology S' A]
    [IsModuleTopology S' B] (e : A ≃ₐ[S] B) [IsBiscalar S S' e.toAlgHom] (a : A) :
    continuousAlgEquivOfIsBiscalar S' e a = e a :=
  rfl

-- pin: continuousAlgEquivOfAlgEquiv (Definitions/Def_Mathlib_IsModuleTopology.lean:420)
def continuousAlgEquivOfAlgEquiv {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₐ[R] B) :
    A ≃A[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

-- pin: t2Space (Definitions/Def_Mathlib_IsModuleTopology.lean:433)
theorem t2Space (R : Type*) {M : Type*} [Semiring R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [TopologicalSpace R] [TopologicalSpace M] [T2Space R]
    [ContinuousAdd R] [ContinuousMul R] [IsModuleTopology R M]
    : T2Space M := by
  have := IsModuleTopology.isTopologicalAddGroup R M
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
  let f := (Module.Free.chooseBasis R M).repr |>.toLinearMap
  let g : (Module.Free.ChooseBasisIndex R M →₀ R) →ₗ[R] (Module.Free.ChooseBasisIndex R M → R) := {
    __ := Finsupp.coeFnAddHom
    map_smul' _ _ := rfl
  }
  suffices hpre : (g.comp f) ⁻¹' {0} = {0}  by
    rw [← hpre]
    apply IsClosed.preimage <| IsModuleTopology.continuous_of_linearMap (g.comp f)
    exact isClosed_singleton
  ext x
  simp [map_eq_zero_iff g DFunLike.coe_injective,
    map_eq_zero_iff f (Module.Free.chooseBasis R M).repr.injective]

-- pin: t2Space' (Definitions/Def_Mathlib_IsModuleTopology.lean:452)
theorem t2Space' {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [TopologicalSpace K] [TopologicalSpace V] [T2Space K]
    [ContinuousAdd K] [ContinuousMul K] [mt : IsModuleTopology K V]
    : T2Space V := by
  apply t2Space (R := K)

section locally_compact

variable (R : Type*) [τR : TopologicalSpace R] [Ring R] [IsTopologicalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]

-- pin: locallyCompactSpaceOfFinite (Definitions/Def_Mathlib_IsModuleTopology.lean:463)
theorem locallyCompactSpaceOfFinite [LocallyCompactSpace R] [Module.Finite R M] :
    LocallyCompactSpace M := by
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  exact IsOpenQuotientMap.locallyCompactSpace
    (IsModuleTopology.isOpenQuotientMap_of_surjective hφ)

end locally_compact

section ModuleFinite

-- pin: Module.Basis.equivFun_homeo (Definitions/Def_Mathlib_IsModuleTopology.lean:482)
@[simps!]
noncomputable
def Module.Basis.equivFun_homeo (K R : Type*) [Field K] [Ring R] [Module K R]
    [Module.Finite K R] [TopologicalSpace K] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalRing K] [IsModuleTopology K R] : R ≃L[K] (Fin (Module.finrank K R) → K) where
  __ := Module.Basis.equivFun (Module.finBasisOfFinrankEq K R (rfl))
  continuous_toFun :=
    IsModuleTopology.continuous_of_linearMap
      (Module.Basis.equivFun (Module.finBasisOfFinrankEq K R (rfl))).toLinearMap
  continuous_invFun :=
    IsModuleTopology.continuous_of_linearMap
      (Module.Basis.equivFun (Module.finBasisOfFinrankEq K R (rfl))).symm.toLinearMap

end ModuleFinite

section SecondCountableTopology

-- pin: Module.Finite.secondCountabletopology (Definitions/Def_Mathlib_IsModuleTopology.lean:497)
lemma _root_.Module.Finite.secondCountabletopology (R M : Type*)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [TopologicalSpace M]
    [IsModuleTopology R M] : SecondCountableTopology M := by
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  exact Topology.IsOpenQuotientMap.secondCountableTopology
    (IsModuleTopology.isOpenQuotientMap_of_surjective hφ)

end SecondCountableTopology

end IsModuleTopology

end
