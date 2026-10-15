/-
  Base-change data for the infinite adele ring: the number-field archimedean base change
  `K∞ ⊗_K L ≃ L∞` and the data it is assembled from.

  Transcribed from the pin's `Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean`
  (pinned `aa2d8b3`, 360 lines / 36 declarations), whole and at the pin's names, with a
  `-- pin:` provenance comment on every declaration.  The pin's bare mathlib import is
  replaced by the explicit imports below, and the pin's `Def_NumberField_Extension` is the
  landed W1 module `FLTForHuman/NumberTheory/NumberField/Extension.lean`.

  ## Substitutions against mathlib `v4.34.0`

  | pin declaration | mathlib `v4.34.0` | action |
  |---|---|---|
  | `Pi.algHom` (used by `tensorPiAlgHom`) | `AlgHom.pi` | substituted — the pin's name is deprecated since 2026-05-30 |
  | `TensorProduct.induction_on` (used by `tensorPiAlgHom_bijective`) | `TensorProduct.inductionOn` | substituted — deprecated alias; the separate `zero` case is dropped |
  | `algebraMap_infiniteAdeleRing_apply` | `InfiniteAdeleRing.algebraMap_apply` (statement `algebraMap K K∞ x v = x`) | transcribed: the pin's `L`-generic completion-valued form is the one `baseChangeRingEquiv_one_tmul` consumes |

  Every other declaration is genuinely absent from mathlib `v4.34.0`
  (`evalAlgHom`, `InfinitePlaceData`, `tensorPiAlgHom`, `tensorPiAlgEquiv`, `collapsePlaces`,
  `BaseChangeData`, `adeleAlgebra`, `conorm`, the `self*` block and the gates) and is
  transcribed at the pin's name.

  ## Cap discipline

  The pin pins definitional-equality transparency low and raises its heartbeat budget on
  `tensorPiAlgHom_bijective`.  Neither is transcribed: the proof is re-elaborated under the
  plain 200k cap with no option set anywhere in this file.
-/
import FLTForHuman.NumberTheory.NumberField.Extension
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open NumberField TensorProduct

open scoped TensorProduct

namespace FLT.InfiniteAdeleBaseChange

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

-- pin: evalAlgHom (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:14)
def evalAlgHom (v : InfinitePlace K) : InfiniteAdeleRing K →ₐ[K] v.Completion where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

-- pin: evalAlgHom_apply (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:22)
@[simp] lemma evalAlgHom_apply (v : InfinitePlace K) (x : InfiniteAdeleRing K) :
    evalAlgHom K v x = x v := rfl

-- pin: InfinitePlaceData (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:25)
structure InfinitePlaceData where

  placeEquiv (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) ≃+* ((w : v.Extension L) → w.1.Completion)

  placeEquiv_one_tmul (v : InfinitePlace K) (l : L) (w : v.Extension L) :
    placeEquiv v ((1 : v.Completion) ⊗ₜ[K] l) w = algebraMap L w.1.Completion l

-- pin: tensorPiAlgHom (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:33)
def tensorPiAlgHom :
    ((InfiniteAdeleRing K) ⊗[K] L) →ₐ[K] ((v : InfinitePlace K) → (v.Completion ⊗[K] L)) :=
  AlgHom.pi fun v => Algebra.TensorProduct.map (evalAlgHom K v) (AlgHom.id K L)

-- pin: tensorPiAlgHom_tmul_apply (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:38)
@[simp] lemma tensorPiAlgHom_tmul_apply (x : InfiniteAdeleRing K) (l : L)
    (v : InfinitePlace K) :
    tensorPiAlgHom K L (x ⊗ₜ[K] l) v = x v ⊗ₜ[K] l := rfl

-- pin: tensorPiAlgHom_bijective (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:45)
theorem tensorPiAlgHom_bijective [NumberField K] :
    Function.Bijective (tensorPiAlgHom K L) := by
  classical
  let e : ((InfiniteAdeleRing K) ⊗[K] L) ≃ₐ[K]
      ((v : InfinitePlace K) → (v.Completion ⊗[K] L)) :=
    (Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L).trans
      ((Algebra.TensorProduct.piRight K K L fun v : InfinitePlace K => v.Completion).trans
        (AlgEquiv.piCongrRight fun v : InfinitePlace K =>
          Algebra.TensorProduct.comm K L v.Completion))
  have h : tensorPiAlgHom K L = e.toAlgHom := by
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x l =>
      funext v
      show x v ⊗ₜ[K] l = Algebra.TensorProduct.comm K L v.Completion
        ((Algebra.TensorProduct.piRight K K L fun v : InfinitePlace K => v.Completion)
          (Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L (x ⊗ₜ[K] l)) v)

      rfl
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]
  rw [h]
  exact e.bijective

-- pin: tensorPiAlgEquiv (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:74)
def tensorPiAlgEquiv [NumberField K] :
    ((InfiniteAdeleRing K) ⊗[K] L) ≃ₐ[K] ((v : InfinitePlace K) → (v.Completion ⊗[K] L)) :=
  AlgEquiv.ofBijective (tensorPiAlgHom K L) (tensorPiAlgHom_bijective K L)

-- pin: tensorPiAlgEquiv_tmul_apply (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:78)
@[simp] lemma tensorPiAlgEquiv_tmul_apply [NumberField K] (x : InfiniteAdeleRing K) (l : L)
    (v : InfinitePlace K) :
    tensorPiAlgEquiv K L (x ⊗ₜ[K] l) v = x v ⊗ₜ[K] l := rfl

-- pin: collapsePlaces (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:82)
def collapsePlaces :
    ((v : InfinitePlace K) → ((w : v.Extension L) → w.1.Completion)) ≃+*
      InfiniteAdeleRing L where
  toFun x w := x (w.comap (algebraMap K L)) ⟨w, rfl⟩
  invFun y v w := y w.1
  left_inv x := by
    funext v w
    obtain ⟨w, rfl⟩ := w
    rfl
  right_inv y := by funext w; rfl
  map_mul' x y := rfl
  map_add' x y := rfl

-- pin: collapsePlaces_apply (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:95)
@[simp] lemma collapsePlaces_apply
    (x : (v : InfinitePlace K) → ((w : v.Extension L) → w.1.Completion))
    (w : InfinitePlace L) :
    collapsePlaces K L x w = x (w.comap (algebraMap K L)) ⟨w, rfl⟩ := rfl

-- pin: algebraMap_infiniteAdeleRing_apply (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:100)
lemma algebraMap_infiniteAdeleRing_apply (l : L) (w : InfinitePlace L) :
    algebraMap L (InfiniteAdeleRing L) l w = algebraMap L w.Completion l := rfl

variable {K L}

namespace InfinitePlaceData

variable (D : InfinitePlaceData K L)

section Derived

variable [NumberField K]

-- pin: InfinitePlaceData.baseChangeRingEquiv (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:113)
def baseChangeRingEquiv :
    ((InfiniteAdeleRing K) ⊗[K] L) ≃+* InfiniteAdeleRing L :=
  ((tensorPiAlgEquiv K L).toRingEquiv.trans
    (RingEquiv.piCongrRight fun v => D.placeEquiv v)).trans (collapsePlaces K L)

-- pin: InfinitePlaceData.baseChangeRingEquiv_apply (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:118)
lemma baseChangeRingEquiv_apply (z : (InfiniteAdeleRing K) ⊗[K] L) (w : InfinitePlace L) :
    D.baseChangeRingEquiv z w =
      D.placeEquiv (w.comap (algebraMap K L))
        (tensorPiAlgEquiv K L z (w.comap (algebraMap K L))) ⟨w, rfl⟩ := rfl

-- pin: InfinitePlaceData.baseChangeRingEquiv_one_tmul (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:123)
theorem baseChangeRingEquiv_one_tmul (l : L) :
    D.baseChangeRingEquiv ((1 : InfiniteAdeleRing K) ⊗ₜ[K] l) =
      algebraMap L (InfiniteAdeleRing L) l := by
  funext w
  have h1 : D.baseChangeRingEquiv ((1 : InfiniteAdeleRing K) ⊗ₜ[K] l) w =
      D.placeEquiv (w.comap (algebraMap K L))
        ((1 : (w.comap (algebraMap K L)).Completion) ⊗ₜ[K] l) ⟨w, rfl⟩ := rfl
  rw [h1, algebraMap_infiniteAdeleRing_apply]
  exact D.placeEquiv_one_tmul (w.comap (algebraMap K L)) l ⟨w, rfl⟩

-- pin: InfinitePlaceData.conorm (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:133)
def conorm : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  D.baseChangeRingEquiv.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom

-- pin: InfinitePlaceData.conorm_apply (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:136)
lemma conorm_apply (x : InfiniteAdeleRing K) :
    D.conorm x = D.baseChangeRingEquiv (x ⊗ₜ[K] (1 : L)) := rfl

-- pin: InfinitePlaceData.baseChangeRingEquiv_tmul_one (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:139)
lemma baseChangeRingEquiv_tmul_one (x : InfiniteAdeleRing K) :
    D.baseChangeRingEquiv (x ⊗ₜ[K] (1 : L)) = D.conorm x := rfl

-- pin: InfinitePlaceData.conorm_algebraMap (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:142)
theorem conorm_algebraMap (c : K) :
    D.conorm (algebraMap K (InfiniteAdeleRing K) c) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L c) := by
  have key : (algebraMap K (InfiniteAdeleRing K) c) ⊗ₜ[K] (1 : L) =
      (1 : InfiniteAdeleRing K) ⊗ₜ[K] (algebraMap K L c) := by
    rw [Algebra.algebraMap_eq_smul_one (A := InfiniteAdeleRing K) c,
      Algebra.algebraMap_eq_smul_one (A := L) c, TensorProduct.smul_tmul]
  rw [conorm_apply, key, D.baseChangeRingEquiv_one_tmul]

-- pin: InfinitePlaceData.adeleAlgebra (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:151)
@[reducible] def adeleAlgebra : Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
  D.conorm.toAlgebra

-- pin: InfinitePlaceData.baseChangeAlgEquiv (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:154)
def baseChangeAlgEquiv :
    letI := D.adeleAlgebra
    ((InfiniteAdeleRing K) ⊗[K] L) ≃ₐ[InfiniteAdeleRing K] InfiniteAdeleRing L :=
  letI := D.adeleAlgebra
  AlgEquiv.ofRingEquiv (f := D.baseChangeRingEquiv) (fun x => by
    rw [show algebraMap (InfiniteAdeleRing K) ((InfiniteAdeleRing K) ⊗[K] L) x
        = x ⊗ₜ[K] (1 : L) from rfl]
    rw [D.baseChangeRingEquiv_tmul_one]
    rfl)

-- pin: InfinitePlaceData.baseChangeAlgEquiv_apply (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:164)
lemma baseChangeAlgEquiv_apply (z : (InfiniteAdeleRing K) ⊗[K] L) :
    D.baseChangeAlgEquiv z = D.baseChangeRingEquiv z := rfl

-- pin: InfinitePlaceData.baseChangeAlgEquiv_one_tmul (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:167)
theorem baseChangeAlgEquiv_one_tmul (l : L) :
    D.baseChangeAlgEquiv ((1 : InfiniteAdeleRing K) ⊗ₜ[K] l) =
      algebraMap L (InfiniteAdeleRing L) l :=
  D.baseChangeRingEquiv_one_tmul l

end Derived

end InfinitePlaceData

variable (K L)

-- pin: BaseChangeData (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:178)
structure BaseChangeData [NumberField K]
    [Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L)] where

  tensorEquiv : ((InfiniteAdeleRing K) ⊗[K] L) ≃ₐ[InfiniteAdeleRing K] InfiniteAdeleRing L

  tensorEquiv_one_tmul (l : L) :
    tensorEquiv ((1 : InfiniteAdeleRing K) ⊗ₜ[K] l) = algebraMap L (InfiniteAdeleRing L) l

variable {K L}

-- pin: BaseChangeData.ofInfinitePlaceData (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:188)
def BaseChangeData.ofInfinitePlaceData [NumberField K] (D : InfinitePlaceData K L) :
    letI := D.adeleAlgebra
    BaseChangeData K L :=
  letI := D.adeleAlgebra
  { tensorEquiv := D.baseChangeAlgEquiv
    tensorEquiv_one_tmul := fun l => D.baseChangeAlgEquiv_one_tmul l }

section SelfExtension

variable (K)

-- pin: uniqueSelfExtension (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:199)
instance uniqueSelfExtension (v : InfinitePlace K) : Unique (v.Extension K) where
  default := ⟨v, rfl⟩
  uniq w := Subtype.ext w.property

-- pin: selfPiEquiv (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:203)
def selfPiEquiv (v : InfinitePlace K) :
    ((w : v.Extension K) → w.1.Completion) ≃+* v.Completion :=
  RingEquiv.piUnique fun w : v.Extension K => w.1.Completion

-- pin: selfPlaceEquiv (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:207)
def selfPlaceEquiv (v : InfinitePlace K) :
    (v.Completion ⊗[K] K) ≃+* ((w : v.Extension K) → w.1.Completion) :=
  (Algebra.TensorProduct.rid K K v.Completion).toRingEquiv.trans (selfPiEquiv K v).symm

-- pin: selfPlaceEquiv_apply_default (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:211)
lemma selfPlaceEquiv_apply_default (v : InfinitePlace K) (z : v.Completion ⊗[K] K) :
    selfPlaceEquiv K v z (default : v.Extension K) =
      Algebra.TensorProduct.rid K K v.Completion z := rfl

-- pin: selfPlaceEquiv_one_tmul (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:215)
lemma selfPlaceEquiv_one_tmul (v : InfinitePlace K) (l : K) (w : v.Extension K) :
    selfPlaceEquiv K v ((1 : v.Completion) ⊗ₜ[K] l) w = algebraMap K w.1.Completion l := by
  obtain rfl : w = default := Unique.eq_default w
  rw [selfPlaceEquiv_apply_default, Algebra.TensorProduct.rid_tmul]
  exact (Algebra.algebraMap_eq_smul_one l).symm

-- pin: selfInfinitePlaceData (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:221)
def selfInfinitePlaceData : InfinitePlaceData K K where
  placeEquiv := selfPlaceEquiv K
  placeEquiv_one_tmul := selfPlaceEquiv_one_tmul K

-- pin: selfBaseChangeData (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:225)
def selfBaseChangeData [NumberField K] :
    letI := (selfInfinitePlaceData K).adeleAlgebra
    BaseChangeData K K :=
  BaseChangeData.ofInfinitePlaceData (selfInfinitePlaceData K)

end SelfExtension

section Gates

-- pin: algebraMap_rat_injective (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:234)
theorem algebraMap_rat_injective :
    Function.Injective (algebraMap ℚ (InfiniteAdeleRing ℚ)) :=
  (algebraMap ℚ (InfiniteAdeleRing ℚ)).injective

-- pin: gate_principal_two_ne_three (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:238)
theorem gate_principal_two_ne_three :
    algebraMap ℚ (InfiniteAdeleRing ℚ) 2 ≠ algebraMap ℚ (InfiniteAdeleRing ℚ) 3 := fun h =>
  (by norm_num : (2 : ℚ) ≠ 3) (algebraMap_rat_injective h)

-- pin: gate_baseChangeRingEquiv_separates (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:242)
theorem gate_baseChangeRingEquiv_separates :
    (selfInfinitePlaceData ℚ).baseChangeRingEquiv ((1 : InfiniteAdeleRing ℚ) ⊗ₜ[ℚ] (2 : ℚ))
      ≠ (selfInfinitePlaceData ℚ).baseChangeRingEquiv
          ((1 : InfiniteAdeleRing ℚ) ⊗ₜ[ℚ] (3 : ℚ)) := by
  rw [InfinitePlaceData.baseChangeRingEquiv_one_tmul,
    InfinitePlaceData.baseChangeRingEquiv_one_tmul]
  exact gate_principal_two_ne_three

-- pin: gate_conorm_self_fixes_principal (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:250)
theorem gate_conorm_self_fixes_principal (q : ℚ) :
    (selfInfinitePlaceData ℚ).conorm (algebraMap ℚ (InfiniteAdeleRing ℚ) q)
      = algebraMap ℚ (InfiniteAdeleRing ℚ) q := by
  have h := (selfInfinitePlaceData ℚ).conorm_algebraMap q
  rwa [show algebraMap ℚ ℚ q = q from rfl] at h

-- pin: gate_conorm_separates (Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean:256)
theorem gate_conorm_separates :
    (selfInfinitePlaceData ℚ).conorm (algebraMap ℚ (InfiniteAdeleRing ℚ) 2)
      ≠ (selfInfinitePlaceData ℚ).conorm (algebraMap ℚ (InfiniteAdeleRing ℚ) 3) := by
  rw [gate_conorm_self_fixes_principal, gate_conorm_self_fixes_principal]
  exact gate_principal_two_ne_three

end Gates

end

end FLT.InfiniteAdeleBaseChange
