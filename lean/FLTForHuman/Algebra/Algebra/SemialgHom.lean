/-
  Mathlib supplement: `SemialgHom`, ring homomorphisms lying above a ring homomorphism.

  Backported from the pin's `Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean`
  (pinned `aa2d8b3`), which mirrors the mathlib path `Mathlib/Algebra/Algebra/Hom.lean`;
  it lives at the same path under `FLTForHuman/`.  A `SemialgHom φ A B` (notation
  `A →ₛₐ[φ] B`) is a ring homomorphism `ψ : A →+* B` lying above `φ`, i.e. with
  `ψ (r • a) = φ r • ψ a`, and `SemialgHomClass` is its `FunLike` class.

  Substitutions against mathlib `v4.34.0`: none — mathlib has neither `SemialgHom`
  nor `SemialgHomClass` (nor any of the API below), so the pin's declarations are
  transcribed whole at the pin's names; only the imports are made explicit.
-/
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.LinearMap.Defs

set_option autoImplicit false

section

section semialghom

/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `SemialgHom φ A B` or `A →ₛₐ[φ] B` is the ring homomorphisms `ψ : A →+* B`
making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`).
-/
-- pin: SemialgHom (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:11)
structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A →ₛₗ[φ] B, RingHom A B

/-- Reinterpret a `SemialgHom` as a `RingHom`. -/
add_decl_doc SemialgHom.toRingHom

@[inherit_doc SemialgHom]
infixr:25 " →ₛₐ " => SemialgHom _

@[inherit_doc]
notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

-- pin: instFunLike (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:27)
instance instFunLike : FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

variable {φ} {A} {B} in
-- pin: SemialgHom.map_smul (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:36)
lemma SemialgHom.map_smul (ψ : A →ₛₐ[φ] B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
  LinearMap.map_smul' ψ.toLinearMap m x

-- pin: coe_mk (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:40)
@[simp]
theorem coe_mk (f : A →ₛₗ[φ] B) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : A →ₛₐ[φ] B) : A → B) = f :=
  rfl

end semialghom

section semialghomclass

-- pin: SemialgHomClass (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:47)
class SemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B

variable (F : Type*) {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]

-- pin: SemialgHomClass.instSemialgHom (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:57)
instance SemialgHomClass.instSemialgHom : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero

variable {F} {φ} {A} {B} in

-- pin: SemialgHomClass.toSemialgHom (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:66)
def SemialgHomClass.toSemialgHom (f : F) : A →ₛₐ[φ] B :=
  { (f : A →ₛₗ[φ] B), (f : A →+* B) with }

-- pin: instCoeTC (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:69)
instance : CoeTC F (A →ₛₐ[φ] B) :=
  ⟨SemialgHomClass.toSemialgHom⟩

-- pin: SemialgHom.coe_coe (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:73)
@[simp]
theorem SemialgHom.coe_coe (f : F) : ⇑(f : A →ₛₐ[φ] B) = f :=
  rfl

end semialghomclass

section semialghom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

-- pin: SemialgHom.commutes (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:83)
lemma SemialgHom.commutes (ψ : A →ₛₐ[φ] B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) := by
  have := ψ.map_smul r 1
  rw [Algebra.smul_def, mul_one, map_one] at this
  rw [this, Algebra.smul_def, mul_one]

-- pin: SemialgHom.toLinearMap_eq_coe (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:89)
theorem SemialgHom.toLinearMap_eq_coe (f : A →ₛₐ[φ] B) : f.toLinearMap = f :=
  rfl

-- pin: SemialgHom.toRingHom_eq_coe (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:92)
theorem SemialgHom.toRingHom_eq_coe (f : A →ₛₐ[φ] B) : f.toRingHom = f :=
  rfl

-- pin: SemialgHom.algebraMap_apply (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:95)
theorem SemialgHom.algebraMap_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra S B] (f : A →ₛₐ[φ] B) (a : A) :
    letI := f.toAlgebra
    algebraMap A B a = f a := rfl

-- pin: SemialgHom.comp (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:100)
def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ]
    (g : B →ₛₐ[ψ] C) (f : A →ₛₐ[φ] B) :
    A →ₛₐ[ξ] C where
  __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
  __ := RingHom.comp g.toRingHom f.toRingHom

-- pin: AlgHom.toSemialgHom (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:107)
def AlgHom.toSemialgHom {R : Type*} [CommSemiring R] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    A →ₛₐ[RingHom.id R] B where
  __ := f
  map_smul' _ _ := by simp

-- pin: SemialgHom.compAlgHom (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:113)
def SemialgHom.compAlgHom {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} [Algebra S A] (g : B →ₛₐ[ψ] C) (f : A →ₐ[S] B) :
    A →ₛₐ[ψ] C :=
  g.comp f.toSemialgHom

-- pin: SemialgHom.prod (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:118)
def SemialgHom.prod {C : Type*} [Semiring C] [Algebra S C] (f : A →ₛₐ[φ] B)
    (g : A →ₛₐ[φ] C) :
    A →ₛₐ[φ] B × C where
  __ := RingHom.prod f.toRingHom g.toRingHom
  map_smul' r x := by simp

-- pin: SemialgHom.prodMap (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:124)
def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D]
    [Algebra S C] [Algebra S D] [Algebra R B] (f : A →ₛₐ[φ] C) (g : B →ₛₐ[φ] D) :
    A × B →ₛₐ[φ] C × D :=
  (f.compAlgHom (AlgHom.fst R A B)).prod (g.compAlgHom (AlgHom.snd R A B))

-- pin: SemialgHom.restrictScalars (Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean:130)
@[simps!]
def SemialgHom.restrictScalars {R S R' S' : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] {φ : R →+* S}
    (ψ : R' →ₛₐ[φ] S') {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [Algebra R' A] [Algebra S' B] [IsScalarTower R R' A] [IsScalarTower S S' B]
    (f : A →ₛₐ[ψ.toRingHom] B) : A →ₛₐ[φ] B where
  __ := f.toRingHom
  map_smul' r a := by
    have := f.map_smul (algebraMap R R' r) a
    simp_all [SemialgHom.toLinearMap_eq_coe, Algebra.algebraMap_eq_smul_one, ψ.map_smul]

end semialghom

end
