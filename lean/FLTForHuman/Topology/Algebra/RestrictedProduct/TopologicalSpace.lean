/-
  The topological restricted product: continuous maps, homeomorphisms, and second countability.

  On top of mathlib's construction of the restricted product `Πʳ i, [G i, A i]_[𝓕]` this
  module collects the topological API used by the FLT development. Functoriality appears as
  the continuous map `Continuous.restrictedProduct_congrRight` and the continuous monoid
  equivalence `ContinuousMulEquiv.restrictedProductCongrRight`. The binary, finite-product
  and matrix rearrangements are homeomorphisms (`Homeomorph.restrictedProductProd`,
  `Homeomorph.restrictedProductPi`, `Homeomorph.restrictedProductMatrix`), upgraded to
  continuous monoid equivalences `ContinuousMulEquiv.restrictedProductPi` and
  `ContinuousMulEquiv.restrictedProductMatrix` with their matrix-ring units form
  `ContinuousMulEquiv.restrictedProductMatrixUnits`; the units of a restricted product are
  handled by `ContinuousMulEquiv.restrictedProductUnits`, with the local input
  `Submonoid.unitsContinuousMulEquivUnitsType`. The fibres of an index map are glued by the
  flattening homeomorphisms `flatten_homeomorph` / `flatten_homeomorph'`. Neighbourhoods are
  described by the bases `RestrictedProduct.mem_nhds_iff_of_principal`,
  `RestrictedProduct.mem_nhds_of_exists_nhds_of_cofinite` and
  `RestrictedProduct.mem_nhds_iff_of_cofinite`, which also give openness of the componentwise
  maps (`RestrictedProduct.isOpenMap_of_open_components`) and second countability
  (`RestrictedProduct.SecondCountableTopology_of_principal`,
  `RestrictedProduct.secondCountableTopology`). Finally a principal restricted product splits
  as a product (`Homeomorph.restrictedProductPrincipal`,
  `ContinuousMulEquiv.restrictedProductPrincipal`), and the single-coordinate and evaluation
  maps are continuous additive monoid homomorphisms (`singleContinuousAddMonoidHom`,
  `evalContinuousAddMonoidHom`).

  Transcribed verbatim from `Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace.lean`
  (pinned `aa2d8b3`, 576 lines / 36 declarations).

  Substitutions (declarations not redeclared here because `v4.34.0` supplies them):
  * `Submonoid.units_isOpen` → mathlib `Submonoid.isOpen_units`: the pin's
    `Def_Mathlib_Topology_Algebra_Group_Units` node was fully substituted, since `v4.34.0` has
    the identically stated `Submonoid.isOpen_units` in
    `Mathlib.Topology.Algebra.Group.Units`; this pin import is dropped and the use in
    `ContinuousMulEquiv.restrictedProductUnits` becomes `Submonoid.isOpen_units (hA i)`.
  * `RestrictedProduct.singleAddMonoidHom`: the port's `RestrictedProduct.Basic` deliberately
    does not redeclare it, because `v4.34.0` generates it as the `@[to_additive]` companion of
    `RestrictedProduct.mulSingleMonoidHom`. mathlib's first explicit argument is the
    submonoid element family (carrier `G` implicit), whereas the pin's section names the
    carrier `A : ι → Type*` and the element family `B : (i : ι) → S i`, so
    `singleContinuousAddMonoidHom` writes `singleAddMonoidHom (G := A) B j` (term-level only).

  Proof/body-level drift adaptations (statements unchanged):
  * `ContinuousMulEquiv.restrictedProductCongrRight`, `toFun`/`invFun`: the pin's
    `by filter_upwards [hφ]; exact fun i ↦ …` witnesses are written
    `hφ.mono fun i ↦ …`. As in the sibling `Equiv.lean` port, `v4.34.0`'s
    `filter_upwards` produces a raw set-membership proof that no longer unifies with
    `RestrictedProduct.map`'s `∀ᶠ`-binder at the transparency `simp`/`rw` use, so
    `RestrictedProduct.map_apply` cannot fire; `.mono` returns the `∀ᶠ`-typed witness.
    The two terms are definitionally equal by proof irrelevance.
  * `Equiv.continuous_restrictedProductProd`: the pin's
    `simp only [Equiv.restrictedProductProd, coe_fn_mk]; fun_prop` is replaced by
    `rw [funext fun x => Equiv.restrictedProductProd_apply x]; fun_prop`: in `v4.34.0`
    `Equiv.coe_fn_mk` does not reduce the `Equiv.mk` coercion under `simp only` (the goal
    keeps `⇑(Equiv.mk …)`), so the goal is first rewritten to the explicit pair function
    through the `@[simps]` projection lemma `Equiv.restrictedProductProd_apply`.
  * `Equiv.continuous_restrictedProductProd_symm`: `simp only [restrictedProductProd,
    coe_fn_symm_mk]` becomes `simp only [Equiv.restrictedProductProd]`; the
    `coe_fn_symm_mk` argument is unused in `v4.34.0` (the `symm` coercion already reduces
    here) and the definition name is namespace-qualified.
  * `ContinuousMulEquiv.restrictedProductMatrix`, `map_mul'`: the pin's
    `apply map_sum (RestrictedProduct.evalAddMonoidHom _ _) _ _` is written
    `apply map_sum (RestrictedProduct.evalAddMonoidHom A i (B := C)) _ _`. `v4.34.0`
    does not infer the subobject family `B` from the goal before synthesizing
    `AddMonoidHomClass`, so it is supplied explicitly (term-level only).
  * `RestrictedProduct.mem_nhds_of_exists_nhds_of_cofinite` and
    `RestrictedProduct.mem_nhds_iff_of_cofinite`: the pin's `Set.mem_setOf_eq` is the
    `v4.34.0` name `Set.mem_ofPred_eq` (the former is deprecated); same statement.
  * `Homeomorph.restrictedProductPrincipal`, `continuous_invFun`: the pin's
    `by_cases hi` / `simp only [principalEquivProd, Function.comp_apply, mk_apply, hi,
    ↓reduceDIte]` / `fun_prop` no longer reduces the `Equiv.symm` application in
    `v4.34.0`; it is replaced by a `change` to the explicit `dite` form followed by
    `split_ifs with hi <;> fun_prop`.
  * Cosmetic only: the pin's blank-bodied `@[to_additive` + whitespace + `]` attributes
    are written `@[to_additive]`; the generated additive companion names are unchanged.

  The pin's `import Mathlib` and its five stub imports are replaced by the specific
  mathlib sources above and the port's sibling modules
  `FLTForHuman.Topology.Algebra.ContinuousMonoidHom`,
  `FLTForHuman.Topology.Algebra.RestrictedProduct.Equiv`,
  `FLTForHuman.Order.Filter.Cofinite` and `FLTForHuman.Topology.Bases`; the pin's
  `Def_Mathlib_Topology_Algebra_Group_Units` import has no counterpart (substitution 1).
-/
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Bases
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic
import FLTForHuman.Topology.Algebra.ContinuousMonoidHom
import FLTForHuman.Topology.Algebra.RestrictedProduct.Equiv
import FLTForHuman.Order.Filter.Cofinite
import FLTForHuman.Topology.Bases

set_option autoImplicit false

section

open RestrictedProduct

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)] in
@[fun_prop]
theorem Continuous.restrictedProduct_congrRight {φ : (i : ι) → G i → H i}
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (C i) (D i))
    (hφcont : ∀ i, Continuous (φ i)) :
    Continuous (map φ hφ) :=
  mapAlong_continuous G H id Filter.tendsto_id φ hφ hφcont

section groups

variable {S T : ι → Type*}
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

variable [Π i, Monoid (G i)] [Π i, SubmonoidClass (S i) (G i)]
    [Π i, Monoid (H i)] [Π i, SubmonoidClass (T i) (H i)]
    [Π i, TopologicalSpace (G i)]
    [Π i, TopologicalSpace (H i)] in

@[to_additive]
def ContinuousMulEquiv.restrictedProductCongrRight (φ : (i : ι) → G i ≃ₜ* H i)
    (hφ : ∀ᶠ i in ℱ, Set.BijOn (φ i) (A i) (B i)) :
    (Πʳ i, [G i, A i]_[ℱ]) ≃ₜ* (Πʳ i, [H i, B i]_[ℱ]) where
  toFun := map (fun i ↦ φ i)
    (hφ.mono fun i ↦ Set.BijOn.mapsTo)
  invFun := map (fun i ↦ (φ i).symm)
    (hφ.mono fun i ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm)
  map_mul' _ _ := by ext; simp
  left_inv x := by
    ext i
    exact ContinuousMulEquiv.symm_apply_apply _ _
  right_inv x := by
    ext i
    exact ContinuousMulEquiv.apply_symm_apply _ _

end groups

section binary

variable {ι : Type*} {ℱ : Filter ι} {A B : ι → Type*}
  {C : (i : ι) → Set (A i)} {D : (i : ι) → Set (B i)}

lemma Equiv.continuous_restrictedProductProd
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Continuous (Equiv.restrictedProductProd (C := C) (D := D) (ℱ := ℱ)) := by
  rw [funext fun x => Equiv.restrictedProductProd_apply x]
  fun_prop

@[fun_prop]
lemma Equiv.continuous_restrictedProductProd_symm {S : Set ι}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Continuous (Equiv.restrictedProductProd (C := C) (D := D) (ℱ := .principal S)).symm := by
  simp only [Equiv.restrictedProductProd]
  rw [continuous_rng_of_principal_iff_forall]
  intro i
  rw [continuous_prodMk]
  constructor
  · exact (RestrictedProduct.continuous_eval i).comp continuous_fst
  · exact (RestrictedProduct.continuous_eval i).comp continuous_snd

def Homeomorph.restrictedProductProd [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    (hCopen : ∀ (i : ι), IsOpen (C i)) (hDopen : ∀ (i : ι), IsOpen (D i)) :
    Πʳ i, [A i × B i, C i ×ˢ D i] ≃ₜ (Πʳ i, [A i, C i]) × (Πʳ i, [B i, D i]) where
  __ := Equiv.restrictedProductProd
  continuous_toFun := Equiv.continuous_restrictedProductProd
  continuous_invFun := by
    rw [RestrictedProduct.continuous_dom_prod hCopen hDopen]
    intro S hS
    rw [Equiv.invFun_as_coe, Equiv.restrictedProductProd_symm_comp_inclusion]
    fun_prop

end binary

section pi

variable {ι : Type*} {ℱ : Filter ι} {n : Type*} [Fintype n]
    {A : n → ι → Type*}
    {C : (j : n) → (i : ι) → Set (A j i)}

open Filter

lemma Equiv.continuous_restrictedProductPi [∀ j i, TopologicalSpace (A j i)] :
    Continuous (Equiv.restrictedProductPi (C := C) (ℱ := ℱ)) := by
  simp only [Equiv.restrictedProductPi, coe_fn_mk]
  fun_prop

@[fun_prop]
lemma Equiv.continuous_restrictedProductPi_symm {S : Set ι}
    [∀ j i, TopologicalSpace (A j i)] :
    Continuous (Equiv.restrictedProductPi (C := C) (ℱ := .principal S)).symm := by
  rw [continuous_rng_of_principal_iff_forall]
  intro i
  rw [continuous_pi_iff]
  intro j
  exact (RestrictedProduct.continuous_eval i).comp (continuous_apply _)

def Homeomorph.restrictedProductPi {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)]
    {C : (j : n) → (i : ι) → Set (A j i)} (hCopen : ∀ j i, IsOpen (C j i)) :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}] ≃ₜ Π j, (Πʳ i, [A j i, C j i]) where
  __ := Equiv.restrictedProductPi
  continuous_toFun := Equiv.continuous_restrictedProductPi
  continuous_invFun := by
    rw [RestrictedProduct.continuous_dom_pi hCopen]
    intro S hS
    rw [Equiv.invFun_as_coe, Equiv.restrictedProductPi_symm_comp_inclusion]
    fun_prop

@[to_additive]
def ContinuousMulEquiv.restrictedProductPi {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)] [∀ j i, Group (A j i)]
    {C : (j : n) → (i : ι) → Subgroup (A j i)} (hCopen : ∀ j i, IsOpen (C j i : Set (A j i))) :
    Πʳ i, [Π j, A j i, Subgroup.pi (Set.univ : Set n) (fun j ↦ C j i)] ≃ₜ*
      Π j, (Πʳ i, [A j i, C j i]) where
  toFun x j := map (fun i t ↦ t _)
    (Filter.Eventually.of_forall (fun _ _ ↦ by simp_all [Subgroup.mem_pi])) x
  invFun y := .mk (fun i j ↦ y j i)
    (by have h := fun j ↦ (y j).property; simp [-eventually_cofinite, Subgroup.mem_pi] at h ⊢; exact h)
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; simp [RestrictedProduct.map]
  continuous_toFun := by
    exact continuous_pi fun j ↦
      Continuous.restrictedProduct_congrRight _ fun _ ↦ continuous_apply j
  continuous_invFun := by
    refine (continuous_dom_pi hCopen).mpr fun S hS ↦ ?_
    change Continuous
      (inclusion (fun i ↦ (j : n) → A j i)
        (fun i ↦ Subgroup.pi Set.univ (fun j ↦ C j i)) hS
      ∘ (fun (y : (j : n) → Πʳ (i : ι), [A j i, C j i]_[𝓟 S]) ↦ .mk (fun i j ↦ y j i)
        (by have h := fun j ↦ (y j).property; simp [-eventually_principal, Subgroup.mem_pi] at h ⊢; exact h)))
    exact Continuous.comp (by fun_prop) <|
      continuous_rng_of_principal_iff_forall.mpr fun _ ↦ continuous_pi fun _ ↦
        (RestrictedProduct.continuous_eval _).comp (continuous_apply _)

@[to_additive (attr := simp)]
lemma ContinuousMulEquiv.restrictedProductPi_apply {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)] [∀ j i, Group (A j i)]
    {C : (j : n) → (i : ι) → Subgroup (A j i)} {hCopen : ∀ j i, IsOpen (C j i : Set (A j i))}
    {x : Πʳ i, [Π j, A j i, Subgroup.pi (Set.univ : Set n) (fun j ↦ C j i)]} {i : ι} {j : n} :
    ContinuousMulEquiv.restrictedProductPi hCopen x j i
    = (x i) j :=
  rfl

@[to_additive (attr := simp)]
lemma ContinuousMulEquiv.restrictedProductPi_symm_apply {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)] [∀ j i, Group (A j i)]
    {C : (j : n) → (i : ι) → Subgroup (A j i)} {hCopen : ∀ j i, IsOpen (C j i : Set (A j i))}
    {x : Π j, (Πʳ i, [A j i, C j i])} {i : ι} {j : n} :
    (ContinuousMulEquiv.restrictedProductPi hCopen).symm x i j
    = (x j) i :=
  rfl

theorem Homeomorph.restrictedProductMatrix_aux {ι n : Type*} [Finite n] {A : ι → Type*}
    [(i : ι) → TopologicalSpace (A i)] {C : (i : ι) → Set (A i)}
    (i : ι) (hCopen : ∀ (i : ι), IsOpen (C i)) :
    IsOpen {f : n → A i | ∀ (a : n), f a ∈ C i} := by
  convert isOpen_set_pi (s := fun _ : n ↦ C i) (Set.toFinite .univ) (fun _ _ ↦ hCopen i)
  ext f
  simp

def Homeomorph.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    {C : (i : ι) → Set (A i)} (hCopen : ∀ i, IsOpen (C i)) :
    Πʳ i, [Matrix m n (A i), (C i).matrix] ≃ₜ Matrix m n (Πʳ i, [A i, C i]) :=
  (Homeomorph.restrictedProductPi (fun _ _ ↦ restrictedProductMatrix_aux _ hCopen)).trans
    (Homeomorph.piCongrRight fun _ ↦ Homeomorph.restrictedProductPi (fun _ ↦ hCopen))

lemma Homeomorph.restrictedProductMatrix_toEquiv {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    {C : (i : ι) → Set (A i)} (hCopen : ∀ i, IsOpen (C i)) :
    (restrictedProductMatrix hCopen).toEquiv =
      Equiv.restrictedProductMatrix (m := m) (n := n) :=
  rfl

open MulOpposite MonoidHom Units Equiv Set in

@[to_additive]
def Submonoid.unitsContinuousMulEquivUnitsType {M : Type*} [TopologicalSpace M] [Monoid M]
    {S : Submonoid M} (hS : IsOpen (S : Set M)) : S.units ≃ₜ* Sˣ where
  toMulEquiv := S.unitsEquivUnitsType
  continuous_toFun := {
    isOpen_preimage U hU := by
      obtain ⟨t, ht, rfl⟩ := isInducing_embedProduct.isOpen_iff.mpr hU
      let g : Sˣ →* Mˣ := Units.map S.subtype
      have hg : IsOpenMap g := isOpenMap_map (by simp) hS.isOpenMap_subtype_val
      refine ⟨g '' (embedProduct S ⁻¹' t), hg _ (isOpen_induced ht), Set.ext fun s ↦ ?_⟩
      simp only [mem_preimage, mem_image, embedProduct_apply, inv_mk, coeHom_apply, g,
        unitsEquivUnitsType]
      exact ⟨fun ⟨_, ⟨h₁, h₂⟩⟩ ↦ by simp [← h₂, h₁],
        fun h ↦ ⟨S.unitsEquivUnitsType s, by simp [unitsEquivUnitsType, h]⟩⟩
  }
  continuous_invFun := {
    isOpen_preimage U hU := by
      obtain ⟨t, ⟨V, hV, rfl⟩, rfl⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mpr hU
      let f : S × Sᵐᵒᵖ → M × Mᵐᵒᵖ := Prod.map Subtype.val (op ∘ Subtype.val ∘ unop)
      have hf : Continuous f := continuous_subtype_val.fst'.prodMk <| continuous_op.comp' <|
        continuous_subtype_val.comp' <| continuous_unop.comp' continuous_snd
      exact ⟨f ⁻¹' V, hf.isOpen_preimage V hV, rfl⟩
  }

def ContinuousMulEquiv.restrictedProductUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)]
    [(i : ι) → ContinuousMul (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)]
    (A : Π i, S i) (hA : ∀ i, IsOpen (A i : Set (M i))) :
    (Πʳ i, [M i, A i])ˣ ≃ₜ*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units] :=
    have : Fact (∀ i, IsOpen (A i : Set (M i))) := Fact.mk hA
    have hA' : ∀ i, IsOpen ((Submonoid.ofClass (A i)).units : Set (M i)ˣ) :=
      fun i ↦ Submonoid.isOpen_units (hA i)
    have : Fact (∀ i, IsOpen ((Submonoid.ofClass (A i)).units : Set (M i)ˣ)) := Fact.mk hA'

    let sM := structureMapMonoidHom M A cofinite
    let f : ((i : ι) → (A i))ˣ ≃ₜ ((i : ι) → (A i)ˣ) := ContinuousMulEquiv.piUnits.toHomeomorph
    let g : ((i : ι) → (Submonoid.ofClass (A i))ˣ) ≃ₜ ((i : ι) → (Submonoid.ofClass (A i)).units) :=
      Homeomorph.piCongrRight fun i ↦
        (Submonoid.unitsContinuousMulEquivUnitsType (hA i)).symm.toHomeomorph
    let sMx := structureMap (fun i ↦ (M i)ˣ) (fun i ↦ (Submonoid.ofClass (A i)).units) cofinite
  {
  __ := MulEquiv.restrictedProductUnits
  continuous_toFun := by
    apply continuous_of_continuousAt_one MulEquiv.restrictedProductUnits
    intro N hN
    have hN' : (f.trans g) ⁻¹' (sMx ⁻¹' N) ∈ nhds 1 := (f.trans g).continuous.continuousAt
      |>.preimage_mem_nhds <| isEmbedding_structureMap.continuous.continuousAt.preimage_mem_nhds hN
    apply mem_of_superset <| Units.isOpenMap_map (f := sM) isEmbedding_structureMap.injective
      (isOpenEmbedding_structureMap hA).isOpenMap |>.image_mem_nhds hN'
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  continuous_invFun := by
    apply continuous_of_continuousAt_one MulEquiv.restrictedProductUnits.symm
    intro N hN
    have hN' : (Units.map sM) ⁻¹' N ∈ nhds 1 :=
      Units.continuous_map isEmbedding_structureMap.continuous |>.continuousAt.preimage_mem_nhds hN
    apply mem_of_superset <| (isOpenEmbedding_structureMap hA').isOpenMap.image_mem_nhds <|
      (f.trans g).isOpenMap.image_mem_nhds hN'
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hx
      }

set_option backward.isDefEq.respectTransparency false in

def ContinuousMulEquiv.restrictedProductMatrix {ι : Type*}
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, Ring (A i)]
    {C : (i : ι) → Subring (A i)} (hCopen : ∀ i, IsOpen ((C i) : Set (A i))) :
    Matrix n n (Πʳ i, [A i, C i]) ≃ₜ*
      Πʳ i, [Matrix n n (A i), ((C i).matrix : Subring (Matrix n n (A i)))] :=
    let restrictedProductMatrix :
        Matrix n n (Πʳ i, [A i, C i]) ≃ₜ
          Πʳ i, [Matrix n n (A i), ((C i).matrix : Subring (Matrix n n (A i)))] :=
      Homeomorph.symm (Homeomorph.restrictedProductMatrix hCopen)
  {
  __ := restrictedProductMatrix
  map_mul' x y := by
    ext i j k
    rw [mul_apply, Matrix.mul_apply]
    have h {x : Matrix n n Πʳ (i : ι), [A i, ↑(C i)]} {i : ι} {j k : n} :
        (restrictedProductMatrix.toFun x) i j k = (x j k) i := by
      simp [restrictedProductMatrix, Homeomorph.restrictedProductMatrix,
        Homeomorph.restrictedProductPi, Equiv.restrictedProductPi, Matrix]
    simp only [h, Matrix.mul_apply]
    conv_rhs => arg 2; intro _; rw [← mul_apply]
    apply map_sum (RestrictedProduct.evalAddMonoidHom A i (B := C)) _ _
      }

def ContinuousMulEquiv.restrictedProductMatrixUnits {ι : Type*}
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, Ring (A i)] [∀ i, IsTopologicalRing (A i)]
    {C : (i : ι) → Subring (A i)} (hCopen : ∀ i, IsOpen ((C i) : Set (A i))) :
    (Matrix n n (Πʳ i, [A i, C i]))ˣ ≃ₜ*
      Πʳ i, [(Matrix n n (A i))ˣ, ((C i).matrix.units : Subgroup (Matrix n n (A i))ˣ)] :=
  (ContinuousMulEquiv.restrictedProductMatrix hCopen).units_map.trans
    (ContinuousMulEquiv.restrictedProductUnits (fun i => (C i).matrix) (fun i => (hCopen i).matrix))

end pi

section flatten

variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)
variable (hf : Filter.comap f 𝒢 = ℱ)

namespace RestrictedProduct

variable [Π i, TopologicalSpace (G i)]

def flatten_homeomorph :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃ₜ
    Πʳ i, [G i, C i]_[ℱ] where
  __ := flatten_equiv C hf
  continuous_toFun := by
    dsimp only [flatten_equiv]
    apply mapAlong_continuous
    fun_prop
  continuous_invFun := by
    dsimp only [flatten_equiv]
    rw [continuous_dom]
    intro S hS
    set T := (f '' Sᶜ)ᶜ with hTval
    have hT : 𝒢 ≤ Filter.principal T := by
      rwa [Filter.le_principal_iff, hTval, ← Filter.mem_comap_iff_compl, hf,
        ← Filter.le_principal_iff]
    let g : Πʳ i, [G i, C i]_[Filter.principal S] → Πʳ j, [Π (i : f ⁻¹' {j}), G i,
        Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[Filter.principal T] :=
      fun x ↦ ⟨fun _ i ↦ x i, by
        have : Filter.comap f (Filter.principal T) ≤ Filter.principal S := by
          rw [Filter.le_principal_iff, Filter.mem_comap]
          use T
          refine ⟨Filter.mem_principal_self T, ?_⟩
          rw [hTval, Set.preimage_compl, Set.compl_subset_comm]
          apply Set.subset_preimage_image
        have hx := Filter.Eventually.filter_mono this x.prop
        rw [Filter.eventually_comap] at hx
        filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
    let hg: Continuous g := by
      rw [continuous_rng_of_principal]
      unfold g
      fun_prop
    apply (continuous_inclusion hT).comp hg

@[simp]
lemma flatten_homeomorph_apply (x) (i : ι) :
    flatten_homeomorph C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_homeomorph_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_homeomorph C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

def flatten_homeomorph' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃ₜ
    Πʳ i, [G i, C i] :=
  flatten_homeomorph C <|
    le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

@[simp]
lemma flatten_homeomorph'_apply (x) (i : ι) :
    flatten_homeomorph' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_homeomorph'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_homeomorph' C hf).symm x i j = x j.1 :=
  rfl

end RestrictedProduct

end flatten

section nhds

open scoped Filter

variable [Π i, TopologicalSpace (G i)]

lemma RestrictedProduct.mem_nhds_iff_of_principal {T : Set ι} {x : Πʳ i, [G i, C i]_[𝓟 T]}
    (U : Set Πʳ i, [G i, C i]_[𝓟 T]) :
    U ∈ nhds x ↔ ∃ (I : Set ι) (s : (i : ι) → Set (G i)), I.Finite ∧ (∀ i, s i ∈ nhds (x i)) ∧
    (↑) ⁻¹' I.pi s ⊆ U := by
  rw [isEmbedding_coe_of_principal.nhds_eq_comap, Filter.mem_comap, nhds_pi]
  simp_rw [Filter.mem_pi]
  exact ⟨fun ⟨t, ⟨I, hIf, s, hs, ht⟩, htU⟩ ↦ ⟨I, s, hIf, hs, by grw [ht, htU]⟩,
    fun ⟨I, s, hIf, hs, hU⟩ ↦ ⟨I.pi s, ⟨I, hIf, s, hs, subset_rfl⟩, hU⟩⟩

lemma RestrictedProduct.mem_nhds_of_exists_nhds_of_cofinite {x : Πʳ i, [G i, C i]}
    {U : Set Πʳ i, [G i, C i]} (hCopen : ∀ i, IsOpen (C i : Set (G i))) (s : (i : ι) → Set (G i))
    (hs : ∀ i, s i ∈ nhds (x i)) (hf : ∀ᶠ i in Filter.cofinite, C i ⊆ s i)
    (hU : (↑) ⁻¹' Set.univ.pi s ⊆ U) : U ∈ nhds x := by
  set I := {i | ¬C i ⊆ s i} with hIval
  set T := {i | x i ∉ C i} with hTval
  have hT : Filter.cofinite ≤ Filter.principal Tᶜ := by simpa using x.eventually
  have hT' : ∀ᶠ (i : ι) in Filter.principal Tᶜ, x i ∈ C i := by simp [hTval]
  obtain ⟨x', hx⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually G C hT hT'
  have hs' : ∀ i, s i ∈ nhds (x' i) := by simpa [← hx] using hs
  rw [← hx, nhds_eq_map_inclusion hCopen hT, Filter.mem_map, mem_nhds_iff_of_principal]
  refine ⟨I ∪ T, s, Set.Finite.union hf x.eventually, hs', ?_⟩
  grw [← hU, ← Set.preimage_comp, coe_comp_inclusion, ← Set.image_subset_iff,
      Set.image_preimage_eq_inter_range, range_coe_principal]
  rintro y hy i -
  simp only [Set.mem_inter_iff, Set.mem_pi] at hy
  by_cases h : i ∈ I ∪ T
  · apply hy.left i h
  · simp only [Set.mem_union, not_or] at h
    have hy' : y i ∈ C i := hy.right i h.right
    simp only [hIval, Set.mem_ofPred_eq, not_not] at h
    exact h.left hy'

lemma RestrictedProduct.mem_nhds_iff_of_cofinite {x : Πʳ i, [G i, C i]} {U : Set Πʳ i, [G i, C i]}
    (hCopen : ∀ i, IsOpen (C i : Set (G i))) :
    U ∈ nhds x ↔ ∃ (s : (i : ι) → Set (G i)), (∀ i, s i ∈ nhds (x i)) ∧
    (∀ᶠ i in Filter.cofinite, s i = C i) ∧ Set.univ.pi s ⊆ (↑) '' U := by
  refine ⟨fun hn ↦ ?_, fun ⟨s, hs, hsf, hsU⟩ ↦ ?_⟩
  · set T := {i | x i ∉ C i} with hTval
    have hT : Filter.cofinite ≤ Filter.principal Tᶜ := by simpa using x.eventually
    have hT' : ∀ᶠ (i : ι) in Filter.principal Tᶜ, x i ∈ C i := by simp [hTval]
    obtain ⟨x', hx⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually G C hT hT'
    rw [← hx, nhds_eq_map_inclusion hCopen hT, Filter.mem_map, mem_nhds_iff_of_principal] at hn
    obtain ⟨I, s, hIf, hs, hU⟩ := hn
    refine ⟨fun i ↦ (s i ∪ {x | i ∉ I}) ∩ (C i ∪ {x | i ∈ T}), ?_, ?_, ?_⟩
    · intro i
      rw [← hx]
      apply Filter.inter_mem (Filter.mem_of_superset (hs i) Set.subset_union_left)
      apply IsOpen.mem_nhds (IsOpen.union (hCopen i) isOpen_const)
      rw [Set.mem_union, Set.mem_ofPred_eq, or_iff_not_imp_right]
      apply x'.eventually
    · filter_upwards [hIf.compl_mem_cofinite, x.eventually] with i (hI : i ∉ I) hC
      simp [hI, hC, hTval]
    · grw [← image_coe_preimage_inclusion_subset _ _ hT, ← hU, Set.image_preimage_eq_inter_range,
        range_coe_principal]
      simp [Set.subset_def, or_iff_not_imp_right, forall_and]
  · apply mem_nhds_of_exists_nhds_of_cofinite hCopen s hs
    · filter_upwards [hsf] with _ using superset_of_eq
    · exact Set.preimage_subset hsU DFunLike.coe_injective.injOn

end nhds

section openmap

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)]

lemma RestrictedProduct.isOpenMap_of_open_components
    (hCopen : ∀ i, IsOpen (C i : Set (G i))) (hDopen : ∀ i, IsOpen (D i : Set (H i)))
    (f : Πʳ i, [G i, C i] → Πʳ i, [H i, D i]) (g : (i : ι) → G i → H i)
    (hcomponent : ∀ x i, f x i = g i (x i)) (hg : ∀ i, IsOpenMap (g i))
    (hsurj : ∀ᶠ i in Filter.cofinite, Set.SurjOn (g i) (C i) (D i)) :
    IsOpenMap f := by
  refine IsOpenMap.of_nhds_le fun x ↦ Filter.le_map fun U hU ↦ ?_
  obtain ⟨s, hf, hs, hU⟩ := (mem_nhds_iff_of_cofinite hCopen).mp hU
  apply mem_nhds_of_exists_nhds_of_cofinite hDopen fun i ↦ (g i) '' (s i)
  · intro i
    rw [hcomponent]
    exact IsOpenMap.image_mem_nhds (hg i) (hf i)
  · filter_upwards [hsurj, hs] with i hsurj' heq using heq ▸ hsurj'
  · apply Set.preimage_subset _ DFunLike.coe_injective.injOn
    grw [← Set.piMap_image_univ_pi, hU, ← Set.image_comp,
      ← Set.image_comp, ← components_comp_coe_eq_coe_apply hcomponent]
    rfl

end openmap

open RestrictedProduct Filter in
instance RestrictedProduct.SecondCountableTopology_of_principal
    {ι : Type*} [Countable ι]
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (C : (i : ι) → Set (X i))
    [∀ i, SecondCountableTopology (X i)]
    {S : Set ι} :
    SecondCountableTopology (Πʳ i, [X i, C i]_[𝓟 S]) :=
  isEmbedding_coe_of_principal.secondCountableTopology

open Filter RestrictedProduct in
lemma RestrictedProduct.secondCountableTopology {ι : Type*} [Countable ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {C : (i : ι) → Set (X i)} (hCopen : ∀ (i : ι), IsOpen (C i))
    [∀ i, SecondCountableTopology (X i)] :
    SecondCountableTopology (Πʳ i, [X i, C i]) :=
  TopologicalSpace.secondCountableTopology_of_countable_cover'
    (fun S : (.cofinite : Filter ι).sets ↦ inclusion X C (Filter.le_principal_iff.2 S.2))
    (fun S ↦ RestrictedProduct.isOpenEmbedding_inclusion_principal hCopen
        (Filter.le_principal_iff.2 S.2))
    (fun f ↦ ⟨⟨_, f.2⟩, ⟨f.1, by aesop⟩, rfl⟩)

section equivs

open Classical Filter in

noncomputable def Homeomorph.restrictedProductPrincipal {ι : Type*}
    (R : ι → Type*) (A : Π i, Set (R i)) [∀ i, TopologicalSpace (R i)] (J : Set ι) :
    Πʳ i, [R i, A i]_[𝓟 J] ≃ₜ (Π i : J, A i) × (Π i : (Jᶜ : Set ι), R i) where
  __ := RestrictedProduct.principalEquivProd R J A
  continuous_toFun := continuous_prodMk.mpr
    ⟨continuous_pi fun _ ↦ continuous_induced_rng.mpr <| continuous_eval _,
      continuous_pi fun _ ↦ continuous_eval _⟩
  continuous_invFun := by
    refine continuous_rng_of_principal.mpr <| continuous_pi fun i ↦ ?_
    change Continuous (fun a : (Π i : J, A i) × (Π i : (Jᶜ : Set ι), R i) =>
        (dite (i ∈ J) (fun h => ↑(a.1 ⟨i, h⟩)) (fun h => a.2 ⟨i, h⟩) : R i))
    split_ifs with hi <;> fun_prop
open Filter in

@[to_additive]
noncomputable def ContinuousMulEquiv.restrictedProductPrincipal {ι : Type*}
    {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {A : Π i, S i}
    (J : Set ι) :
    Πʳ i, [R i, A i]_[𝓟 J] ≃ₜ* (Π i : J, A i) × (Π i : (Jᶜ : Set ι), R i) where
  toHomeomorph := Homeomorph.restrictedProductPrincipal R (fun i ↦ A i) J
  map_mul' _ _ := rfl

end equivs

namespace RestrictedProduct

section single

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R] (A : ι → Type*) {𝓕 : Filter ι}
    {S : ι → Type*}
    [(i : ι) → SetLike (S i) (A i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → AddCommMonoid (A i)]
    [(i : ι) → Module R (A i)] [∀ (i : ι), AddSubmonoidClass (S i) (A i)]

variable [∀ i, TopologicalSpace (A i)]
open Filter in

noncomputable def singleContinuousAddMonoidHom (j : ι) : A j →ₜ+ Πʳ i, [A i, B i] where
  __ := singleAddMonoidHom (G := A) B j
  continuous_toFun := by
    let S : Set ι := {j}ᶜ
    let single' : A j → Πʳ i, [A i, B i]_[𝓟 S] :=
      fun x ↦ ⟨Pi.single j x,
        eventually_principal.mpr
        fun i hi ↦ by simp [Pi.single_eq_of_ne (Set.mem_compl_singleton_iff.mp hi)]⟩
    have : Continuous single' := by
      simp only [continuous_rng_of_principal]
      exact continuous_single j
    apply (isEmbedding_inclusion_principal
      (le_principal_iff.mpr (Set.finite_singleton j).compl_mem_cofinite)).continuous.comp this

lemma singleContinuousAddMonoidHom_apply_same {j : ι} (x : A j) :
    (singleContinuousAddMonoidHom A j x : Πʳ i, [A i, B i]) j = x :=
  Pi.single_eq_same j x

lemma singleContinuousAddMonoidHom_apply_of_ne {j i : ι} (h : i ≠ j) (x : A j) :
    (singleContinuousAddMonoidHom A j x : Πʳ i, [A i, B i]) i = 0 :=
  Pi.single_eq_of_ne h x

end single

section eval

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R] (A : ι → Type*) {𝓕 : Filter ι}
    {S : ι → Type*}
    [(i : ι) → SetLike (S i) (A i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → AddCommMonoid (A i)]
    [(i : ι) → Module R (A i)] [∀ (i : ι), AddSubmonoidClass (S i) (A i)]

variable [∀ i, TopologicalSpace (A i)]

def evalContinuousAddMonoidHom (j : ι) : Πʳ i, [A i, B i] →ₜ+ A j := {
  __ := evalAddMonoidHom A j
  continuous_toFun := continuous_eval j
}

end eval

end RestrictedProduct
