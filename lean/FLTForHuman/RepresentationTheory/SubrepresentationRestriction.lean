/-
  Restricting a representation to an invariant submodule.

  For a representation `ρ` of `G` on `V` over a field `k` and a `k`-submodule `S ≤ V` stable
  under every `ρ g`, `restrictRep ρ S hS` is the representation of `G` on `S` obtained by
  restricting each linear map; `restrictInvt` spells it on a bundled invariant submodule, i.e.
  on a term of `ρ.invtSubmodule`. The two `_apply_coe` lemmas are the defining unfoldings. The
  algebraic half says that this restriction is the subrepresentation's own module: the
  `asModule` of `restrictInvt ρ p` is `MonoidAlgebra k G`-linearly equivalent to the
  `mapSubmodule` `ρ.mapSubmodule p` (`exists_linearEquiv_asModule_mapSubmodule`, through
  `coe_asAlgebraHom_restrictRep`), and a simple type-algebra submodule `T` makes the
  restricted representation irreducible (`isIrreducible_of_isSimpleModule`).

  The first consumer is the archimedean dual cut: the vanishing theorem
  `AutomorphicForm.ArchDualCut.rightConv_eq_zero_of_isIrreducible_of_le_CBD` restricts `fdOrbitRep`
  to the underlying space of an isotypic component, and the dual-cut inclusion transports a
  surjection between such spaces. Mathlib has the vocabulary these statements use
  (`Representation.asModule`, `asModuleEquiv`, `invtSubmodule`, `mapSubmodule`,
  `Representation.IsIrreducible`, `Subrepresentation.toRepresentation`) but no restriction of a
  representation to an invariant submodule — searched for a restriction/`restrictRep` on
  `Representation` and for an `asModule`-level statement tying it to `mapSubmodule`; the
  closest is `ContRepresentation.restrict` (`RepresentationTheory/Continuous/Basic.lean`), which
  restricts along a monoid hom, a different operation.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.lean:814–912`
  (pinned `aa2d8b3`; the pin's `FarmC3G1G2` section), minus its `p2m_reactivate` scaffolding and
  its `set_option backward.isDefEq.respectTransparency false` guards. Assumes mathlib only.

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.lean   -- comparable copy
-/

import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Submodule
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Representation

variable {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V]

/-- The restriction of `ρ` to a `k`-submodule `S` stable under every `ρ g`. -/
def restrictRep (ρ : _root_.Representation k G V) (S : Submodule k V) (hS : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) :
    _root_.Representation k G S where
  toFun g := (ρ g).restrict (fun v hv => hS g v hv)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[scoped simp] theorem restrictRep_apply_coe (ρ : _root_.Representation k G V) (S : Submodule k V)
    (hS : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) (g : G) (v : S) : ((restrictRep ρ S hS g v : S) : V) = ρ g v := rfl

/-- The restriction of `ρ` to a bundled invariant submodule. -/
def restrictInvt (ρ : _root_.Representation k G V) (p : ρ.invtSubmodule) : _root_.Representation k G (p : Submodule k V) :=
  restrictRep ρ p fun g _ hv => (Module.End.mem_invtSubmodule _).mp ((ρ.mem_invtSubmodule).mp p.2 g) hv

@[scoped simp] theorem restrictInvt_apply_coe (ρ : _root_.Representation k G V) (p : ρ.invtSubmodule) (g : G) (v : (p : Submodule k V)) :
    ((restrictInvt ρ p g v : (p : Submodule k V)) : V) = ρ g v := rfl

theorem coe_asAlgebraHom_restrictRep (ρ : _root_.Representation k G V) (S : Submodule k V)
    (hS : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) (r : MonoidAlgebra k G) (y : S) :
    (((restrictRep ρ S hS).asAlgebraHom r y : S) : V) = ρ.asAlgebraHom r (y : V) := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
      rw [_root_.Representation.asAlgebraHom_of, _root_.Representation.asAlgebraHom_of]
      rfl
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | smul c a ha => rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, ha]

theorem exists_linearEquiv_asModule_mapSubmodule (ρ : _root_.Representation k G V) (p : ρ.invtSubmodule) :
    ∃ e : (restrictInvt ρ p).asModule ≃ₗ[MonoidAlgebra k G] ↥(ρ.mapSubmodule p),
      ∀ x : (restrictInvt ρ p).asModule,
        ((e x : ρ.mapSubmodule p) : ρ.asModule) =
          ρ.asModuleEquiv.symm (((restrictInvt ρ p).asModuleEquiv x : (p : Submodule k V)) : V) := by
  let π := restrictInvt ρ p
  have hmem : ∀ x : π.asModule,
      ρ.asModuleEquiv.symm ((π.asModuleEquiv x : (p : Submodule k V)) : V) ∈ ρ.mapSubmodule p := fun x =>
    ⟨((π.asModuleEquiv x : (p : Submodule k V)) : V), (π.asModuleEquiv x).2, rfl⟩
  have hmem' : ∀ y : ρ.mapSubmodule p, ρ.asModuleEquiv (y : ρ.asModule) ∈ (p : Submodule k V) := by
    rintro ⟨y, ⟨v, hv, rfl⟩⟩
    simpa using hv
  let e : π.asModule ≃ₗ[MonoidAlgebra k G] ↥(ρ.mapSubmodule p) :=
    { toFun := fun x => ⟨_, hmem x⟩
      invFun := fun y => π.asModuleEquiv.symm ⟨ρ.asModuleEquiv (y : ρ.asModule), hmem' y⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp only [map_add, Submodule.coe_add]
      map_smul' := fun r x => by
        apply Subtype.ext
        change ρ.asModuleEquiv.symm ((π.asModuleEquiv (r • x) : (p : Submodule k V)) : V) =
          r • ρ.asModuleEquiv.symm ((π.asModuleEquiv x : (p : Submodule k V)) : V)
        rw [LinearEquiv.symm_apply_eq, _root_.Representation.asModuleEquiv_map_smul,
          _root_.Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]
        exact coe_asAlgebraHom_restrictRep ρ p _ r (π.asModuleEquiv x)
      left_inv := fun x => by simp
      right_inv := fun y => by apply Subtype.ext; simp }
  exact ⟨e, fun x => rfl⟩

set_option linter.style.haveILetI false in
theorem isIrreducible_of_isSimpleModule (ρ : _root_.Representation k G V) (T : Submodule (MonoidAlgebra k G) ρ.asModule)
    [IsSimpleModule (MonoidAlgebra k G) T]
    (hS : ∀ (g : G), ∀ v ∈ (T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap,
      ρ g v ∈ (T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) :
    _root_.Representation.IsIrreducible (restrictRep ρ ((T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) hS) := by

  let p : ρ.invtSubmodule := ⟨(T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap, by
    rw [_root_.Representation.mem_invtSubmodule]
    intro g
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    exact hS g v hv⟩
  have hpT : ρ.mapSubmodule p = T := by
    apply le_antisymm
    · rintro x ⟨v, hv, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
      simpa using hy
    · intro x hx
      refine ⟨ρ.asModuleEquiv x, Submodule.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp
  have hπ : restrictRep ρ ((T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) hS = restrictInvt ρ p := rfl
  rw [hπ, _root_.Representation.irreducible_iff_isSimpleModule_asModule]
  obtain ⟨e, -⟩ := exists_linearEquiv_asModule_mapSubmodule ρ p
  haveI : IsSimpleModule (MonoidAlgebra k G) ↥(ρ.mapSubmodule p) := by rw [hpT]; infer_instance
  exact IsSimpleModule.congr e

end Representation
