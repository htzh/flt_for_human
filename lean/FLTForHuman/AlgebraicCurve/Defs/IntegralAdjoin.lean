/-
The generic `Algebra.adjoin` integrality transport lemmas, after FLT's
`P2M/Sol/S_AlgebraicCurve_isIntegral_adjoin_*.lean` (statements from the
`Theorems/Thm_AlgebraicCurve_isIntegral_adjoin_*.lean` wrappers,
<https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b3/Theorems>).

These are pure `Algebra.adjoin`/`IsIntegral` algebra with no `Place` in sight;
they are consumed by T5 and T9 as well as T1 (`TOPIC-t1-ord-interface.md` §1).
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.FieldTheory.IntermediateField.Basic

set_option autoImplicit false

set_option linter.style.haveILetI false

noncomputable section

namespace AlgebraicCurve

theorem isIntegral_adjoin_intermediateField_mk {L F : Type*} [Field L] [Field F]
    [Algebra L F] (E : IntermediateField L F) {j x : F} (hj : j ∈ E) (hx : x ∈ E)
    (h : IsIntegral (Algebra.adjoin L {j}) x) :
    IsIntegral (Algebra.adjoin L {(⟨j, hj⟩ : E)}) (⟨x, hx⟩ : E) := by
  have hmapeq : (Algebra.adjoin L {(⟨j, hj⟩ : E)}).map E.val
      = Algebra.adjoin L {j} := by
    rw [← Algebra.adjoin_image, Set.image_singleton]
    rfl
  let ψfwd : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) →ₐ[L] ↥(Algebra.adjoin L {j}) :=
    (Subalgebra.equivOfEq _ _ hmapeq).toAlgHom.comp
      (E.val.subalgebraMap (Algebra.adjoin L {(⟨j, hj⟩ : E)}))
  have hcoeF : ∀ b : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}),
      ((ψfwd b : ↥(Algebra.adjoin L {j})) : F) = ((b : E) : F) := fun b => rfl
  have hinjE : Function.Injective ((↑) : E → F) := Subtype.coe_injective
  have hbij : Function.Bijective ψfwd := by
    constructor
    · intro a b hab
      exact Subtype.ext (hinjE (by
        have := congrArg (Subtype.val : ↥(Algebra.adjoin L {j}) → F) hab
        rwa [hcoeF a, hcoeF b] at this))
    · exact (Subalgebra.equivOfEq _ _ hmapeq).surjective.comp
        (E.val.subalgebraMap_surjective _)
  let e := RingEquiv.ofBijective ψfwd hbij
  have hcoe : ∀ a : ↥(Algebra.adjoin L {j}),
      (((e.symm a : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)})) : E) : F) = (a : F) := by
    intro a
    have h2 : ψfwd (e.symm a) = a := e.apply_symm_apply a
    calc (((e.symm a : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)})) : E) : F)
        = ((ψfwd (e.symm a) : ↥(Algebra.adjoin L {j})) : F) := (hcoeF _).symm
      _ = (a : F) := by rw [h2]
  letI : Algebra ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) F :=
    ((algebraMap E F).comp (algebraMap ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) E)).toAlgebra
  have hxT : IsIntegral ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) x :=
    IsIntegral.map_of_comp_eq e.symm.toRingHom (RingHom.id F)
      (by ext a; exact hcoe a) h
  let f : E →ₐ[↥(Algebra.adjoin L {(⟨j, hj⟩ : E)})] F :=
    { toRingHom := (E.val : E →+* F), commutes' := fun t => rfl }
  have hinjf : Function.Injective f := hinjE
  exact (isIntegral_algHom_iff f hinjf).mp hxT

theorem isIntegral_adjoin_map_algHom {K F F' : Type*} [CommRing K] [CommRing F]
    [CommRing F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') {j x : F}
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin K {φ j}) (φ x) := by
  have hle : (Algebra.adjoin K {j}).map φ ≤ Algebra.adjoin K {φ j} := by
    rw [Subalgebra.map_le]
    refine Algebra.adjoin_le fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    show j ∈ Subalgebra.comap φ (Algebra.adjoin K {φ j})
    rw [Subalgebra.mem_comap]
    exact Algebra.subset_adjoin rfl
  have hmem : ∀ a : ↥(Algebra.adjoin K {j}),
      (φ.comp (Algebra.adjoin K {j}).val) a ∈ Algebra.adjoin K {φ j} :=
    fun a => hle (Subalgebra.mem_map.mpr ⟨(a : F), a.2, rfl⟩)
  have key := IsIntegral.map_of_comp_eq
    ((φ.comp (Algebra.adjoin K {j}).val).codRestrict (Algebra.adjoin K {φ j}) hmem).toRingHom
    φ.toRingHom (by ext a; rfl) hx
  exact key

theorem isIntegral_adjoin_of_isScalarTower {K L F : Type*} [CommRing K] [CommRing L]
    [CommRing F] [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F] {j x : F}
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin L {j}) x := by
  have hsub : Algebra.adjoin K {j} ≤ Subalgebra.restrictScalars K (Algebra.adjoin L {j}) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      ((Subalgebra.mem_restrictScalars K).mpr (Algebra.subset_adjoin rfl)))
  let φ' : ↥(Algebra.adjoin K {j}) →+* ↥(Algebra.adjoin L {j}) :=
    { toFun := fun a => ⟨(a : F), (Subalgebra.mem_restrictScalars K).mp (hsub a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact IsIntegral.map_of_comp_eq φ' (RingHom.id F) (by ext a; rfl) hx

end AlgebraicCurve
