/-
  Mathlib supplement: `UniformSpace.Completion.mapSemialgHom`, the completion of a
  continuous ring homomorphism as a `SemialgHom`.

  Backported from the pin's
  `Definitions/Def_Mathlib_Topology_Algebra_UniformRing.lean` (pinned `aa2d8b3`),
  which mirrors the mathlib path `Mathlib/Topology/Algebra/UniformRing.lean`; it
  lives at the same path under `FLTForHuman/`.  The pin imports the `SemialgHom`
  supplement (`Def_Mathlib_Algebra_Algebra_Hom`); here that is the explicit import
  `FLTForHuman.Algebra.Algebra.SemialgHom`.

  Substitutions against mathlib `v4.34.0`: none — mathlib has no `mapSemialgHom`
  (`SemialgHom` itself is absent), so the pin's three declarations are transcribed
  whole at the pin's names.
-/
import Mathlib.Topology.Algebra.UniformRing
import FLTForHuman.Algebra.Algebra.SemialgHom

set_option autoImplicit false

section

namespace UniformSpace.Completion

-- pin: mapSemialgHom (Definitions/Def_Mathlib_Topology_Algebra_UniformRing.lean:14)
noncomputable def mapSemialgHom {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f) :
    Completion α →ₛₐ[f] Completion β where
  __ := UniformSpace.Completion.mapRingHom f hf
  map_smul' m x := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr
    exact extensionHom_coe _ _ m

-- pin: mapSemialgHom_apply (Definitions/Def_Mathlib_Topology_Algebra_UniformRing.lean:26)
theorem mapSemialgHom_apply {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f)
    (x : UniformSpace.Completion α) :
    mapSemialgHom f hf x = UniformSpace.Completion.map f x := rfl

-- pin: mapSemialgHom_coe (Definitions/Def_Mathlib_Topology_Algebra_UniformRing.lean:32)
theorem mapSemialgHom_coe {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] {f : α →+* β} (hf : UniformContinuous f)
    (a : α) :
    mapSemialgHom f hf.continuous a = f a := by
  rw [mapSemialgHom_apply, map_coe hf]

end UniformSpace.Completion

end
