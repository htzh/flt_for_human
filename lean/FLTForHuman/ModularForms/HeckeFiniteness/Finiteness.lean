/-
  Finiteness and freeness of the Hecke algebra over `ℤ`.

  The Hecke algebra acts on the integral lattice, a finitely generated free `ℤ`-module,
  so restricting an operator to the lattice embeds the algebra `ℤ`-linearly into the
  endomorphism ring of a finitely generated free `ℤ`-module. That embedding is injective
  because the lattice spans the space over `ℂ`, so an operator vanishing on the lattice
  is zero. Hence the algebra is a finite free `ℤ`-module, and its `ℤ`-span is finitely
  generated, in every weight.

  FLT provenance, pinned `aa2d8b3`: `Theorems/Thm_CuspForm_moduleFinite_heckeAlgebra.lean`,
  `…_HasIntegralStructure_moduleFree_heckeAlgebra.lean`,
  `…_HasIntegralStructure_eq_zero_of_forall_mem_intLattice.lean`,
  `…_fg_toSubmodule_heckeAlgebra.lean`.
-/
import FLTForHuman.Algebra.Module.Torsion.AddTorsionFree
import FLTForHuman.ModularForms.HeckeFiniteness.IntegralStructure
import FLTForHuman.ModularForms.HeckeFiniteness.Lattice
import FLTForHuman.ModularForms.HeckeFiniteness.LowWeight

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold

namespace CuspForm

/-- An operator vanishing on the integral lattice is zero: the lattice spans the space
over `ℂ`. -/
theorem eq_zero_of_forall_mem_intLattice {N : ℕ} [NeZero N] {k : ℤ}
    (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k))
    (h : ∀ f ∈ CuspForm.intLattice N k, t f = 0) : t = 0 :=
  LinearMap.ext_on (CuspForm.hasIntegralStructure N k) fun f hf ↦ by
    rw [LinearMap.zero_apply]
    exact h f hf

/-- The Hecke algebra is a finite `ℤ`-module, in every weight: the lattice embedding
`t ↦ t|_L` is injective, and `End_ℤ(L)` is finitely generated for `L` finitely generated
and free. -/
theorem moduleFinite_heckeAlgebra (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N k S) := by
  classical
  let V := CuspForm (CongruenceSubgroup.Gamma0 N) k
  let L : Submodule ℤ V := intLattice N k
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr (CuspForm.intLattice_fg N k)
  have : IsAddTorsionFree V := IsAddTorsionFree.of_module_complex V
  have : Module.Free ℤ L := inferInstance
  have hLat : ∀ (t : heckeAlgebra N k S) (f : V), f ∈ L → (t : Module.End ℂ V) f ∈ L :=
    fun t f hf ↦ CuspForm.mem_intLattice_of_mem_heckeAlgebra t.2 hf
  let ψ : heckeAlgebra N k S →ₗ[ℤ] Module.End ℤ L :=
    { toFun := fun t ↦ ((t : Module.End ℂ V).restrictScalars ℤ).restrict (hLat t)
      map_add' := fun t t' ↦ by ext f; rfl
      map_smul' := fun n t ↦ by ext f; rfl }
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    apply Subtype.ext
    refine CuspForm.eq_zero_of_forall_mem_intLattice (t : Module.End ℂ V) fun f hf ↦ ?_
    calc (t : Module.End ℂ V) f = ((ψ t ⟨f, hf⟩ : L) : V) := rfl
      _ = 0 := by rw [ht]; rfl
  exact Module.Finite.of_injective ψ hψ

/-- The Hecke algebra is a free `ℤ`-module, in every weight. -/
theorem moduleFree_heckeAlgebra (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ) :
    Module.Free ℤ (CuspForm.heckeAlgebra N k S) := by
  have := CuspForm.moduleFinite_heckeAlgebra N k S
  infer_instance

/-- The `ℤ`-span of the Hecke algebra is finitely generated, in every weight. -/
theorem toSubmodule_heckeAlgebra_fg (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ) :
    (Subalgebra.toSubmodule (CuspForm.heckeAlgebra N k S)).FG :=
  Module.Finite.iff_fg.mp (CuspForm.moduleFinite_heckeAlgebra N k S)

end CuspForm

end
