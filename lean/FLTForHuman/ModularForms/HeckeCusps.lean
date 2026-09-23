/-
  The cusp-class layer: `U_p`/`T_p` preserve boundedness/vanishing at cusps.

  FLT states the four targets in four 132-line `S_` files
  (`S_ModularFormClass_isBoundedAt_hecke{U,T}.lean`,
  `S_CuspFormClass_isZeroAt_hecke{U,T}.lean`) whose ~95-line blocks are
  identical: rational-cusp transport (`isCusp_ratCast_smul`,
  `isBoundedAt_slash_ratCast`, `isZeroAt_slash_ratCast`), the rational model
  `ratUpperTriangularGL` of `upperTriangularGL`, the two `Finset` extension
  lemmas (`isBoundedAt_sum`/`isZeroAt_sum`) and the same four `isBoundedAt`/
  `isZeroAt` proofs. This module writes that block **once** and lands the four
  public theorems verbatim from their `Theorems/` wrappers (pinned `aa2d8b3`):

  - `ModularFormClass.isBoundedAt_heckeU`, `ModularFormClass.isBoundedAt_heckeT`;
  - `CuspFormClass.isZeroAt_heckeU`, `CuspFormClass.isZeroAt_heckeT`.

  One promotion is required: `upperTriangularGL` (and its `val_` display), which
  T1 had kept `private`, is made public in `Defs/HeckeOperator.lean` — the pin
  has it public and the block's rational model `upperTriangularGL_eq_map` names
  it.

  FLT provenance: `P2M/Sol/S_ModularFormClass_isBoundedAt_heckeU.lean` lines
  14–127 (the shared block) and the three sibling files.
-/
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import FLTForHuman.ModularForms.Defs.HeckeOperator

set_option autoImplicit false

noncomputable section

open UpperHalfPlane OnePoint
open scoped MatrixGroups ModularForm

namespace ModularForm

/-! ## The shared block (private) -/

section RatCusps

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

/-- `IsCusp` is preserved by the `GL₂(ℚ)`-action through `ℚ ↪ ℝ`. -/
private theorem isCusp_ratCast_smul {c : OnePoint ℝ} (hc : IsCusp c Γ) (g : GL (Fin 2) ℚ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

/-- Transport of boundedness at a cusp along the rational slash. -/
private theorem isBoundedAt_slash_ratCast [ModularFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k :=
  OnePoint.IsBoundedAt.smul_iff.mp (ModularFormClass.bdd_at_cusps f (isCusp_ratCast_smul hc g))

/-- Transport of vanishing at a cusp along the rational slash. -/
private theorem isZeroAt_slash_ratCast [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k :=
  OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f (isCusp_ratCast_smul hc g))

end RatCusps

section HeckeMatrices

/-- The `ℚ`-model `!![a, b; 0, d]` of `upperTriangularGL`. -/
private def ratUpperTriangularGL (a b d : ℚ) (had : a * d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

/-- `upperTriangularGL` is the rational model mapped along `ℚ ↪ ℝ`. -/
private theorem upperTriangularGL_eq_map (a b d : ℚ) (had : a * d ≠ 0) :
    upperTriangularGL a b d (by exact_mod_cast had) =
      Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (ratUpperTriangularGL a b d had) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ratUpperTriangularGL, upperTriangularGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- `heckeMatrix p j` is rational. -/
private theorem exists_heckeMatrix_eq_map (p j : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeMatrix p j = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by simp [heckeMatrix]⟩
  · refine ⟨ratUpperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeMatrix, hp, ratUpperTriangularGL, upperTriangularGL,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- `heckeDiagMatrix p` is rational. -/
private theorem exists_heckeDiagMatrix_eq_map (p : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeDiagMatrix p = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by simp [heckeDiagMatrix]⟩
  · refine ⟨ratUpperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeDiagMatrix, hp, ratUpperTriangularGL, upperTriangularGL,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]

end HeckeMatrices

section Cusps

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

/-- Boundedness at a cusp is preserved by finite sums. -/
private theorem isBoundedAt_sum {ι : Type*} {c : OnePoint ℝ} {k : ℤ} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, c.IsBoundedAt (f i) k) : c.IsBoundedAt (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact Filter.const_boundedAtFilter _ (0 : ℂ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Vanishing at a cusp is preserved by finite sums. -/
private theorem isZeroAt_sum {ι : Type*} {c : OnePoint ℝ} {k : ℤ} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, c.IsZeroAt (f i) k) : c.IsZeroAt (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The `U_p` boundedness proof, before the wrapper's explicit binders. -/
private theorem isBoundedAt_heckeU [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsBoundedAt (heckeU k p ⇑f) k := by
  rw [heckeU_def]
  refine isBoundedAt_sum _ fun j _ => ?_
  obtain ⟨g, hg⟩ := exists_heckeMatrix_eq_map p j
  rw [hg]
  exact isBoundedAt_slash_ratCast f g hc

/-- The `T_p` boundedness proof, before the wrapper's explicit binders. -/
private theorem isBoundedAt_heckeT [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsBoundedAt (heckeT k p ⇑f) k := by
  rw [heckeT_eq_heckeU_add]
  refine (isBoundedAt_heckeU f p hc).add ?_
  obtain ⟨g, hg⟩ := exists_heckeDiagMatrix_eq_map p
  rw [hg]
  exact isBoundedAt_slash_ratCast f g hc

/-- The `U_p` vanishing proof, before the wrapper's explicit binders. -/
private theorem isZeroAt_heckeU [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsZeroAt (heckeU k p ⇑f) k := by
  rw [heckeU_def]
  refine isZeroAt_sum _ fun j _ => ?_
  obtain ⟨g, hg⟩ := exists_heckeMatrix_eq_map p j
  rw [hg]
  exact isZeroAt_slash_ratCast f g hc

/-- The `T_p` vanishing proof, before the wrapper's explicit binders. -/
private theorem isZeroAt_heckeT [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsZeroAt (heckeT k p ⇑f) k := by
  rw [heckeT_eq_heckeU_add]
  refine (isZeroAt_heckeU f p hc).add ?_
  obtain ⟨g, hg⟩ := exists_heckeDiagMatrix_eq_map p
  rw [hg]
  exact isZeroAt_slash_ratCast f g hc

end Cusps

end ModularForm

/-! ## The four public theorems (verbatim from their wrappers) -/

namespace ModularFormClass

/-- `U_p` preserves boundedness at cusps. Stated verbatim from
`Theorems/Thm_ModularFormClass_isBoundedAt_heckeU.lean`. -/
theorem isBoundedAt_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsBoundedAt c (ModularForm.heckeU k p ⇑f) k :=
  ModularForm.isBoundedAt_heckeU f p hc

/-- `T_p` preserves boundedness at cusps. Stated verbatim from
`Theorems/Thm_ModularFormClass_isBoundedAt_heckeT.lean`. -/
theorem isBoundedAt_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsBoundedAt c (ModularForm.heckeT k p ⇑f) k :=
  ModularForm.isBoundedAt_heckeT f p hc

end ModularFormClass

namespace CuspFormClass

/-- `U_p` preserves vanishing at cusps. Stated verbatim from
`Theorems/Thm_CuspFormClass_isZeroAt_heckeU.lean`. -/
theorem isZeroAt_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsZeroAt c (ModularForm.heckeU k p ⇑f) k :=
  ModularForm.isZeroAt_heckeU f p hc

/-- `T_p` preserves vanishing at cusps. Stated verbatim from
`Theorems/Thm_CuspFormClass_isZeroAt_heckeT.lean`. -/
theorem isZeroAt_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsZeroAt c (ModularForm.heckeT k p ⇑f) k :=
  ModularForm.isZeroAt_heckeT f p hc

end CuspFormClass

end
