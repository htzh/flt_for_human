/-
  Vanishing at cusps is preserved by the slash action of `Γ₀(M)`-matrices and of the
  Hecke diagonal matrix:

  * `CuspFormClass.isZeroAt_slash_of_mem_Gamma0` — for a cusp form of weight `k` for
    `Γ_H(M)`, `f ∣[k] (σ : GL₂(ℝ))` vanishes at every cusp `c`;
  * `CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0` — the same
    for `f ∣[k] σ ∣[k] heckeDiagMatrix ℓ`.

  The ports of the two pin leaves (42 and 56 pin lines), together with the
  statements of their `Theorems/` wrappers, in one module because their proofs
  share the rational-model gadgets `mapGL_rat_eq`, `Gamma_le_GammaH'` and the
  `scoped instance GammaH_finiteIndex'` verbatim (both pin `S_` files carry them).

  The mathematics: `Γ ≤ Γ_H(M)` puts the cusp in the arithmetic case, and
  mathlib's `OnePoint.IsZeroAt.smul_iff` transports vanishing along the rational
  slash `GL₂(ℚ)`; the two nodes differ only in which rational matrix is realized
  (`σ`, resp. `σ` times the diagonal `diagQ ℓ`).

  One private helper is re-proved, not imported: the port homes the pin node
  `CuspFormClass.isZeroAt_slash_ratCast` only as a **private** theorem in
  `FLTForHuman/ModularForms/HeckeCusps.lean:58`, so it cannot be imported here;
  this module carries its three-line proof (and the two-line
  `isCusp_ratCast_smul` it needs) under a `private` name. Nothing public is added
  by that: `spec/check_port.py` does not see private declarations, and the two
  checked statements are the wrappers' verbatim text.

  Assumes: mathlib `v4.34.0` and the port's `ModularForms/Defs/GammaH.lean`
  (`CohCarrier.mem_GammaH_iff`, `gamma0Units`, `val_gamma0Units`) and
  `ModularForms/Defs/HeckeOperator.lean` (`heckeDiagMatrix`,
  `val_heckeDiagMatrix`). `Def_CohCarrier_Level` and `Def_ModularForm_HeckeOperator`
  are home; nothing is re-proved from them.

  Mathlib-first check (2026-10-20): mathlib has `CuspFormClass.zero_at_cusps` and
  the `IsArithmetic`-transport `OnePoint.IsZeroAt.smul_iff`, but no statement that
  vanishing survives the slash by an explicit `Γ₀(M)`-element or by
  `heckeDiagMatrix` — `rg -n "isZeroAt_slash_of_mem_Gamma0"`
  and `rg -n "isZeroAt_slash_slash_heckeDiagMatrix"` over `Mathlib/` find nothing.

  Drift: `scoped instance GammaH_finiteIndex'` is carried verbatim — note that a
  `scoped instance` is parser-invisible to the checker, so the port has 8 public
  declarations here of which 6 are wired (the two `GammaH_finiteIndex'` copies are
  one declaration; the checker counts what it can parse). The pin's inline
  `#print axioms` commands are not carried.

  spec-pin: Theorems/Thm_CuspFormClass_isZeroAt_slash_of_mem_Gamma0.lean
  spec-pin: P2M/Sol/S_CuspFormClass_isZeroAt_slash_of_mem_Gamma0.lean
  spec-pin: Theorems/Thm_CuspFormClass_isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0.lean
  spec-pin: P2M/Sol/S_CuspFormClass_isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0.lean
-/
import Mathlib.NumberTheory.ModularForms.Basic
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.Defs.HeckeOperator

set_option autoImplicit false

open UpperHalfPlane OnePoint

open scoped MatrixGroups ModularForm

namespace ModularForm

section RatCusps

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

/-- `IsCusp` is preserved by the `GL₂(ℚ)`-action through `ℚ ↪ ℝ`. -/
private theorem isCusp_ratCast_smul {c : OnePoint ℝ} (hc : IsCusp c Γ) (g : GL (Fin 2) ℚ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

/-- Transport of vanishing at a cusp along the rational slash. -/
private theorem isZeroAt_slash_ratCast [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k :=
  OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f (isCusp_ratCast_smul hc g))

end RatCusps

end ModularForm

theorem mapGL_rat_eq (σ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ σ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL]

namespace ModularForm

theorem Gamma_le_GammaH' (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := CongruenceSubgroup.Gamma_mem.mp hA
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

scoped instance GammaH_finiteIndex' (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH' M H)

end ModularForm

theorem CuspFormClass.isZeroAt_slash_of_mem_Gamma0
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (σ : CongruenceSubgroup.Gamma0 M)
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {c : OnePoint ℝ} (hc : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) k := by
  have := ModularForm.isZeroAt_slash_ratCast f (Matrix.SpecialLinearGroup.mapGL ℚ (σ : SL(2, ℤ))) hc
  rwa [mapGL_rat_eq] at this

noncomputable def diagQ (ℓ : ℕ) [NeZero ℓ] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ℓ : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne ℓ])

theorem map_diagQ (ℓ : ℕ) [NeZero ℓ] :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (diagQ ℓ) = ModularForm.heckeDiagMatrix ℓ := by
  apply Units.ext
  rw [ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagQ, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ℓ : ℕ) [NeZero ℓ]
    (σ : CongruenceSubgroup.Gamma0 M)
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {c : OnePoint ℝ} (hc : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c
      ((⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) ∣[k]
        ModularForm.heckeDiagMatrix ℓ) k := by
  have := ModularForm.isZeroAt_slash_ratCast f (Matrix.SpecialLinearGroup.mapGL ℚ (σ : SL(2, ℤ)) * diagQ ℓ) hc
  rwa [map_mul, mapGL_rat_eq, map_diagQ, SlashAction.slash_mul] at this
