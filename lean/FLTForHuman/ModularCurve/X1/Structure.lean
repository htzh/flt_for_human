/-
  Four headlines of the `X₁` structure layer, from FLT's
  `P2M/Sol/S_ModularCurve_{isCurveOver,essFiniteType,diffQExp}_x1FunctionFieldBar*.lean`
  and `P2M/Sol/S_ModularCurve_closure_elemSet_eq_top.lean` (pin `aa2d8b3`); each
  statement is verbatim from the matching `Theorems/Thm_ModularCurve_*.lean` wrapper.

  * `ModularCurve.isCurveOver_x1FunctionFieldBar` and
    `ModularCurve.essFiniteType_x1FunctionFieldBar`: X₁'s base-changed function field
    is a curve over `ℚ̄` and is essentially of finite type over `ℚ̄`.  Both consume the
    same transcendental + finite-dimensional generator produced by
    `ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange`
    (`X1/FunctionFieldBaseChange.lean`) and differ only in the final application.
  * `ModularCurve.diffQExp_x1FunctionFieldBar_injective`: the `q`-expansion
    differential `diffQExp` (`Defs/HeckeDifferential.lean`) is injective.  An element
    of the Kähler module is put in the form `c • D` by
    `KaehlerDifferential.exists_unique_smul_D_of_transcendental`
    (`AlgebraicCurve/Defs/KaehlerTranscendental.lean`), and `diffQExp_smul_D` then
    splits the two branches: `c = 0`, or the generator is an algebraic element
    carried by a constant.
  * `ModularCurve.closure_elemSet_eq_top`: the elementary unipotents `elemSet (ZMod N)`
    already generate `SL(2, ZMod N)`, by pushing mathlib's generators `{S, T}` of
    `SL(2, ℤ)` through the surjective reduction map of
    `ModularForms/WeightOne/LevelOneHauptmodul.lean`.

  Dedup / adaptation notes.  The pin's `Γ₁(M)` finite-index input
  (`by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]`), the
  `upperElem`/`lowerElem` closure-membership lemmas, the `q`-expansion-differential
  API and the `q`-coefficient bookkeeping lemmas are public in the port
  (`X1/FunctionFieldBaseChange.lean`, `Defs/SL2Elementary.lean`,
  `Defs/HeckeDifferential.lean`, `Defs/Laurent.lean`) and are used directly; no
  `P2M.Util`-style scaffolding is transcribed.  The one genuinely local wall is the
  `diffQExp` proof's `haveI` block, which is spelled `have` here: Lean 4 `have`
  registers the same local instances, so the inlining behaviour of `haveI` has no
  effect on a proof of a `Prop`.  The wrappers' `attribute [-instance]` /
  `attribute [-simp]` preambles name declarations of unported modules and are not
  transcribed; nor is the pin's `set_option synthInstance.maxHeartbeats 1600000`
  (the tier-0 build is clean without it).

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_isCurveOver_x1FunctionFieldBar.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_essFiniteType_x1FunctionFieldBar.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_diffQExp_x1FunctionFieldBar_injective.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_closure_elemSet_eq_top.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_isCurveOver_x1FunctionFieldBar.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_essFiniteType_x1FunctionFieldBar.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_diffQExp_x1FunctionFieldBar_injective.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_closure_elemSet_eq_top.lean
-/
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.ModularCurve.Defs.HeckeDifferential
import FLTForHuman.ModularCurve.Defs.SL2Elementary
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

open ModularCurve
open AlgebraicCurve hiding isCurveOver_of_transcendental_of_perfectField
open Matrix MatrixGroups Subgroup
open scoped MatrixGroups

/-! ## `IsCurveOver` and `EssFiniteType` for X₁'s base-changed function field -/

/-- **X₁'s function field over `ℚ̄` is a curve.**  Verbatim from
`Theorems/Thm_ModularCurve_isCurveOver_x1FunctionFieldBar.lean`. -/
theorem ModularCurve.isCurveOver_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by
  obtain ⟨x, htr, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd

/-- **X₁'s function field over `ℚ̄` is essentially of finite type.**  Verbatim from
`Theorems/Thm_ModularCurve_essFiniteType_x1FunctionFieldBar.lean`. -/
theorem ModularCurve.essFiniteType_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by
  obtain ⟨x, htr, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  exact AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfd

/-! ## Injectivity of the `q`-expansion differential -/

/-- **`diffQExp` is injective on X₁'s function field.**  Verbatim from
`Theorems/Thm_ModularCurve_diffQExp_x1FunctionFieldBar_injective.lean`. -/
theorem ModularCurve.diffQExp_x1FunctionFieldBar_injective (M : ℕ) [NeZero M] :
    Function.Injective ⇑(ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)) := by
  obtain ⟨x, hxT, hxfd⟩ : ∃ x : ↥(ModularCurve.x1FunctionFieldBar M), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.x1FunctionFieldBar M)))
        ↥(ModularCurve.x1FunctionFieldBar M) :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
      (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  have hfin : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.x1FunctionFieldBar M)))
      ↥(ModularCurve.x1FunctionFieldBar M) := hxfd
  have halg : Algebra.IsAlgebraic
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.x1FunctionFieldBar M)))
      ↥(ModularCurve.x1FunctionFieldBar M) := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.x1FunctionFieldBar M)))
      ↥(ModularCurve.x1FunctionFieldBar M) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField

  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨c, hc, -⟩ := KaehlerDifferential.exists_unique_smul_D_of_transcendental (AlgebraicClosure ℚ) x hxT ω
  rw [hc, ModularCurve.diffQExp_smul_D] at hω
  rcases mul_eq_zero.mp hω with hc0 | hq0
  · have hc00 : c = 0 := by exact_mod_cast hc0
    rw [hc, hc00, zero_smul]
  ·
    exfalso
    apply hxT
    have hcoeff : ∀ n : ℤ, n ≠ 0 → (x : LaurentSeries (AlgebraicClosure ℚ)).coeff n = 0 := by
      intro n hn
      have h := congrArg (fun y : LaurentSeries (AlgebraicClosure ℚ) => y.coeff n) hq0
      simp only [HahnSeries.coeff_zero] at h
      change ((n : AlgebraicClosure ℚ)) * (x : LaurentSeries (AlgebraicClosure ℚ)).coeff n = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (Int.cast_ne_zero.mpr hn)
    set a : AlgebraicClosure ℚ := (x : LaurentSeries (AlgebraicClosure ℚ)).coeff 0 with ha
    have hx : (x : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a := by
      rw [ModularCurve.algebraMap_laurentSeries_eq_single]
      ext n
      by_cases hn : n = 0
      · subst hn; simp [ha]
      · rw [hcoeff n hn, HahnSeries.coeff_single_of_ne hn]
    have hx' : x = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) a := by
      apply Subtype.ext
      rw [hx, IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)
        (LaurentSeries (AlgebraicClosure ℚ)) a]
      rfl
    rw [hx']
    exact isAlgebraic_algebraMap _

/-! ## The elementary unipotents generate `SL(2, ZMod N)` -/

/-- **`SL(2, ZMod N)` is generated by the elementary unipotents.**  Verbatim from
`Theorems/Thm_ModularCurve_closure_elemSet_eq_top.lean`. -/
theorem ModularCurve.closure_elemSet_eq_top (N : ℕ) [NeZero N] :
    Subgroup.closure (ModularCurve.elemSet (ZMod N)) = ⊤ := by
  set φ : SL(2, ℤ) →* SL(2, ZMod N) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) with hφ
  have hT : φ ModularGroup.T = upperElem (1 : ZMod N) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hφ, ModularGroup.coe_T]
  have hS : φ ModularGroup.S =
      upperElem (-1 : ZMod N) * lowerElem 1 * upperElem (-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hφ, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hsurj : Function.Surjective φ :=
    ModularCurve.surjective_specialLinearGroup_map_zmod N
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective φ hsurj,
    ← SpecialLinearGroup.SL2Z_generators, MonoidHom.map_closure]
  refine (closure_le _).mpr ?_
  rintro x ⟨y, hy, rfl⟩
  rcases hy with rfl | rfl
  · rw [hS]
    exact mul_mem (mul_mem (upperElem_mem_closure_elemSet _)
      (lowerElem_mem_closure_elemSet _)) (upperElem_mem_closure_elemSet _)
  · rw [hT]
    exact upperElem_mem_closure_elemSet _

end
