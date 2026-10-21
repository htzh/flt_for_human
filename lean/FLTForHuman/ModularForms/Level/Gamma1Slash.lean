/-
  The `Γ₁` slash and level-change toolkit.

  Four constructions and their consequences, which every level-changing argument in the
  pin re-derives inside its own `S_` file:

  * `restrictF` — restrict a modular form along an inclusion `Γ' ≤ Γ` (and the two
    level-of-`Γ₁` instances `resLevel`, `resSL`);
  * `le_conj_of_SL` — `Γ₀(L)` (as a subgroup of `GL(2, ℝ)`) sits inside `β⁻¹ • Γ₁(L)`,
    which is what makes the slash `f ∣[k] β` a form on `Γ₀(L)`;
  * `slashForm` — that slash, as a `ModularForm (ΓGL (Γ₀(L))) k`;
  * the four property transfers along a slash: periodicity (`periodic_slash`),
    holomorphy (`mdifferentiable_slash`), boundedness at the cusp
    (`bdd_slash`) and analyticity of the cusp function (`analyticAt_slash`).

  This module is the *home* for that block: the pin carries it as `section Level` of
  `S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean`
  (261 lines), and copies of pieces of it sit `private` in `WeightOne/Gamma0Integral.lean`,
  `X1/DiamondAut.lean`, `LevelN/QExpBridge.lean`, `DeligneSerre/Relevement.lean`,
  `WeightOne/Gamma1IntegralBasis.lean`, `ModularCurve/X1/Inputs.lean` and
  `HeckeEigenNebentypus.lean`.  Those copies are
  **not** touched here; folding them in is recorded in `lean/CARRY-FORWARD.md`.

  What is imported rather than restated: `Gamma1_le_of_dvd` from
  `NumberTheory/ModularForms/CongruenceSubgroupOrder.lean`, which is the `Γ₁`-order
  supplement and states it at the general shape.  `T_mem_Gamma1` and `Gamma_le_Gamma1` are
  stated here because this is the `Γ₁`-membership home and both are a handful of lines; the
  port's other public copies (`WeightOne/Defs/GammaRational.lean`, `Analytic/NormSqPow.lean`)
  predate this module and are not added to.

  Everything is transcribed at the pin's own signatures, so `spec/check_port.py` diffs it.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean

  spec-pin: P2M/Sol/S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupOrder

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace ModularForm.Level

local notation "Γ₁(" M ")" => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {L : ℕ} {k : ℤ}

/-- A subgroup of `SL(2, ℤ)` read as a subgroup of `GL(2, ℝ)`. -/
abbrev ΓGL (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 (L : ℕ) : ModularGroup.T ∈ Gamma1 L := by
  simp

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁(L)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 L)]
  exact AddSubgroup.mem_zmultiples 1

theorem L_mem_strictPeriods_Gamma (L : ℕ) :
    (L : ℝ) ∈ (ΓGL (CongruenceSubgroup.Gamma L)).strictPeriods := by
  rw [ΓGL, CongruenceSubgroup.strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples _

theorem Gamma_le_Gamma1 (L : ℕ) : CongruenceSubgroup.Gamma L ≤ Gamma1 L := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

/-- Restrict a modular form along an inclusion of level subgroups. -/
def restrictF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[scoped simp] theorem coe_restrictF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ)
    (f : ModularForm Γ k) : (⇑(restrictF h f) : ℍ → ℂ) = f := rfl

/-- Level raising: a `Γ₁(L)`-form is a `Γ₁(L')`-form when `L ∣ L'`. -/
def resLevel {L L' : ℕ} (h : L ∣ L') (f : ModularForm Γ₁(L) k) : ModularForm Γ₁(L') k :=
  restrictF (Subgroup.map_mono (Gamma1_le_of_dvd h)) f

@[scoped simp] theorem coe_resLevel {L L' : ℕ} (h : L ∣ L') (f : ModularForm Γ₁(L) k) :
    (⇑(resLevel h f) : ℍ → ℂ) = f := rfl

/-- A level-one form as a form on `ΓGL Γ`. -/
def resSL (Γ : Subgroup SL(2, ℤ)) {k : ℤ} (f : ModularForm 𝒮ℒ k) : ModularForm (ΓGL Γ) k :=
  restrictF (Subgroup.map_le_range _ _) f

@[scoped simp] theorem coe_resSL (Γ : Subgroup SL(2, ℤ)) {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    (⇑(resSL Γ f) : ℍ → ℂ) = f := rfl

/-- `Γ₀(L)` is contained in the conjugate of `Γ₁(L)` by any `β ∈ SL(2, ℤ)`. -/
theorem le_conj_of_SL (L : ℕ) (β : SL(2, ℤ)) :
    ΓGL (CongruenceSubgroup.Gamma L) ≤ ConjAct.toConjAct ((β : GL (Fin 2) ℝ))⁻¹ • Γ₁(L) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨β * δ * β⁻¹, ?_, ?_⟩
  · exact Gamma_le_Gamma1 L (Subgroup.Normal.conj_mem (Gamma_normal L) δ hδ β)
  · simp only [map_mul, map_inv]; rfl

/-- The slash `f ∣[k] β` of a `Γ₁(L)`-form, as a form on `Γ₀(L)`. -/
def slashForm [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    ModularForm (ΓGL (CongruenceSubgroup.Gamma L)) k :=
  restrictF (le_conj_of_SL L β) (ModularForm.translate f (β : GL (Fin 2) ℝ))

@[scoped simp] theorem coe_slashForm [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    (⇑(slashForm β f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] β := by
  rw [slashForm, coe_restrictF, ModularForm.coe_translate, ← ModularForm.SL_slash]

theorem periodic_slash [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    Periodic (((⇑f : ℍ → ℂ) ∣[k] β) ∘ ofComplex) L := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex (slashForm β f) (L_mem_strictPeriods_Gamma L)
  rwa [coe_slashForm] at this

theorem mdifferentiable_slash [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑f : ℍ → ℂ) ∣[k] β) := (slashForm β f).holo'

theorem bdd_slash [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    IsBoundedAtImInfty ((⇑f : ℍ → ℂ) ∣[k] β) := by
  have := ModularFormClass.bdd_at_infty (slashForm β f)
  rwa [coe_slashForm] at this

theorem analyticAt_slash [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    AnalyticAt ℂ (cuspFunction L ((⇑f : ℍ → ℂ) ∣[k] β)) 0 :=
  analyticAt_cuspFunction_zero (Nat.cast_pos.mpr (NeZero.pos L)) (periodic_slash β f)
    (mdifferentiable_slash β f) (bdd_slash β f)

end ModularForm.Level
