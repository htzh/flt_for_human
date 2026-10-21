/-
The analytic-at-the-cusp predicate and its `q`-expansion API.

The pin writes this block — `def Nice (F : ℍ → ℂ) := AnalyticAt ℂ (cuspFunction 1 F) 0`
and its closure under `1`, `0`, `+`, `*`, `^`, `∑`, together with the resulting
`qExpansion_{pow,sum}'` and the two "a modular form is analytic at the cusp"
lemmas — into **22** `P2M/Sol/` files under the name `Nice` and **2** under the
name `An1` (`P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean:465`,
`S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.lean`).
The port already carries two copies of it, both public and both inside a *node*
module rather than a subject home:

* `ModularCurve.JOneES.Nice` in `ModularCurve/X1/FunctionField.lean:516`
  (the `JOneES` finrank/index node);
* `ModularCurve.RelrankSol.An1` in `ModularCurve/XH/Relrank.lean:533`
  (the `X_H` relative-degree node).

This module is the home. It is stated once, generally, under one name — the
pin's two spellings `Nice`/`An1` are *not* both reproduced (§3.1 of
`lean/topics/TOPIC-dedup-refactoring.md`: two spellings of one predicate forty
lines apart is the failure mode, not the fix); a consumer states its local
wrapper if it must keep the pin's binder spelling.

Consolidating the two existing port copies onto this home is a separate order:
each sits inside a module this cut does not touch (`topics/TOPIC-dedup-refactoring.md`
§6, fourth rule, and §8's residue rule).

The statements of `qExpansion_pow'`/`qExpansion_sum'` and `AnalyticAtCusp.mul/add`
are the pin's, with the pin's `Nice`↔`An1` name folded away; the proofs are the
port's already-verified ones (`X1/FunctionField.lean:516-575`), which are the
pin's.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups

open UpperHalfPlane ModularForm

namespace ModularCurve

/-- `F` is analytic at the cusp `∞`: its `q`-expansion function `cuspFunction 1 F`
is analytic at `0`. The pin's `Nice`/`An1`. -/
def AnalyticAtCusp (F : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction 1 F) 0

theorem AnalyticAtCusp.mul {F G : ℍ → ℂ} (hF : AnalyticAtCusp F) (hG : AnalyticAtCusp G) :
    AnalyticAtCusp (F * G) := by
  unfold AnalyticAtCusp at *
  rw [cuspFunction_mul hF.continuousAt hG.continuousAt]
  exact hF.mul hG

theorem AnalyticAtCusp.add {F G : ℍ → ℂ} (hF : AnalyticAtCusp F) (hG : AnalyticAtCusp G) :
    AnalyticAtCusp (F + G) := by
  unfold AnalyticAtCusp at *
  rw [cuspFunction_add hF.continuousAt hG.continuousAt]
  exact hF.add hG

theorem analyticAtCusp_one : AnalyticAtCusp (1 : ℍ → ℂ) := by
  have h : (1 : ℍ → ℂ) = ⇑(1 : ModularForm 𝒮ℒ 0) := rfl
  unfold AnalyticAtCusp
  rw [h]
  exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL

theorem analyticAtCusp_zero : AnalyticAtCusp (0 : ℍ → ℂ) := by
  have h : (0 : ℍ → ℂ) = ⇑(0 : ModularForm 𝒮ℒ 0) := rfl
  unfold AnalyticAtCusp
  rw [h]
  exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL

theorem AnalyticAtCusp.pow {F : ℍ → ℂ} (hF : AnalyticAtCusp F) :
    ∀ n : ℕ, AnalyticAtCusp (F ^ n)
  | 0 => by rw [pow_zero]; exact analyticAtCusp_one
  | n + 1 => by rw [pow_succ]; exact (AnalyticAtCusp.pow hF n).mul hF

theorem qExpansion_pow' {F : ℍ → ℂ} (hF : AnalyticAtCusp F) :
    ∀ n : ℕ, qExpansion 1 (F ^ n) = qExpansion 1 F ^ n
  | 0 => by rw [pow_zero, pow_zero, qExpansion_one]
  | n + 1 => by
    rw [pow_succ, pow_succ, qExpansion_mul (AnalyticAtCusp.pow hF n) hF, qExpansion_pow' hF n]

theorem AnalyticAtCusp.sum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (hF : ∀ i ∈ s, AnalyticAtCusp (F i)) : AnalyticAtCusp (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact analyticAtCusp_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem qExpansion_sum' {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (hF : ∀ i ∈ s, AnalyticAtCusp (F i)) :
    qExpansion 1 (∑ i ∈ s, F i) = ∑ i ∈ s, qExpansion 1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      qExpansion_add (hF a (Finset.mem_insert_self a s))
        (AnalyticAtCusp.sum s fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

/-- A modular form for a level `Γ` containing `T` is analytic at the cusp `∞`.
The pin's `An1.of_form` (in the `RelIndex` file) and `nice_of_modularForm` /
`nice_of_GG` / `nice_of_HH` (in the `Relrank` file) in one statement. -/
theorem analyticAtCusp_of_modularForm {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (F : ModularForm Γg k) :
    AnalyticAtCusp (F : ℍ → ℂ) :=
  ModularFormClass.analyticAt_cuspFunction_zero _ one_pos hΓ

end ModularCurve
