/-
The degree of the `α`-row on `X₁(M)`:
`[Γ₁(M) ∩ Γ₀(Mq) : Γ₁(M)] = q` when `q ∣ M` and `= q + 1` otherwise
(`ModularCurve.finrankAlong_heckeAlphaOneBar`), after FLT's
`P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaOneBar.lean` (pin `aa2d8b3`), statement
verbatim from `Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaOneBar.lean:11-14`.

The pin pays for the shared `FinrankAlphaHSol` engine **twice**: its `X₁` `S_` file
repeats, up to the prime's name (`q` for `ℓ`), the whole ~340-line block that its
`X_H` `S_` file carries. That engine has one home here, public, in
`ModularCurve/XH/HeckeDegree.lean` (`ModularCurve.HeckeDegree.*`); this module
**imports** it and adds only the `H = ⊥` assembly, whose helpers are `private`. The
headline below is this module's only public declaration.

The `q ∣ M` case collapses to the index `q`
(`CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd` through
`relIndex_Gam'_bot_of_dvd`, with the `≥ q` direction through
`relIndex_gamma0_le_relrank_adjoin_insert_jqNModC` — this is where `map_jqNModC` is
used); the `q ∤ M` case is the engine itself at `H = ⊥`.

**Demand.** `ModularCurve.finrankAlong_heckeAlphaOneBar` is cited by
`ModularCurve.heckeOperatorOneBar_comm` and the rest of the `X₁` Hecke-row column, which
is not landed yet: this is the degree layer those commutativity lemmas are stated
against.

The pin's `P2M` scaffolding (`p2m_export`/`p2m_open`/`p2m_reactivate`, `solution`, the
`M4*`/`FinrankAlphaHOne` inner namespaces) and its `attribute [-instance]` /
`attribute [-simp]` walls are dropped: **none of them turned out to be needed**.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaOneBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaOneBar.lean

  spec-pin: Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaOneBar.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaOneBar.lean
-/
import FLTForHuman.ModularCurve.XH.HeckeDegree
import FLTForHuman.ModularCurve.X1.HeckeOperator
import FLTForHuman.ModularCurve.X1.FunctionField
import FLTForHuman.ModularCurve.X1.FunctionFieldInclusion
import FLTForHuman.ModularCurve.RelIndex.LeRelrank
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.X0.FunctionFieldFull
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupLattice

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open scoped MatrixGroups

namespace ModularCurve

open CongruenceSubgroup IntermediateField AlgebraicCurve HahnSeries UpperHalfPlane
open ModularCurve.RelrankSol (Gam Gam' Gam'_le T_mem_Gam')
open ModularCurve.HeckeDegree

variable (M : ℕ) [NeZero M] (q : ℕ)

section Bot

private theorem FF_bot : FF M ⊥ = x1FunctionField M := by
  show qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊥) = qExpFunctionFieldC ℚ (Gamma1 M)
  rw [CohCarrier.GammaH_bot]

private theorem FF'_bot : FF' M ⊥ q = x1x0FunctionFieldC ℚ M (M * q) := by
  show qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊥ ⊓ Gamma0 (M * q)) =
    qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 (M * q))
  rw [CohCarrier.GammaH_bot]

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem finrankAlong_alphaOne [NeZero q] :
    finrankAlong L (heckeAlphaOneBar L M q) = relfinrank (KL M ⊥ L) (EL M ⊥ q L) := by
  have hle : laurentBaseChange L (x1FunctionField M) ≤
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * q)) := by
    rw [← FF_bot, ← FF'_bot]
    exact KL_le_EL M ⊥ q L
  rw [heckeAlphaOneBar_eq_inclusion M q hle]
  erw [finrankAlong_inclusion hle]
  show relfinrank (laurentBaseChange L (x1FunctionField M))
      (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * q))) =
    relfinrank (laurentBaseChange L (FF M ⊥)) (laurentBaseChange L (FF' M ⊥ q))
  rw [FF_bot, FF'_bot]

variable [Fact q.Prime]

private theorem relIndex_Gam'_bot_of_dvd (hq : q ∣ M) :
    (Gamma0 (M * q)).relIndex (Gam M ⊥) = q := by
  have h := CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd M q hq
  rw [Subgroup.inf_relIndex_left] at h
  show (Gamma0 (M * q)).relIndex (CohCarrier.GammaH M ⊥) = q
  rw [CohCarrier.GammaH_bot]
  exact h

private theorem jqNModC_mem_EL :
    jqNModC ℂ (M * q) ∈ laurentBaseChange ℂ (FF' M ⊥ q) := by
  haveI : NeZero (M * q) := NeZero.mul
  have h1 : jqNModC ℚ (M * q) ∈ FF' M ⊥ q := by
    have hfull : jqNModC ℚ (M * q) ∈ modularFunctionFieldFullC ℚ (M * q) :=
      jqModCd_mem_full ℚ (M * q) dvd_rfl
    have h0 : jqNModC ℚ (M * q) ∈ qExpFunctionFieldC ℚ (Gamma0 (M * q)) :=
      ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * q) hfull
    exact qExpFunctionFieldC_mono ℚ (inf_le_right : Gam' M ⊥ q ≤ Gamma0 (M * q)) h0
  have h2 : coeffEmb ℂ (jqNModC ℚ (M * q)) = jqNModC ℂ (M * q) :=
    ModularCurve.map_jqNModC (algebraMap ℚ ℂ) (M * q)
  rw [← h2]
  exact coeffEmb_mem_laurentBaseChange ℂ h1

private theorem relrank_C_ge_of_dvd (hq : q ∣ M) :
    ((q : ℕ) : Cardinal) ≤
      relrank (laurentBaseChange ℂ (FF M ⊥)) (laurentBaseChange ℂ (FF' M ⊥ q)) := by
  haveI : NeZero (M * q) := NeZero.mul
  have h23 := ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC (Gam M ⊥)
    (CohCarrier.translation_mem_GammaH M ⊥) (M * q)
  rw [relIndex_Gam'_bot_of_dvd M q hq] at h23
  change ((q : ℕ) : Cardinal) ≤ relrank (An (Gam M ⊥))
    (adjoin ℂ (insert (jqNModC ℂ (M * q)) (anSet (Gam M ⊥)))) at h23
  have hins : adjoin ℂ (insert (jqNModC ℂ (M * q)) (anSet (Gam M ⊥))) ≤
      laurentBaseChange ℂ (FF' M ⊥ q) := by
    rw [adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨jqNModC_mem_EL M q, ?_⟩
    intro x hx
    exact KL_le_EL M ⊥ q ℂ (An_Gam_le M ⊥ (subset_adjoin ℂ _ hx))
  have hsub : An (Gam M ⊥) ≤ adjoin ℂ (insert (jqNModC ℂ (M * q)) (anSet (Gam M ⊥))) :=
    adjoin.mono ℂ _ _ (Set.subset_insert _ _)
  calc ((q : ℕ) : Cardinal) ≤ relrank (An (Gam M ⊥))
        (adjoin ℂ (insert (jqNModC ℂ (M * q)) (anSet (Gam M ⊥)))) := h23
    _ ≤ relrank (An (Gam M ⊥)) (laurentBaseChange ℂ (FF' M ⊥ q)) := relrank_mono_right hsub hins
    _ = relrank (laurentBaseChange ℂ (FF M ⊥)) (laurentBaseChange ℂ (FF' M ⊥ q)) := by
          rw [laurentBaseChange_FF_eq_An]

private theorem relrank_C_le_of_dvd (hq : q ∣ M) :
    relrank (laurentBaseChange ℂ (FF M ⊥)) (laurentBaseChange ℂ (FF' M ⊥ q)) ≤
      ((q : ℕ) : Cardinal) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hind : (Gam' M ⊥ q).relIndex (Gam M ⊥) ≠ 0 := by
    intro h0
    have hdvd := Subgroup.relIndex_dvd_index_of_le (Gam'_le M ⊥ q)
    rw [h0, zero_dvd_iff] at hdvd
    exact Subgroup.FiniteIndex.index_ne_zero hdvd
  have hC2 := ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex (Gam M ⊥) (Gam' M ⊥ q)
    (Gam'_le M ⊥ q) (T_mem_Gam' M ⊥ q) hind
  change relrank (An (Gam M ⊥)) (An (Gam' M ⊥ q)) ≤ _ at hC2
  have hidx : (Gam' M ⊥ q).relIndex (Gam M ⊥) = q := by
    rw [Subgroup.inf_relIndex_left]
    exact relIndex_Gam'_bot_of_dvd M q hq
  calc relrank (laurentBaseChange ℂ (FF M ⊥)) (laurentBaseChange ℂ (FF' M ⊥ q))
        ≤ relrank (laurentBaseChange ℂ (FF M ⊥)) (An (Gam' M ⊥ q)) :=
          relrank_mono_right (KL_le_EL M ⊥ q ℂ) (laurentBaseChange_le_An (Gam' M ⊥ q))
    _ = relrank (An (Gam M ⊥)) (An (Gam' M ⊥ q)) := by rw [laurentBaseChange_FF_eq_An]
    _ ≤ ((Gam' M ⊥ q).relIndex (Gam M ⊥) : Cardinal) := hC2
    _ = ((q : ℕ) : Cardinal) := by rw [hidx]

private theorem relfinrank_FF_FF'_of_dvd (hq : q ∣ M) :
    relfinrank (FF M ⊥) (FF' M ⊥ q) = q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hC := relrank_C_le_of_dvd M q hq
  have hCge := relrank_C_ge_of_dvd M q hq
  have heq : relrank (laurentBaseChange ℂ (FF M ⊥)) (laurentBaseChange ℂ (FF' M ⊥ q)) =
      ((q : ℕ) : Cardinal) := le_antisymm hC hCge
  have hbc : relfinrank (laurentBaseChange ℂ (FF M ⊥)) (laurentBaseChange ℂ (FF' M ⊥ q)) =
      relfinrank (FF M ⊥) (FF' M ⊥ q) := relfinrank_KL_EL M ⊥ q ℂ
  rw [← hbc, relfinrank_eq_toNat_relrank, heq, Cardinal.toNat_natCast]

end Bot

/-- **The degree of the `α`-row on `X₁(M)`.** `[Γ₁(M) ∩ Γ₀(Mq) : Γ₁(M)]` is `q` when
`q ∣ M` and `q + 1` otherwise. Verbatim from
`Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaOneBar.lean:11-14`. -/
theorem finrankAlong_heckeAlphaOneBar (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (q : ℕ) [Fact q.Prime] :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaOneBar L M q) =
      if q ∣ M then q else q + 1 := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [finrankAlong_alphaOne, relfinrank_KL_EL]
  by_cases hq : q ∣ M
  · rw [ite_eq_left hq]
    exact relfinrank_FF_FF'_of_dvd M q hq
  · rw [ite_eq_right hq]
    exact relfinrank_FF_FF' M ⊥ q hq

end ModularCurve

end
