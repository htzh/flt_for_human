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

The second headline is the `β` row's degree, the pin's `DBeta` tower
(`ModularCurve.finrankAlong_heckeBetaOneBar`, statement verbatim from
`Theorems/Thm_ModularCurve_finrankAlong_heckeBetaOneBar.lean:11-14`, whose hypothesis
`h : HeckeBetaOneDefined M ℓ` is part of the statement): the `q ↦ q^ℓ` substitution
does not change the degree over `ℚ(j(q^d) : d ∣ Mℓ)`, so the β degree is the α degree
read inside the base-changed tower. The pin's `DBeta` block is transcribed as one
`private` namespace below; the β headline is this module's only new public declaration.

That private vocabulary is **imported, not re-proved**, wherever the port already has a
public home: `qExpandAlg`/`qExpandAlg_apply` are the port's own general
`K`-algebra map `ModularCurve.qExpandAlg`/`qExpandAlg_apply`
(`ModularCurve/Defs/Laurent.lean`, beside `qExpand`: the pin's private `def` of
these two `S_` files, homed once); `relfinrank_lbc_lbc` is the public
`ModularCurve.relfinrank_laurentBaseChange_eq` (the pin wants the nonzero degree over the
*top* field, the public lemma over the base: one `relfinrank_mul_relfinrank` step at each
of the two call sites); the one-line aliases `relfinrank_B0_F0'`, `F0_le_F0'` and
`B0_le_F0'` are spelled with the public `relfinrank_qExpand_full`, `full_degeneracy_le`
and `full_degeneracy_map_le`; and `relfinrank_F0_F0'` takes `dedekindPsi M ≠ 0` from the
public `dedekindPsi_pos` instead of the pin's three-level nonzero tower. The tower's
*shared* half (`F0`, `F0'`, `B0`, `dd`, `jq_mem_F0`, `jqN_mem_B0`, `adjoin_jq_le_F0`,
`relfinrank_F0_F0'`, `relfinrank_ne_zero_of_tower`, `laurentBaseChange_map_qExpand`) is
not private here at all: it is the engine's public `HeckeDegree` prelude, imported.
`FF`, `FF'`, `BB` (this side's fields) and the remaining `DBeta` steps stay `private`.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaOneBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaOneBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrankAlong_heckeBetaOneBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrankAlong_heckeBetaOneBar.lean

  spec-pin: Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaOneBar.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaOneBar.lean
  spec-pin: Theorems/Thm_ModularCurve_finrankAlong_heckeBetaOneBar.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrankAlong_heckeBetaOneBar.lean
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

/-! ## The `β`-row on `X₁(M)` — the pin's `DBeta` tower

`FF = X₁`'s function field, `FF' = X₁ ∩ X₀(Mℓ)`, `F0`/`F0'` the full divisor fields,
`B0 = F0.map (q ↦ q^ℓ)`, `BB = FF.map (q ↦ q^ℓ)` and `dd = if ℓ ∣ M then ℓ else ℓ + 1`.
The relative degrees `[F0' : F0]`, `[B0 : F0']`, `[B0 : BB]` and `[BB : FF']` are known
from the full-level computation and the α headline; cancelling the (nonzero) degree
`[FF : F0]` gives `[BB : FF'] = dd`, which is `finrankAlong β` once the β map's
`fieldRange` is identified. `FF`, `FF'`, `BB` and everything else left in this namespace
are `private`; `F0`, `F0'`, `B0`, `dd` and the five shared steps are the engine's public
prelude (`ModularCurve.HeckeDegree`, above), which this module imports. -/

namespace BetaOne

variable (ℓ : ℕ) [NeZero ℓ]

private abbrev Gam' : Subgroup SL(2, ℤ) := Gamma1 M ⊓ Gamma0 (M * ℓ)

private instance : (Gam' M ℓ).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact Gamma1_le_of_dvd (dvd_mul_right M ℓ)

private theorem T_mem_Gam' : ModularGroup.T ∈ Gam' M ℓ := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp [ModularGroup.T]
  · rw [Gamma0_mem]
    simp [ModularGroup.T]

private abbrev FF : IntermediateField ℚ (LaurentSeries ℚ) := x1FunctionField M

private abbrev FF' : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gam' M ℓ)

private abbrev BB : IntermediateField ℚ (LaurentSeries ℚ) := (x1FunctionField M).map (qExpandₐ ℓ)

private theorem FF_le : FF M ≤ FF' M ℓ := x1FunctionFieldC_le_x1x0 ℚ M (M * ℓ)

private theorem F0_le_FF : F0 M ≤ FF M := by
  rw [show F0 M = modularFunctionFieldFullC ℚ M from (modularFunctionFieldFullC_rat M).symm]
  exact (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M).trans
    (qExpFunctionFieldC_mono ℚ (Gamma1_in_Gamma0 M))

private theorem F0'_le_FF' : F0' M ℓ ≤ FF' M ℓ := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  rw [show F0' M ℓ = modularFunctionFieldFullC ℚ (M * ℓ) from
    (modularFunctionFieldFullC_rat (M * ℓ)).symm]
  exact (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * ℓ)).trans
    (qExpFunctionFieldC_mono ℚ inf_le_right)

private theorem B0_le_BB : B0 M ℓ ≤ BB M ℓ := by
  intro x hx
  rw [IntermediateField.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, F0_le_FF M hy, rfl⟩

private theorem BB_le_FF' (h : HeckeBetaOneDefined M ℓ) : BB M ℓ ≤ FF' M ℓ := by
  intro x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h y hy

private theorem relfinrank_adjoin_FF'_ne_zero (t : LaurentSeries ℚ) (ht : t ∈ FF' M ℓ)
    (htr : Transcendental ℚ t) :
    relfinrank (adjoin ℚ ({t} : Set (LaurentSeries ℚ))) (FF' M ℓ) ≠ 0 := by
  obtain ⟨x', -, hfd'⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam' M ℓ)
      (T_mem_Gam' M ℓ)
  let y : FF' M ℓ := ⟨t, ht⟩
  have hyt : Transcendental ℚ y := fun h =>
    htr ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF' M ℓ) (x := y)).mp
      (isAlgebraic_of_subsingleton_ratAlgebra _ h))
  haveI := hfd'
  have hfdy : FiniteDimensional (adjoin ℚ ({y} : Set (FF' M ℓ))) (FF' M ℓ) :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x' hyt
  exact relfinrank_adjoin_ne_zero (FF' M ℓ) y
    (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfdy)

private theorem relfinrank_B0_BB :
    relfinrank (B0 M ℓ) (BB M ℓ) = relfinrank (F0 M) (FF M) :=
  IntermediateField.relfinrank_map_map (F0 M) (FF M) (qExpandₐ ℓ)

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem fieldRange_heckeBetaOneBar (h : HeckeBetaOneDefined M ℓ) :
    ((laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))).val.comp
        (heckeBetaOneBar L M ℓ)).fieldRange =
      (laurentBaseChange L (FF M)).map (qExpandAlg L ℓ) := by
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(y : LaurentSeries L), y.2, ?_⟩
    rw [qExpandAlg_apply, AlgHom.comp_apply, ← coe_heckeBetaOneBar M ℓ h y]
    rfl
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    rw [qExpandAlg_apply, AlgHom.comp_apply, ← coe_heckeBetaOneBar M ℓ h ⟨z, hz⟩]
    rfl

end BaseChange

section Assembly

variable [Fact ℓ.Prime]

private theorem finrankAlong_heckeAlphaOneBar_eq (L : Type*) [Field L] [Algebra ℚ L] :
    finrankAlong L (heckeAlphaOneBar L M ℓ) =
      relfinrank (laurentBaseChange L (FF M)) (laurentBaseChange L (FF' M ℓ)) := by
  have hle : laurentBaseChange L (FF M) ≤ laurentBaseChange L (FF' M ℓ) :=
    laurentBaseChange_mono L (FF_le M ℓ)
  rw [heckeAlphaOneBar_eq_inclusion M ℓ hle]
  exact finrankAlong_inclusion hle

private theorem relfinrank_FF_FF' (L : Type*) [Field L] [Algebra ℚ L] :
    relfinrank (FF M) (FF' M ℓ) = dd M ℓ := by
  have hα := (finrankAlong_heckeAlphaOneBar_eq M ℓ L).symm.trans
    (ModularCurve.finrankAlong_heckeAlphaOneBar L M ℓ)
  have hmem : jq ∈ FF M := F0_le_FF M (jq_mem_F0 M)
  have hle : FF M ≤ FF' M ℓ := FF_le M ℓ
  have hfin : relfinrank (adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (FF' M ℓ) ≠ 0 :=
    relfinrank_adjoin_FF'_ne_zero M ℓ jq (hle hmem) transcendental_jq
  have hR : relfinrank (adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (FF M) ≠ 0 := by
    have h := relfinrank_mul_relfinrank
      (adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)) hle
    rw [← h] at hfin
    exact left_ne_zero_of_mul hfin
  rwa [ModularCurve.relfinrank_laurentBaseChange_eq L hle hmem transcendental_jq hR] at hα

private theorem relfinrank_F0'_FF'_eq (L : Type*) [Field L] [Algebra ℚ L] :
    relfinrank (F0' M ℓ) (FF' M ℓ) = relfinrank (F0 M) (FF M) ∧
      relfinrank (F0 M) (FF M) ≠ 0 := by
  have t1 := relfinrank_mul_relfinrank (F0_le_FF M) (FF_le M ℓ)
  have t2 := relfinrank_mul_relfinrank (full_degeneracy_le (dvd_mul_right M ℓ)) (F0'_le_FF' M ℓ)
  rw [relfinrank_FF_FF' M ℓ L] at t1
  rw [relfinrank_F0_F0', ← t1, mul_comm] at t2
  have hd : 0 < dd M ℓ := by
    have := (Fact.out : ℓ.Prime).pos
    unfold dd
    split_ifs <;> omega
  refine ⟨Nat.eq_of_mul_eq_mul_right hd t2, ?_⟩
  have hF0 : relfinrank (adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (FF' M ℓ) ≠ 0 :=
    relfinrank_adjoin_FF'_ne_zero M ℓ jq
      ((F0_le_FF M).trans (FF_le M ℓ) (jq_mem_F0 M)) transcendental_jq
  have h' := (relfinrank_ne_zero_of_tower (adjoin_jq_le_F0 M)
    ((F0_le_FF M).trans (FF_le M ℓ)) hF0).2
  exact (relfinrank_ne_zero_of_tower (F0_le_FF M) (FF_le M ℓ) h').1

private theorem relfinrank_BB_FF' (L : Type*) [Field L] [Algebra ℚ L]
    (h : HeckeBetaOneDefined M ℓ) :
    relfinrank (BB M ℓ) (FF' M ℓ) = dd M ℓ := by
  obtain ⟨hc, hc0⟩ := relfinrank_F0'_FF'_eq M ℓ L
  have s1 := relfinrank_mul_relfinrank (B0_le_BB M ℓ) (BB_le_FF' M ℓ h)
  have s2 := relfinrank_mul_relfinrank (full_degeneracy_map_le M ℓ) (F0'_le_FF' M ℓ)
  rw [relfinrank_B0_BB] at s1
  rw [relfinrank_qExpand_full M ℓ, hc, ← s1, mul_comm] at s2
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) s2).symm

private theorem main (L : Type*) [Field L] [Algebra ℚ L] (h : HeckeBetaOneDefined M ℓ) :
    finrankAlong L (heckeBetaOneBar L M ℓ) = dd M ℓ := by
  have e1 := AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange (laurentBaseChange L (FF M))
    (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) (heckeBetaOneBar L M ℓ)
  have e2 := fieldRange_heckeBetaOneBar M ℓ L h
  have e3 : relfinrank ((laurentBaseChange L (FF M)).map (qExpandAlg L ℓ))
      (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) = dd M ℓ := by
    have hle2 : BB M ℓ ≤ x1x0FunctionFieldC ℚ M (M * ℓ) := BB_le_FF' M ℓ h
    have hmem : jqN ℓ ∈ BB M ℓ := B0_le_BB M ℓ (jqN_mem_B0 M ℓ)
    have hfin : relfinrank (adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
        (x1x0FunctionFieldC ℚ M (M * ℓ)) ≠ 0 :=
      relfinrank_adjoin_FF'_ne_zero M ℓ (jqN ℓ)
        (F0'_le_FF' M ℓ (full_degeneracy_map_le M ℓ (jqN_mem_B0 M ℓ))) (transcendental_jqN ℓ)
    have hR : relfinrank (adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ))) (BB M ℓ) ≠ 0 := by
      have h := relfinrank_mul_relfinrank
        (adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)) hle2
      rw [← h] at hfin
      exact left_ne_zero_of_mul hfin
    rw [← laurentBaseChange_map_qExpand,
      ModularCurve.relfinrank_laurentBaseChange_eq L hle2 hmem (transcendental_jqN ℓ) hR]
    exact relfinrank_BB_FF' M ℓ L h
  rw [← e2] at e3
  exact e1.trans e3

end Assembly

end BetaOne

/-- **The degree of the `β`-row on `X₁(M)`.** The `q ↦ q^ℓ` degeneracy map has
`finrankAlong` equal to `ℓ` when `ℓ ∣ M` and `ℓ + 1` otherwise, under the hypothesis
that `q ↦ q^ℓ` preserves `X₁(M)`. Verbatim from
`Theorems/Thm_ModularCurve_finrankAlong_heckeBetaOneBar.lean:11-14`. -/
theorem finrankAlong_heckeBetaOneBar (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (h : ModularCurve.HeckeBetaOneDefined M ℓ) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L M ℓ) =
      if ℓ ∣ M then ℓ else ℓ + 1 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact BetaOne.main M ℓ L h

end ModularCurve

end
