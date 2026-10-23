/-
The degree of the `α`-row on `X_H(M)`: `[Γ_H(M) ∩ Γ₀(Mℓ) : Γ_H(M)] = ℓ + 1`
(`ModularCurve.finrankAlong_heckeAlphaHBar`), after FLT's
`P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaHBar.lean` (pin `aa2d8b3`), statement
verbatim from `Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar.lean:10-12`.

This module owns the shared engine, **once**: the pin pays for it twice (its `X₁` file
`P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaOneBar.lean` carries a ~340-line
`FinrankAlphaHSol` block identical to this one up to the prime's name). The `X₁`
specialisation (`FLTForHuman/ModularCurve/X1/HeckeDegree.lean`) imports the engine from
here and adds only its `H = ⊥` assembly. The engine is therefore **public**, at the
pin's declaration names; the engine's namespace is `ModularCurve.HeckeDegree` (the
pin's `FinrankAlphaHSol`).

**Demand.** `ModularCurve.finrankAlong_heckeAlphaHBar` is cited by the `X_H` Hecke-row
column (`ModularCurve.heckeOperatorHAlong_comm`, …), which is not landed yet: this is the
degree layer those commutativity lemmas are stated against, and the frontier lists it as
`used_by(project) 10`. The `X₁` twin (`ModularCurve/X1/HeckeDegree.lean`) is cited by
`ModularCurve.heckeOperatorOneBar_comm` and the rest of the `X₁` column.

Reused rather than re-proved (all already public elsewhere): `Gam`, `Gam'`, `Gam'_le`,
`T_mem_Gam'` and `coeffEmb_intSeriesC` are `ModularCurve.RelrankSol.*`
(`ModularCurve/XH/Relrank.lean`); `anSet` is `ModularCurve.RelIndex.ratioSet`
(`ModularCurve/RelIndex/RatioField.lean`) — only the abbreviation is written here, so
that the pin's statement text still diffs; `laurentBaseChange_mono'` is
`Defs/Laurent.lean`'s `laurentBaseChange_mono`.

The pin's `P2M` scaffolding (`p2m_export`/`p2m_open`/`p2m_reactivate`, `solution`, the
`M4*`/`FinrankAlphaHOne` inner namespaces) is dropped, as are its `attribute [-instance]`
/ `attribute [-simp]` walls: **none of them turned out to be needed** — the module
elaborates without them (the port's convention; see `porting-playbook.md` §3).

One thing *was* added to make elaboration work, and it is not an `attribute [-]` line:
the private `isTorsionFree_extendScalars` below. `rank_pos`/`Module.finrank_pos` need
`Module.IsTorsionFree ↥A ↥(extendScalars h)`, and the generic search for it — through
`FaithfulSMul.to_isTorsionFree`, whose `FaithfulSMul ↥A ↥(extendScalars h)` side is what
blows up — exceeds the default `synthInstance.maxHeartbeats` (20000) inside this module's
instance environment. The private lemma supplies the instance directly (injectivity of
the inclusion, `Subtype.val`), so the file needs **no** heartbeat bump: it builds at the
defaults. Call sites: `relrank_mono_right` and `relfinrank_FF_FF'`; the same instance in
`relfinrank_adjoin_ne_zero` is the `adjoin`-shaped twin and is supplied inline there.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaHBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrankAlong_heckeBetaHBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrankAlong_heckeBetaHBar.lean

Two more headlines follow the engine, both below the `α` headline and both outside the
engine block: the `p ∣ M` branch of the `α` row
(`ModularCurve.finrankAlong_heckeAlphaHBar_of_dvd`, `Theorems/…_of_dvd.lean:12-15`) and
the `β` row (`ModularCurve.finrankAlong_heckeBetaHBar`, `Theorems/…_heckeBetaHBar.lean:14-16`).
Their machinery — the pin's `FinrankAlphaHDvdSol` and `DBetaH` blocks — is `private`; the
`β` headline needs no `Defined` hypothesis because on the `H` side `heckeBetaHBar` is total
(its fallback is `heckeAlphaHBar`), and the missing hypothesis is supplied by
`ModularCurve.heckeInputsHAlong` (`ModularCurve/XH/HeckeInputs.lean`, public).

Four imports were added for these two blocks and nothing else changed in the file's
import list: `XH/HeckeInputs` (`heckeInputsHAlong`), `X1/FunctionFieldInclusion`
(`modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0`), `X0/FunctionFieldFull`
(`jqModCd_mem_full`), and `NumberTheory/ModularForms/CongruenceSubgroupLattice`
(`relIndex_gamma1_inf_gamma0_mul_of_dvd`). As in the `X₁` module, the pin's private
vocabulary is imported rather than re-proved wherever the port has a public home
(`qExpandAlg`, which the pin writes privately in these two `S_` files, is the port's
general `ModularCurve.qExpandAlg` in `ModularCurve/Defs/Laurent.lean` — the same name,
homed beside `qExpand`; `relfinrank_lbc_lbc` →
`relfinrank_laurentBaseChange_eq`, `relfinrank_B0_F0'` → `relfinrank_qExpand_full`,
`F0_le_F0'` → `full_degeneracy_le`, `B0_le_F0'` → `full_degeneracy_map_le`, and
`dedekindPsi_pos` for the nonzero `ψ(M)`); no statement moved in that pass.

The `β` tower's *shared* half is not repeated here either: it lives once, public, in the
engine block (§ "the `β`-row prelude" below) — `F0`, `F0'`, `B0`, `dd`, `jq_mem_F0`,
`jqN_mem_B0`, `adjoin_jq_le_F0`, `relfinrank_F0_F0'`, `relfinrank_ne_zero_of_tower`,
`laurentBaseChange_map_qExpand` — because the same ten are needed by `X₁`'s `DBeta` and
by this module's `DBetaH` and reference neither side's `FF`/`FF'`/`BB`. Only the
side-specific `BB` and `relfinrank_B0_BB` stay `private` in `DBetaH`.

  spec-pin: Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaHBar.lean
  spec-pin: Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd.lean
  spec-pin: Theorems/Thm_ModularCurve_finrankAlong_heckeBetaHBar.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrankAlong_heckeBetaHBar.lean
-/
import FLTForHuman.ModularCurve.XH.Relrank
import FLTForHuman.ModularCurve.XH.FunctionField
import FLTForHuman.ModularCurve.XH.HeckeOperator
import FLTForHuman.ModularCurve.XH.HeckeInputs
import FLTForHuman.ModularCurve.X1.FunctionField
import FLTForHuman.ModularCurve.X1.FunctionFieldInclusion
import FLTForHuman.ModularCurve.X1.QExpansionDiv
import FLTForHuman.ModularCurve.X0.FunctionFieldFull
import FLTForHuman.ModularCurve.RelIndex.LeRelrank
import FLTForHuman.ModularCurve.RelIndex.LeRelIndex
import FLTForHuman.ModularCurve.Degree.LaurentGlue
import FLTForHuman.ModularCurve.Degree.Relfinrank
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.IsCurveOver.FinitenessTransfer
import FLTForHuman.ModularCurve.Gamma0Index
import FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupLattice

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open scoped MatrixGroups

namespace ModularCurve

namespace HeckeDegree

open CongruenceSubgroup IntermediateField AlgebraicCurve HahnSeries UpperHalfPlane
open ModularCurve.RelrankSol (Gam Gam' Gam'_le T_mem_Gam' coeffEmb_intSeriesC)

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

section Groups

/-- A field acting on a field extension is torsion-free; stated privately because the
generic instance search for `Module.IsTorsionFree` over `IntermediateField.extendScalars`
does not find it within the default instance-heartbeat budget. -/
private theorem isTorsionFree_extendScalars {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A B : IntermediateField K L} (h : A ≤ B) : Module.IsTorsionFree ↥A ↥(extendScalars h) := by
  refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
  intro a b hab
  simpa using congrArg Subtype.val hab

scoped instance : (Gam M H).FiniteIndex := Subgroup.finiteIndex_of_le (CohCarrier.Gamma1_le_GammaH M H)

scoped instance [NeZero ℓ] : (Gam' M H ℓ).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (ModularCurve.Gamma1_le_of_dvd (dvd_mul_right M ℓ)).trans (CohCarrier.Gamma1_le_GammaH M H)

theorem Gam'_eq (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : Gam' M H ℓ = Gamma0 ℓ ⊓ Gam M H := by
  ext A
  simp only [Subgroup.mem_inf, Gamma0_mem]
  constructor
  · rintro ⟨hA, h0⟩
    refine ⟨?_, hA⟩
    have : ((M * ℓ : ℕ) : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      ((show ((ℓ : ℕ) : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans this)
  · rintro ⟨h0, hA⟩
    refine ⟨hA, ?_⟩
    have hM : ((M : ℕ) : ℤ) ∣ A 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp (CohCarrier.GammaH_le_Gamma0 H hA))
    have hl : ((ℓ : ℕ) : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    have hcop : IsCoprime ((M : ℕ) : ℤ) ((ℓ : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))
    have := hcop.mul_dvd hM hl
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast this)

theorem index_Gamma0_prime [Fact ℓ.Prime] : (Gamma0 ℓ).index = ℓ + 1 := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  rw [ModularCurve.Gamma0_index, ModularCurve.dedekindPsi, _root_.dedekindPsi]
  have h1 : (ℓ.divisors.filter Squarefree) = {1, ℓ} := by
    rw [Nat.Prime.divisors hp]
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro (rfl | rfl)
      exacts [⟨Or.inl rfl, squarefree_one⟩, ⟨Or.inr rfl, hp.squarefree⟩]
  rw [h1, Finset.sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos]

theorem relIndex_Gam'_le [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    (Gam' M H ℓ).relIndex (Gam M H) ≤ ℓ + 1 := by
  rw [Gam'_eq M H ℓ Fact.out hℓM, Subgroup.inf_relIndex_right]
  have hidx : (Gamma0 ℓ).index = ℓ + 1 := index_Gamma0_prime ℓ
  calc (Gamma0 ℓ).relIndex (Gam M H) ≤ (Gamma0 ℓ).relIndex ⊤ :=
        Subgroup.relIndex_le_of_le_right le_top (by
          rw [Subgroup.relIndex_top_right, hidx]; exact Nat.succ_ne_zero _)
    _ = ℓ + 1 := by rw [Subgroup.relIndex_top_right, hidx]

end Groups

section RatFields

abbrev FF : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gam M H)

abbrev FF' : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gam' M H ℓ)

theorem FF_eq : FF M H = xHFunctionField M H := rfl

theorem FF'_eq : FF' M H ℓ = xHTopFunctionFieldC ℚ M H (M * ℓ) := rfl

theorem FF_le : FF M H ≤ FF' M H ℓ := qExpFunctionFieldC_mono ℚ (Gam'_le M H ℓ)

theorem relfinrank_adjoin_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (B : IntermediateField K E) (x : B) :
    relfinrank (adjoin K ({(x : E)} : Set E)) B = Module.finrank (adjoin K ({x} : Set B)) B := by
  have hc : (adjoin K ({(x : E)} : Set E)).comap B.val = adjoin K ({x} : Set B) := by
    apply le_antisymm
    · intro y hy
      change B.val y ∈ adjoin K ({(x : E)} : Set E) at hy
      have h' : (y : E) ∈ lift (adjoin K ({x} : Set B)) := by
        rw [lift_adjoin_simple]; exact hy
      exact (IntermediateField.mem_lift y).mp h'
    · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      change B.val x ∈ adjoin K ({(x : E)} : Set E)
      exact mem_adjoin_simple_self K (x : E)
  have h := IntermediateField.finrank_comap B.val (A := adjoin K ({(x : E)} : Set E))
  rw [fieldRange_val] at h
  rw [← h]
  exact congrArg (fun C : IntermediateField K B => Module.finrank C B) hc

theorem relfinrank_adjoin_ne_zero {K E : Type*} [Field K] [Field E] [Algebra K E]
    (B : IntermediateField K E) (x : B) (h : FiniteDimensional (adjoin K ({x} : Set B)) B) :
    relfinrank (adjoin K ({(x : E)} : Set E)) B ≠ 0 := by
  rw [relfinrank_adjoin_eq_finrank]
  haveI : Module.IsTorsionFree ↥(adjoin K ({x} : Set B)) ↥B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective _ _)
  exact Module.finrank_pos.ne'

theorem transcendental_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F} (h : @Transcendental ℚ F _ _ i₁ x) : @Transcendental ℚ F _ _ i₂ x := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

theorem isAlgebraic_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F} (h : @IsAlgebraic ℚ F _ _ i₁ x) : @IsAlgebraic ℚ F _ _ i₂ x := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

theorem finiteDimensional_adjoin_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F}
    (h : letI := i₁; FiniteDimensional (adjoin ℚ ({x} : Set F)) F) :
    letI := i₂; FiniteDimensional (adjoin ℚ ({x} : Set F)) F := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

variable [NeZero ℓ]

theorem exists_good_x :
    ∃ x : LaurentSeries ℚ, x ∈ FF M H ∧ Transcendental ℚ x ∧
      relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF M H) ≠ 0 ∧
      relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF' M H ℓ) ≠ 0 := by
  obtain ⟨x, hxt, hfd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam M H)
      (CohCarrier.translation_mem_GammaH M H)
  obtain ⟨x', hxt', hfd'⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam' M H ℓ)
      (T_mem_Gam' M H ℓ)

  let y : FF' M H ℓ := ⟨(x : LaurentSeries ℚ), FF_le M H ℓ x.2⟩
  have hxE : Transcendental ℚ (x : LaurentSeries ℚ) := fun h =>
    transcendental_of_subsingleton_ratAlgebra _ hxt
      ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF M H) (x := x)).mpr h)
  have hyt : Transcendental ℚ y := fun h =>
    hxE ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF' M H ℓ) (x := y)).mp
      (isAlgebraic_of_subsingleton_ratAlgebra _ h))
  haveI := hfd'
  have hfdy : FiniteDimensional (adjoin ℚ ({y} : Set (FF' M H ℓ))) (FF' M H ℓ) :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x' hyt
  refine ⟨_, x.2, hxE,
    relfinrank_adjoin_ne_zero (FF M H) x (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfd),
    relfinrank_adjoin_ne_zero (FF' M H ℓ) y
      (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfdy)⟩

end RatFields

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]

abbrev KL : IntermediateField L (LaurentSeries L) := laurentBaseChange L (FF M H)

abbrev EL : IntermediateField L (LaurentSeries L) := laurentBaseChange L (FF' M H ℓ)

theorem KL_le_EL : KL M H L ≤ EL M H ℓ L := laurentBaseChange_mono L (FF_le M H ℓ)

variable [NeZero ℓ]

theorem relfinrank_KL_EL :
    relfinrank (KL M H L) (EL M H ℓ L) = relfinrank (FF M H) (FF' M H ℓ) := by
  obtain ⟨x, hxF, hxt, hF, -⟩ := exists_good_x M H ℓ
  have h1 := ModularCurve.relfinrank_laurentBaseChange L (FF M H) x hxF hxt
  have h2 := ModularCurve.relfinrank_laurentBaseChange L (FF' M H ℓ) x (FF_le M H ℓ hxF) hxt
  have hxle : adjoin ℚ ({x} : Set (LaurentSeries ℚ)) ≤ FF M H := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact hxF
  have hxLle : adjoin L ({coeffEmb L x} : Set (LaurentSeries L)) ≤ KL M H L := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact coeffEmb_mem_laurentBaseChange L hxF
  have tQ := relfinrank_mul_relfinrank hxle (FF_le M H ℓ)
  have tL := relfinrank_mul_relfinrank hxLle (KL_le_EL M H ℓ L)
  rw [h1, h2, ← tQ] at tL
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hF) tL

theorem fieldRange_val_comp_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (h : A ≤ B) :
    (B.val.comp (IntermediateField.inclusion h)).fieldRange = A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem finrankAlong_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (h : A ≤ B) :
    finrankAlong K (IntermediateField.inclusion h) = relfinrank A B := by
  rw [AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange, fieldRange_val_comp_inclusion]

theorem finrankAlong_alpha :
    finrankAlong L (heckeAlphaHBar L M H ℓ) = relfinrank (KL M H L) (EL M H ℓ L) := by
  rw [heckeAlphaHBar_eq_inclusion M H ℓ (KL_le_EL M H ℓ L)]
  exact finrankAlong_inclusion (KL_le_EL M H ℓ L)

end BaseChange

section ComplexSide

abbrev anSet (Δ : Subgroup SL(2, ℤ)) : Set (LaurentSeries ℂ) := RelIndex.ratioSet Δ

abbrev An (Δ : Subgroup SL(2, ℤ)) : IntermediateField ℂ (LaurentSeries ℂ) := adjoin ℂ (anSet Δ)

theorem coeffEmb_image_subset (Δ : Subgroup SL(2, ℤ)) :
    coeffEmb ℂ '' intFormRatiosC ℚ Δ ⊆ anSet Δ := by
  rintro _ ⟨x, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
  refine ⟨k, f, g, ?_, ?_⟩
  · intro h0
    apply hg0
    have := RelrankSol.coeffEmb_intSeriesC hg
    rw [h0, map_zero] at this
    exact (map_eq_zero_iff _ (RingHom.injective _)).mp this
  · rw [map_div₀, RelrankSol.coeffEmb_intSeriesC hf, RelrankSol.coeffEmb_intSeriesC hg]
    rfl

theorem laurentBaseChange_le_An (Δ : Subgroup SL(2, ℤ)) :
    laurentBaseChange ℂ (qExpFunctionFieldC ℚ Δ) ≤ An Δ := by
  rw [qExpFunctionFieldC, laurentBaseChange_adjoin]
  exact adjoin.mono ℂ _ _ (coeffEmb_image_subset Δ)

theorem An_Gam_le : An (Gam M H) ≤ laurentBaseChange ℂ (FF M H) := by
  rw [adjoin_le_iff]
  rintro _ ⟨k, f, g, hg, rfl⟩
  have hg' : g ≠ 0 := by
    rintro rfl
    exact hg (by rw [FunLike.coe_zero, qExpansion_zero])
  exact ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField M H f g hg'

theorem laurentBaseChange_FF_eq_An : laurentBaseChange ℂ (FF M H) = An (Gam M H) :=
  le_antisymm (laurentBaseChange_le_An (Gam M H)) (An_Gam_le M H)

theorem relrank_mono_right {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B C : IntermediateField K E} (hAB : A ≤ B) (hBC : B ≤ C) : relrank A B ≤ relrank A C := by
  rw [← relrank_mul_relrank hAB hBC]
  have h0 : relrank B C ≠ 0 := by
    rw [relrank_eq_rank_of_le hBC]
    haveI : Module.IsTorsionFree ↥B ↥(extendScalars hBC) := isTorsionFree_extendScalars hBC
    exact rank_pos.ne'
  exact Cardinal.le_mul_right h0

variable [Fact ℓ.Prime]

theorem relrank_C_le (hℓM : ¬ ℓ ∣ M) :
    relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) ≤ ((ℓ + 1 : ℕ) : Cardinal) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hind : (Gam' M H ℓ).relIndex (Gam M H) ≠ 0 := by
    intro h0
    have hdvd := Subgroup.relIndex_dvd_index_of_le (Gam'_le M H ℓ)
    rw [h0, zero_dvd_iff] at hdvd
    exact Subgroup.FiniteIndex.index_ne_zero hdvd
  have hC2 := ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex (Gam M H) (Gam' M H ℓ)
    (Gam'_le M H ℓ) (T_mem_Gam' M H ℓ) hind
  change relrank (An (Gam M H)) (An (Gam' M H ℓ)) ≤ _ at hC2
  calc relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ))
        ≤ relrank (laurentBaseChange ℂ (FF M H)) (An (Gam' M H ℓ)) :=
          relrank_mono_right (KL_le_EL M H ℓ ℂ) (laurentBaseChange_le_An (Gam' M H ℓ))
    _ = relrank (An (Gam M H)) (An (Gam' M H ℓ)) := by rw [laurentBaseChange_FF_eq_An]
    _ ≤ ((Gam' M H ℓ).relIndex (Gam M H) : Cardinal) := hC2
    _ ≤ ((ℓ + 1 : ℕ) : Cardinal) := by exact_mod_cast relIndex_Gam'_le M H ℓ hℓM

end ComplexSide

section Assembly

variable [Fact ℓ.Prime]

theorem relfinrank_FF_FF' (hℓM : ¬ ℓ ∣ M) : relfinrank (FF M H) (FF' M H ℓ) = ℓ + 1 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

  have hlo : ((ℓ + 1 : ℕ) : Cardinal) ≤ relrank (FF M H) (FF' M H ℓ) :=
    ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd M H hℓM

  have hC := relrank_C_le M H ℓ hℓM
  have hbc : relfinrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) =
      relfinrank (FF M H) (FF' M H ℓ) := relfinrank_KL_EL M H ℓ ℂ
  have hfinC : relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) < Cardinal.aleph0 :=
    lt_of_le_of_lt hC (Cardinal.natCast_lt_aleph0)
  have h1 : ((relfinrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) : ℕ) : Cardinal) =
      relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) := by
    rw [relfinrank_eq_toNat_relrank]
    exact Cardinal.cast_toNat_of_lt_aleph0 hfinC
  have hup : relfinrank (FF M H) (FF' M H ℓ) ≤ ℓ + 1 := by
    rw [← hbc]
    have : ((relfinrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) : ℕ) : Cardinal)
        ≤ ((ℓ + 1 : ℕ) : Cardinal) := h1 ▸ hC
    exact_mod_cast this

  have hneC : relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) ≠ 0 := by
    rw [relrank_eq_rank_of_le (KL_le_EL M H ℓ ℂ)]
    haveI : Module.IsTorsionFree ↥(KL M H ℂ) ↥(extendScalars (KL_le_EL M H ℓ ℂ)) :=
      isTorsionFree_extendScalars (KL_le_EL M H ℓ ℂ)
    exact rank_pos.ne'
  have hne : relfinrank (FF M H) (FF' M H ℓ) ≠ 0 := by
    rw [← hbc]
    intro h0
    rw [h0, Nat.cast_zero] at h1
    exact hneC h1.symm
  have hfin : relrank (FF M H) (FF' M H ℓ) < Cardinal.aleph0 := by
    rw [relfinrank_eq_toNat_relrank] at hne
    by_contra hinf
    exact hne (Cardinal.toNat_apply_of_aleph0_le (le_of_not_gt hinf))
  have h2 : ((relfinrank (FF M H) (FF' M H ℓ) : ℕ) : Cardinal) = relrank (FF M H) (FF' M H ℓ) := by
    rw [relfinrank_eq_toNat_relrank]
    exact Cardinal.cast_toNat_of_lt_aleph0 hfin
  have hlo' : ℓ + 1 ≤ relfinrank (FF M H) (FF' M H ℓ) := by
    have : ((ℓ + 1 : ℕ) : Cardinal) ≤ ((relfinrank (FF M H) (FF' M H ℓ) : ℕ) : Cardinal) := h2 ▸ hlo
    exact_mod_cast this
  omega

end Assembly

/-! ## The `β`-row prelude — the shared half of the two `β` proofs

Both `β` towers (`X₁`'s `DBeta` and `X_H`'s `DBetaH`) are the same computation over
the full divisor field `F0 = ℚ(j(q^d) : d ∣ M)` and its image under `q ↦ q^ℓ`: the
statements below never mention `Γ_H(M)`, `Γ₁(M)` or either side's `FF`, `FF'`, `BB`
(those are the per-side fields and stay `private` in the two β namespaces), so this
half is stated **once**, here, and both modules consume it. `F0`, `F0'`, `B0` and
`dd` are the abbreviations the statements mention; `dd = if ℓ ∣ M then ℓ else ℓ + 1`
is the common degree.

Pin text verbatim from `P2M/Sol/S_ModularCurve_finrankAlong_heckeBetaHBar.lean`
(identical in `…_heckeBetaOneBar.lean`, whose own `FF` is `x1FunctionField`).
`laurentBaseChange_map_qExpand` writes its codomain as `.map (qExpandAlg L ℓ)`, the
pin's own text: `qExpandAlg` is the pin's `def` of these two `S_` files, and since
HD1d it is the port's one general `K`-algebra form of `qExpand`
(`ModularCurve/Defs/Laurent.lean`). All ten declarations of this prelude are
therefore text-identical to the pin, and the module carries **no** `own:`
exemption. -/

section BetaPrelude

variable [NeZero ℓ]

abbrev F0 : IntermediateField ℚ (LaurentSeries ℚ) := modularFunctionFieldFull M

abbrev F0' : IntermediateField ℚ (LaurentSeries ℚ) := modularFunctionFieldFull (M * ℓ)

abbrev B0 : IntermediateField ℚ (LaurentSeries ℚ) :=
  (modularFunctionFieldFull M).map (qExpandₐ ℓ)

abbrev dd : ℕ := if ℓ ∣ M then ℓ else ℓ + 1

theorem relfinrank_ne_zero_of_tower {K E : Type*} [Field K] [Field E] [Algebra K E]
    {T A C : IntermediateField K E} (hTA : T ≤ A) (hAC : A ≤ C) (h : relfinrank T C ≠ 0) :
    relfinrank T A ≠ 0 ∧ relfinrank A C ≠ 0 := by
  have := relfinrank_mul_relfinrank hTA hAC
  rw [← this] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

theorem jq_mem_F0 : jq ∈ F0 M := by
  have h := jqd_mem_full M (one_dvd M)
  rwa [qExpand_one_apply] at h

theorem jqN_mem_B0 : jqN ℓ ∈ B0 M ℓ := ⟨jq, jq_mem_F0 M, rfl⟩

theorem adjoin_jq_le_F0 : adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤ F0 M := by
  rw [adjoin_le_iff, Set.singleton_subset_iff]
  exact jq_mem_F0 M

theorem relfinrank_F0_F0' [Fact ℓ.Prime] : relfinrank (F0 M) (F0' M ℓ) = dd M ℓ := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  have h1 := relfinrank_full_eq_dedekindPsi M
  have h2 := relfinrank_full_eq_dedekindPsi (M * ℓ)
  have t := relfinrank_mul_relfinrank (adjoin_jq_le_F0 M) (full_degeneracy_le (dvd_mul_right M ℓ))
  rw [h1, h2, dedekindPsi_mul_prime M ℓ Fact.out, mul_comm] at t
  exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos M (NeZero.ne M)) t

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem laurentBaseChange_map_qExpand (A : IntermediateField ℚ (LaurentSeries ℚ)) :
    laurentBaseChange L (A.map (qExpandₐ ℓ)) = (laurentBaseChange L A).map (qExpandAlg L ℓ) := by
  rw [laurentBaseChange, laurentBaseChange, IntermediateField.adjoin_map,
    IntermediateField.coe_map, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun y _ => ?_
  show coeffMap (algebraMap ℚ L) (qExpand ℚ ℓ y) = qExpand L ℓ (coeffMap (algebraMap ℚ L) y)
  exact coeffMap_qExpand _ _ _

end BetaPrelude

end HeckeDegree

/-- **The degree of the `α`-row on `X_H(M)`.** `[Γ_H(M) ∩ Γ₀(Mℓ) : Γ_H(M)] = ℓ + 1` for
`ℓ ∤ M`. Verbatim from
`Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar.lean:10-12`. -/
theorem finrankAlong_heckeAlphaHBar (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaHBar L M H ℓ) = ℓ + 1 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [HeckeDegree.finrankAlong_alpha, HeckeDegree.relfinrank_KL_EL,
    HeckeDegree.relfinrank_FF_FF' M H ℓ hℓM]

open CongruenceSubgroup IntermediateField AlgebraicCurve HahnSeries UpperHalfPlane
open ModularCurve.RelrankSol (Gam Gam' Gam'_le T_mem_Gam')
open HeckeDegree

/-! ## The `p ∣ M` branch of the `α` row

For `p ∣ M` the level-`p` cover is already contained in `Γ₀(Mp)` at level `M`
(`Γ_H(M) ⊆ Γ₀(M)` and `Γ₀(Mp) ≤ Γ₀(M)`), so the relative index collapses to the
`Γ₀`-index `p` and the degree follows by the engine's `KL`/`EL` base change, exactly as in
the `ℓ ∤ M` headline. This is the pin's `FinrankAlphaHDvdSol` block, `private` here. -/

namespace AlphaHDvd

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

private theorem dedekindPsi_mul_of_dvd :
    ∀ (n : ℕ), n ≠ 0 → n ∣ M → dedekindPsi (M * n) = n * dedekindPsi M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hnM
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · exact (hn0 rfl).elim
      · simp
    · obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      obtain ⟨n', rfl⟩ := hqn
      have hn'0 : n' ≠ 0 := fun h => hn0 (by rw [h, mul_zero])
      have hn'M : n' ∣ M := (Dvd.intro_left q rfl).trans hnM
      have hqM : q ∣ M := (Dvd.intro n' rfl).trans hnM
      have hlt : n' < q * n' := by
        have h2 : 2 ≤ q := hq.two_le
        nlinarith [Nat.pos_of_ne_zero hn'0]
      have h1 := ih n' hlt hn'0 hn'M
      haveI : NeZero (M * n') := ⟨mul_ne_zero (NeZero.ne M) hn'0⟩
      have h2 := dedekindPsi_mul_prime (M * n') q hq
      rw [ite_eq_left (dvd_mul_of_dvd_left hqM n')] at h2
      rw [show M * (q * n') = M * n' * q by ring, h2, h1]
      ring

private theorem relIndex_Gamma0_mul_Gam (hℓM : ℓ ∣ M) :
    (Gamma0 (M * ℓ)).relIndex (Gam M H) = ℓ := by
  have hℓ0 : ℓ ≠ 0 := NeZero.ne ℓ
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) hℓ0⟩
  have hup0 : (Gamma0 (M * ℓ)).relIndex (Gamma0 M) = ℓ := by
    have h := Subgroup.relIndex_mul_index (Gamma0_le_of_dvd (dvd_mul_right M ℓ))
    rw [ModularCurve.Gamma0_index, ModularCurve.Gamma0_index,
      dedekindPsi_mul_of_dvd M ℓ hℓ0 hℓM] at h
    have hψ : dedekindPsi M ≠ 0 := by
      rw [← ModularCurve.Gamma0_index]
      exact Subgroup.FiniteIndex.index_ne_zero
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hψ) h
  have hne0 : (Gamma0 (M * ℓ)).relIndex (Gamma0 M) ≠ 0 := by rw [hup0]; exact hℓ0
  have hup : (Gamma0 (M * ℓ)).relIndex (Gam M H) ≤ ℓ :=
    (Subgroup.relIndex_le_of_le_right (CohCarrier.GammaH_le_Gamma0 H) hne0).trans hup0.le
  have hlo0 : (Gamma0 (M * ℓ)).relIndex (Gamma1 M) = ℓ := by
    rw [← Subgroup.inf_relIndex_right, inf_comm]
    exact CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd M ℓ hℓM
  have hneH : (Gamma0 (M * ℓ)).relIndex (Gam M H) ≠ 0 := by
    rw [← Subgroup.inf_relIndex_right,
      ← show Gam' M H ℓ = Gamma0 (M * ℓ) ⊓ Gam M H from inf_comm _ _]
    intro h0
    have hdvd := Subgroup.relIndex_dvd_index_of_le (Gam'_le M H ℓ)
    rw [h0, zero_dvd_iff] at hdvd
    exact Subgroup.FiniteIndex.index_ne_zero hdvd
  have hlo : ℓ ≤ (Gamma0 (M * ℓ)).relIndex (Gam M H) :=
    hlo0.symm.le.trans (Subgroup.relIndex_le_of_le_right (CohCarrier.Gamma1_le_GammaH M H) hneH)
  exact le_antisymm hup hlo

private theorem relIndex_Gam'_eq (hℓM : ℓ ∣ M) :
    (Gam' M H ℓ).relIndex (Gam M H) = ℓ := by
  rw [show Gam' M H ℓ = Gamma0 (M * ℓ) ⊓ Gam M H from inf_comm _ _, Subgroup.inf_relIndex_right]
  exact relIndex_Gamma0_mul_Gam M H ℓ hℓM

private theorem relrank_C_le (hℓM : ℓ ∣ M) :
    relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) ≤
      ((ℓ : ℕ) : Cardinal) := by
  have hind : (Gam' M H ℓ).relIndex (Gam M H) ≠ 0 := by
    intro h0
    have hdvd := Subgroup.relIndex_dvd_index_of_le (Gam'_le M H ℓ)
    rw [h0, zero_dvd_iff] at hdvd
    exact Subgroup.FiniteIndex.index_ne_zero hdvd
  have hC2 := ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex (Gam M H) (Gam' M H ℓ)
    (Gam'_le M H ℓ) (T_mem_Gam' M H ℓ) hind
  change relrank (An (Gam M H)) (An (Gam' M H ℓ)) ≤ _ at hC2
  calc relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ))
        ≤ relrank (laurentBaseChange ℂ (FF M H)) (An (Gam' M H ℓ)) :=
          relrank_mono_right (KL_le_EL M H ℓ ℂ) (laurentBaseChange_le_An (Gam' M H ℓ))
    _ = relrank (An (Gam M H)) (An (Gam' M H ℓ)) := by rw [laurentBaseChange_FF_eq_An]
    _ ≤ ((Gam' M H ℓ).relIndex (Gam M H) : Cardinal) := hC2
    _ = ((ℓ : ℕ) : Cardinal) := by rw [relIndex_Gam'_eq M H ℓ hℓM]

private theorem jqNModC_mem_EL : jqNModC ℂ (M * ℓ) ∈ laurentBaseChange ℂ (FF' M H ℓ) := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  rw [← ModularCurve.map_jqNModC (algebraMap ℚ ℂ) (M * ℓ)]
  refine coeffEmb_mem_laurentBaseChange ℂ ?_
  have h1 : jqNModC ℚ (M * ℓ) ∈ modularFunctionFieldFullC ℚ (M * ℓ) :=
    jqModCd_mem_full ℚ (M * ℓ) (dvd_refl _)
  have h2 := ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * ℓ) h1
  exact qExpFunctionFieldC_mono ℚ (inf_le_right : Gam' M H ℓ ≤ Gamma0 (M * ℓ)) h2

private theorem relrank_C_ge (hℓM : ℓ ∣ M) :
    ((ℓ : ℕ) : Cardinal) ≤
      relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  have h23 := ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC (Gam M H)
    (CohCarrier.translation_mem_GammaH M H) (M * ℓ)
  rw [relIndex_Gamma0_mul_Gam M H ℓ hℓM] at h23
  change ((ℓ : ℕ) : Cardinal) ≤ relrank (An (Gam M H))
    (adjoin ℂ (insert (jqNModC ℂ (M * ℓ)) (anSet (Gam M H)))) at h23
  have hins : adjoin ℂ (insert (jqNModC ℂ (M * ℓ)) (anSet (Gam M H))) ≤
      laurentBaseChange ℂ (FF' M H ℓ) := by
    rw [adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨jqNModC_mem_EL M H ℓ, ?_⟩
    intro x hx
    exact KL_le_EL M H ℓ ℂ (An_Gam_le M H (subset_adjoin ℂ _ hx))
  have hsub : An (Gam M H) ≤ adjoin ℂ (insert (jqNModC ℂ (M * ℓ)) (anSet (Gam M H))) :=
    adjoin.mono ℂ _ _ (Set.subset_insert _ _)
  calc ((ℓ : ℕ) : Cardinal) ≤ relrank (An (Gam M H))
        (adjoin ℂ (insert (jqNModC ℂ (M * ℓ)) (anSet (Gam M H)))) := h23
    _ ≤ relrank (An (Gam M H)) (laurentBaseChange ℂ (FF' M H ℓ)) := relrank_mono_right hsub hins
    _ = relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) := by
          rw [laurentBaseChange_FF_eq_An]

private theorem relfinrank_FF_FF'_of_dvd (hℓM : ℓ ∣ M) :
    relfinrank (FF M H) (FF' M H ℓ) = ℓ := by
  have hC := relrank_C_le M H ℓ hℓM
  have hCge := relrank_C_ge M H ℓ hℓM
  have heq : relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) =
      ((ℓ : ℕ) : Cardinal) := le_antisymm hC hCge
  rw [← relfinrank_KL_EL M H ℓ ℂ, relfinrank_eq_toNat_relrank, heq, Cardinal.toNat_natCast]

end AlphaHDvd

/-- **The `p ∣ M` branch of the `α`-row's degree on `X_H(M)`.** For `p ∣ M` the
relative index `[Γ_H(M) ∩ Γ₀(Mp) : Γ_H(M)]` is just `p`. Verbatim from
`Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd.lean:12-15`. -/
theorem finrankAlong_heckeAlphaHBar_of_dvd (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [NeZero p] (hpM : p ∣ M) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaHBar L M H p) = p := by
  rw [HeckeDegree.finrankAlong_alpha, HeckeDegree.relfinrank_KL_EL]
  exact AlphaHDvd.relfinrank_FF_FF'_of_dvd M H p hpM

/-! ## The `β` row on `X_H(M)` — the pin's `DBetaH` tower

The same tower as the `X₁` module's `BetaOne`, over `Γ_H(M)` instead of `Γ₁(M)`: the
`q ↦ q^ℓ` map does not change the degree over the full field `ℚ(j(q^d) : d ∣ Mℓ)`, so the
β degree is `dd = if ℓ ∣ M then ℓ else ℓ + 1`, the α-H degree, read inside the
base-changed tower. On this side `heckeBetaHBar` is total, so no `Defined` hypothesis is
needed: `ModularCurve.heckeInputsHAlong` supplies `HeckeBetaHDefined`. The tower's shared
half (`F0`, `F0'`, `B0`, `dd`, `jq_mem_F0`, `jqN_mem_B0`, `adjoin_jq_le_F0`,
`relfinrank_F0_F0'`, `relfinrank_ne_zero_of_tower`, `laurentBaseChange_map_qExpand`) is
the engine's public prelude above; everything left in this namespace — the Γ_H fields
`FF`/`FF'`, the side field `BB`, `relfinrank_B0_BB` and the assembly — is `private`. -/

namespace DBetaH

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

private abbrev BB : IntermediateField ℚ (LaurentSeries ℚ) :=
  (FF M H).map (qExpandₐ ℓ)

private theorem F0_le_FF : F0 M ≤ FF M H := by
  rw [show F0 M = modularFunctionFieldFullC ℚ M from (modularFunctionFieldFullC_rat M).symm]
  exact (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M).trans
    (qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 H))

private theorem F0'_le_FF' : F0' M ℓ ≤ FF' M H ℓ := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  rw [show F0' M ℓ = modularFunctionFieldFullC ℚ (M * ℓ) from
    (modularFunctionFieldFullC_rat (M * ℓ)).symm]
  exact (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * ℓ)).trans
    (qExpFunctionFieldC_mono ℚ inf_le_right)

private theorem B0_le_BB : B0 M ℓ ≤ BB M H ℓ := by
  intro x hx
  rw [IntermediateField.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, F0_le_FF M H hy, rfl⟩

private theorem BB_le_FF' (h : HeckeBetaHDefined M H ℓ) : BB M H ℓ ≤ FF' M H ℓ := by
  intro x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h y hy

private theorem relfinrank_adjoin_FF'_ne_zero (t : LaurentSeries ℚ) (ht : t ∈ FF' M H ℓ)
    (htr : Transcendental ℚ t) :
    relfinrank (adjoin ℚ ({t} : Set (LaurentSeries ℚ))) (FF' M H ℓ) ≠ 0 := by
  obtain ⟨x', -, hfd'⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam' M H ℓ)
      (T_mem_Gam' M H ℓ)
  let y : FF' M H ℓ := ⟨t, ht⟩
  have hyt : Transcendental ℚ y := fun h =>
    htr ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF' M H ℓ) (x := y)).mp
      (isAlgebraic_of_subsingleton_ratAlgebra _ h))
  haveI := hfd'
  have hfdy : FiniteDimensional (adjoin ℚ ({y} : Set (FF' M H ℓ))) (FF' M H ℓ) :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x' hyt
  exact relfinrank_adjoin_ne_zero (FF' M H ℓ) y
    (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfdy)

private theorem relfinrank_B0_BB :
    relfinrank (B0 M ℓ) (BB M H ℓ) = relfinrank (F0 M) (FF M H) :=
  IntermediateField.relfinrank_map_map (F0 M) (FF M H) (qExpandₐ ℓ)

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem fieldRange_heckeBetaHBar (h : HeckeBetaHDefined M H ℓ) :
    ((laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))).val.comp
        (heckeBetaHBar L M H ℓ)).fieldRange =
      (laurentBaseChange L (FF M H)).map (qExpandAlg L ℓ) := by
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(y : LaurentSeries L), y.2, ?_⟩
    rw [qExpandAlg_apply, AlgHom.comp_apply, ← coe_heckeBetaHBar M H ℓ h y]
    rfl
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    rw [qExpandAlg_apply, AlgHom.comp_apply, ← coe_heckeBetaHBar M H ℓ h ⟨z, hz⟩]
    rfl

end BaseChange

section Assembly

variable [Fact ℓ.Prime]

private theorem finrankAlong_heckeAlphaHBar_dd (L : Type*) [Field L] [Algebra ℚ L] :
    finrankAlong L (heckeAlphaHBar L M H ℓ) = dd M ℓ := by
  unfold dd
  split_ifs with hℓM
  · exact ModularCurve.finrankAlong_heckeAlphaHBar_of_dvd L M H ℓ hℓM
  · exact ModularCurve.finrankAlong_heckeAlphaHBar L M H hℓM

private theorem relfinrank_FF_FF' (L : Type*) [Field L] [Algebra ℚ L] :
    relfinrank (FF M H) (FF' M H ℓ) = dd M ℓ := by
  unfold dd
  split_ifs with hℓM
  · exact AlphaHDvd.relfinrank_FF_FF'_of_dvd M H ℓ hℓM
  · exact HeckeDegree.relfinrank_FF_FF' M H ℓ hℓM

private theorem relfinrank_F0'_FF'_eq (L : Type*) [Field L] [Algebra ℚ L] :
    relfinrank (F0' M ℓ) (FF' M H ℓ) = relfinrank (F0 M) (FF M H) ∧
      relfinrank (F0 M) (FF M H) ≠ 0 := by
  have t1 := relfinrank_mul_relfinrank (F0_le_FF M H) (FF_le M H ℓ)
  have t2 := relfinrank_mul_relfinrank (full_degeneracy_le (dvd_mul_right M ℓ)) (F0'_le_FF' M H ℓ)
  rw [relfinrank_FF_FF' M H ℓ L] at t1
  rw [relfinrank_F0_F0', ← t1, mul_comm] at t2
  have hd : 0 < dd M ℓ := by
    have := (Fact.out : ℓ.Prime).pos
    unfold dd
    split_ifs <;> omega
  refine ⟨Nat.eq_of_mul_eq_mul_right hd t2, ?_⟩
  have hF0 : relfinrank (adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (FF' M H ℓ) ≠ 0 :=
    relfinrank_adjoin_FF'_ne_zero M H ℓ jq
      ((F0_le_FF M H).trans (FF_le M H ℓ) (jq_mem_F0 M)) transcendental_jq
  have h' := (relfinrank_ne_zero_of_tower (adjoin_jq_le_F0 M)
    ((F0_le_FF M H).trans (FF_le M H ℓ)) hF0).2
  exact (relfinrank_ne_zero_of_tower (F0_le_FF M H) (FF_le M H ℓ) h').1

private theorem relfinrank_BB_FF' (L : Type*) [Field L] [Algebra ℚ L]
    (h : HeckeBetaHDefined M H ℓ) :
    relfinrank (BB M H ℓ) (FF' M H ℓ) = dd M ℓ := by
  obtain ⟨hc, hc0⟩ := relfinrank_F0'_FF'_eq M H ℓ L
  have s1 := relfinrank_mul_relfinrank (B0_le_BB M H ℓ) (BB_le_FF' M H ℓ h)
  have s2 := relfinrank_mul_relfinrank (full_degeneracy_map_le M ℓ) (F0'_le_FF' M H ℓ)
  rw [relfinrank_B0_BB] at s1
  rw [relfinrank_qExpand_full M ℓ, hc, ← s1, mul_comm] at s2
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) s2).symm

private theorem main (L : Type*) [Field L] [Algebra ℚ L] (h : HeckeBetaHDefined M H ℓ) :
    finrankAlong L (heckeBetaHBar L M H ℓ) = dd M ℓ := by
  have e1 := AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange (laurentBaseChange L (FF M H))
    (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) (heckeBetaHBar L M H ℓ)
  have e2 := fieldRange_heckeBetaHBar M H ℓ L h
  have e3 : relfinrank ((laurentBaseChange L (FF M H)).map (qExpandAlg L ℓ))
      (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) = dd M ℓ := by
    have hle2 : BB M H ℓ ≤ xHTopFunctionFieldC ℚ M H (M * ℓ) := BB_le_FF' M H ℓ h
    have hmem : jqN ℓ ∈ BB M H ℓ := B0_le_BB M H ℓ (jqN_mem_B0 M ℓ)
    have hfin : relfinrank (adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
        (xHTopFunctionFieldC ℚ M H (M * ℓ)) ≠ 0 :=
      relfinrank_adjoin_FF'_ne_zero M H ℓ (jqN ℓ)
        (F0'_le_FF' M H ℓ (full_degeneracy_map_le M ℓ (jqN_mem_B0 M ℓ))) (transcendental_jqN ℓ)
    have hR : relfinrank (adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ))) (BB M H ℓ) ≠ 0 := by
      have h := relfinrank_mul_relfinrank
        (adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)) hle2
      rw [← h] at hfin
      exact left_ne_zero_of_mul hfin
    rw [← laurentBaseChange_map_qExpand,
      ModularCurve.relfinrank_laurentBaseChange_eq L hle2 hmem (transcendental_jqN ℓ) hR]
    exact relfinrank_BB_FF' M H ℓ L h
  rw [← e2] at e3
  exact e1.trans e3

end Assembly

end DBetaH

/-- **The degree of the `β`-row on `X_H(M)`.** The `q ↦ q^ℓ` degeneracy map has
`finrankAlong` equal to `ℓ` when `ℓ ∣ M` and `ℓ + 1` otherwise; no `Defined` hypothesis
is needed because on the `H` side `heckeBetaHBar` is total. Verbatim from
`Theorems/Thm_ModularCurve_finrankAlong_heckeBetaHBar.lean:14-16`. -/
theorem finrankAlong_heckeBetaHBar (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaHBar L M H ℓ) =
      if ℓ ∣ M then ℓ else ℓ + 1 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨h, _⟩ := ModularCurve.heckeInputsHAlong L M H ℓ
  exact DBetaH.main M H ℓ L h

end ModularCurve

end
