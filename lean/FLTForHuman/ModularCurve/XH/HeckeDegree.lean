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

  spec-pin: Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaHBar.lean
-/
import FLTForHuman.ModularCurve.XH.Relrank
import FLTForHuman.ModularCurve.XH.FunctionField
import FLTForHuman.ModularCurve.XH.HeckeOperator
import FLTForHuman.ModularCurve.X1.FunctionField
import FLTForHuman.ModularCurve.X1.QExpansionDiv
import FLTForHuman.ModularCurve.RelIndex.LeRelrank
import FLTForHuman.ModularCurve.RelIndex.LeRelIndex
import FLTForHuman.ModularCurve.Degree.LaurentGlue
import FLTForHuman.ModularCurve.Degree.Relfinrank
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.IsCurveOver.FinitenessTransfer
import FLTForHuman.ModularCurve.Gamma0Index

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

end ModularCurve

end
