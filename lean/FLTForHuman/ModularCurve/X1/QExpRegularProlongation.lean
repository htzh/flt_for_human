/-
  The Gauss regular prolongation of the `q`-expansion valuation at `q = 0`:
  `ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC` and its two
  `_residue_div` / `_residue_mul_eq` siblings.

  Proof transcribed from FLT's
  `P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean`
  and its two siblings, which repeat the shared block verbatim (they differ only in the
  `namespace` line and a 7–8-line assembly tail).  Statements verbatim from the matching
  `Theorems/` wrappers.

  Reuse.  The pin's `Coeff` and `Gauss` blocks are already ported — stated for an arbitrary `Γ`,
  hence without the pin's `hT` — in `X1/FunctionFieldResidue.lean`
  (`ModularCurve.QExpDeuring.{ι, ϖ, IsInt, gaussRing, exists_witness, wit, wit_spec, resL,
  resHom, resHom_eq, resHom_algebraMap, algebraMap_mem_gaussRing_iff, resHom_eq_zero_iff,
  coe_algebraMap, exists_frac_form}`), together with `exists_resHom_eq`, which *is* the pin's
  `resF_surjective` argument.  This module adds only what the pin has and the engine does not:
  the `Lam` / `homSpan` / `IsFrac` fractional-form layer (the pin's `Forms` block), the fourth
  conjunct of `exists_frac_form` (that the reduced ratio lies in the residue function field —
  the pin's only consumer of it is `resHom_mem`), and the `resF` / `gaussProlongation`
  assembly.  The pin's `resRange` / `qExpFunctionFieldC_le_resRange` / `resF_surjective` block
  is not ported.

  Not transcribed: the pin's `set_option synthInstance.maxHeartbeats 1600000` (and the
  `400000` bumps on its wrappers).  The file must close at the project's default diagnostic
  bound.

  The three files are one development: their shared block is byte-identical through line 815
  (`diff` shows only the `namespace` lines and the assembly tail), and the two siblings' tails both
  start at 816.  The port transcribes that block once, in the target file's line numbering, so a
  declaration near the end comes from either tail.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq.lean

  spec-pin: Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean
  spec-pin: Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div.lean
  spec-pin: Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq.lean
-/
import FLTForHuman.ModularCurve.X1.FunctionFieldResidue
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.AlgebraicCurve.RegularProlongation
import FLTForHuman.RingTheory.PowerSeries.Saturation

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped Classical MatrixGroups
open IntermediateField HahnSeries PowerSeries

namespace ModularCurve

namespace QExpDeuring

/-! ## The pin's `Forms` block — `Lam Γ κ`, the graded `homSpan`, `IsFrac` -/

section Forms

private def Lam (Γ : Subgroup SL(2, ℤ)) (κ : ℤ) : Set (PowerSeries ℤ) :=
  {p | ∃ f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ, IsIntegralQExp f p}

private theorem zero_mem_Lam (Γ : Subgroup SL(2, ℤ)) (κ : ℤ) : (0 : PowerSeries ℤ) ∈ Lam Γ κ :=
  ⟨0, by rw [FunLike.coe_zero]; exact isIntegralQExp_zero⟩

private theorem one_mem_Lam (Γ : Subgroup SL(2, ℤ)) : (1 : PowerSeries ℤ) ∈ Lam Γ 0 :=
  ⟨1, by rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one⟩

private theorem one_mem_strictPeriods {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

private theorem add_mem_Lam {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {κ : ℤ}
    {p p' : PowerSeries ℤ} (hp : p ∈ Lam Γ κ) (hp' : p' ∈ Lam Γ κ) : p + p' ∈ Lam Γ κ := by
  obtain ⟨f, hf⟩ := hp
  obtain ⟨g, hg⟩ := hp'
  refine ⟨f + g, ?_⟩
  rw [IsIntegralQExp, map_add, hf, hg, FunLike.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods hT)]

private theorem neg_mem_Lam {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {κ : ℤ}
    {p : PowerSeries ℤ} (hp : p ∈ Lam Γ κ) : -p ∈ Lam Γ κ := by
  obtain ⟨f, hf⟩ := hp
  refine ⟨-f, ?_⟩
  rw [IsIntegralQExp, map_neg, hf, FunLike.coe_neg]
  exact (ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods hT) f).symm

private theorem mul_mem_Lam {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {κ μ : ℤ}
    {p p' : PowerSeries ℤ} (hp : p ∈ Lam Γ κ) (hp' : p' ∈ Lam Γ μ) :
    p * p' ∈ Lam Γ (κ + μ) := by
  obtain ⟨f, hf⟩ := hp
  obtain ⟨g, hg⟩ := hp'
  refine ⟨f.mul g, ?_⟩
  rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
  exact (ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods hT) f g).symm

private theorem Lam_saturated {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {κ : ℤ} (n : ℤ)
    (p : PowerSeries ℤ) (hn : n ≠ 0) (h : n • p ∈ Lam Γ κ) : p ∈ Lam Γ κ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨((n : ℂ)⁻¹) • f, ?_⟩
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [IsIntegralQExp, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods hT), ← hf, map_zsmul,
    ← Int.cast_smul_eq_zsmul ℂ n, smul_smul, inv_mul_cancel₀ hn', one_smul]

private def LamSub {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) (κ : ℤ) :
    AddSubgroup (PowerSeries ℤ) where
  carrier := Lam Γ κ
  zero_mem' := zero_mem_Lam Γ κ
  add_mem' := fun hp hp' => add_mem_Lam hT hp hp'
  neg_mem' := fun hp => neg_mem_Lam hT hp

private def homSpan (Γ : Subgroup SL(2, ℤ)) (K : Type*) [Field K] (κ : ℤ) :
    Submodule K (LaurentSeries K) :=
  Submodule.span K (intSeriesC K '' Lam Γ κ)

private theorem intSeriesC_mem_homSpan (Γ : Subgroup SL(2, ℤ)) (K : Type*) [Field K] {κ : ℤ}
    {p : PowerSeries ℤ} (hp : p ∈ Lam Γ κ) : intSeriesC K p ∈ homSpan Γ K κ :=
  Submodule.subset_span ⟨p, hp, rfl⟩

private theorem mul_intSeriesC_mem_homSpan {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
    {K : Type*} [Field K] {κ μ : ℤ}
    {U : LaurentSeries K} (hU : U ∈ homSpan Γ K κ) {n : PowerSeries ℤ} (hn : n ∈ Lam Γ μ) :
    U * intSeriesC K n ∈ homSpan Γ K (κ + μ) := by
  induction hU using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    rw [← intSeriesC_mul]
    exact intSeriesC_mem_homSpan Γ K (mul_mem_Lam hT hp hn)
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← HahnSeries.C_mul_eq_smul, mul_assoc, HahnSeries.C_mul_eq_smul]
    exact Submodule.smul_mem _ _ hx

private theorem mul_mem_homSpan {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
    {K : Type*} [Field K] {κ μ : ℤ}
    {U V : LaurentSeries K} (hU : U ∈ homSpan Γ K κ) (hV : V ∈ homSpan Γ K μ) :
    U * V ∈ homSpan Γ K (κ + μ) := by
  induction hV using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact mul_intSeriesC_mem_homSpan hT hU hp
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul]
    exact Submodule.smul_mem _ _ hx

private theorem algebraMap_mem_homSpan (Γ : Subgroup SL(2, ℤ)) (K : Type*) [Field K] (c : K) :
    algebraMap K (LaurentSeries K) c ∈ homSpan Γ K 0 := by
  have h1 : algebraMap K (LaurentSeries K) c = c • intSeriesC K 1 := by
    rw [intSeriesC_one, ← HahnSeries.C_mul_eq_smul, mul_one, HahnSeries.C_apply,
      algebraMap_laurentSeries_eq_single]
  rw [h1]
  exact Submodule.smul_mem _ _ (intSeriesC_mem_homSpan Γ K (one_mem_Lam Γ))

private def IsFrac (Γ : Subgroup SL(2, ℤ)) (K : Type*) [Field K] (x : LaurentSeries K) : Prop :=
  ∃ (κ : ℤ) (U : LaurentSeries K) (n : PowerSeries ℤ), U ∈ homSpan Γ K κ ∧ n ∈ Lam Γ κ ∧
    intSeriesC K n ≠ 0 ∧ x * intSeriesC K n = U

private theorem isFrac_of_mem_intFormRatiosC (Γ : Subgroup SL(2, ℤ)) (K : Type*) [Field K]
    {x : LaurentSeries K} (hx : x ∈ intFormRatiosC K Γ) : IsFrac Γ K x := by
  obtain ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  exact ⟨κ, intSeriesC K pf, pg, intSeriesC_mem_homSpan Γ K ⟨f, hf⟩, ⟨g, hg⟩, hg0,
    div_mul_cancel₀ _ hg0⟩

private theorem isFrac_algebraMap (Γ : Subgroup SL(2, ℤ)) (K : Type*) [Field K] (c : K) :
    IsFrac Γ K (algebraMap K (LaurentSeries K) c) :=
  ⟨0, algebraMap K (LaurentSeries K) c, 1, algebraMap_mem_homSpan Γ K c, one_mem_Lam Γ,
    by rw [intSeriesC_one]; exact one_ne_zero, by rw [intSeriesC_one, mul_one]⟩

private theorem IsFrac.add {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) (K : Type*) [Field K]
    {x y : LaurentSeries K} (hx : IsFrac Γ K x) (hy : IsFrac Γ K y) :
    IsFrac Γ K (x + y) := by
  obtain ⟨κ, U, n, hU, hn, hn0, hxU⟩ := hx
  obtain ⟨μ, U', n', hU', hn', hn0', hyU⟩ := hy
  refine ⟨κ + μ, U * intSeriesC K n' + U' * intSeriesC K n, n * n', ?_,
    mul_mem_Lam hT hn hn', ?_, ?_⟩
  · refine Submodule.add_mem _ (mul_intSeriesC_mem_homSpan hT hU hn') ?_
    rw [add_comm κ μ]
    exact mul_intSeriesC_mem_homSpan hT hU' hn
  · rw [intSeriesC_mul]; exact mul_ne_zero hn0 hn0'
  · rw [intSeriesC_mul, add_mul, ← hxU, ← hyU]; ring

private theorem IsFrac.mul {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) (K : Type*) [Field K]
    {x y : LaurentSeries K} (hx : IsFrac Γ K x) (hy : IsFrac Γ K y) :
    IsFrac Γ K (x * y) := by
  obtain ⟨κ, U, n, hU, hn, hn0, hxU⟩ := hx
  obtain ⟨μ, U', n', hU', hn', hn0', hyU⟩ := hy
  refine ⟨κ + μ, U * U', n * n', mul_mem_homSpan hT hU hU', mul_mem_Lam hT hn hn', ?_, ?_⟩
  · rw [intSeriesC_mul]; exact mul_ne_zero hn0 hn0'
  · rw [intSeriesC_mul, ← hxU, ← hyU]; ring

private theorem isFrac_of_mem_adjoin {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
    (K : Type*) [Field K] {x : LaurentSeries K}
    (hx : x ∈ Algebra.adjoin K (intFormRatiosC K Γ)) : IsFrac Γ K x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact isFrac_of_mem_intFormRatiosC Γ K hx
  | algebraMap c => exact isFrac_algebraMap Γ K c
  | add x y _ _ hx hy => exact hx.add hT K hy
  | mul x y _ _ hx hy => exact hx.mul hT K hy

end Forms

/-! ## The pin's `BaseChange` block — the inclusion `FF ≤ qExpFunctionFieldC L Γ` -/

section BaseChange

variable {L : Type*} [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ))

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

private theorem laurentBaseChange_le : FF ≤ qExpFunctionFieldC L Γ := by
  change adjoin L _ ≤ adjoin L _
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ) := hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (intFormRatiosC L Γ)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (intFormRatiosC L Γ)).algebraMap_mem _
  · obtain ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hz
    have hgL : intSeriesC L pg ≠ 0 := by
      have h : coeffEmb L (intSeriesC ℚ pg) ≠ 0 :=
        (map_ne_zero_iff (coeffEmb L) (coeffEmb_injective L)).mpr hg0
      rwa [coeffEmb_intSeriesC] at h
    have hcoe : coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) =
        intSeriesC L pf / intSeriesC L pg := by
      rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
    rw [hcoe]
    exact IntermediateField.subset_adjoin L _ ⟨κ, f, g, pf, pg, hf, hg, hgL, rfl⟩

private theorem mem_qExp_of_mem_FF {x : LaurentSeries L} (hx : x ∈ FF) :
    x ∈ qExpFunctionFieldC L Γ :=
  (SetLike.le_def.mp (laurentBaseChange_le Γ)) hx

end BaseChange

/-! ## The pin's `FracForm` block — primitive forms and the reduced ratio -/

section FracForm

variable {Γ : Subgroup SL(2, ℤ)}
variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A

private def ofPS (K : Type*) [Field K] : PowerSeries K →ₗ[K] LaurentSeries K where
  toFun := HahnSeries.ofPowerSeries ℤ K
  map_add' := map_add _
  map_smul' := fun c x => by
    rw [PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
      RingHom.id_apply]

private theorem ofPS_apply (K : Type*) [Field K] (x : PowerSeries K) :
    ofPS K x = HahnSeries.ofPowerSeries ℤ K x :=
  rfl

private theorem intSeriesC_eq_ofPS (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K p = ofPS K (p.map (Int.castRingHom K)) := rfl

private theorem homSpan_eq_map (Γ : Subgroup SL(2, ℤ)) (K : Type*) [Field K] (κ : ℤ) :
    homSpan Γ K κ =
      (Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) '' Lam Γ κ)).map
        (ofPS K) := by
  rw [homSpan, Submodule.map_span, ← Set.image_comp]
  rfl

private theorem div_mem_qExpFunctionFieldC_of_mem_span (Γ : Subgroup SL(2, ℤ)) (K : Type*) [Field K]
    {μ : ℤ} {X Y : PowerSeries K}
    (hX : X ∈ Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) '' Lam Γ μ))
    (hY : Y ∈ Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) '' Lam Γ μ))
    (hY0 : Y ≠ 0) :
    ofPS K X / ofPS K Y ∈ qExpFunctionFieldC K Γ := by
  classical
  obtain ⟨p₀, hp₀, hp₀0⟩ : ∃ p₀ ∈ Lam Γ μ, intSeriesC K p₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hY0
    have hbot : Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) ''
        Lam Γ μ) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨p, hp, rfl⟩
      have h := hall p hp
      rw [intSeriesC_eq_ofPS, ofPS_apply] at h
      exact HahnSeries.ofPowerSeries_injective (by rw [h, map_zero])
    rw [hbot] at hY
    exact (Submodule.mem_bot K).mp hY
  obtain ⟨g₀, hg₀⟩ := hp₀
  have key : ∀ Z ∈ Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) ''
      Lam Γ μ), ofPS K Z * (intSeriesC K p₀)⁻¹ ∈ qExpFunctionFieldC K Γ := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, ⟨f, hf⟩, rfl⟩ := hx
      rw [← intSeriesC_eq_ofPS, ← div_eq_mul_inv]
      exact div_mem_qExpFunctionFieldC f g₀ hf hg₀ hp₀0
    | zero => rw [map_zero, zero_mul]; exact IntermediateField.zero_mem _
    | add x y _ _ hx hy => rw [map_add, add_mul]; exact IntermediateField.add_mem _ hx hy
    | smul a x _ hx =>
      rw [PowerSeries.smul_eq_C_mul, ofPS_apply, map_mul, HahnSeries.ofPowerSeries_C, ← ofPS_apply,
        mul_assoc, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]
      exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ a) hx
  have hXY : ofPS K X / ofPS K Y =
      (ofPS K X * (intSeriesC K p₀)⁻¹) / (ofPS K Y * (intSeriesC K p₀)⁻¹) := by
    rw [mul_div_mul_right _ _ (inv_ne_zero hp₀0)]
  rw [hXY]
  exact IntermediateField.div_mem _ (key X hX) (key Y hY)

private theorem exists_primitive_of_mem_homSpan (hT : ModularGroup.T ∈ Γ)
    {μ : ℤ} {V : LaurentSeries L} (hV : V ∈ homSpan Γ L μ) (hV0 : V ≠ 0) :
    ∃ (c : L) (u₀ : LaurentSeries A), c ≠ 0 ∧ V = algebraMap L (LaurentSeries L) c * ι A u₀ ∧
      ϖ A u₀ ≠ 0 ∧ ∃ ub : PowerSeries kk, ϖ A u₀ = ofPS kk ub ∧
        ub ∈ Submodule.span kk ((fun p : PowerSeries ℤ => p.map (Int.castRingHom kk)) ''
          Lam Γ μ) := by
  rw [homSpan_eq_map] at hV
  obtain ⟨V₀, hV₀, rfl⟩ := hV
  have hV₀0 : V₀ ≠ 0 := by rintro rfl; exact hV0 (map_zero _)
  obtain ⟨c, u, hc0, hVu, hu0, humem⟩ :=
    PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated A (LamSub hT μ)
      (fun n p hn h => Lam_saturated hT n p hn h)
      (V := V₀) hV₀ hV₀0
  refine ⟨c, HahnSeries.ofPowerSeries ℤ A u, hc0, ?_, ?_, u.map (IsLocalRing.residue A), ?_, humem⟩
  · rw [ofPS_apply, hVu, map_mul, HahnSeries.ofPowerSeries_C, coeffMap_ofPowerSeries,
      HahnSeries.C_apply, algebraMap_laurentSeries_eq_single]
  · rw [coeffMap_ofPowerSeries]
    exact fun h => hu0 (HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]))
  · rw [coeffMap_ofPowerSeries]; rfl

private theorem exists_frac_form_mem (hT : ModularGroup.T ∈ Γ)
    (f : FF) (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ u₀ w₀ : LaurentSeries A, ϖ A u₀ ≠ 0 ∧ ϖ A w₀ ≠ 0 ∧
      (f : LaurentSeries L) * ι A w₀ = algebraMap L (LaurentSeries L) c * ι A u₀ ∧
      ϖ A u₀ / ϖ A w₀ ∈ qExpFunctionFieldC kk Γ := by
  have hfF : (f : LaurentSeries L) ∈ qExpFunctionFieldC L Γ := mem_qExp_of_mem_FF Γ f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp hfF
  have hf0' : (f : LaurentSeries L) ≠ 0 := fun h => hf (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, div_zero])
  obtain ⟨κ, U, n, hU, hn, hn0, hrU⟩ := isFrac_of_mem_adjoin hT L hr
  obtain ⟨μ, U', n', hU', hn', hn0', hsU⟩ := isFrac_of_mem_adjoin hT L hs
  set V : LaurentSeries L := U * intSeriesC L n' with hVdef
  set W : LaurentSeries L := U' * intSeriesC L n with hWdef
  have hVmem : V ∈ homSpan Γ L (κ + μ) := mul_intSeriesC_mem_homSpan hT hU hn'
  have hWmem : W ∈ homSpan Γ L (κ + μ) := by
    rw [add_comm]; exact mul_intSeriesC_mem_homSpan hT hU' hn
  have hW0 : W ≠ 0 := by
    rw [hWdef, ← hsU]; exact mul_ne_zero (mul_ne_zero hs0 hn0') hn0
  have hfW : (f : LaurentSeries L) * W = V := by
    rw [hWdef, hVdef, ← hsU, ← hrU, hrs]
    field_simp
  have hV0 : V ≠ 0 := by rw [← hfW]; exact mul_ne_zero hf0' hW0
  obtain ⟨cV, u₀, hcV, hVu, hu0, ub, hub, hubmem⟩ := exists_primitive_of_mem_homSpan A hT hVmem hV0
  obtain ⟨cW, w₀, hcW, hWw, hw0, wb, hwb, hwbmem⟩ := exists_primitive_of_mem_homSpan A hT hWmem hW0
  refine ⟨cV / cW, div_ne_zero hcV hcW, u₀, w₀, hu0, hw0, ?_, ?_⟩
  · have hcW' : algebraMap L (LaurentSeries L) cW ≠ 0 := (map_ne_zero _).mpr hcW
    have h1 : (f : LaurentSeries L) * (algebraMap L (LaurentSeries L) cW * ι A w₀) =
        algebraMap L (LaurentSeries L) cV * ι A u₀ := by rw [← hWw, hfW, hVu]
    rw [map_div₀]
    field_simp
    linear_combination h1
  · rw [hub, hwb]
    have hwb0 : wb ≠ 0 := by rintro rfl; exact hw0 (by rw [hwb, map_zero])
    exact div_mem_qExpFunctionFieldC_of_mem_span Γ kk hubmem hwbmem hwb0

end FracForm

/-! ## The Gauss adapters — `resHom` into the residue function field -/

section Gauss

variable {Γ : Subgroup SL(2, ℤ)}
variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A

private theorem resHom_apply (f : gaussRing A Γ) : resHom A Γ f = resL A Γ f := rfl

private theorem ι_mem_gaussRing {y : LaurentSeries A} (hyF : ι A y ∈ FF) :
    (⟨ι A y, hyF⟩ : FF) ∈ gaussRing A Γ :=
  ⟨y, 1, by simp, by simp⟩

private theorem resHom_ι {y : LaurentSeries A} (hyF : ι A y ∈ FF) :
    resHom A Γ ⟨⟨ι A y, hyF⟩, ι_mem_gaussRing A hyF⟩ = ϖ A y := by
  rw [resHom_eq A Γ (x := y) (y := 1) (by simp) (by simp)]; simp

private theorem inv_mem_gaussRing_of_resHom_ne_zero (f : gaussRing A Γ)
    (h0 : resHom A Γ f ≠ 0) : ((f : FF)⁻¹ : FF) ∈ gaussRing A Γ := by
  obtain ⟨hy, h⟩ := wit_spec A Γ f
  rw [resHom_eq A Γ hy h] at h0
  have hx : ϖ A (wit A Γ f).1 ≠ 0 := fun hx => h0 (by rw [hx, zero_div])
  refine ⟨(wit A Γ f).2, (wit A Γ f).1, hx, ?_⟩
  rw [IntermediateField.coe_inv]
  exact IsInt.inv_of (A := A) hx h

private theorem ker_resHom : RingHom.ker (resHom A Γ) = IsLocalRing.maximalIdeal (gaussRing A Γ) := by
  ext f
  rw [RingHom.mem_ker, resHom_eq_zero_iff]

private theorem coe_smul' (c : L) (f : FF) :
    ((c • f : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c * (f : LaurentSeries L) := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]

private theorem exists_smul_mem_gaussRing (hT : ModularGroup.T ∈ Γ)
    (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A Γ, resHom A Γ ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h, -⟩ := exists_frac_form_mem A hT f hf
  have key : ((c⁻¹ • f : FF) : LaurentSeries L) * ι A y₀ = ι A x₀ := by
    rw [coe_smul', mul_assoc, h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  have hmem : c⁻¹ • f ∈ gaussRing A Γ := (mem_gaussRing_iff A Γ _).mpr ⟨x₀, y₀, hy₀, key⟩
  refine ⟨c⁻¹, hmem, ?_⟩
  rw [Ne, resHom_eq A Γ (f := ⟨_, hmem⟩) hy₀ key]
  exact div_ne_zero hx₀ hy₀

private theorem resHom_mem (hT : ModularGroup.T ∈ Γ)
    (f : gaussRing A Γ) : resHom A Γ f ∈ qExpFunctionFieldC kk Γ := by
  by_cases hf : (f : FF) = 0
  · have : f = 0 := Subtype.ext hf
    rw [this, map_zero]
    exact IntermediateField.zero_mem _
  obtain ⟨hy, h⟩ := wit_spec A Γ f
  obtain ⟨c, hc0, u₀, w₀, hu₀, hw₀, hfrac, hmem⟩ := exists_frac_form_mem A hT (f : FF) hf
  rw [resHom_eq A Γ hy h]
  have caseA : c ∈ A → ϖ A (wit A Γ f).1 / ϖ A (wit A Γ f).2 ∈ qExpFunctionFieldC kk Γ := by
    intro hc
    have hxw : (wit A Γ f).1 * w₀ = HahnSeries.C ⟨c, hc⟩ * u₀ * (wit A Γ f).2 := by
      apply ι_injective A
      rw [map_mul, map_mul, map_mul, ι_C, ← h, ← hfrac, mul_right_comm]
    have hred := congrArg (ϖ A) hxw
    rw [map_mul, map_mul, map_mul, ϖ_C] at hred
    have hxy : ϖ A (wit A Γ f).1 / ϖ A (wit A Γ f).2 =
        algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A ⟨c, hc⟩) * (ϖ A u₀ / ϖ A w₀) := by
      rw [← mul_div_assoc, div_eq_div_iff hy hw₀]
      exact hred
    rw [hxy]
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _) hmem
  rcases A.mem_or_inv_mem c with hc | hc
  · exact caseA hc
  · by_cases hu : IsUnit (⟨c⁻¹, hc⟩ : A)
    · apply caseA
      obtain ⟨u, hu⟩ := hu
      have h1 : ((↑(u⁻¹ : Aˣ) : A) : L) * c⁻¹ = 1 := by
        have := congrArg (fun a : A => (a : L)) u.inv_val
        simpa [hu] using this
      rw [mul_inv_eq_one₀ hc0] at h1
      rw [← h1]; exact SetLike.coe_mem _
    · exfalso
      have hcm : (⟨c⁻¹, hc⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
        (IsLocalRing.mem_maximalIdeal _).mpr hu
      have hxw : HahnSeries.C ⟨c⁻¹, hc⟩ * ((wit A Γ f).1 * w₀) = u₀ * (wit A Γ f).2 := by
        apply ι_injective A
        have e1 : ι A (HahnSeries.C ⟨c⁻¹, hc⟩ * ((wit A Γ f).1 * w₀)) =
            algebraMap L (LaurentSeries L) c⁻¹ *
              ((((f : FF) : LaurentSeries L) * ι A w₀) * ι A (wit A Γ f).2) := by
          rw [map_mul, map_mul, ι_C, ← h]; ring
        rw [e1, hfrac, map_mul, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0,
          map_one, one_mul]
      have hred := congrArg (ϖ A) hxw
      have hzero : ϖ A (HahnSeries.C ⟨c⁻¹, hc⟩) = 0 := by
        rw [ϖ_C, (IsLocalRing.residue_eq_zero_iff _).mpr hcm, map_zero]
      rw [map_mul, hzero, zero_mul, map_mul] at hred
      exact mul_ne_zero hu₀ hy hred.symm

private def resF (hT : ModularGroup.T ∈ Γ) :
    gaussRing A Γ →+* qExpFunctionFieldC kk Γ :=
  (resHom A Γ).codRestrict (qExpFunctionFieldC kk Γ).toSubring fun f => resHom_mem A hT f

private theorem coe_resF (hT : ModularGroup.T ∈ Γ) (f : gaussRing A Γ) :
    ((resF A hT f : qExpFunctionFieldC kk Γ) : LaurentSeries kk) = resHom A Γ f :=
  rfl

private theorem resF_ne_zero_iff (hT : ModularGroup.T ∈ Γ)
    (f : gaussRing A Γ) : resF A hT f ≠ 0 ↔ resHom A Γ f ≠ 0 := by
  rw [Ne, Ne, ← coe_resF A hT, ZeroMemClass.coe_eq_zero]

private theorem ker_resF (hT : ModularGroup.T ∈ Γ) :
    RingHom.ker (resF A hT) = IsLocalRing.maximalIdeal (gaussRing A Γ) := by
  ext f
  rw [RingHom.mem_ker, ← resHom_eq_zero_iff, ← coe_resF A hT, ZeroMemClass.coe_eq_zero]

private theorem resF_surjective (hT : ModularGroup.T ∈ Γ) :
    Function.Surjective (resF A hT) := by
  intro z
  obtain ⟨f, hf⟩ := exists_resHom_eq A Γ z.2
  exact ⟨f, Subtype.ext hf⟩

private theorem resF_algebraMap (hT : ModularGroup.T ∈ Γ) (a : A)
    (h : algebraMap L FF a ∈ gaussRing A Γ) :
    resF A hT ⟨algebraMap L FF a, h⟩ =
      algebraMap kk (qExpFunctionFieldC kk Γ) (IsLocalRing.residue A a) :=
  Subtype.ext (by rw [coe_resF A hT, resHom_algebraMap]; rfl)

private theorem exists_smul_mem_resF (hT : ModularGroup.T ∈ Γ)
    (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A Γ, resF A hT ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A hT f hf
  exact ⟨c, h, (resF_ne_zero_iff A hT _).mpr hne⟩

end Gauss

/-! ## The three assembly tails -/

section Assembly

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A

private abbrev gaussProlongation :
    AlgebraicCurve.RegularProlongation A FF (qExpFunctionFieldC kk Γ) where
  integers := gaussRing A Γ
  residue := resF A hT
  algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A Γ
  residue_surjective := resF_surjective A hT
  ker_residue := ker_resF A hT
  residue_algebraMap a := resF_algebraMap A hT a _
  exists_smul_mem := exists_smul_mem_resF A hT

private theorem mem_integers_gaussProlongation_iff (f : FF) :
    f ∈ (gaussProlongation hT A).integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x :=
  Iff.rfl

private theorem residue_gaussProlongation (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF) :
    ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ (gaussProlongation hT A).integers,
      (((gaussProlongation hT A).residue ⟨_, hO⟩ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) =
        coeffMap (IsLocalRing.residue A) y :=
  ⟨ι_mem_gaussRing A hy, by
    change ((resF A hT _ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) = _
    rw [coe_resF]
    exact resHom_ι A hy⟩

private theorem residue_gaussProlongation_mul (f : (gaussProlongation hT A).integers)
    (x y : LaurentSeries A) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x) :
    (((gaussProlongation hT A).residue f : qExpFunctionFieldC kk Γ) : LaurentSeries kk) *
        coeffMap (IsLocalRing.residue A) y = coeffMap (IsLocalRing.residue A) x := by
  change ((resF A hT f : qExpFunctionFieldC kk Γ) : LaurentSeries kk) * ϖ A y = ϖ A x
  rw [coe_resF, resHom_eq A Γ (f := f) hy h, div_mul_cancel₀ _ hy]

private theorem residue_gaussProlongation_mul_eq (f : FF)
    (hf : f ∈ (gaussProlongation hT A).integers) (x y : LaurentSeries A)
    (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (h : (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x) :
    (((gaussProlongation hT A).residue ⟨f, hf⟩ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) *
        coeffMap (IsLocalRing.residue A) y = coeffMap (IsLocalRing.residue A) x := by
  change ((resF A hT ⟨f, hf⟩ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) * _ = _
  rw [coe_resF, resHom_eq A Γ (f := ⟨f, hf⟩) (x := x) (y := y) hy h]
  exact div_mul_cancel₀ _ hy

include hT in
private theorem main :
    ∃ R : AlgebraicCurve.RegularProlongation A FF (qExpFunctionFieldC kk Γ),
      (∀ f : FF, f ∈ R.integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) =
            coeffMap (IsLocalRing.residue A) y :=
  ⟨gaussProlongation hT A, mem_integers_gaussProlongation_iff hT A, residue_gaussProlongation hT A⟩

end Assembly

end QExpDeuring

/-! ## The three headlines (the `Theorems/` wrappers' statements, verbatim) -/

open QExpDeuring in
theorem exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) :
    ∃ R : AlgebraicCurve.RegularProlongation A
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      (∀ f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
        f ∈ R.integers ↔
          ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            (f : LaurentSeries L) * ModularCurve.coeffMap A.subtype y =
              ModularCurve.coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y :=
  main hT A

open QExpDeuring in
theorem exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) :
    ∃ R : AlgebraicCurve.RegularProlongation A
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      (∀ f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
        f ∈ R.integers ↔
          ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            (f : LaurentSeries L) * ModularCurve.coeffMap A.subtype y =
              ModularCurve.coeffMap A.subtype x) ∧
      (∀ (f : R.integers) (x y : LaurentSeries A),
        ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 →
        ((f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) :
            LaurentSeries L) *
            ModularCurve.coeffMap A.subtype y = ModularCurve.coeffMap A.subtype x →
        ((R.residue f : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
            LaurentSeries (IsLocalRing.ResidueField A)) *
            ModularCurve.coeffMap (IsLocalRing.residue A) y =
          ModularCurve.coeffMap (IsLocalRing.residue A) x) ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y :=
  ⟨gaussProlongation hT A, mem_integers_gaussProlongation_iff hT A,
    residue_gaussProlongation_mul hT A, residue_gaussProlongation hT A⟩

open QExpDeuring in
theorem exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) :
    ∃ R : AlgebraicCurve.RegularProlongation A
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      (∀ f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
        f ∈ R.integers ↔
          ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            (f : LaurentSeries L) * ModularCurve.coeffMap A.subtype y =
              ModularCurve.coeffMap A.subtype x) ∧
      (∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y) ∧
      (∀ (f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (hf : f ∈ R.integers) (x y : LaurentSeries A),
        ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 →
        (f : LaurentSeries L) * ModularCurve.coeffMap A.subtype y = ModularCurve.coeffMap A.subtype x →
        ((R.residue ⟨f, hf⟩ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
            LaurentSeries (IsLocalRing.ResidueField A)) *
            ModularCurve.coeffMap (IsLocalRing.residue A) y =
          ModularCurve.coeffMap (IsLocalRing.residue A) x) :=
  ⟨gaussProlongation hT A, mem_integers_gaussProlongation_iff hT A,
    residue_gaussProlongation hT A, residue_gaussProlongation_mul_eq hT A⟩

end ModularCurve

end
