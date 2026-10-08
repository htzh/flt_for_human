/-
  The `JOneES` finrank/index bound
  (`ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index`).

  Proof transcribed from FLT's
  `P2M/Sol/S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean`
  (pin `aa2d8b3`), statement verbatim from
  `Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean`.

  The promoted `ModularCurve.JOneES*` block of `ModularCurve/X1/FunctionField.lean`
  (`JOneESAlg`/`JOneESLevelOne`/`JOneESNorm`/`JOneESRat`) is imported, not
  re-transcribed: the shared `linearIndependent_map`,
  `finiteDimensional_of_forall_aeval_eq_zero`, the `Cos`-indexed norm engine, the
  `intFormRatiosC` closure and `mem_qExpFunctionFieldC_iff` all come from there.

  What is genuinely new in the pin's file is the *discriminant* generator
  `wq = q(Δ)/q(E₄³)` (the promoted engine is the `xq = q(E₆²)/q(E₄³)` variant, a
  different generator), its `q(Δ)`-monomial span, the `wq`-form rational relation
  `exists_rat_relation`, the `finrank_adjoin_wq_le` bound, and the relative-degree
  base-change tail `FIdxBC`. Those are transcribed below at the pin's names.

  The pin's own anonymous `Fintype (Cos Γ)` instance is re-declared here (the port's
  is `private` and unimportable); `FIdxNorm.Cos` is a thin alias for the promoted
  `JOneES.JOneESNorm.Cos` so the re-hosted statements spell the pin's `FIdxNorm.Cos`
  verbatim.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean
-/
import FLTForHuman.ModularCurve.X1.FunctionField
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularCurve.Degree.PhiDegree
import FLTForHuman.ModularCurve.Degree.Relfinrank

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

-- The pin's own scaffolding: without this, instance search picks the global
-- `DivisionRing.toRatAlgebra` for `Algebra ℚ ↥(qExpFunctionFieldC ℚ Γ)` while
-- `FIdxAlg`'s generic lemma uses `IntermediateField.algebra'`, and the two
-- `Module.finrank` carriers are not defeq (`...le_index.lean:18`).
attribute [-instance] DivisionRing.toRatAlgebra

noncomputable section

open HahnSeries Polynomial
open scoped MatrixGroups ModularForm Polynomial

namespace ModularCurve

/-! ## `FIdxAlg` — the two algebra lemmas the pin adds to the promoted block -/

namespace FIdxAlg

section A3

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The bounded-degree criterion, in the `finrank` form the pin's bound uses. -/
theorem finrank_le_of_forall_aeval_eq_zero [PerfectField K] (D : ℕ)
    (h : ∀ y : F, ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ D ∧ aeval y p = 0) :
    Module.finrank K F ≤ D := by
  haveI : FiniteDimensional K F :=
    JOneES.JOneESAlg.finiteDimensional_of_forall_aeval_eq_zero D h
  haveI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  haveI : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K F
  have hdeg : (minpoly K α).natDegree = Module.finrank K F :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα
  obtain ⟨p, hp0, hpD, hpy⟩ := h α
  have hle : (minpoly K α).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd (minpoly.dvd K _ hpy) hp0
  rw [← hdeg]
  exact hle.trans hpD

end A3

section A4

variable {K A : Type*} [Field K] [Field A] [Algebra K A]

theorem adjoin_simple_eq_comap (E : IntermediateField K A) (x : E) :
    IntermediateField.adjoin K ({x} : Set E) =
      (IntermediateField.adjoin K ({(x : A)} : Set A)).comap (IntermediateField.val E) := by
  apply IntermediateField.lift_injective
  erw [IntermediateField.lift_adjoin_simple]
  change _ = ((IntermediateField.adjoin K ({(x : A)} : Set A)).comap E.val).map E.val
  rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left.mpr]
  exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr x.2)

theorem finrank_adjoin_simple_eq_relfinrank (E : IntermediateField K A) (x : E) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set E)) E =
      IntermediateField.relfinrank (IntermediateField.adjoin K ({(x : A)} : Set A)) E := by
  rw [adjoin_simple_eq_comap, IntermediateField.finrank_comap, IntermediateField.fieldRange_val]

end A4

end FIdxAlg

/-! ## `FIdxLevelOne` — the `q(Δ)`-monomial span -/

namespace FIdxLevelOne

open ModularForm UpperHalfPlane EisensteinSeries
open scoped MatrixGroups

noncomputable abbrev q4 : PowerSeries ℂ := JOneES.JOneESLevelOne.q4

noncomputable abbrev qΔ : PowerSeries ℂ :=
  qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)

noncomputable def monomialSpan (m : ℕ) : Submodule ℂ (PowerSeries ℂ) :=
  Submodule.span ℂ (Set.range fun b : Fin (m + 1) => q4 ^ (3 * (m - b)) * qΔ ^ (b : ℕ))

theorem monomial_mem (m : ℕ) (b : ℕ) (hb : b ≤ m) :
    q4 ^ (3 * (m - b)) * qΔ ^ b ∈ monomialSpan m :=
  Submodule.subset_span ⟨⟨b, Nat.lt_succ_of_le hb⟩, rfl⟩

theorem q4_coeff_zero : PowerSeries.coeff 0 q4 = 1 := JOneES.JOneESLevelOne.q4_coeff_zero

theorem qExpansion_mem_monomialSpan (m : ℕ) :
    ∀ (k : ℤ) (hk : k = 12 * (m : ℤ)) (h : ModularForm 𝒮ℒ k),
      qExpansion 1 (h : ℍ → ℂ) ∈ monomialSpan m := by
  induction m with
  | zero =>
    intro k hk h
    simp only [Nat.cast_zero, mul_zero] at hk
    subst hk
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const h
    have hh : h = c • (1 : ModularForm 𝒮ℒ 0) := by
      ext z
      rw [hc, smul_apply]
      simp
    rw [hh, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_one]
    refine Submodule.smul_mem _ _ ?_
    have := monomial_mem 0 0 le_rfl
    simpa using this
  | succ m ih =>
    intro k hk h
    set a₀ : ℂ := PowerSeries.coeff 0 (qExpansion 1 (h : ℍ → ℂ)) with ha₀
    let P : ModularForm 𝒮ℒ k := (E₄.pow (3 * (m + 1))).mcast (by rw [hk]; push_cast; ring)
    have hP : qExpansion 1 (P : ℍ → ℂ) = q4 ^ (3 * (m + 1)) := by
      simp only [P, ModularForm.qExpansion_mcast,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    let g : ModularForm 𝒮ℒ k := h - a₀ • P
    have hg : qExpansion 1 (g : ℍ → ℂ) =
        qExpansion 1 (h : ℍ → ℂ) - a₀ • q4 ^ (3 * (m + 1)) := by
      simp only [g]
      rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, FunLike.coe_smul,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hP]
    have hg0 : PowerSeries.coeff 0 (qExpansion 1 (g : ℍ → ℂ)) = 0 := by
      have h4 : PowerSeries.coeff 0 (q4 ^ (3 * (m + 1))) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, q4_coeff_zero, one_pow]
      rw [hg, map_sub, map_smul, h4, smul_eq_mul, mul_one, ha₀, sub_self]

    have hΔ := ModularForm.qExpansion_eq_qExpansion_discriminant_mul g hg0
    have hk' : k - 12 = 12 * (m : ℤ) := by rw [hk]; push_cast; ring
    have hIH := ih (k - 12) hk' (CuspForm.discriminantEquiv (g.toCuspForm hg0))

    have hh : qExpansion 1 (h : ℍ → ℂ) =
        a₀ • q4 ^ (3 * (m + 1)) +
          qΔ * qExpansion 1 (CuspForm.discriminantEquiv (g.toCuspForm hg0) : ℍ → ℂ) := by
      rw [← hΔ, hg]; abel
    rw [hh]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_
    · have := monomial_mem (m + 1) 0 (Nat.zero_le _)
      simpa using this
    ·
      refine Submodule.span_induction (p := fun x _ => qΔ * x ∈ monomialSpan (m + 1))
        ?_ ?_ ?_ ?_ hIH
      · rintro _ ⟨b, rfl⟩
        have hb : (b : ℕ) ≤ m := Nat.lt_succ_iff.mp b.2
        have := monomial_mem (m + 1) (b + 1) (Nat.succ_le_succ hb)
        rw [show 3 * (m + 1 - ((b : ℕ) + 1)) = 3 * (m - b) by omega, pow_succ] at this
        rw [show qΔ * (q4 ^ (3 * (m - ↑b)) * qΔ ^ (b : ℕ)) =
          q4 ^ (3 * (m - ↑b)) * (qΔ ^ (b : ℕ) * qΔ) by ring]
        exact this
      · simp
      · intro x y _ _ hx hy
        rw [mul_add]
        exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ _ hx

end FIdxLevelOne

/-! ## `FIdxNorm` — the `Cos` alias and the index formula -/

namespace FIdxNorm

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

/-- The pin's `FIdxNorm.Cos`, re-hosted over the promoted `JOneES.JOneESNorm.Cos`. -/
abbrev Cos (Γ : Subgroup SL(2, ℤ)) : Type := JOneES.JOneESNorm.Cos Γ

noncomputable scoped instance : Fintype (Cos Γ) := Fintype.ofFinite _

open scoped ModularCurve.FIdxNorm

theorem card_cos_eq_index : Nat.card (Cos Γ) = Γ.index := by
  rw [← Subgroup.index, ← Subgroup.relIndex, MonoidHom.range_eq_map,
    show ((Γ : Subgroup (GL (Fin 2) ℝ))) = Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ) from rfl,
    Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]

end FIdxNorm

/-! ## `FIdxRat` — the discriminant generator `wq` and the rational relation -/

namespace FIdxRat

open ModularForm UpperHalfPlane EisensteinSeries HahnSeries _root_.Polynomial
open scoped MatrixGroups ModularForm

-- The shared `hper`/`coeffEmb_intSeriesC`/`coeffEmb_eq_map`/`sum_div_pow_eq` come
-- from the promoted `JOneESRat` block; only the two `exists_rat_relation`-specific
-- names (`monomial_eq`, `exists_rat_relation`) are re-stated at their pin text.
open JOneES.JOneESRat

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

section Lift

variable {Γ' : Subgroup SL(2, ℤ)} {k : ℤ}

omit [Γ.FiniteIndex] in
theorem slash_neg_SL (f : ℍ → ℂ) (hk : Even k) (δ : SL(2, ℤ)) : f ∣[k] (-δ) = f ∣[k] δ := by
  funext τ
  rw [SL_slash_apply, SL_slash_apply]
  have h1 : (-δ) • τ = δ • τ := by simp
  have h2 : denom (-δ : SL(2, ℤ)) τ = - denom δ τ := by
    simp [denom]; ring
  rw [h1, h2, (Even.neg hk).neg_zpow]

noncomputable def liftEven (hΓ' : Γ ≤ Γ') (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ) (hk : Even k)
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := f
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    rcases hneg γ hγ with h | h
    · exact f.slash_action_eq' _ ⟨γ, h, rfl⟩
    · have h' : (⇑f) ∣[k] (-γ) = ⇑f := f.slash_action_eq' _ ⟨-γ, h, rfl⟩
      change (⇑f) ∣[k] γ = ⇑f
      rw [← neg_neg γ, slash_neg_SL _ hk]
      exact h'
  holo' := f.holo'
  bdd_at_cusps' {c} hc := by
    haveI : Γ'.FiniteIndex := Subgroup.finiteIndex_of_le hΓ'
    have hc' : IsCusp c (Γ : Subgroup (GL (Fin 2) ℝ)) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc
    exact f.bdd_at_cusps' hc'

omit [Γ.FiniteIndex] in
@[scoped simp]
theorem coe_liftEven (hΓ' : Γ ≤ Γ') (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ) (hk : Even k)
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) [Γ.FiniteIndex] :
    (liftEven hΓ' hneg hk f : ℍ → ℂ) = f := rfl

end Lift

omit [Γ.FiniteIndex] in

noncomputable abbrev PΔ : PowerSeries ℤ := PowerSeries.X * dedekindEtaUnit

variable (Γ) in

noncomputable def D12 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

omit [Γ.FiniteIndex] in
theorem coe_D12 : (D12 Γ : ℍ → ℂ) = ModularForm.discriminant := rfl

omit [Γ.FiniteIndex] in
theorem isIntegralQExp_D12 : IsIntegralQExp (D12 Γ : ℍ → ℂ) PΔ := by
  rw [IsIntegralQExp, coe_D12]
  exact qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

omit [Γ.FiniteIndex] in
theorem isIntegralQExp_Delta : IsIntegralQExp (ModularForm.discriminant : ℍ → ℂ) PΔ :=
  qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

omit [Γ.FiniteIndex] in
theorem intSeriesC_PΔ_ne_zero (K : Type*) [Field K] : intSeriesC K PΔ ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

noncomputable def wq : LaurentSeries ℚ := intSeriesC ℚ PΔ / intSeriesC ℚ (eisenstein4 ^ 3)

omit [Γ.FiniteIndex] in
theorem wq_mem : wq ∈ qExpFunctionFieldC ℚ Γ :=
  div_mem_qExpFunctionFieldC (D12 Γ) (JOneES.JOneESRat.A12 Γ) isIntegralQExp_D12
    JOneES.JOneESRat.isIntegralQExp_A12 JOneES.JOneESRat.intSeriesC_E4_cube_ne_zero

omit [Γ.FiniteIndex] in

theorem jqModC_mul_delta (K : Type*) [Field K] :
    jqModC K * intSeriesC K PΔ = intSeriesC K (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

omit [Γ.FiniteIndex] in

theorem wq_eq_inv : wq = (jqModC ℚ)⁻¹ := by
  rw [wq, eq_comm, inv_eq_iff_eq_inv, inv_div, eq_div_iff (intSeriesC_PΔ_ne_zero ℚ),
    jqModC_mul_delta]

omit [Γ.FiniteIndex] in

theorem wq_transcendental : Transcendental ℚ wq := by
  intro halg
  rw [wq_eq_inv] at halg
  exact transcendental_jqModC ℚ (IsAlgebraic.inv_iff.mp halg)

omit [Γ.FiniteIndex] in
theorem intSeriesC_add {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

omit [Γ.FiniteIndex] in
theorem intSeriesC_neg {K : Type*} [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (-p) = -intSeriesC K p := by
  simp [intSeriesC]

section Relation

variable {Γ' : Subgroup SL(2, ℤ)} [Γ'.FiniteIndex]
variable (hT : ModularGroup.T ∈ Γ) (hΓ' : Γ ≤ Γ') (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
include hT hΓ' hneg

local notation "μ" => Nat.card (FIdxNorm.Cos Γ')

omit [Γ.FiniteIndex] [Γ'.FiniteIndex] hT hΓ' hneg in

theorem monomial_eq {K : Type*} [Field K] {m b : ℕ} (hb : b ≤ m) (Q4 QD : K) (h4 : Q4 ≠ 0) :
    Q4 ^ (3 * (m - b)) * QD ^ b = Q4 ^ (3 * m) * (QD / Q4 ^ 3) ^ b := by
  rw [show 3 * m = 3 * (m - b) + 3 * b by omega, _root_.pow_add, div_pow, ← pow_mul, mul_assoc]
  congr 1
  rw [mul_comm 3 b, mul_div_assoc', mul_comm (Q4 ^ (b * 3)), mul_div_assoc,
    div_self (pow_ne_zero _ h4), mul_one]

theorem exists_rat_relation {k : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ (m : ℕ) (d : Fin (μ + 1) × Fin (m + 1) → ℚ),
      (∃ ib, d ib ≠ 0) ∧
      ∑ ib, d ib • (wq ^ (ib.2 : ℕ) * (intSeriesC ℚ pf / intSeriesC ℚ pg) ^ (ib.1 : ℕ)) = 0 := by
  classical

  have hgne : g ≠ 0 := by
    intro h0
    apply hg0
    have : pg = 0 := by
      apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
      rw [hg, h0, FunLike.coe_zero, qExpansion_zero, map_zero]
    rw [this, intSeriesC_zero]
  have hk : 0 ≤ k := by
    by_contra hlt
    exact hgne (ModularForm.isZero_of_neg_weight (not_le.mp hlt) g)

  have hw : (11 : ℕ) * k + k = 12 * k := by ring
  have heven : Even (12 * k) := ⟨6 * k, by ring⟩
  let f₀ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * k) := ((g.pow 11).mul f).mcast hw
  let g₀ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * k) := ((g.pow 11).mul g).mcast hw
  let f' : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) (12 * k) := liftEven hΓ' hneg heven f₀
  let g' : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) (12 * k) := liftEven hΓ' hneg heven g₀
  have hqf' : qExpansion 1 (f' : ℍ → ℂ) =
      qExpansion 1 (g : ℍ → ℂ) ^ 11 * qExpansion 1 (f : ℍ → ℂ) := by
    simp only [f', f₀, coe_liftEven, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos (hper hT),
      ModularForm.qExpansion_pow one_pos (hper hT)]
  have hqg' : qExpansion 1 (g' : ℍ → ℂ) =
      qExpansion 1 (g : ℍ → ℂ) ^ 11 * qExpansion 1 (g : ℍ → ℂ) := by
    simp only [g', g₀, coe_liftEven, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos (hper hT),
      ModularForm.qExpansion_pow one_pos (hper hT)]
  have hqg : qExpansion 1 (g : ℍ → ℂ) ≠ 0 := by
    rwa [Ne, ModularForm.qExpansion_eq_zero_iff one_pos (hper hT)]
  have hg'ne : g' ≠ 0 := by
    intro h0
    have : qExpansion 1 (g' : ℍ → ℂ) = 0 := by rw [h0, FunLike.coe_zero, qExpansion_zero]
    rw [hqg'] at this
    exact (mul_ne_zero (pow_ne_zero _ hqg) hqg) this

  have hT' : ModularGroup.T ∈ Γ' := hΓ' hT
  have hrel := JOneES.JOneESNorm.sum_qExpansion_coeffForm_mul_pow_eq_zero f' g' hT'
  have htop := JOneES.JOneESNorm.qExpansion_coeffForm_card_ne_zero f' g' hg'ne
  set m : ℕ := k.toNat * μ with hm
  have hkm : 12 * k * (μ : ℤ) = 12 * (m : ℤ) := by
    rw [hm]; push_cast; rw [Int.toNat_of_nonneg hk]; ring
  have hspan : ∀ i, qExpansion 1 (JOneES.JOneESNorm.coeffForm f' g' i : ℍ → ℂ) ∈
      FIdxLevelOne.monomialSpan m :=
    fun i => FIdxLevelOne.qExpansion_mem_monomialSpan m _ hkm _
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan i)

  let Φ : PowerSeries ℂ →+* LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ
  have hΦ : Function.Injective Φ := HahnSeries.ofPowerSeries_injective
  set Q4 : LaurentSeries ℂ := Φ FIdxLevelOne.q4 with hQ4
  set QD : LaurentSeries ℂ := Φ FIdxLevelOne.qΔ with hQD
  set QF : LaurentSeries ℂ := Φ (qExpansion 1 (f : ℍ → ℂ)) with hQF
  set QG : LaurentSeries ℂ := Φ (qExpansion 1 (g : ℍ → ℂ)) with hQG
  set QE : ℕ → LaurentSeries ℂ := fun i =>
    Φ (qExpansion 1 (JOneES.JOneESNorm.coeffForm f' g' i : ℍ → ℂ)) with hQE
  have hQG0 : QG ≠ 0 := fun h => hqg (hΦ (by rw [map_zero]; exact h))
  have hQ40 : Q4 ≠ 0 := by
    intro h
    have : FIdxLevelOne.q4 = 0 := hΦ (by rw [map_zero]; exact h)
    have h0 := congrArg (PowerSeries.coeff 0) this
    rw [FIdxLevelOne.q4_coeff_zero, map_zero] at h0
    exact one_ne_zero h0

  have hrel' : ∑ i ∈ Finset.range (μ + 1), QE i * (QG ^ 11 * QF) ^ i * (QG ^ 11 * QG) ^ (μ - i)
      = 0 := by
    have := congrArg Φ hrel
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hQE, hQF, hQG, map_mul, map_pow, hqf', hqg']
  have hdiv := sum_div_pow_eq (n := μ) QE (QG ^ 11 * QF) (QG ^ 11 * QG)
    (mul_ne_zero (pow_ne_zero _ hQG0) hQG0) hrel'
  have hratio : (QG ^ 11 * QF) / (QG ^ 11 * QG) = QF / QG :=
    mul_div_mul_left _ _ (pow_ne_zero _ hQG0)
  rw [hratio] at hdiv

  set Wh : LaurentSeries ℂ := QD / Q4 ^ 3 with hWh
  have hQEi : ∀ i, QE i = Q4 ^ (3 * m) * ∑ b : Fin (m + 1), HahnSeries.C (c i b) * Wh ^ (b : ℕ) := by
    intro i
    simp only [hQE]
    rw [← hc i, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [PowerSeries.smul_eq_C_mul, map_mul, map_mul, map_pow, map_pow,
      monomial_eq (Nat.lt_succ_iff.mp b.2) _ _ hQ40]
    simp only [Φ, HahnSeries.ofPowerSeries_C]
    ring

  have hsum : ∑ ib : Fin (μ + 1) × Fin (m + 1),
      c ib.1 ib.2 • (Wh ^ (ib.2 : ℕ) * (QF / QG) ^ (ib.1 : ℕ)) = 0 := by
    have h1 : Q4 ^ (3 * m) * ∑ i : Fin (μ + 1),
        (∑ b : Fin (m + 1), HahnSeries.C (c i b) * Wh ^ (b : ℕ)) * (QF / QG) ^ (i : ℕ) = 0 := by
      rw [Finset.mul_sum, ← hdiv, Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hQEi, mul_assoc]
    have h2 := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hQ40)
    rw [Fintype.sum_prod_type, ← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← HahnSeries.C_mul_eq_smul, mul_assoc]

  have hnz : ∃ b, c μ b ≠ 0 := by
    by_contra hall
    push Not at hall
    apply htop
    rw [← hc μ]
    exact Finset.sum_eq_zero fun b _ => by rw [hall b, zero_smul]

  obtain ⟨b₀, hb₀⟩ := hnz
  let v : Fin (μ + 1) × Fin (m + 1) → LaurentSeries ℚ :=
    fun ib => wq ^ (ib.2 : ℕ) * (intSeriesC ℚ pf / intSeriesC ℚ pg) ^ (ib.1 : ℕ)
  have hvmap : ∀ ib, HahnSeries.map (v ib) (algebraMap ℚ ℂ) =
      Wh ^ (ib.2 : ℕ) * (QF / QG) ^ (ib.1 : ℕ) := by
    intro ib
    rw [← coeffEmb_eq_map, map_mul, map_pow, map_pow, wq, map_div₀, map_div₀,
      coeffEmb_intSeriesC, coeffEmb_intSeriesC, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
    have h4 : eisenstein4.map (Int.castRingHom ℂ) = FIdxLevelOne.q4 :=
      JOneES.JOneESRat.isIntegralQExp_E4
    have hD : PΔ.map (Int.castRingHom ℂ) = FIdxLevelOne.qΔ := isIntegralQExp_Delta
    have hf' : pf.map (Int.castRingHom ℂ) = qExpansion 1 (f : ℍ → ℂ) := hf
    have hg' : pg.map (Int.castRingHom ℂ) = qExpansion 1 (g : ℍ → ℂ) := hg
    simp only [map_pow, h4, hD, hf', hg']
    rfl
  have hdep : ¬ LinearIndependent ℂ (fun ib => HahnSeries.map (v ib) (algebraMap ℚ ℂ)) := by
    rw [Fintype.not_linearIndependent_iff]
    refine ⟨fun ib => c ib.1 ib.2, ?_, ⟨(Fin.last μ, b₀), by simpa using hb₀⟩⟩
    simp_rw [hvmap]
    exact hsum
  have hdepQ : ¬ LinearIndependent ℚ v := fun h => hdep (JOneES.JOneESAlg.linearIndependent_map h)
  rw [Fintype.not_linearIndependent_iff] at hdepQ
  obtain ⟨d, hd, ib₁, hib₁⟩ := hdepQ
  exact ⟨m, d, ⟨ib₁, hib₁⟩, hd⟩

end Relation

section Bound

variable {Γ' : Subgroup SL(2, ℤ)} [Γ'.FiniteIndex]
variable (hT : ModularGroup.T ∈ Γ) (hΓ' : Γ ≤ Γ') (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
include hT hΓ' hneg

omit [Γ.FiniteIndex] [Γ'.FiniteIndex] hT hΓ' hneg in

theorem jqModC_mem : jqModC ℚ ∈ qExpFunctionFieldC ℚ Γ := by
  have h : (wq)⁻¹ ∈ qExpFunctionFieldC ℚ Γ := inv_mem wq_mem
  rwa [wq_eq_inv, inv_inv] at h

theorem finrank_adjoin_wq_le :
    Module.finrank
        (IntermediateField.adjoin ℚ
          ({(⟨wq, wq_mem⟩ : qExpFunctionFieldC ℚ Γ)} : Set (qExpFunctionFieldC ℚ Γ)))
        (qExpFunctionFieldC ℚ Γ) ≤ Nat.card (FIdxNorm.Cos Γ') := by
  classical
  let F := qExpFunctionFieldC ℚ Γ
  let X₀ : F := ⟨wq, wq_mem⟩
  let φ : F →+* LaurentSeries ℚ := algebraMap F (LaurentSeries ℚ)
  have hφQ : φ.comp (algebraMap ℚ F) = algebraMap ℚ (LaurentSeries ℚ) := Subsingleton.elim _ _
  have hX₀ : Transcendental ℚ X₀ := by
    rintro ⟨r, hr0, hr⟩
    refine wq_transcendental ⟨r, hr0, ?_⟩
    have := Polynomial.hom_eval₂ r (algebraMap ℚ F) φ X₀
    rw [hφQ] at this
    rw [Polynomial.aeval_def, show wq = φ X₀ from rfl, ← this, ← Polynomial.aeval_def, hr,
      map_zero]
  let K₀ := IntermediateField.adjoin ℚ ({X₀} : Set F)
  let Xk : K₀ := ⟨X₀, IntermediateField.mem_adjoin_simple_self ℚ X₀⟩
  have hrat : ∀ e : ℚ,
      (((algebraMap ℚ K₀ e : K₀) : F) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) e := by
    intro e
    have h := RingHom.congr_fun (Subsingleton.elim
      ((φ.comp (algebraMap K₀ F)).comp (algebraMap ℚ K₀)) (algebraMap ℚ (LaurentSeries ℚ))) e
    rw [← h]
    rfl
  haveI : PerfectField K₀ := PerfectField.ofCharZero
  refine FIdxAlg.finrank_le_of_forall_aeval_eq_zero (Nat.card (FIdxNorm.Cos Γ')) ?_
  intro Y
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hY⟩ := (JOneES.JOneESRat.mem_qExpFunctionFieldC_iff hT).mp Y.2
  obtain ⟨m, d, ⟨ib₀, hib₀⟩, hd⟩ := exists_rat_relation hT hΓ' hneg f g hf hg hg0

  let coef : Fin (Nat.card (FIdxNorm.Cos Γ') + 1) → K₀ :=
    fun i => ∑ b : Fin (m + 1), algebraMap ℚ K₀ (d (i, b)) * Xk ^ (b : ℕ)
  have hcoef : ∀ i, (((coef i : K₀) : F) : LaurentSeries ℚ) =
      ∑ b : Fin (m + 1), algebraMap ℚ (LaurentSeries ℚ) (d (i, b)) * wq ^ (b : ℕ) := by
    intro i
    simp only [coef]
    rw [IntermediateField.coe_sum, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow,
      hrat]
  let p : K₀[X] := ∑ i : Fin (Nat.card (FIdxNorm.Cos Γ') + 1), Polynomial.monomial (i : ℕ) (coef i)
  have hcoeff : ∀ i : Fin (Nat.card (FIdxNorm.Cos Γ') + 1), p.coeff i = coef i := by
    intro i
    simp only [p, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hji
      rw [ite_eq_right]
      exact fun h => hji (Fin.ext h)
  refine ⟨p, ?_, ?_, ?_⟩
  ·
    intro hp
    have h1 : coef ib₀.1 = 0 := by rw [← hcoeff, hp, Polynomial.coeff_zero]
    apply wq_transcendental
    let r : ℚ[X] := ∑ b : Fin (m + 1), Polynomial.monomial (b : ℕ) (d (ib₀.1, b))
    have hr0 : r ≠ 0 := by
      intro hr
      have := congrArg (fun q : ℚ[X] => q.coeff ib₀.2) hr
      simp only [r, finsetSum_coeff, coeff_monomial, Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single_of_mem ib₀.2 (Finset.mem_univ _)] at this
      · simp only [↓reduceIte] at this; exact hib₀ this
      · intro j _ hji; rw [ite_eq_right]; exact fun h => hji (Fin.ext h)
    refine ⟨r, hr0, ?_⟩
    have h2 : (((coef ib₀.1 : K₀) : F) : LaurentSeries ℚ) = 0 := by rw [h1]; rfl
    rw [hcoef] at h2
    rw [← h2]
    simp only [r, map_sum, Polynomial.aeval_monomial]
  ·
    exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp i.2)
  ·
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero]
    have hd' : ∑ ib : Fin (Nat.card (FIdxNorm.Cos Γ') + 1) × Fin (m + 1),
        algebraMap ℚ (LaurentSeries ℚ) (d ib) *
          (wq ^ (ib.2 : ℕ) * (intSeriesC ℚ pf / intSeriesC ℚ pg) ^ (ib.1 : ℕ)) = 0 := by
      rw [← hd]
      refine Finset.sum_congr rfl fun ib _ => ?_
      rw [← HahnSeries.C_mul_eq_smul, HahnSeries.C_eq_algebraMap]
      congr 1
      exact RingHom.congr_fun (Subsingleton.elim _ _) _
    rw [← hd']
    simp only [p, map_sum, Polynomial.aeval_monomial]
    rw [IntermediateField.coe_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, ← hY, IntermediateField.algebraMap_apply,
      hcoef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end Bound

end FIdxRat

/-! ## `FIdxBC` — the relative-degree base change -/

namespace FIdxBC

open scoped MatrixGroups

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem coeffEmb_eq_map (z : LaurentSeries ℚ) : coeffEmb L z = HahnSeries.map z (algebraMap ℚ L) := by
  ext n; rw [coeffEmb_coeff]; rfl

theorem coeffEmb_jqModC : coeffEmb L (jqModC ℚ) = jqModC L := by
  rw [coeffEmb_eq_map, map_jqModC]

theorem adjoin_wq_eq :
    IntermediateField.adjoin ℚ ({FIdxRat.wq} : Set (LaurentSeries ℚ)) =
      IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)) := by
  rw [FIdxRat.wq_eq_inv]
  apply le_antisymm
  · exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _)))
  · refine IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ?_)
    have := inv_mem (IntermediateField.mem_adjoin_simple_self ℚ (jqModC ℚ)⁻¹)
    rwa [inv_inv] at this

theorem finrank_le (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup SL(2, ℤ)) (hΓ' : Γ ≤ Γ') (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (y : laurentBaseChange L (qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries L) = jqModC L) :
    Module.finrank
        (IntermediateField.adjoin L ({y} : Set (laurentBaseChange L (qExpFunctionFieldC ℚ Γ))))
        (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) ≤ Γ'.index := by
  haveI : Γ'.FiniteIndex := Subgroup.finiteIndex_of_le hΓ'

  have hQ := FIdxRat.finrank_adjoin_wq_le (Γ := Γ) hT hΓ' hneg
  rw [FIdxNorm.card_cos_eq_index] at hQ
  have hQ' : IntermediateField.relfinrank
      (IntermediateField.adjoin ℚ ({FIdxRat.wq} : Set (LaurentSeries ℚ)))
      (qExpFunctionFieldC ℚ Γ) ≤ Γ'.index := by
    have h := FIdxAlg.finrank_adjoin_simple_eq_relfinrank (qExpFunctionFieldC ℚ Γ)
      (⟨FIdxRat.wq, FIdxRat.wq_mem⟩ : qExpFunctionFieldC ℚ Γ)
    rw [← h]
    exact hQ
  rw [adjoin_wq_eq] at hQ'

  have hbc := relfinrank_laurentBaseChange L (qExpFunctionFieldC ℚ Γ) (jqModC ℚ)
    FIdxRat.jqModC_mem (transcendental_jqModC ℚ)
  rw [coeffEmb_jqModC] at hbc
  have h2 := FIdxAlg.finrank_adjoin_simple_eq_relfinrank
    (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) y
  rw [hy, hbc] at h2
  exact h2.trans_le hQ'

end FIdxBC

open scoped MatrixGroups in

/-- **The `JOneES` finrank/index bound.** Verbatim from
`Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean`. -/
theorem finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
    (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (y : laurentBaseChange L (qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries L) = jqModC L) :
    Module.finrank
        (IntermediateField.adjoin L
          ({y} : Set (laurentBaseChange L (qExpFunctionFieldC ℚ Γ))))
        (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) ≤ Γ'.index :=
  FIdxBC.finrank_le L Γ hT Γ' hΓ' hneg y hy

end ModularCurve

end
