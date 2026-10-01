/-
  X1's `intSeriesC`/`intFormRatiosC` and the pin's `jqModC_mem_intFormRatiosC`:
  `jqModC = q⁻¹ · j(q) = E₄³ / Δ` exhibits `jqModC` as a ratio of two integral
  `q`-expansions.

  The two definitions are the pin's `Def_ModularCurve_X1.lean` `FunctionField`
  block (lines 66–99), transcribed verbatim; `intSeriesC_one`/`_zero`/`_mul` are
  the block's three arithmetic lemmas. `restrictForm` is the pin's proof-only
  helper, kept `private` here per the port's cross-module-`private` policy (it is
  already duplicated `private` in `WeightOne/Gamma0Integral.lean`).
  `one_mem_intFormRatiosC` and `qExpFunctionFieldC` are the rest of that block and
  are deferred until a consumer needs them.

  The proof of the headline is the pin's
  `P2M/Sol/S_ModularCurve_jqModC_mem_intFormRatiosC.lean`, with the first helper
  collapsed: the pin re-derives `IsIntegralQExp E₄ eisenstein4` coefficient-wise,
  while the port already publishes `qExpansion_E4_eq_map_eisenstein4`
  (`ModularForms/JqAnalyticModel.lean`), of which it is the `.symm`.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_jqModC_mem_intFormRatiosC.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_jqModC_mem_intFormRatiosC.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1.lean
-/
import FLTForHuman.ModularForms.WeightOne.Gamma0Integral
import FLTForHuman.ModularCurve.Defs.JqCoeff

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open UpperHalfPlane ModularForm HahnSeries
open scoped MatrixGroups ModularForm

namespace ModularCurve

/-! ## X1's `FunctionField` vocabulary -/

private def restrictForm {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ)
    (f : ModularForm Γ k) : ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[simp] private theorem coe_restrictForm {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (h : Γ' ≤ Γ) (f : ModularForm Γ k) : (⇑(restrictForm h f) : ℍ → ℂ) = f := rfl

variable (K : Type*) [Field K]

/-- The integral `q`-expansion `p` as a Laurent series over `K`. -/
def intSeriesC (p : PowerSeries ℤ) : LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K (p.map (Int.castRingHom K))

@[simp] theorem intSeriesC_one : intSeriesC K 1 = 1 := by
  simp [intSeriesC]

@[simp] theorem intSeriesC_zero : intSeriesC K 0 = 0 := by
  simp [intSeriesC]

theorem intSeriesC_mul (p p' : PowerSeries ℤ) :
    intSeriesC K (p * p') = intSeriesC K p * intSeriesC K p' := by
  simp [intSeriesC]

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

/-- The set of ratios `intSeriesC K pf / intSeriesC K pg` of integral
`q`-expansions of modular forms of a common weight for `Γ`. -/
def intFormRatiosC : Set (LaurentSeries K) :=
  {x | ∃ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
      IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC K pg ≠ 0 ∧
        x = intSeriesC K pf / intSeriesC K pg}

variable {K Γ} in
theorem mem_intFormRatiosC {k : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC K pg ≠ 0) :
    intSeriesC K pf / intSeriesC K pg ∈ intFormRatiosC K Γ :=
  ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩

/-! ## `jqModC` as such a ratio

The pin's `JqMemRatios` block. Every helper is `private` in its `S_` file, so the
port transcribes them `private`; only the headline is public. -/

private theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [IsIntegralQExp]
  exact qExpansion_E4_eq_map_eisenstein4.symm

private def e4cube : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) ((E₄.pow 3).mcast (by norm_num))

private def delta : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

private theorem isIntegralQExp_e4cube :
    IsIntegralQExp (e4cube Γ : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, e4cube, coe_restrictForm, map_pow, isIntegralQExp_E4,
    ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

private theorem coe_delta : (delta Γ : ℍ → ℂ) = ModularForm.discriminant := rfl

private theorem isIntegralQExp_delta :
    IsIntegralQExp (delta Γ : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) := by
  rw [IsIntegralQExp, coe_delta]
  exact qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

private theorem intSeriesC_delta_ne_zero :
    intSeriesC K (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
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

private theorem jqModC_mul_delta :
    jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

private theorem jqModC_eq_div :
    jqModC K = intSeriesC K (eisenstein4 ^ 3) / intSeriesC K (PowerSeries.X * dedekindEtaUnit) := by
  rw [eq_div_iff (intSeriesC_delta_ne_zero K), jqModC_mul_delta]

/-- **`jqModC` is a ratio of integral `q`-expansions**: `jqModC = E₄³ / Δ`.
Verbatim from `Theorems/Thm_ModularCurve_jqModC_mem_intFormRatiosC.lean`.

The pin's anonymous constructor is used rather than the named
`mem_intFormRatiosC`: applying the latter forces instance/defeq search over the
`(Γ : Subgroup (GL (Fin 2) ℝ))` coercion and does not terminate in a bounded
budget, while the anonymous constructor elaborates in milliseconds. -/
theorem jqModC_mem_intFormRatiosC (K : Type*) [Field K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    jqModC K ∈ intFormRatiosC K Γ :=
  ⟨12, e4cube Γ, delta Γ, eisenstein4 ^ 3, PowerSeries.X * dedekindEtaUnit,
    isIntegralQExp_e4cube Γ, isIntegralQExp_delta Γ, intSeriesC_delta_ne_zero K, jqModC_eq_div K⟩

end ModularCurve

end
