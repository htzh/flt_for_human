/-
The pin node `ModularCurve.jqModC_mem_intFormRatiosC`: `jqModC = q⁻¹ · j(q) = E₄³ / Δ`
exhibits `jqModC` as a ratio of two integral `q`-expansions — and its analytic
companion `jqModC_eq_qExpansion_E4_cube_div_discriminant`.

This is a **node** module.  The definition-layer content it used to carry — the
pin's `Restrict` block (`restrictForm` and its two lemmas) and the whole
`FunctionField` block (`intSeriesC` + `_one`/`_zero`/`_mul`, `intFormRatiosC`,
`mem_intFormRatiosC`, `qExpFunctionFieldC`, `intFormRatiosC_subset`,
`div_mem_qExpFunctionFieldC`) — is the pin's
`Definitions/Def_ModularCurve_X1.lean` and now lives at its own home,
`FLTForHuman/ModularCurve/X1/Defs.lean`, which this module imports.  Before the
move, every consumer of the `q`-expansion function field imported this node to
reach its definition layer.

The proof of the headline is the pin's
`P2M/Sol/S_ModularCurve_jqModC_mem_intFormRatiosC.lean`, with the first helper
collapsed: the pin re-derives `IsIntegralQExp E₄ eisenstein4` coefficient-wise,
while the port already publishes `qExpansion_E4_eq_map_eisenstein4`
(`ModularForms/JqAnalyticModel.lean`), of which it is the `.symm`.

The pin keeps every helper but the headline `private`; the port transcribed them
the same way, and they are **promoted public** here because the `RelIndex` set
(`topics/modularCurve/TOPIC-relIndex-relrank.md`) is a second consumer of the same
mathematics and its `LevelOne` block is the `ℂ`-instance of it.  Promotion is an
exposure, not a copy: no proof moved.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_jqModC_mem_intFormRatiosC.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_jqModC_mem_intFormRatiosC.lean

Wired here, not in the frozen registry: this module's own `spec-pin:` lines below
replaced its `PORT_FILES` entry (`spec/old_check_stmts.py`), so
`spec/check_port.py` diffs every public declaration against the pin files named.

spec-pin: Theorems/Thm_ModularCurve_jqModC_mem_intFormRatiosC.lean
spec-pin: P2M/Sol/S_ModularCurve_jqModC_mem_intFormRatiosC.lean
spec-pin: Theorems/Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant.lean
spec-pin: P2M/Sol/S_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant.lean
spec-pin: P2M/Sol/S_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean
spec-pin: P2M/Sol/S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean
-/
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularForms.JqAnalyticModel

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open UpperHalfPlane ModularForm HahnSeries
open scoped MatrixGroups ModularForm

namespace ModularCurve

variable (K : Type*) [Field K]

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

/-! ## `jqModC` as such a ratio -/

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [IsIntegralQExp]
  exact qExpansion_E4_eq_map_eisenstein4.symm

def e4cube : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) ((E₄.pow 3).mcast (by norm_num))

def delta : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem isIntegralQExp_e4cube :
    IsIntegralQExp (e4cube Γ : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, e4cube, coe_restrictForm, map_pow, isIntegralQExp_E4,
    ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem coe_delta : (delta Γ : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem isIntegralQExp_delta :
    IsIntegralQExp (delta Γ : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) := by
  rw [IsIntegralQExp, coe_delta]
  exact qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem intSeriesC_delta_ne_zero :
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

theorem jqModC_mul_delta :
    jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

theorem jqModC_eq_div :
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

/-- **`jqModC` against the analytic `q`-expansions**: `jqModC ℂ = (q(E₄))³ / q(Δ)`.
Verbatim from `Theorems/Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant.lean`.

This is `jqModC_eq_div` at `K = ℂ` with the two `q`-expansions substituted for
their integral series via the ported `qExpansion_E4_eq_map_eisenstein4` /
`qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`; the pin's `S_` file proves
the same identity analytically. -/
theorem jqModC_eq_qExpansion_E4_cube_div_discriminant :
    jqModC ℂ = (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 /
      ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by
  have hE : ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = intSeriesC ℂ eisenstein4 := by
    rw [qExpansion_E4_eq_map_eisenstein4]
    rfl
  have hD : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = intSeriesC ℂ (PowerSeries.X * dedekindEtaUnit) := by
    rw [qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit]
    rfl
  have hpow : intSeriesC ℂ (eisenstein4 ^ 3) = (intSeriesC ℂ eisenstein4) ^ 3 := by
    simp only [intSeriesC, map_pow]
  rw [jqModC_eq_div, hpow, hE, hD]

/-! ## `coeffEmb` and the integral series

The `intSeriesC`-facing half of the pin's `X1LDLaurent`/`XHLDLaurent` block
(`P2M/Sol/S_ModularCurve_relfinrank_{x1,xH}HeckeCompositum_eq_mul.lean:417-478`
and `:530-589`, byte-identical in the two files). The `qExpAlg`/`laurentBaseChange`
half of the same block is in `ModularCurve/Defs/Laurent.lean` (the ring maps) and
`ModularCurve/Degree/LaurentGlue.lean` (`laurentBaseChange_map`/`_sup`, next to
`laurentBaseChange_adjoin`). -/

section CoeffEmbIntSeries

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem map_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R p).map f = HahnSeries.ofPowerSeries ℤ S (p.map f) := by
  ext k
  rw [HahnSeries.map_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

/-- Base change of an integral `q`-expansion: `coeffEmb` is `intSeriesC` at the target field.
This is the general spelling of the fact (the pin's `coeffEmb_intSeriesC'`); the ℂ-specific
`.map` spelling (`= HahnSeries.ofPowerSeries ℤ ℂ (p.map (Int.castRingHom ℂ))`) is the pin's
`S_:782` text and lives, faithfully, as
`JOneES.JOneESAlg.JOneESLevelOne.JOneESNorm.JOneESRat.coeffEmb_intSeriesC` in
`X1/FunctionField.lean` — both are kept, each checked in its own module. Because this one sits in
`namespace ModularCurve`, the *unqualified* name in any module of that namespace resolves to it
first, ahead of an `open`ed copy; that is why `X1/FunctionFieldDegree.lean`'s pin-transcribed step
needs `intSeriesC` unfolded (see the comment there). -/
theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  rw [coeffEmb_apply, intSeriesC, intSeriesC, map_ofPowerSeries, powerSeries_map_map,
    RingHom.ext_int ((algebraMap ℚ L).comp (Int.castRingHom ℚ)) (Int.castRingHom L)]

theorem intSeriesC_eq_zero_iff (K : Type*) [Field K] [CharZero K] (p : PowerSeries ℤ) :
    intSeriesC K p = 0 ↔ p = 0 := by
  constructor
  · intro h
    rw [intSeriesC] at h
    have h1 : p.map (Int.castRingHom K) = 0 := by
      have : HahnSeries.ofPowerSeries ℤ K (p.map (Int.castRingHom K)) =
          HahnSeries.ofPowerSeries ℤ K 0 := by
        rw [h, map_zero]
      exact HahnSeries.ofPowerSeries_injective this
    ext n
    have := congrArg (PowerSeries.coeff n) h1
    simp only [PowerSeries.coeff_map, map_zero, eq_intCast, Int.cast_eq_zero] at this
    simpa using this
  · rintro rfl; simp

theorem coeffEmb_image_intFormRatiosC (Γ : Subgroup SL(2, ℤ)) :
    coeffEmb L '' intFormRatiosC ℚ Γ = intFormRatiosC L Γ := by
  have := charZero_of_algebraRat L
  ext x
  constructor
  · rintro ⟨y, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    have hg0' : intSeriesC L pg ≠ 0 := by
      rw [Ne, intSeriesC_eq_zero_iff]
      exact fun h => hg0 (by rw [h]; simp)
    refine ⟨k, f, g, pf, pg, hf, hg, hg0', ?_⟩
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  · rintro ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hg0' : intSeriesC ℚ pg ≠ 0 := by
      rw [Ne, intSeriesC_eq_zero_iff]
      exact fun h => hg0 (by rw [h]; simp)
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, ⟨k, f, g, pf, pg, hf, hg, hg0', rfl⟩, ?_⟩
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

end CoeffEmbIntSeries

end ModularCurve

end
