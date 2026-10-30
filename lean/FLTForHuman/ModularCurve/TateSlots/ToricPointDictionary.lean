/-
  The toric-point dictionary at the `Γ_H(M, ⊥)` and `Γ₁(M)` levels: the two
  headlines

    * `ModularCurve.exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq`
      — the two-level dictionary `t ↦ (w₁ t, w₂ t)` into the `q`-expansion
      function field of `Γ_H(M, ⊥)`: the two normalised toric coordinates of
      `toricPoint K 1 (ζ ^ t)` at every unit `t ∈ (ZMod M)ˣ`, and the
      `ρ`-equivariance of the pair against the inverse unit
      `(CohCarrier.gamma0Units M γ)⁻¹` for every `IsDiamondPullbackModL K M ⊥ ρ`;
    * `ModularCurve.c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1`
      — the same two ratios at `t = 1`, at the `Γ₁(M)` level.

  Statements verbatim from the pinned wrappers; proofs transcribed from the
  matching `P2M/Sol/S_*` files (pin `aa2d8b3`), adapted to mathlib `v4.34.0`.

  ## The shared engine

  The two headlines share one engine, written once below at the pin's names:

    `FB` (the five-object structure of the pin's `W769.FB`: the two families of
    `Γ₁(M)`-forms `B`/`D`, their integral `q`-expansions `b`/`d`, and the four
    properties), `E4Γ`/`E6Γ` (`E₄`/`E₆` restricted to `Γ_H(M, ⊥)`), `BΓ`/`DΓ`/
    `f6` (the `Γ_H(M, ⊥)`-level forms, `f6 = B · E₄`), the membership lemmas
    `isIntegralQExp_*`, the slash laws `E4_slash`/`E6_slash`/`f6_slash`/
    `D_slash`, the field elements `β`/`δ` (the two ratios, at the `Γ_H` level
    and through `div_mem_qExpFunctionFieldC`), the dictionary elements
    `w₁`/`w₂`, their coefficient formulas `coe_w₁`/`coe_w₂` (the two-level
    dictionary, read off the Γ₁ engine
    `exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum`), and the
    equivariance block `ρ_β`/`ρ_δ`/`sum_reindex`/`ρ_w₁`/`ρ_w₂`.

  The first headline is the pin's `solution`: package `w₁`/`w₂` with
  `coe_w₁`/`coe_w₂` and `ρ_w₁`/`ρ_w₂`.  The second headline is the `t = 1`
  specialisation of the same engine (`CohCarrier.GammaH_bot M` identifies
  `Γ_H(M, ⊥)` with `Γ₁(M)`) — see "Deviations" below.

  `ModularCurve.IsDiamondPullbackModL` and its projection
  `IsDiamondPullbackModL.coe_apply_eq` are imported from
  `ModularCurve/Defs/XHDiamondModL.lean` (WORKORDER MSDEF), not restated;
  `ModularCurve.qExpansion_E6_eq_map_mk` is imported from
  `ModularCurve/X1/IntegralityJqNModC.lean` at its pin name (promoted out of the
  `EisensteinCube` namespace), also not restated.

  ## Public / private split

  Public: exactly the two headlines.  Everything else (the whole engine) is
  `private`: the pin's `W769` namespace is an implementation detail of these two
  statements, and neither the port nor the pin has a second consumer of the
  `FB`-indexed dictionary, so no promotion is owed.  (The pin's own `S_` file
  declares `main` and `solution`; the port declares no wrapper — the headline
  carries the engine's proof term directly, as in `TateSlots/Invariants.lean`.)

  Deviations from the pin.

  * 168 (`c4_mul_…_gamma1`): the pin proves it independently in its
    `WeberCusp.Forms`/`WeberCusp.Series` sections, redoing the same
    `1 + 12 · ⟨toric point⟩` and `… + 2 a₄` Fourier computation that 373-XH's
    `coe_w₁`/`coe_w₂` already performs.  Here it is the `t = 1`
    specialisation of the shared engine instead: `coe_w₁`/`coe_w₂` at
    `t = 1` (`ZMod.val_one`, `pow_one`) compose with
    `CohCarrier.GammaH_bot` to give exactly the pinned statement.  The pin's
    `WeberCusp` block is therefore *not* transcribed; its two reusable pieces
    (`one_mem_strictPeriods`, the `E₄`/`E₆` restricted integrality) are part of
    the shared engine above.
  * The pin's `omit X in` / `variable (M) in` dance is replaced by explicit
    section order and named arguments, and `FB` carries no `[NeZero M]`
    parameter (nothing in its fields needs one).  The seven declarations of the
    field section whose signatures do not use the section's `[NeZero M]`
    instance (`coe_β`, `coe_δ`, `coe_algebraMap`, `unit_ne_zero`,
    `coe_gamma0Units_inv`, `ρ_β`, `ρ_δ`) carry a local `omit [NeZero M] in` —
    the `unusedSectionVars` linter's own recommended fix — so the pin's
    module-wide `linter.unusedSectionVars false` / `linter.unusedVariables
    false` suppressions are not needed and the port sets no linter option.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1.lean

  spec-pin: Theorems/Thm_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.lean
  spec-pin: Theorems/Thm_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1.lean
  spec-pin: P2M/Sol/S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1.lean
-/
import FLTForHuman.ModularCurve.TateSlots.Invariants
import FLTForHuman.ModularCurve.Degree.FinrankAdjoinJqNModC
import FLTForHuman.ModularCurve.Defs.TateFormal
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.X1.Integral
import FLTForHuman.ModularCurve.Defs.XHDiamondModL

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open UpperHalfPlane hiding I
open ModularForm CongruenceSubgroup HahnSeries IntermediateField
open scoped MatrixGroups ModularForm

namespace ToricPointDict

/-! ## The `Γ_H(M, ⊥)`-level restricted forms and the two ratio denominators -/

section Prelim

variable (M : ℕ)

local notation "Γᴳ" =>
  ((CohCarrier.GammaH M ⊥ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γ₁ᴳ" =>
  ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem le_Gamma1 : Γᴳ ≤ Γ₁ᴳ := Subgroup.map_mono (CohCarrier.GammaH_bot M).le

private theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γᴳ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem
    (CohCarrier.translation_mem_GammaH M ⊥)]
  exact AddSubgroup.mem_zmultiples 1

private def E4Γ : ModularForm Γᴳ 4 :=
  restrictForm (Subgroup.map_le_range _ _) ModularForm.E₄

private def E6Γ : ModularForm Γᴳ 6 :=
  restrictForm (Subgroup.map_le_range _ _) ModularForm.E₆

private theorem coe_E4Γ : (⇑(E4Γ M) : ℍ → ℂ) = ⇑ModularForm.E₄ := rfl

private theorem coe_E6Γ : (⇑(E6Γ M) : ℍ → ℂ) = ⇑ModularForm.E₆ := rfl

private theorem isIntegralQExp_E4Γ : IsIntegralQExp (E4Γ M) eisenstein4 := by
  rw [IsIntegralQExp, coe_E4Γ]
  exact ModularCurve.qExpansion_E4_eq_map_eisenstein4.symm

private theorem isIntegralQExp_E6Γ : IsIntegralQExp (E6Γ M) eisenstein6 := by
  rw [IsIntegralQExp, coe_E6Γ, eisenstein6]
  exact ModularCurve.qExpansion_E6_eq_map_mk.symm

/-- The pin's `W769.FB`: the five objects the Γ₁ engine produces. -/
private structure FB where
  B : ZMod M → ModularForm Γ₁ᴳ 2
  D : ZMod M → ModularForm Γ₁ᴳ 4
  b : ZMod M → PowerSeries ℤ
  d : ZMod M → PowerSeries ℤ
  hb : ∀ c : ZMod M, IsIntegralQExp (B c) (b c)
  hd : ∀ c : ZMod M, IsIntegralQExp (D c) (d c)
  hB : ∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ Gamma0 M →
    (⇑(B c) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(B (c * ((γ 0 0 : ℤ) : ZMod M)))
  hD : ∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ Gamma0 M →
    (⇑(D c) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(D (c * ((γ 0 0 : ℤ) : ZMod M)))

end Prelim

section WithX

variable {M : ℕ}

local notation "Γᴳ" =>
  ((CohCarrier.GammaH M ⊥ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (X : FB M)

private def BΓ (c : ZMod M) : ModularForm Γᴳ 2 := restrictForm (le_Gamma1 M) (X.B c)

private def DΓ (c : ZMod M) : ModularForm Γᴳ 4 := restrictForm (le_Gamma1 M) (X.D c)

private def f6 (c : ZMod M) : ModularForm Γᴳ 6 := ((BΓ X c).mul (E4Γ M)).mcast (by norm_num)

private theorem coe_BΓ (c : ZMod M) : (⇑(BΓ X c) : ℍ → ℂ) = ⇑(X.B c) := rfl

private theorem coe_DΓ (c : ZMod M) : (⇑(DΓ X c) : ℍ → ℂ) = ⇑(X.D c) := rfl

private theorem coe_f6 (c : ZMod M) : (⇑(f6 X c) : ℍ → ℂ) = ⇑(X.B c) * ⇑ModularForm.E₄ := rfl

private theorem isIntegralQExp_DΓ (c : ZMod M) : IsIntegralQExp (DΓ X c) (X.d c) := X.hd c

private theorem isIntegralQExp_f6 (c : ZMod M) :
    IsIntegralQExp (f6 X c) (X.b c * eisenstein4) := by
  rw [IsIntegralQExp, show (⇑(f6 X c) : ℍ → ℂ) = ⇑((BΓ X c).mul (E4Γ M)) from rfl,
    ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods M), map_mul, coe_BΓ, coe_E4Γ,
    ModularCurve.qExpansion_E4_eq_map_eisenstein4, X.hb c]

private theorem E4_slash (γ : SL(2, ℤ)) :
    (⇑ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑ModularForm.E₄ := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq ModularForm.E₄ _ ⟨γ, rfl⟩

private theorem E6_slash (γ : SL(2, ℤ)) :
    (⇑ModularForm.E₆ : ℍ → ℂ) ∣[(6 : ℤ)] γ = ⇑ModularForm.E₆ := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq ModularForm.E₆ _ ⟨γ, rfl⟩

private theorem f6_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(f6 X c) : ℍ → ℂ) ∣[(6 : ℤ)] γ = ⇑(f6 X (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_f6, coe_f6, show (6 : ℤ) = 2 + 4 from rfl, ModularForm.mul_slash_SL2, X.hB c γ hγ,
    E4_slash]

private theorem D_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(DΓ X c) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(DΓ X (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_DΓ, coe_DΓ]
  exact X.hD c γ hγ

end WithX

/-! ## The function-field elements `β`, `δ`, `w₁`, `w₂`

Everything below lives in `F̄ = qExpFunctionFieldC K (Γ_H(M, ⊥))`, the field the
first headline is stated in; the second headline reads the same elements at
`t = 1` and pushes them across `Γ_H(M, ⊥) = Γ₁(M)`.
-/

section Field

variable {M : ℕ} [NeZero M]

variable (X : FB M)

variable (K : Type*) [Field K]

local notation "F̄" => qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)

private theorem natCast_ne_zero {ζ : K} (hζ : IsPrimitiveRoot ζ M) : (M : K) ≠ 0 := by
  have := hζ.neZero'
  exact NeZero.ne (M : K)

private theorem natCast_laurent_ne_zero {ζ : K} (hζ : IsPrimitiveRoot ζ M) :
    (M : LaurentSeries K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (LaurentSeries K)) M]
  exact (map_ne_zero_iff _ (algebraMap K (LaurentSeries K)).injective).mpr
    (natCast_ne_zero (M := M) (K := K) hζ)

private theorem algebraMap_laurent_eq_C (r : K) :
    algebraMap K (LaurentSeries K) r = HahnSeries.C r := by
  show HahnSeries.ofPowerSeries ℤ K (algebraMap K (PowerSeries K) r) = _
  simp

private theorem intSeriesC_eisenstein4 : intSeriesC K eisenstein4 = (tateLaurent K).c₄ :=
  (ModularCurve.c4_tateLaurent K).symm

private theorem intSeriesC_eisenstein6 : intSeriesC K eisenstein6 = -(tateLaurent K).c₆ := by
  rw [tateLaurent, WeierstrassCurve.map_c₆, ModularCurve.c6_tatePowerSeries, map_neg, neg_neg]
  rfl

private theorem intSeriesC_ne_zero_of_constantCoeff {p : PowerSeries ℤ}
    (hp : PowerSeries.constantCoeff p = 1) : intSeriesC K p ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 0) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, map_one] at h1
  exact one_ne_zero h1

private theorem intSeriesC_eisenstein4_ne_zero : intSeriesC K eisenstein4 ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff K constantCoeff_eisenstein4

private theorem intSeriesC_eisenstein6_ne_zero : intSeriesC K eisenstein6 ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff K constantCoeff_eisenstein6

private def β (c : ZMod M) : F̄ :=
  ⟨intSeriesC K (X.b c * eisenstein4) / intSeriesC K eisenstein6,
    div_mem_qExpFunctionFieldC (f6 X c) (E6Γ M) (isIntegralQExp_f6 X c)
      (isIntegralQExp_E6Γ M) (intSeriesC_eisenstein6_ne_zero K)⟩

private def δ (c : ZMod M) : F̄ :=
  ⟨intSeriesC K (X.d c) / intSeriesC K eisenstein4,
    div_mem_qExpFunctionFieldC (DΓ X c) (E4Γ M) (isIntegralQExp_DΓ X c)
      (isIntegralQExp_E4Γ M) (intSeriesC_eisenstein4_ne_zero K)⟩

omit [NeZero M] in
@[simp] private theorem coe_β (c : ZMod M) :
    ((β X K c : F̄) : LaurentSeries K) =
      intSeriesC K (X.b c * eisenstein4) / intSeriesC K eisenstein6 := rfl

omit [NeZero M] in
@[simp] private theorem coe_δ (c : ZMod M) :
    ((δ X K c : F̄) : LaurentSeries K) = intSeriesC K (X.d c) / intSeriesC K eisenstein4 := rfl

local notation "ι" => algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))

omit [NeZero M] in
private theorem coe_algebraMap (r : K) :
    ((ι r : F̄) : LaurentSeries K) = algebraMap K (LaurentSeries K) r := rfl

/-- `w₁`: the `c₄`-normalised toric coordinate, as an element of `F̄`. -/
private def w₁ (ζ : K) (t : (ZMod M)ˣ) : F̄ :=
  ι (-((M : K)⁻¹ ^ 3)) * ∑ c : ZMod M, ι (ζ ^ ((t : ZMod M) * c).val) * β X K c

/-- `w₂`: the `c₄`-normalised `℘ + 6℘² + 2a₄` coordinate, as an element of `F̄`. -/
private def w₂ (ζ : K) (t : (ZMod M)ˣ) : F̄ :=
  ι ((M : K)⁻¹ ^ 5) * ∑ c : ZMod M, ι (ζ ^ ((t : ZMod M) * c).val) * δ X K c

omit [NeZero M] in
private theorem unit_ne_zero (hM : 2 ≤ M) (t : (ZMod M)ˣ) : (t : ZMod M) ≠ 0 := by
  have : Nontrivial (ZMod M) := ZMod.nontrivial_iff.mpr (by omega)
  exact t.ne_zero

private theorem coe_w₁ {ζ : K} (hζ : IsPrimitiveRoot ζ M) (hM : 2 ≤ M)
    (hK : ∀ s : ZMod M, s ≠ 0 →
      (M : LaurentSeries K) ^ 3 * (1 + 12 * (toricPoint K 1 (ζ ^ s.val)).1) =
        ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (X.b c))
    (t : (ZMod M)ˣ) :
    ((w₁ X K ζ t : F̄) : LaurentSeries K) =
      (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1) /
        (tateLaurent K).c₆ := by
  have hid := hK (t : ZMod M) (unit_ne_zero hM t)
  have e : ∀ (r : K) (x : LaurentSeries K), r • x = algebraMap K (LaurentSeries K) r * x := by
    intro r x
    rw [algebraMap_laurent_eq_C]
    exact HahnSeries.C_mul_eq_smul.symm
  simp only [e] at hid
  have hMne := natCast_laurent_ne_zero (M := M) (K := K) hζ
  set Y : LaurentSeries K := 1 + 12 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 with hY
  have hcoe : ((w₁ X K ζ t : F̄) : LaurentSeries K) =
      algebraMap K (LaurentSeries K) (-((M : K)⁻¹ ^ 3)) *
        ∑ c : ZMod M, algebraMap K (LaurentSeries K) (ζ ^ ((t : ZMod M) * c).val) *
          (intSeriesC K (X.b c * eisenstein4) / intSeriesC K eisenstein6) := by
    simp only [w₁, IntermediateField.coe_mul, IntermediateField.coe_sum, coe_algebraMap, coe_β]
  have hsum : ∑ c : ZMod M, algebraMap K (LaurentSeries K) (ζ ^ ((t : ZMod M) * c).val) *
      (intSeriesC K (X.b c * eisenstein4) / intSeriesC K eisenstein6) =
      (M : LaurentSeries K) ^ 3 * Y * ((tateLaurent K).c₄ / -(tateLaurent K).c₆) := by
    rw [hid, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_mul, intSeriesC_eisenstein4 K, intSeriesC_eisenstein6 K]
    ring
  rw [hcoe, hsum, map_neg, map_pow, map_inv₀, map_natCast, div_neg, mul_neg, neg_mul_neg,
    ← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hMne, one_pow, one_mul,
    mul_div_assoc', mul_comm Y]

private theorem coe_w₂ {ζ : K} (hζ : IsPrimitiveRoot ζ M) (hM : 2 ≤ M)
    (hK : ∀ s : ZMod M, s ≠ 0 →
      (M : LaurentSeries K) ^ 5 *
          ((toricPoint K 1 (ζ ^ s.val)).1 + 6 * (toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
            2 * (tateLaurent K).a₄) =
        ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (X.d c))
    (t : (ZMod M)ˣ) :
    ((w₂ X K ζ t : F̄) : LaurentSeries K) =
      ((toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 +
          6 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 ^ 2 + 2 * (tateLaurent K).a₄) /
        (tateLaurent K).c₄ := by
  have hid := hK (t : ZMod M) (unit_ne_zero hM t)
  have e : ∀ (r : K) (x : LaurentSeries K), r • x = algebraMap K (LaurentSeries K) r * x := by
    intro r x
    rw [algebraMap_laurent_eq_C]
    exact HahnSeries.C_mul_eq_smul.symm
  simp only [e] at hid
  have hMne := natCast_laurent_ne_zero (M := M) (K := K) hζ
  set Y : LaurentSeries K := (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 +
      6 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 ^ 2 + 2 * (tateLaurent K).a₄ with hY
  have hcoe : ((w₂ X K ζ t : F̄) : LaurentSeries K) =
      algebraMap K (LaurentSeries K) ((M : K)⁻¹ ^ 5) *
        ∑ c : ZMod M, algebraMap K (LaurentSeries K) (ζ ^ ((t : ZMod M) * c).val) *
          (intSeriesC K (X.d c) / intSeriesC K eisenstein4) := by
    simp only [w₂, IntermediateField.coe_mul, IntermediateField.coe_sum, coe_algebraMap, coe_δ]
  have hsum : ∑ c : ZMod M, algebraMap K (LaurentSeries K) (ζ ^ ((t : ZMod M) * c).val) *
      (intSeriesC K (X.d c) / intSeriesC K eisenstein4) =
      (M : LaurentSeries K) ^ 5 * Y / (tateLaurent K).c₄ := by
    rw [hid, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_eisenstein4 K]
    ring
  rw [hcoe, hsum, map_pow, map_inv₀, map_natCast, mul_div_assoc, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hMne, one_pow, one_mul]

variable {ρ : Gamma0 M →*
  (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
    qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))}

omit [NeZero M] in
private theorem ρ_β (hρ : IsDiamondPullbackModL K M ⊥ ρ) (γ : Gamma0 M) (c : ZMod M) :
    ρ γ (β X K (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) = β X K c := by
  apply Subtype.ext
  rw [coe_β]
  exact hρ.coe_apply_eq γ (f := f6 X c) (g := E6Γ M)
    (f₁ := f6 X (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (g₁ := E6Γ M)
    (pf := X.b c * eisenstein4) (pg := eisenstein6)
    (pf₁ := X.b (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)) * eisenstein4) (pg₁ := eisenstein6)
    (isIntegralQExp_f6 X c) (isIntegralQExp_E6Γ M)
    (isIntegralQExp_f6 X (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (isIntegralQExp_E6Γ M)
    (f6_slash X c γ γ.2).symm (by rw [coe_E6Γ, E6_slash]) (intSeriesC_eisenstein6_ne_zero K)
    (coe_β X K (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)))

omit [NeZero M] in
private theorem ρ_δ (hρ : IsDiamondPullbackModL K M ⊥ ρ) (γ : Gamma0 M) (c : ZMod M) :
    ρ γ (δ X K (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) = δ X K c := by
  apply Subtype.ext
  rw [coe_δ]
  exact hρ.coe_apply_eq γ (f := DΓ X c) (g := E4Γ M)
    (f₁ := DΓ X (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (g₁ := E4Γ M)
    (pf := X.d c) (pg := eisenstein4)
    (pf₁ := X.d (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (pg₁ := eisenstein4)
    (isIntegralQExp_DΓ X c) (isIntegralQExp_E4Γ M)
    (isIntegralQExp_DΓ X (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (isIntegralQExp_E4Γ M)
    (D_slash X c γ γ.2).symm (by rw [coe_E4Γ, E4_slash]) (intSeriesC_eisenstein4_ne_zero K)
    (coe_δ X K (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)))

omit [NeZero M] in
private theorem coe_gamma0Units_inv (γ : Gamma0 M) :
    (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) =
      (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) := rfl

private theorem sum_reindex (ζ : K) (G : ZMod M → F̄) (t : ZMod M) (u : (ZMod M)ˣ) :
    ∑ c : ZMod M, ι (ζ ^ (t * c).val) * G (c * (u : ZMod M)) =
      ∑ c : ZMod M, ι (ζ ^ ((t * (u⁻¹ : (ZMod M)ˣ)) * c).val) * G c := by
  have h : ∀ c : ZMod M, ι (ζ ^ (t * c).val) * G (c * (u : ZMod M)) =
      (fun x => ι (ζ ^ ((t * (u⁻¹ : (ZMod M)ˣ)) * x).val) * G x)
        (Units.mulRight u c) := by
    intro c
    show _ = ι (ζ ^ ((t * (u⁻¹ : (ZMod M)ˣ)) * (c * (u : ZMod M))).val) * G (c * (u : ZMod M))
    congr 4
    rw [mul_assoc, ← mul_assoc ((u⁻¹ : (ZMod M)ˣ) : ZMod M),
      mul_comm ((u⁻¹ : (ZMod M)ˣ) : ZMod M) c, mul_assoc c, Units.inv_mul, mul_one]
  rw [Finset.sum_congr rfl fun c _ => h c]
  exact Equiv.sum_comp (Units.mulRight u)
    (fun x => ι (ζ ^ ((t * (u⁻¹ : (ZMod M)ˣ)) * x).val) * G x)

private theorem ρ_w₁ (hρ : IsDiamondPullbackModL K M ⊥ ρ) (ζ : K) (γ : Gamma0 M)
    (t : (ZMod M)ˣ) :
    ρ γ (w₁ X K ζ t) = w₁ X K ζ (t * (CohCarrier.gamma0Units M γ)⁻¹) := by
  have key : ∀ c : ZMod M, ρ γ (β X K c) =
      β X K (c * ((CohCarrier.gamma0Units M γ : (ZMod M)ˣ) : ZMod M)) := by
    intro c
    have h := ρ_β X K hρ γ (c * ((CohCarrier.gamma0Units M γ : (ZMod M)ˣ) : ZMod M))
    rwa [mul_assoc, ← coe_gamma0Units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      mul_one] at h
  rw [w₁, map_mul, AlgEquiv.commutes, map_sum]
  simp_rw [map_mul, AlgEquiv.commutes, key]
  rw [sum_reindex K ζ (fun c => β X K c) (t : ZMod M) (CohCarrier.gamma0Units M γ), w₁,
    Units.val_mul]

private theorem ρ_w₂ (hρ : IsDiamondPullbackModL K M ⊥ ρ) (ζ : K) (γ : Gamma0 M)
    (t : (ZMod M)ˣ) :
    ρ γ (w₂ X K ζ t) = w₂ X K ζ (t * (CohCarrier.gamma0Units M γ)⁻¹) := by
  have key : ∀ c : ZMod M, ρ γ (δ X K c) =
      δ X K (c * ((CohCarrier.gamma0Units M γ : (ZMod M)ˣ) : ZMod M)) := by
    intro c
    have h := ρ_δ X K hρ γ (c * ((CohCarrier.gamma0Units M γ : (ZMod M)ˣ) : ZMod M))
    rwa [mul_assoc, ← coe_gamma0Units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      mul_one] at h
  rw [w₂, map_mul, AlgEquiv.commutes, map_sum]
  simp_rw [map_mul, AlgEquiv.commutes, key]
  rw [sum_reindex K ζ (fun c => δ X K c) (t : ZMod M) (CohCarrier.gamma0Units M γ), w₂,
    Units.val_mul]

end Field

end ToricPointDict

/-! ## The two headlines -/

open ToricPointDict

universe u

/-- The two-level toric-point dictionary in the `q`-expansion function field of
`Γ_H(M, ⊥)`, with its diamond equivariance. -/
theorem exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ w₁ w₂ : (ZMod M)ˣ → qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
      (∀ t : (ZMod M)ˣ, (w₁ t : LaurentSeries K) =
        (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1) /
          (tateLaurent K).c₆) ∧
      (∀ t : (ZMod M)ˣ, (w₂ t : LaurentSeries K) =
        ((toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 +
            6 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄) ∧
      ∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ (γ : CongruenceSubgroup.Gamma0 M) (t : (ZMod M)ˣ),
          ρ γ (w₁ t) = w₁ (t * (CohCarrier.gamma0Units M γ)⁻¹) ∧
            ρ γ (w₂ t) = w₂ (t * (CohCarrier.gamma0Units M γ)⁻¹) := by
  have : NeZero M := ⟨by omega⟩
  obtain ⟨B, D, b, d, hb, hd, hslash, hK⟩ :=
    ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum (M := M)
  let X : ToricPointDict.FB M :=
    ⟨B, D, b, d, hb, hd, fun c γ hγ => (hslash c γ hγ).1, fun c γ hγ => (hslash c γ hγ).2⟩
  have hK₁ := fun s hs => (hK K ζ hζ s hs).1
  have hK₂ := fun s hs => (hK K ζ hζ s hs).2
  exact ⟨ToricPointDict.w₁ X K ζ, ToricPointDict.w₂ X K ζ,
    fun t => ToricPointDict.coe_w₁ (X := X) (K := K) hζ hM hK₁ t,
    fun t => ToricPointDict.coe_w₂ (X := X) (K := K) hζ hM hK₂ t,
    fun ρ hρ γ t => ⟨ToricPointDict.ρ_w₁ (X := X) (K := K) hρ ζ γ t,
      ToricPointDict.ρ_w₂ (X := X) (K := K) hρ ζ γ t⟩⟩

/-- The `Γ₁(M)`-level twin: the two normalised toric coordinates at `t = 1` lie
in the `q`-expansion function field of `Γ₁(M)`. -/
theorem c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 ζ).1) / (tateLaurent K).c₆ ∈
        qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) ∧
      ((toricPoint K 1 ζ).1 + 6 * (toricPoint K 1 ζ).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄ ∈
        qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) := by
  have : NeZero M := ⟨by omega⟩
  obtain ⟨B, D, b, d, hb, hd, hslash, hK⟩ :=
    ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum (M := M)
  let X : ToricPointDict.FB M :=
    ⟨B, D, b, d, hb, hd, fun c γ hγ => (hslash c γ hγ).1, fun c γ hγ => (hslash c γ hγ).2⟩
  have hcoe₁ := ToricPointDict.coe_w₁ (X := X) (K := K) hζ hM
    (fun s hs => (hK K ζ hζ s hs).1) (1 : (ZMod M)ˣ)
  have hcoe₂ := ToricPointDict.coe_w₂ (X := X) (K := K) hζ hM
    (fun s hs => (hK K ζ hζ s hs).2) (1 : (ZMod M)ˣ)
  have hval : (1 : ZMod M).val = 1 := ZMod.val_one'' (by omega)
  simp only [Units.val_one, hval, pow_one] at hcoe₁ hcoe₂
  refine ⟨?_, ?_⟩
  · rw [← hcoe₁, ← CohCarrier.GammaH_bot M]
    exact (ToricPointDict.w₁ X K ζ 1).2
  · rw [← hcoe₂, ← CohCarrier.GammaH_bot M]
    exact (ToricPointDict.w₂ X K ζ 1).2

end ModularCurve

end
