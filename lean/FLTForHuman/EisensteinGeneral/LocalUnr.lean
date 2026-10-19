/-
  The local twisted integral at an unramified place: the two headlines, with the
  machinery they need.

  `untwisted χ s` is the `A = B = 1` specialization of Set A's local integrand:
  `1` on the integer ring `𝒪_v` and `charExt χ⁻¹ y · |y|^{-(2s+1)}` off it.  Over it the
  two headlines read: `integrable_twisted_and_integral_norm_eq` — the integrand
  `untwisted χ s · ψ(-(ξ·))` is `L¹` and the integral of its absolute value is
  `μ(𝒪) · (1 - ‖χϖ‖ q^{-(2s+1)}) · (1 - ‖χϖ‖ q^{-2s})⁻¹`, the geometric series in
  `q^{-2s}` produced by the shells `|x| = q^{-k}` on which `untwisted` is constant; and
  `integral_twisted_eq_zero_of_exp_lt` — it vanishes once the additive character's level
  `n` is below `|ξ|`, because translating the integrand by a well-chosen `t` of valuation
  `≤ 1` multiplies the integral by `ψ x₀ ≠ 1`.

  This is the **listed** module of the set (WORKORDER-E2): its two statements are copied
  verbatim from the pin's `Theorems/` wrappers
  (`Thm_EisensteinGeneral_LocalUnr_{integrable_twisted_and_integral_norm_eq,
  integral_twisted_eq_zero_of_exp_lt}.lean`), which are the statement authority the
  checker diffs.  Unlike Set A's engine, this machinery has no other consumer, so it is
  written here, public, at the pin names, in `namespace
  EisensteinGeneral.TwistedUnramifiedLocal` — the pin's `P2MW.S_…TwistedUnramifiedLocal`
  keeping its meaningful half, as every engine does.  The pin's two `S_` files share
  `untwisted`, `untwisted_of_le` and `untwisted_of_lt`; they are written once here.

  Proofs are the pin's, with the substitution of three declarations for landed port
  lemmas (never re-proved): `isCompact_integers`
  (`NumberField.TateGlobal.LocalZetaUnramified.isCompact_integers`),
  `norm_addChar_of_level` and `modulus_eq_of_valued_eq`
  (`EisensteinGeneral.TwistedSmoothLocal`, the Set A engine `LocalTwisted.lean`).  The
  pin's `AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion`
  is the port's
  `NumberField.TateGlobal.WeylUnramified.integral_unramifiedWeylIntegrand_adicCompletion`,
  and the pin's own `isOpen_setOf_valued_le` that `isOpen_ball` consumes is the port's
  `NumberField.AdelicLevel.isOpen_setOf_valued_le` (same signature).
  The pin's `Elab.async` and `attribute [-instance]`/`[-simp]` preludes and all `p2m_*`
  scaffolding are not transcribed, and no heartbeats cap is set.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`, mathlib `v4.34.0`.
-/
import FLTForHuman.EisensteinGeneral.LocalTwisted
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import FLTForHuman.NumberTheory.NumberField.TateGlobal.LocalZetaUnramified
import FLTForHuman.NumberTheory.NumberField.TateGlobal.WeylUnramified

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField

namespace EisensteinGeneral

namespace TwistedUnramifiedLocal

open IsDedekindDomain.HeightOneSpectrum Filter Topology
open LanglandsTunnell.TateLocal NumberField.AdelicLevel
open NumberField.TateGlobal.LocalZetaUnramified

section Auxiliary

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

-- pin: valued_uniformizer_zpow (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:23)
theorem valued_uniformizer_zpow (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℤ) :
    Valued.v ((ϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = WithZero.exp (-k) := by
  have hϖ' : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hϖ
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ', ← WithZero.exp_zsmul]
  congr 1
  simp

-- pin: isOpen_ball (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:31)
theorem isOpen_ball (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℤ) :
    IsOpen {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((ϖ ^ (-k) : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 := Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizer_zpow ϖ hϖ, neg_neg] at h
  exact h

-- pin: measureReal_integers_pos (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:44)
theorem measureReal_integers_pos [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] :
    0 < μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [measureReal_def, ENNReal.toReal_pos_iff]
  exact ⟨(Valued.isOpen_valuationSubring _).measure_pos μ
      ⟨0, (v.adicCompletionIntegers F).zero_mem⟩,
    (isCompact_integers (F := F) (v := v)).measure_lt_top⟩

-- pin: continuous_addChar_of_level (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:52)
theorem continuous_addChar_of_level (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmem : (fun y => y - x) ⁻¹' {y : v.adicCompletion F | Valued.v y ≤ WithZero.exp n} ∈ 𝓝 x := by
    apply ((isOpen_ball ϖ hϖ n).preimage (continuous_id.sub continuous_const)).mem_nhds
    simp
  have hev : (fun _ : v.adicCompletion F => ψ x) =ᶠ[𝓝 x] ψ := by
    filter_upwards [hmem] with y hy
    have hy' : ψ (y - x) = 1 := hψn _ hy
    calc ψ x = ψ (y - x) * ψ x := by rw [hy', one_mul]
      _ = ψ (y - x + x) := (AddChar.map_add_eq_mul ψ _ _).symm
      _ = ψ y := by rw [sub_add_cancel]
  exact (continuousAt_congr hev).mp continuousAt_const

-- pin: untwisted (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:108)
noncomputable def untwisted (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (x : v.adicCompletion F) : ℂ :=
  (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x

-- pin: untwisted_of_le (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:114)
theorem untwisted_of_le (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) {x : v.adicCompletion F}
    (hx : Valued.v x ≤ 1) : untwisted χ s x = 1 := by
  have hmem : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hx
  have hnot : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := fun h => h hmem
  rw [untwisted, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, add_zero]

-- pin: untwisted_of_lt (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:120)
theorem untwisted_of_lt (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) {x : v.adicCompletion F}
    (hx : 1 < Valued.v x) :
    untwisted χ s x = charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hnot : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun h => not_le.mpr hx h
  have hmem : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := hnot
  rw [untwisted, Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem, zero_add]

-- pin: norm_mul_natCast_cpow (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:127)
theorem norm_mul_natCast_cpow (c w : ℂ) :
    ‖c * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ w‖ = ‖c‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ w.re := by
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN]

-- pin: re_neg_two_mul_add_one (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:133)
theorem re_neg_two_mul_add_one (s : ℂ) : (-(2 * s + 1)).re = -(2 * s.re + 1) := by
  simp

-- pin: integrable_untwisted (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:136)
theorem integrable_untwisted [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    Integrable (untwisted χ s) μ := by
  have hN1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hval :
      ∫ x, untwisted χ s x ∂μ
        = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
    NumberField.TateGlobal.WeylUnramified.integral_unramifiedWeylIntegrand_adicCompletion
      F v μ ϖ hϖ χ hχ s hs
  have hre2 : (-(2 * s)).re = -(2 * s.re) := by simp
  have hre3 : (-(2 * s + 1)).re = -(2 * s.re) + (-1) := by
    rw [re_neg_two_mul_add_one]
    ring
  have ha : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖
      = ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    rw [norm_mul_natCast_cpow, hre2]
  have hb : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))‖
      ≤ ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ := by
    rw [norm_mul_natCast_cpow, hre3, ha, Real.rpow_add hN, Real.rpow_neg_one]
    have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    have h2 : 0 ≤ ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hN.le _)
    calc ‖((χ ϖ : ℂˣ) : ℂ)‖ * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))
            * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹)
          = ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))
            * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by ring
      _ ≤ ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) * 1 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := mul_one _
  have hne1 : (1 : ℂ) - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)) ≠ 0 := by
    refine sub_ne_zero.mpr fun h => ?_
    have h' := congrArg (fun z : ℂ => ‖z‖) h
    simp only [norm_one] at h'
    linarith [hb.trans_lt hs]
  have hne2 : ((1 : ℂ) - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ ≠ 0 := by
    refine inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
    have h' := congrArg (fun z : ℂ => ‖z‖) h
    simp only [norm_one] at h'
    linarith
  have hne0 : ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (measureReal_integers_pos μ).ne'
  by_contra hni
  exact mul_ne_zero (mul_ne_zero hne0 hne1) hne2 (hval.symm.trans (integral_undef hni))

-- pin: normChar (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:188)
noncomputable def normChar (χ : (v.adicCompletion F)ˣ →* ℂˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun u := Units.mk0 ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (χ u).ne_zero))
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp

-- pin: normChar_apply (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:198)
theorem normChar_apply (χ : (v.adicCompletion F)ˣ →* ℂˣ) (u : (v.adicCompletion F)ˣ) :
    ((normChar χ u : ℂˣ) : ℂ) = ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ) := rfl

-- pin: ofReal_norm_untwisted_mul (S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:201)
theorem ofReal_norm_untwisted_mul (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (ψ : AddChar (v.adicCompletion F) ℂ) (hψ1 : ∀ y, ‖ψ y‖ = 1) (ξ x : v.adicCompletion F) :
    ((‖untwisted χ s x * ψ (-(ξ * x))‖ : ℝ) : ℂ) = untwisted (normChar χ) (s.re : ℂ) x := by
  rw [norm_mul, hψ1, mul_one]
  by_cases hx : Valued.v x ≤ 1
  · rw [untwisted_of_le χ s hx, untwisted_of_le (normChar χ) _ hx, norm_one, Complex.ofReal_one]
  · rw [not_le] at hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hx
      exact WithZero.not_lt_zero _ hx
    have hm : (0 : ℝ) < ((modulus x : NNReal) : ℝ) := NNReal.coe_pos.mpr (modulus_pos hx0)
    rw [untwisted_of_lt χ s hx, untwisted_of_lt (normChar χ) _ hx, charExt_of_ne_zero _ hx0,
      charExt_of_ne_zero _ hx0, MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
      Units.val_inv_eq_inv_val, normChar_apply, norm_mul, norm_inv,
      Complex.norm_cpow_eq_rpow_re_of_pos hm, re_neg_two_mul_add_one,
      show (-(2 * (s.re : ℂ) + 1) : ℂ) = ((-(2 * s.re + 1) : ℝ) : ℂ) from (by push_cast; ring),
      ← Complex.ofReal_cpow hm.le]
    push_cast
    ring

-- pin: charExt_inv_eq_of_valued_eq (S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean:30)
theorem charExt_inv_eq_of_valued_eq (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    {x y : v.adicCompletion F} (hx : x ≠ 0) (hy : y ≠ 0) (h : Valued.v x = Valued.v y) :
    charExt χ⁻¹ x = charExt χ⁻¹ y := by
  have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have hu : Valued.v ((Units.mk0 x hx * (Units.mk0 y hy)⁻¹ : (v.adicCompletion F)ˣ)
      : v.adicCompletion F) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, map_mul, map_inv₀, h,
      mul_inv_cancel₀ hvy]
  have hχeq : χ (Units.mk0 x hx) = χ (Units.mk0 y hy) := by
    have h1 := hχ _ hu
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hy, MonoidHom.inv_apply, MonoidHom.inv_apply,
    hχeq]

-- pin: untwisted_add_of_lt (S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean:64)
theorem untwisted_add_of_lt (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1) (s : ℂ)
    {t x : v.adicCompletion F} (htx : Valued.v t < Valued.v x) (hx : 1 < Valued.v x) :
    untwisted χ s (t + x) = untwisted χ s x := by
  have hv : Valued.v (t + x) = Valued.v x := Valuation.map_add_eq_of_lt_right _ htx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact WithZero.not_lt_zero _ hx
  have htx0 : t + x ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact hx0 ((Valuation.zero_iff _).mp hv.symm)
  rw [untwisted_of_lt χ s (hv ▸ hx), untwisted_of_lt χ s hx,
    charExt_inv_eq_of_valued_eq χ hχ htx0 hx0 hv,
    EisensteinGeneral.TwistedSmoothLocal.modulus_eq_of_valued_eq hv]

-- pin: untwisted_add_of_le_one (S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean:80)
theorem untwisted_add_of_le_one (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1) (s : ℂ)
    {t : v.adicCompletion F} (ht : Valued.v t ≤ 1) (x : v.adicCompletion F) :
    untwisted χ s (t + x) = untwisted χ s x := by
  by_cases hx : Valued.v x ≤ 1
  · have htx : Valued.v (t + x) ≤ 1 := (Valuation.map_add_le_max' _ t x).trans (max_le ht hx)
    rw [untwisted_of_le χ s htx, untwisted_of_le χ s hx]
  · rw [not_le] at hx
    exact untwisted_add_of_lt χ hχ s (lt_of_le_of_lt ht hx) hx

end Auxiliary

end TwistedUnramifiedLocal

end EisensteinGeneral

open EisensteinGeneral.TwistedUnramifiedLocal
open LanglandsTunnell.TateLocal NumberField.AdelicLevel Filter Topology

-- pin: EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq (Thm_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:11)
theorem EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (ξ : v.adicCompletion F) :
    Integrable (fun x => (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
            * ψ (-(ξ * x)))) μ ∧
      ∫ x, ‖(((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
            * ψ (-(ξ * x)))‖ ∂μ
        = μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F))
            * (1 - ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)))
            * (1 - ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹ := by
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  have hψc : Continuous ψ := continuous_addChar_of_level ϖ hϖ ψ n hψn
  have hψ1 : ∀ y, ‖ψ y‖ = 1 := EisensteinGeneral.TwistedSmoothLocal.norm_addChar_of_level ψ n hψn
  have hint : Integrable (untwisted χ s) μ := integrable_untwisted μ ϖ hϖ χ hχ s hs
  have hmeas : AEStronglyMeasurable (fun x : v.adicCompletion F => ψ (-(ξ * x))) μ :=
    (hψc.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable
  have hintψ : Integrable (fun x => untwisted χ s x * ψ (-(ξ * x))) μ :=
    hint.mul_bdd hmeas (Eventually.of_forall fun x => (hψ1 _).le)
  refine ⟨hintψ, ?_⟩
  have hχ' : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → normChar χ u = 1 := by
    intro u hu
    ext
    rw [normChar_apply, hχ u hu, Units.val_one, norm_one, Complex.ofReal_one]
  have hre1 : (-(2 * (s.re : ℂ))).re = -(2 * s.re) := by simp
  have hre2 : (-(2 * s)).re = -(2 * s.re) := by simp
  have hs' : ‖((normChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ)))‖ < 1 := by
    rw [norm_mul_natCast_cpow, normChar_apply, Complex.norm_real, norm_norm, hre1]
    rw [norm_mul_natCast_cpow, hre2] at hs
    exact hs
  have hval :
      ∫ x, untwisted (normChar χ) (s.re : ℂ) x ∂μ
        = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((normChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ) + 1)))
          * (1 - ((normChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ))))⁻¹ :=
    NumberField.TateGlobal.WeylUnramified.integral_unramifiedWeylIntegrand_adicCompletion F v μ ϖ hϖ
      (normChar χ) hχ' (s.re : ℂ) hs'
  have e1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ) + 1))
      = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)) : ℝ) := by
    rw [Complex.ofReal_cpow hN.le, Complex.ofReal_natCast]
    congr 1
    push_cast
    ring
  have e2 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ)))
      = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) : ℝ) := by
    rw [Complex.ofReal_cpow hN.le, Complex.ofReal_natCast]
    congr 1
    push_cast
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  show ∫ x, ((‖untwisted χ s x * ψ (-(ξ * x))‖ : ℝ) : ℂ) ∂μ = _
  simp_rw [ofReal_norm_untwisted_mul χ s ψ hψ1 ξ]
  rw [hval, normChar_apply, e1, e2]
  push_cast
  ring

-- pin: EisensteinGeneral.LocalUnr.integral_twisted_eq_zero_of_exp_lt (Thm_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean:12)
theorem EisensteinGeneral.LocalUnr.integral_twisted_eq_zero_of_exp_lt
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (hξ : WithZero.exp n < Valued.v ξ) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
          * ψ (-(ξ * x))) ∂μ
      = 0 := by
  have _ := hϖ
  have _ := hs
  have _ := hψn
  obtain ⟨x₀, hx₀, hne⟩ := hψn'
  have hξ0 : Valued.v ξ ≠ 0 := by
    intro h
    rw [h] at hξ
    exact WithZero.not_lt_zero _ hξ
  have hξne : ξ ≠ 0 := (Valuation.ne_zero_iff _).mp hξ0
  have hξ1 : WithZero.exp (n + 1) ≤ Valued.v ξ := by
    rw [← WithZero.exp_log hξ0] at hξ ⊢
    rw [WithZero.exp_lt_exp] at hξ
    exact WithZero.exp_le_exp.mpr (by omega)
  set t : v.adicCompletion F := -(ξ⁻¹ * x₀) with ht_def
  have hξt : -(ξ * t) = x₀ := by rw [ht_def, mul_neg, neg_neg, mul_inv_cancel_left₀ hξne]
  have ht1 : Valued.v t ≤ 1 := by
    rw [ht_def, Valuation.map_neg, map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.mpr hξ0), mul_one]
    exact hx₀.trans hξ1
  have hpt : ∀ x, untwisted χ s (t + x) * ψ (-(ξ * (t + x))) = ψ x₀ * (untwisted χ s x * ψ (-(ξ * x))) := by
    intro x
    rw [untwisted_add_of_le_one χ hχ s ht1 x, mul_add, neg_add, AddChar.map_add_eq_mul, hξt]
    ring
  have htrans : ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ = ψ x₀ * ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ := by
    calc ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ
        = ∫ x, untwisted χ s (t + x) * ψ (-(ξ * (t + x))) ∂μ :=
          (integral_add_left_eq_self (fun x => untwisted χ s x * ψ (-(ξ * x))) t).symm
      _ = ∫ x, ψ x₀ * (untwisted χ s x * ψ (-(ξ * x))) ∂μ := by simp_rw [hpt]
      _ = ψ x₀ * ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ := integral_const_mul _ _
  have h1ne : (1 : ℂ) - ψ x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hprod : ((1 : ℂ) - ψ x₀) * ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ = 0 := by
    rw [sub_mul, one_mul, ← htrans, sub_self]
  show ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ = 0
  exact (mul_eq_zero.mp hprod).resolve_left h1ne
