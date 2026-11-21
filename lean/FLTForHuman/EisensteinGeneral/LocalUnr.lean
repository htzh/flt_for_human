/-
  The local twisted integral at an unramified place: the three headlines, with the
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

  The third headline, `integral_twisted_eq` — the twisted local integral of the unramified
  sector against the additive character of level `n`, at `ξ` of valuation
  `WithZero.exp (n - M)`, is `μ(𝒪) · (1 - χϖ·q^{-(2s+1)}) · ∑_{k ≤ M} (χϖ·q^{-2s})^k`: the
  finite geometric tail that the Eisenstein functional equation reads — is transcribed from
  `S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean` (601 lines) below, together with the
  shell decomposition it needs (`∫` over the annuli `q^{-(k+1)} < |x| ≤ q^{-k}` of `untwisted`,
  each constant, against the ball integral of `ψ(-(ξ·))` from the Tate Fourier identity).
  The pin states all 26 of its engine declarations `private`; they are `private` here too, so
  `check_port` sees only the row (the private surface is covered by the hash diff recorded in
  `lean/tmp/af99/AF99E-REPORT.md`). Of those 26, sixteen are **reused** rather than re-proved,
  because this module (or its import closure) already carries the pin's statement at the pin's
  name — see the block comment above `integral_twisted_eq`; the remaining ten are written here.
  That pin states the row twice, the private engine at `:370` and its one-line `solution` at
  `:580`, with identical statements; the port carries both (as it carries an engine and a row
  for the other two headlines), so `dedup --within` reads one cluster — the pin's own pair.

  Heartbeat probe, never installed (playbook §3.5, FR-0225): silent at 25000, aborts at 20000
  (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N`); the peak is that pin row.  No
  `set_option maxHeartbeats` is carried.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`, mathlib `v4.34.0`.

  spec-pin: P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean
-/
import FLTForHuman.EisensteinGeneral.LocalTwisted
import FLTForHuman.LanglandsTunnell.TateLocal.AddCharLevel
import FLTForHuman.LanglandsTunnell.TateLocal.BallVolume
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

-- pin: valued_uniformizer_zpow (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:23)
theorem valued_uniformizer_zpow (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℤ) :
    Valued.v ((ϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = WithZero.exp (-k) := by
  have hϖ' : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hϖ
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ', ← WithZero.exp_zsmul]
  congr 1
  simp

-- pin: isOpen_ball (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:31)
theorem isOpen_ball (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℤ) :
    IsOpen {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((ϖ ^ (-k) : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 := Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizer_zpow ϖ hϖ, neg_neg] at h
  exact h

-- pin: measureReal_integers_pos (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:44)
theorem measureReal_integers_pos [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] :
    0 < μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [measureReal_def, ENNReal.toReal_pos_iff]
  exact ⟨(Valued.isOpen_valuationSubring _).measure_pos μ
      ⟨0, (v.adicCompletionIntegers F).zero_mem⟩,
    (isCompact_integers (F := F) (v := v)).measure_lt_top⟩

-- pin: continuous_addChar_of_level (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:52)
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

-- pin: untwisted (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:108)
noncomputable def untwisted (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (x : v.adicCompletion F) : ℂ :=
  (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x

-- pin: untwisted_of_le (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:114)
theorem untwisted_of_le (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) {x : v.adicCompletion F}
    (hx : Valued.v x ≤ 1) : untwisted χ s x = 1 := by
  have hmem : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hx
  have hnot : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := fun h => h hmem
  rw [untwisted, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, add_zero]

-- pin: untwisted_of_lt (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:120)
theorem untwisted_of_lt (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) {x : v.adicCompletion F}
    (hx : 1 < Valued.v x) :
    untwisted χ s x = charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hnot : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun h => not_le.mpr hx h
  have hmem : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := hnot
  rw [untwisted, Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem, zero_add]

-- pin: norm_mul_natCast_cpow (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:127)
theorem norm_mul_natCast_cpow (c w : ℂ) :
    ‖c * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ w‖ = ‖c‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ w.re := by
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN]

-- pin: re_neg_two_mul_add_one (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:133)
theorem re_neg_two_mul_add_one (s : ℂ) : (-(2 * s + 1)).re = -(2 * s.re + 1) := by
  simp

-- pin: integrable_untwisted (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:136)
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

-- pin: normChar (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:188)
noncomputable def normChar (χ : (v.adicCompletion F)ˣ →* ℂˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun u := Units.mk0 ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (χ u).ne_zero))
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp

-- pin: normChar_apply (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:198)
theorem normChar_apply (χ : (v.adicCompletion F)ˣ →* ℂˣ) (u : (v.adicCompletion F)ˣ) :
    ((normChar χ u : ℂˣ) : ℂ) = ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ) := rfl

-- pin: ofReal_norm_untwisted_mul (P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:201)
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

-- pin: charExt_inv_eq_of_valued_eq (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean:30)
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

-- pin: untwisted_add_of_lt (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean:64)
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

-- pin: untwisted_add_of_le_one (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean:80)
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

/-  The shell decomposition of the twisted integral.

    Ten of the pin's 27 declarations are written here — the ones no existing declaration of
    the port answers to.  The other sixteen are reused at the pin's name, each verified by
    `statement_db`'s statement hash against the pin's row (`lean/tmp/af99/diff-AF99E.py`):

    * in this module, public: `valued_uniformizer_zpow`, `isOpen_ball`,
      `measureReal_integers_pos`, `charExt_inv_eq_of_valued_eq`, `continuous_addChar_of_level`,
      `untwisted`, `untwisted_of_le`, `untwisted_of_lt`, `untwisted_add_of_lt`,
      `norm_mul_natCast_cpow`, `re_neg_two_mul_add_one`, `integrable_untwisted`;
    * in the import closure: `isCompact_integers`
      (`NumberField.TateGlobal.LocalZetaUnramified`), `modulus_eq_of_valued_eq` and
      `norm_addChar_of_level` (`EisensteinGeneral.TwistedSmoothLocal`, `LocalTwisted.lean`),
      `ofReal_pow_cpow` (`NumberField.TateGlobal.WeylShell`).

    Two premises are *not* in this module's earlier import list and are added by the wire's
    pin: the Tate Fourier identity `tateFourier_indicator_setOf_valued_sub_le`
    (`LanglandsTunnell/TateLocal/AddCharLevel.lean`) and the ball volume
    `measureReal_setOf_valued_le_exp` (`LanglandsTunnell/TateLocal/BallVolume.lean`).  The
    pin's `modulus_adicCompletion_eq_nnnorm` is the port's
    `NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm` in
    `TateGlobal/NormIntegrable.lean`, already in the closure.  -/
section TwistedShells

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

-- pin: measurableSet_ball (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:33)
private theorem measurableSet_ball [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℤ) :
    MeasurableSet {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((ϖ ^ (-k) : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 := Units.ne_zero _
  have h := (isClosed_setOf_valued_le v _ ht).measurableSet
  rw [valued_uniformizer_zpow ϖ hϖ, neg_neg] at h
  exact h

-- pin: measure_ball_lt_top (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:55)
private theorem measure_ball_lt_top [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℤ) :
    μ {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k} < ⊤ := by
  set t : v.adicCompletion F := ((ϖ ^ (-k) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
    with ht_def
  have ht : t ≠ 0 := Units.ne_zero _
  have hvt : Valued.v t = WithZero.exp k := by
    rw [ht_def, valued_uniformizer_zpow ϖ hϖ, neg_neg]
  have himg : (fun x => x * t) '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k} := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [map_mul, hvt]
      calc Valued.v x * WithZero.exp k ≤ 1 * WithZero.exp k := mul_le_mul_left hx _
        _ = WithZero.exp k := one_mul _
    · intro hy
      refine ⟨y * t⁻¹, ?_, by rw [inv_mul_cancel_right₀ ht]⟩
      rw [map_mul, map_inv₀, hvt, mul_inv_le_iff₀ WithZero.exp_pos, one_mul]
      exact hy
  rw [← himg]
  exact ((isCompact_integers (F := F) (v := v)).image
    (continuous_id.mul continuous_const)).measure_lt_top

-- pin: valued_eq_exp_of_lt_of_le (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:91)
private theorem valued_eq_exp_of_lt_of_le {x : v.adicCompletion F} {i : ℤ}
    (h1 : WithZero.exp i < Valued.v x) (h2 : Valued.v x ≤ WithZero.exp (i + 1)) :
    Valued.v x = WithZero.exp (i + 1) := by
  have hx0 : Valued.v x ≠ 0 := by
    intro h
    rw [h] at h1
    exact WithZero.not_lt_zero _ h1
  rw [← WithZero.exp_log hx0] at h1 h2 ⊢
  rw [WithZero.exp_lt_exp] at h1
  rw [WithZero.exp_le_exp] at h2
  rw [WithZero.exp_inj]
  omega

-- pin: toAdd_unzero_exp (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:104)
private theorem toAdd_unzero_exp (j : ℤ) (h : WithZero.exp j ≠ 0) :
    (WithZero.unzero h).toAdd = j :=
  congrArg Multiplicative.toAdd (WithZero.unzero_coe (x := Multiplicative.ofAdd j) h)

-- pin: coe_modulus_of_valued_eq (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:108)
private theorem coe_modulus_of_valued_eq {x : v.adicCompletion F} {j : ℤ}
    (hx : Valued.v x = WithZero.exp j) :
    ((modulus x : NNReal) : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ j := by
  rw [NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm (F := F) (v := v) x, coe_nnnorm,
    NumberField.FinitePlace.norm_def, hx,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp, NNReal.coe_zpow]
  norm_cast

-- pin: charExt_inv_of_valued_eq (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:121)
private theorem charExt_inv_of_valued_eq (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    {x : v.adicCompletion F} {j : ℕ} (hx : Valued.v x = WithZero.exp (j : ℤ)) :
    charExt χ⁻¹ x = ((χ ϖ : ℂˣ) : ℂ) ^ j := by
  have hϖ' : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hϖ
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  have hu : Valued.v ((Units.mk0 x hx0 * ϖ ^ j : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = 1 := by
    rw [Units.val_mul, Units.val_mk0, Units.val_pow_eq_pow_val, map_mul, map_pow, hx, hϖ',
      ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj]
    simp
  have h1 : χ (Units.mk0 x hx0 * ϖ ^ j) = 1 := hχ _ hu
  rw [map_mul, map_pow] at h1
  rw [charExt_of_ne_zero _ hx0, MonoidHom.inv_apply, inv_eq_of_mul_eq_one_right h1,
    Units.val_pow_eq_pow_val]

-- pin: untwisted_of_valued_eq (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:256)
private theorem untwisted_of_valued_eq (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1) (s : ℂ)
    {x : v.adicCompletion F} {j : ℕ} (hj : 1 ≤ j) (hx : Valued.v x = WithZero.exp (j : ℤ)) :
    untwisted χ s x
      = (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ j := by
  have hN0 : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := Nat.cast_nonneg _
  have hx1 : 1 < Valued.v x := by
    rw [hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  rw [untwisted_of_lt χ s hx1, charExt_inv_of_valued_eq ϖ hϖ χ hχ hx, coe_modulus_of_valued_eq hx,
    zpow_natCast, NumberField.TateGlobal.WeylShell.ofReal_pow_cpow hN0, Complex.ofReal_natCast,
    mul_pow]

-- pin: setIntegral_ball_addChar (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:270)
private theorem setIntegral_ball_addChar [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (k : ℤ) :
    ∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k}, ψ (-(ξ * x)) ∂μ
      = (μ.real {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k} : ℂ)
          * {y' : v.adicCompletion F | Valued.v y' ≤ WithZero.exp (n + -k)}.indicator
              (fun _ => (1 : ℂ)) (-ξ) := by
  have h3 := tateFourier_indicator_setOf_valued_sub_le F v μ ψ n hψn hψn' 0 (-k) (-ξ)
  simp only [sub_zero, neg_neg, zero_mul, AddChar.map_zero_eq_one, one_mul] at h3
  rw [← h3]
  unfold tateFourier
  rw [← integral_indicator (measurableSet_ball ϖ hϖ k)]
  congr 1
  funext x
  by_cases hx : x ∈ {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul, mul_neg, mul_comm x ξ]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

-- pin: sum_identity (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:354)
private theorem sum_identity {R : Type*} [CommRing R] (a b N c : R) (h : b * N = a) (M : ℕ) :
    c + (∑ i ∈ Finset.range M, b ^ (i + 1) * (N ^ (i + 1) * c - N ^ i * c)
        + b ^ (M + 1) * (0 - N ^ M * c))
      = c * (1 - b) * ∑ k ∈ Finset.range (M + 1), a ^ k := by
  subst h
  induction M with
  | zero =>
      simp
      ring
  | succ m ih =>
      rw [Finset.sum_range_succ (fun i => b ^ (i + 1) * (N ^ (i + 1) * c - N ^ i * c)) m,
        Finset.sum_range_succ (fun k => (b * N) ^ k) (m + 1)]
      linear_combination ih

end TwistedShells

-- pin: integral_twisted_eq (P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:370)
private theorem integral_twisted_eq
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
    (ξ : v.adicCompletion F) (M : ℕ) (hξ : Valued.v ξ = WithZero.exp (n - (M : ℤ))) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
          * ψ (-(ξ * x))) ∂μ
      = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * ∑ k ∈ Finset.range (M + 1),
              (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ k := by
  have hN1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hNC : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨x₀, hx₀, hne⟩ := id hψn'
  have hξ0 : Valued.v ξ ≠ 0 := by
    rw [hξ]
    exact WithZero.exp_ne_zero
  have hξne : ξ ≠ 0 := (Valuation.ne_zero_iff _).mp hξ0
  have hψc : Continuous ψ := continuous_addChar_of_level ϖ hϖ ψ n hψn
  have hψ1 : ∀ y, ‖ψ y‖ = 1 := EisensteinGeneral.TwistedSmoothLocal.norm_addChar_of_level ψ n hψn
  have hmeas : AEStronglyMeasurable (fun x : v.adicCompletion F => ψ (-(ξ * x))) μ :=
    (hψc.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable
  have hintψ : Integrable (fun x => untwisted χ s x * ψ (-(ξ * x))) μ :=
    (integrable_untwisted μ ϖ hϖ χ hχ s hs).mul_bdd hmeas (Eventually.of_forall fun x => (hψ1 _).le)
  have hψint : ∀ k : ℤ, IntegrableOn (fun x : v.adicCompletion F => ψ (-(ξ * x)))
      {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k} μ := by
    intro k
    have hc : IntegrableOn (fun _ : v.adicCompletion F => (1 : ℝ))
        {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k} μ :=
      integrableOn_const (measure_ball_lt_top μ ϖ hϖ k).ne
    exact Integrable.mono' hc hmeas.restrict (Eventually.of_forall fun x => (hψ1 _).le)

  have hBm : MeasurableSet {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)} :=
    measurableSet_ball ϖ hϖ _

  have htail : ∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)}ᶜ,
      untwisted χ s x * ψ (-(ξ * x)) ∂μ = 0 := by
    rw [← integral_indicator hBm.compl]
    set g : v.adicCompletion F → ℂ :=
      {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)}ᶜ.indicator
        fun x => untwisted χ s x * ψ (-(ξ * x)) with hg_def
    set t : v.adicCompletion F := -(ξ⁻¹ * x₀) with ht_def
    have hξt : -(ξ * t) = x₀ := by rw [ht_def, mul_neg, neg_neg, mul_inv_cancel_left₀ hξne]
    have htM : Valued.v t ≤ WithZero.exp ((M + 1 : ℕ) : ℤ) := by
      rw [ht_def, Valuation.map_neg, map_mul, map_inv₀, hξ, inv_mul_le_iff₀ WithZero.exp_pos,
        ← WithZero.exp_add]
      exact hx₀.trans (WithZero.exp_le_exp.mpr (by push_cast; omega))
    have h01 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp ((M + 1 : ℕ) : ℤ) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by push_cast; omega)
    have hpt : ∀ x, g (t + x) = ψ x₀ * g x := by
      intro x
      by_cases hx : Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)
      · have htx : Valued.v (t + x) ≤ WithZero.exp ((M + 1 : ℕ) : ℤ) :=
          (Valuation.map_add_le_max' _ t x).trans (max_le htM hx)
        have hn1 : t + x ∉ {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)}ᶜ :=
          Set.notMem_compl_iff.mpr htx
        have hn2 : x ∉ {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)}ᶜ :=
          Set.notMem_compl_iff.mpr hx
        rw [hg_def, Set.indicator_of_notMem hn1, Set.indicator_of_notMem hn2, mul_zero]
      · rw [not_le] at hx
        have htx : Valued.v t < Valued.v x := lt_of_le_of_lt htM hx
        have hv : Valued.v (t + x) = Valued.v x := Valuation.map_add_eq_of_lt_right _ htx
        have hxmem : x ∈ {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)}ᶜ :=
          fun h => not_le.mpr hx h
        have htxmem : t + x ∈ {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)}ᶜ :=
          fun h => not_le.mpr hx (hv ▸ h)
        rw [hg_def, Set.indicator_of_mem htxmem, Set.indicator_of_mem hxmem,
          untwisted_add_of_lt χ hχ s htx (lt_of_le_of_lt h01 hx), mul_add, neg_add,
          AddChar.map_add_eq_mul, hξt]
        ring
    have htrans : ∫ x, g x ∂μ = ψ x₀ * ∫ x, g x ∂μ := by
      calc ∫ x, g x ∂μ = ∫ x, g (t + x) ∂μ := (integral_add_left_eq_self g t).symm
        _ = ∫ x, ψ x₀ * g x ∂μ := by simp_rw [hpt]
        _ = ψ x₀ * ∫ x, g x ∂μ := integral_const_mul _ _
    have h1ne : (1 : ℂ) - ψ x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hprod : ((1 : ℂ) - ψ x₀) * ∫ x, g x ∂μ = 0 := by
      rw [sub_mul, one_mul, ← htrans, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left h1ne

  have hT : ∀ k : ℕ, k ≤ M →
      ∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (k : ℤ)}, ψ (-(ξ * x)) ∂μ
        = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ k
            * (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ) := by
    intro k hk
    rw [setIntegral_ball_addChar μ ϖ hϖ ψ n hψn hψn' ξ k]
    have hmem : -ξ ∈ {y' : v.adicCompletion F | Valued.v y' ≤ WithZero.exp (n + -(k : ℤ))} := by
      show Valued.v (-ξ) ≤ WithZero.exp (n + -(k : ℤ))
      rw [Valuation.map_neg, hξ, WithZero.exp_le_exp]
      omega
    rw [Set.indicator_of_mem hmem, mul_one, measureReal_setOf_valued_le_exp F v μ k, zpow_natCast]
    push_cast
    ring
  have hTM : ∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)},
      ψ (-(ξ * x)) ∂μ = 0 := by
    rw [setIntegral_ball_addChar μ ϖ hϖ ψ n hψn hψn' ξ ((M + 1 : ℕ) : ℤ)]
    have hnot : -ξ ∉ {y' : v.adicCompletion F | Valued.v y' ≤ WithZero.exp (n + -((M + 1 : ℕ) : ℤ))} := by
      show ¬ (Valued.v (-ξ) ≤ WithZero.exp (n + -((M + 1 : ℕ) : ℤ)))
      rw [Valuation.map_neg, hξ, WithZero.exp_le_exp]
      push_cast
      omega
    rw [Set.indicator_of_notMem hnot, mul_zero]

  set G : ℕ → ℂ := fun k =>
    ∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (k : ℤ)}, untwisted χ s x * ψ (-(ξ * x)) ∂μ
    with hG_def
  have htel : G (M + 1) = G 0 + ∑ i ∈ Finset.range (M + 1), (G (i + 1) - G i) := by
    rw [Finset.sum_range_sub, add_sub_cancel]
  have hG0 : G 0 = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ) := by
    show (∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((0 : ℕ) : ℤ)},
      untwisted χ s x * ψ (-(ξ * x)) ∂μ) = _
    have heq : Set.EqOn (fun x => untwisted χ s x * ψ (-(ξ * x))) (fun x => ψ (-(ξ * x)))
        {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((0 : ℕ) : ℤ)} := by
      intro x hx
      have hx1 : Valued.v x ≤ 1 := by
        have hx' : Valued.v x ≤ WithZero.exp ((0 : ℕ) : ℤ) := hx
        rwa [Nat.cast_zero, WithZero.exp_zero] at hx'
      simp only [untwisted_of_le χ s hx1, one_mul]
    rw [setIntegral_congr_fun (measurableSet_ball ϖ hϖ _) heq, hT 0 (Nat.zero_le M), pow_zero, one_mul]
  have hdiff : ∀ i : ℕ, i < M + 1 → G (i + 1) - G i
      = (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ (i + 1)
        * ((∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((i + 1 : ℕ) : ℤ)},
              ψ (-(ξ * x)) ∂μ)
            - ∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (i : ℤ)}, ψ (-(ξ * x)) ∂μ) := by
    intro i hi
    have hsub : {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (i : ℤ)}
        ⊆ {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((i + 1 : ℕ) : ℤ)} :=
      fun x hx => le_trans hx (WithZero.exp_le_exp.mpr (by push_cast; omega))
    have hshell : Set.EqOn (fun x => untwisted χ s x * ψ (-(ξ * x)))
        (fun x => (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ (i + 1)
          * ψ (-(ξ * x)))
        ({x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((i + 1 : ℕ) : ℤ)}
          \ {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (i : ℤ)}) := by
      intro x hx
      have hx2 : Valued.v x ≤ WithZero.exp ((i : ℤ) + 1) := by
        have hx2' : Valued.v x ≤ WithZero.exp ((i + 1 : ℕ) : ℤ) := hx.1
        exact_mod_cast hx2'
      have hx1 : WithZero.exp (i : ℤ) < Valued.v x := not_le.mp hx.2
      have hvx : Valued.v x = WithZero.exp ((i + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_succ]
        exact valued_eq_exp_of_lt_of_le hx1 hx2
      show untwisted χ s x * ψ (-(ξ * x)) = _
      rw [untwisted_of_valued_eq ϖ hϖ χ hχ s (by omega) hvx]
    show (∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((i + 1 : ℕ) : ℤ)},
        untwisted χ s x * ψ (-(ξ * x)) ∂μ)
      - (∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (i : ℤ)},
        untwisted χ s x * ψ (-(ξ * x)) ∂μ) = _
    rw [← setIntegral_sdiff (measurableSet_ball ϖ hϖ (i : ℤ)) hintψ.integrableOn hsub,
      setIntegral_congr_fun ((measurableSet_ball ϖ hϖ _).diff (measurableSet_ball ϖ hϖ _)) hshell,
      integral_const_mul, setIntegral_sdiff (measurableSet_ball ϖ hϖ (i : ℤ)) (hψint _) hsub]
  have hmid : ∀ i ∈ Finset.range M, G (i + 1) - G i
      = (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ (i + 1)
        * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (i + 1)
              * (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
            - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ i
              * (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)) := by
    intro i hi
    have hi' : i < M := Finset.mem_range.mp hi
    rw [hdiff i (by omega), hT (i + 1) (by omega), hT i (by omega)]
  have hlast : G (M + 1) - G M
      = (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ (M + 1)
        * (0 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ M
              * (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)) := by
    rw [hdiff M (by omega), hTM, hT M le_rfl]

  have hpow : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (1 : ℂ) := by
    rw [← Complex.cpow_add _ _ hNC]
    congr 1
    ring
  rw [Complex.cpow_one] at hpow
  have hba : ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))
      * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
        = ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)) := by
    rw [mul_assoc, ← hpow]
  have key := sum_identity
    (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
    (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
    ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ) hba M
  have hball : ∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)},
      untwisted χ s x * ψ (-(ξ * x)) ∂μ
        = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * ∑ k ∈ Finset.range (M + 1),
              (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ k := by
    have hGM : (∫ x in {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp ((M + 1 : ℕ) : ℤ)},
        untwisted χ s x * ψ (-(ξ * x)) ∂μ) = G (M + 1) := rfl
    rw [hGM, htel, hG0, Finset.sum_range_succ (fun i => G (i + 1) - G i) M, Finset.sum_congr rfl hmid,
      hlast]
    linear_combination key

  show ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ = _
  rw [← integral_add_compl hBm hintψ, htail, add_zero]
  exact hball

end TwistedUnramifiedLocal

end EisensteinGeneral

open EisensteinGeneral.TwistedUnramifiedLocal
open LanglandsTunnell.TateLocal NumberField.AdelicLevel Filter Topology

-- pin: EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq (Theorems/Thm_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean:11)
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

-- pin: EisensteinGeneral.LocalUnr.integral_twisted_eq_zero_of_exp_lt (Theorems/Thm_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean:12)
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

-- pin: EisensteinGeneral.LocalUnr.integral_twisted_eq (Theorems/Thm_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean:11)
theorem EisensteinGeneral.LocalUnr.integral_twisted_eq
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
    (ξ : v.adicCompletion F) (M : ℕ) (hξ : Valued.v ξ = WithZero.exp (n - (M : ℤ))) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
          * ψ (-(ξ * x))) ∂μ
      = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * ∑ k ∈ Finset.range (M + 1),
              (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ k :=
  EisensteinGeneral.TwistedUnramifiedLocal.integral_twisted_eq F v μ ϖ hϖ χ hχ s hs ψ n hψn hψn' ξ M hξ
