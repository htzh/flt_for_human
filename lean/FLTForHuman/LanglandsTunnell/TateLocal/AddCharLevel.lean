/-
  The level of the additive character, and the support of its Fourier transform.

  `psiLocal_eq_one_of_mem_integers`: the local additive character at a finite place is trivial
  on the integers of the completion.  `psiLocal K v` is the standard character `stdAddChar K`
  of `K` composed with the single-place embedding `adeleSingleAt K v`, and `stdAddChar K` is
  `psiQ ∘ adelicTrace` — the trace to `ℚ` followed by `ψ_ℚ = ψ_arch * ψ_fin`.  For
  `x ∈ 𝓞_{K,v}` the trace datum carries the single-place adèle into the integral finite
  adèles of `ℚ`, all of whose components are integral (`finAdeleSingleAt` is supported at `v`,
  where `x` is integral, and is `0` elsewhere); `psiFin` is then `1` by its product formula
  (`psiFin_eq_one_of_forall_mem`), the archimedean factor is `psiArch 0 = 1`, and `ψ_v x = 1`.

  `forall_eq_one_and_exists_ne_one_of_addCharLevel`: `addCharLevel ψ` is the `sSup` of
  `S = {k : ℤ | ψ = 1 on {x | ‖x‖ ≤ exp k}}` (`addCharLevel_def`, in
  `LanglandsTunnell/StandardLocalConstantsAt.lean`), so its defining property holds in both
  directions.  `S` is bounded above — by `log ‖x₁‖` for any `x₁` with `ψ x₁ ≠ 1` — and `ℤ` is
  conditionally complete, so `sSup S ∈ S` (`Int.csSup_mem`); `sSup S + 1 ∉ S` because it
  exceeds the supremum.  That is exactly "`ψ = 1` on the ball of level `addCharLevel ψ`, and
  not on the next ball".

  `tateFourier_indicator_setOf_valued_sub_le`: the Fourier transform
  `tateFourier ψ μ f y = ∫ x, f x * ψ (x * y) ∂μ` of the indicator of the ball
  `{x | ‖x - a‖ ≤ exp (-m)}` is supported in the dual ball `{y | ‖y‖ ≤ exp (n + m)}`, where
  `ψ` is trivial on the level-`n` ball and nontrivial on the level-`(n + 1)` one (`hψn`,
  `hψn'`: the two halves of the previous row).  Off the dual ball the integral vanishes: the
  translate `x ↦ t + x` by `t = x₁ * y⁻¹` — which is in the `-m`-ball because `‖y‖` exceeds
  `exp (n + m)` — multiplies the integrand by `ψ x₁ ≠ 1`, and Haar invariance turns this into
  `(1 - ψ x₁) * ∫ = 0`.  On the dual ball the integrand is `1` on the whole ball, so the
  integral is `μ.real B`; the shift by `a` contributes the factor `ψ (a * y)`.

  The three public declarations are the pins' `solution` statements byte-for-byte, renamed to
  the published names.  The pin's remaining declarations are `private`; of those, the two
  engines of the third row are transcribed here (the first two pins are single-theorem files).

  References (pin `aa2d8b3`):
  * <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers.lean>
  * <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel.lean>
  * <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le.lean>

  ## Port deltas

  - **Imports.**  The pin's umbrella import is replaced by
    `Mathlib.RingTheory.DedekindDomain.AdicValuation` (FR-0254), and
    `FLTForHuman.AlgebraicCurve.Tate.CommFinite` is added for
    `IsDedekindDomain.HeightOneSpectrum.adicCompletion.isOpen_setOf_valued_le` — the port's
    home of the pin's `isClosed_setOf_valued_le` family
    (`Definitions/Def_NumberField_AdelicLevel.lean`).  Statement-neutral.
  - **`measurableSet_ball`** is proved from that *open*-ball lemma plus the `BorelSpace`
    instance instead of the pin's closed-ball route.  Consequently the pin's private
    `valued_uniformizerUnit_zpow` — used there only to exhibit a `t` with `‖t‖ = exp k` — is
    **not** transcribed; keeping it would be a dead declaration (gate 6).
  - **`integral_indicator_ball_mul`** is the pin's engine, statement and body, kept at its
    name inside `LanglandsTunnell.TateLocal.FourierBallF1` (the pin's search-stage namespace,
    so the row's cross-reference resolves identically).
  - **`Set.mem_setOf_eq` -> `Set.mem_ofPred_eq`** (deprecated at v4.34, FR-0255).
  - **The first row's rewrite chain.**  At v4.34 `AdeleRing R K` is a `def` of a product, and
    `rw` matches at `implicit` transparency, so the pin's direct chain through
    `psiK_apply`/`adelicTrace_apply` is rejected.  The port names the single-place adèle as an
    `AdeleRing` element first (`set Y`, `set Z`, with their `Y.1`/`Y.2` projections), the
    `AdeleRing` analogue of FR-0249's cure; statements are untouched.  The last step is also
    split into `rw` and `exact`: as one `rw` list the elaborated terms make the matcher churn
    past the heartbeat cap.
  - **Visibility.**  The pin's two engines stay `private`, so `check_port` reads the three
    public rows only (FR-0242) and `scaffold_audit` is complete over the pins' public surface.

  ## Build

  Heartbeat probe pair (`-DmaxHeartbeats`, one run per value, never installed): **silent at
  8000**, first failure at **6000** (`isDefEq`, third row).  The module's natural cost is thus
  under 0.2 % of the project's 4,000,000 cap, and it elaborates with no output at the default
  200,000 as well.

  spec-pin: P2M/Sol/S_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le.lean
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import FLTForHuman.LanglandsTunnell.StandardLocalConstantsAt
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.AlgebraicCurve.Tate.CommFinite

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal
open scoped ENNReal NNReal

namespace LanglandsTunnell.TateLocal

theorem psiLocal_eq_one_of_mem_integers (K : Type) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : v.adicCompletion K) (hx : x ∈ v.adicCompletionIntegers K) :
    NumberField.StandardAddChar.psiLocal K v x = 1 := by
  have key : ∀ (y : v.adicCompletion K), Valued.v y ≤ 1 →
      NumberField.StandardAddChar.psiLocal K v y = 1 := by
    intro y hy
    -- Name the single-place adèle at the type `AdeleRing`, where `AdeleRing` is a `def`
    -- of a product (v4.34), so that `psiK_apply`/`adelicTrace_apply` can match it.
    set Y : AdeleRing (𝓞 K) K :=
      ((0 : InfiniteAdeleRing K), NumberField.StandardAddChar.finAdeleSingleAt K v y) with hY
    have hY1 : Y.1 = (0 : InfiniteAdeleRing K) := by rw [hY]
    have hY2 : Y.2 = NumberField.StandardAddChar.finAdeleSingleAt K v y := by rw [hY]
    have hpsi : NumberField.StandardAddChar.psiLocal K v y
        = NumberField.StandardAddChar.psiQ
            ((NumberField.StandardAddChar.adelicTraceData K).adelicTrace Y) := by
      rw [NumberField.StandardAddChar.psiLocal_apply]
      exact congrArg NumberField.StandardAddChar.psiQ
        (congrArg (NumberField.StandardAddChar.adelicTraceData K).adelicTrace hY.symm)
    set Z : AdeleRing (𝓞 ℚ) ℚ :=
      ((NumberField.StandardAddChar.adelicTraceData K).traceInf Y.1,
        (NumberField.StandardAddChar.adelicTraceData K).traceFin Y.2) with hZ
    have hZ1 : Z.1 = (NumberField.StandardAddChar.adelicTraceData K).traceInf Y.1 := by rw [hZ]
    have hZ2 : Z.2 = (NumberField.StandardAddChar.adelicTraceData K).traceFin Y.2 := by rw [hZ]
    have htrace : (NumberField.StandardAddChar.adelicTraceData K).adelicTrace Y = Z := by
      rw [hZ, NumberField.StandardAddChar.AdelicTraceData.adelicTrace_apply]
    have hq : NumberField.StandardAddChar.psiQ
          ((NumberField.StandardAddChar.adelicTraceData K).adelicTrace Y)
        = NumberField.StandardAddChar.psiArch
            ((NumberField.StandardAddChar.adelicTraceData K).traceInf Y.1)
          * NumberField.StandardAddChar.psiFin
            ((NumberField.StandardAddChar.adelicTraceData K).traceFin Y.2) := by
      rw [htrace, NumberField.StandardAddChar.psiQ_apply, hZ1, hZ2]
    have hint : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NumberField.StandardAddChar.finAdeleSingleAt K v y w ∈ w.adicCompletionIntegers K := by
      intro w
      by_cases hw : w = v
      · subst hw
        rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
        exact hy
      · rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne K v y hw]
        exact zero_mem _
    let z : Π w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        w.adicCompletionIntegers K := fun w => ⟨_, hint w⟩
    have hsm : RestrictedProduct.structureMap
          (fun w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
            w.adicCompletion K)
          (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite z
        = NumberField.StandardAddChar.finAdeleSingleAt K v y :=
      RestrictedProduct.ext _ _ fun w => rfl
    rw [hpsi, hq, hY1, map_zero, AddChar.map_zero_eq_one, one_mul, hY2]
    have hz : (NumberField.StandardAddChar.adelicTraceData K).traceFin
          (NumberField.StandardAddChar.finAdeleSingleAt K v y)
        = RestrictedProduct.structureMap
            (fun w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
              w.adicCompletion ℚ)
            (fun w => (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) Filter.cofinite
            (NumberField.AdelicTrace.traceInt K z) := by
      rw [show (NumberField.StandardAddChar.adelicTraceData K).traceFin
          = NumberField.StandardAddChar.traceFinHom K from rfl, ← hsm,
        NumberField.StandardAddChar.traceFinHom_structureMap]
    rw [hz]
    exact NumberField.StandardAddChar.psiFin_eq_one_of_forall_mem _ fun w =>
      (NumberField.AdelicTrace.traceInt K z w).2
  exact key x hx

theorem forall_eq_one_and_exists_ne_one_of_addCharLevel (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψk : ∃ k : ℤ, ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k → ψ x = 1) (hψ : ψ ≠ 1) :
    (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ) → ψ x = 1) ∧
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ + 1) ∧ ψ x ≠ 1 := by
  classical
  set S : Set ℤ := {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1} with hS
  have hlev : addCharLevel ψ = sSup S := by rw [addCharLevel_def]
  have hne : S.Nonempty := hψk
  obtain ⟨x₁, hx₁⟩ := DFunLike.ne_iff.mp hψ
  rw [AddChar.one_apply] at hx₁
  have hx₁0 : x₁ ≠ 0 := fun h => hx₁ (by rw [h, AddChar.map_zero_eq_one])
  have hv₁ : Valued.v x₁ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₁0
  have hbdd : BddAbove S := by
    refine ⟨WithZero.log (Valued.v x₁), fun n hn => ?_⟩
    by_contra hlt
    apply hx₁
    apply hn
    rw [← WithZero.exp_log hv₁]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hmem : sSup S ∈ S := Int.csSup_mem hne hbdd
  have hnot : sSup S + 1 ∉ S := fun h => by
    have := le_csSup hbdd h
    omega
  rw [hlev]
  refine ⟨hmem, ?_⟩
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  exact ⟨x, (Classical.not_imp.mp hx).1, (Classical.not_imp.mp hx).2⟩

namespace FourierBallF1

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem measurableSet_ball [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (k : ℤ) :
    MeasurableSet {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.isOpen_setOf_valued_le K v
    WithZero.exp_ne_zero).measurableSet

private theorem integral_indicator_ball_mul [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (m : ℤ) (y : v.adicCompletion K) :
    ∫ x, {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x * ψ (x * y) ∂μ
      = (μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} : ℂ)
        * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)}.indicator (fun _ => (1 : ℂ)) y := by
  set B : Set (v.adicCompletion K) := {x | Valued.v x ≤ WithZero.exp (-m)} with hB
  have hBmeas : MeasurableSet B := measurableSet_ball v (-m)
  have hind : ∀ x, B.indicator (fun _ => (1 : ℂ)) x * ψ (x * y) = B.indicator (fun x => ψ (x * y)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  simp_rw [hind]
  by_cases hy : Valued.v y ≤ WithZero.exp (n + m)
  ·
    rw [Set.indicator_of_mem (show y ∈ {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)} from hy),
      mul_one, integral_indicator hBmeas]
    have hone : Set.EqOn (fun x => ψ (x * y)) (fun _ => (1 : ℂ)) B := fun x hx => by
      show ψ (x * y) = 1
      apply hψn
      rw [map_mul]
      calc Valued.v x * Valued.v y ≤ WithZero.exp (-m) * WithZero.exp (n + m) :=
            mul_le_mul' hx hy
        _ = WithZero.exp n := by rw [← WithZero.exp_add]; congr 1; ring
    rw [setIntegral_congr_fun hBmeas hone, setIntegral_const, Complex.real_smul, mul_one]
  ·
    rw [Set.indicator_of_notMem (show y ∉ {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)} from hy),
      mul_zero]
    obtain ⟨x₁, hx₁, hne⟩ := hψn'
    rw [not_le] at hy
    have hy0 : y ≠ 0 := fun h => by
      rw [h, map_zero] at hy
      exact not_lt_zero hy
    have hvy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    have hvy : WithZero.exp (n + m + 1) ≤ Valued.v y := by
      rw [← WithZero.exp_log hvy0] at hy ⊢
      rw [WithZero.exp_lt_exp] at hy
      exact WithZero.exp_le_exp.mpr (by omega)
    set t : v.adicCompletion K := x₁ * y⁻¹ with ht
    have htB : t ∈ B := by
      show Valued.v (x₁ * y⁻¹) ≤ WithZero.exp (-m)
      rw [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.mpr hvy0)]
      calc Valued.v x₁ ≤ WithZero.exp (n + 1) := hx₁
        _ = WithZero.exp (-m) * WithZero.exp (n + m + 1) := by rw [← WithZero.exp_add]; congr 1; ring
        _ ≤ WithZero.exp (-m) * Valued.v y := mul_le_mul_right hvy _
    have hty : t * y = x₁ := by rw [ht, inv_mul_cancel_right₀ hy0]
    have hpt : ∀ x, B.indicator (fun x => ψ (x * y)) (t + x) = ψ x₁ * B.indicator (fun x => ψ (x * y)) x := by
      intro x
      by_cases hx : x ∈ B
      · have htx : t + x ∈ B := by
          show Valued.v (t + x) ≤ WithZero.exp (-m)
          exact (Valuation.map_add_le_max' _ t x).trans (max_le htB hx)
        rw [Set.indicator_of_mem htx, Set.indicator_of_mem hx, add_mul, AddChar.map_add_eq_mul, hty]
      · have htx : t + x ∉ B := fun h => hx <| by
          have hsub : Valued.v (t + x - t) ≤ WithZero.exp (-m) :=
            (Valuation.map_sub _ (t + x) t).trans (max_le h htB)
          rwa [add_sub_cancel_left] at hsub
        rw [Set.indicator_of_notMem htx, Set.indicator_of_notMem hx, mul_zero]
    have htrans : ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ = ψ x₁ * ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ := by
      calc ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ
          = ∫ x, B.indicator (fun x => ψ (x * y)) (t + x) ∂μ := (integral_add_left_eq_self _ t).symm
        _ = ∫ x, ψ x₁ * B.indicator (fun x => ψ (x * y)) x ∂μ := by simp_rw [hpt]
        _ = ψ x₁ * ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ := integral_const_mul _ _
    have h1ne : (1 : ℂ) - ψ x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hprod : ((1 : ℂ) - ψ x₁) * ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ = 0 := by
      rw [sub_mul, one_mul, ← htrans, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left h1ne

end FourierBallF1

theorem tateFourier_indicator_setOf_valued_sub_le (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (a : v.adicCompletion K) (m : ℤ) (y : v.adicCompletion K) :
    tateFourier ψ μ ({x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator fun _ => (1 : ℂ)) y
      = ψ (a * y) * ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} : ℝ) : ℂ)
          * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)}.indicator (fun _ => (1 : ℂ)) y := by
  unfold tateFourier
  have hshift : ∀ x : v.adicCompletion K,
      {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) (a + x) * ψ ((a + x) * y)
        = ψ (a * y) * ({x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x
            * ψ (x * y)) := by
    intro x
    have hmem : (a + x ∈ {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)})
        ↔ x ∈ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} := by
      simp only [Set.mem_ofPred_eq, add_sub_cancel_left]
    rw [add_mul, AddChar.map_add_eq_mul]
    by_cases hx : x ∈ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
      ring
    · rw [Set.indicator_of_notMem (fun h => hx (hmem.mp h)), Set.indicator_of_notMem hx]
      ring
  calc ∫ x, {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x * ψ (x * y) ∂μ
      = ∫ x, {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) (a + x)
          * ψ ((a + x) * y) ∂μ :=
        (integral_add_left_eq_self
          (fun x => {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x
            * ψ (x * y)) a).symm
    _ = ∫ x, ψ (a * y) * ({x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x
          * ψ (x * y)) ∂μ := by simp_rw [hshift]
    _ = ψ (a * y) * ∫ x, {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x
          * ψ (x * y) ∂μ := integral_const_mul _ _
    _ = _ := by
        rw [LanglandsTunnell.TateLocal.FourierBallF1.integral_indicator_ball_mul v μ ψ n hψn hψn' m y, mul_assoc]

end LanglandsTunnell.TateLocal

end
