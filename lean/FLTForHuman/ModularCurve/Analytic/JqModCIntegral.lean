/-
Integrality of a ratio of `q`-expansions over `ℂ[jqModC]`.

Two headlines, one engine: for a modular form ratio `g / h` (`h ≠ 0`) whose value is bounded in every
punctured neighbourhood of the upper half plane, the ratio of the two `q`-expansions is integral over
`ℂ[jqModC]` — once in the `Γ₁(M) ≤ Γ` form and once for a general finite-index `Γ` with `T ∈ Γ`.

The two pins are near-identical (`port_advise`: 304 identical lines / 23 proofs, the set's largest
factoring unit); the `of_finiteIndex` one generalises the level parameter to `wd Γ =
Γ.normalCore.index` and takes `T ∈ Γ` as a hypothesis instead of `Γ₁(M) ≤ Γ`.  They are written as
one engine plus two headlines.

Depends on the ported `q`-expansion function field and integrality layer
(`ModularCurve/X1/{Defs,FunctionField}.lean`, `ModularCurve/Defs/JqCoeff.lean`,
`ModularCurve/QExpansionDifferentialLift.lean`) and on mathlib's `ModularForm`/`CuspForm` and
`UpperHalfPlane` API.  `MDiff`/`CMDiff` are mathlib's `UpperHalfPlane` notation for
`MDifferentiable 𝓘(ℂ) 𝓘(ℂ)`; it is the `scoped[Manifold]` elaborator, so the module carries
`open scoped … Manifold`, and `∣[k]` needs `open scoped … ModularForm` and the `•` on subgroups
`open scoped … Pointwise` (the pins get all three from one `open scoped` line).

## What is imported, what is transcribed

* **Imported, not redeclared** (the module's only substituted row): the pin's `T_mem_Gamma1` is
  `ModularCurve.P2MKcSepQ.T_mem_Gamma1` (`ModularCurve/X1/FunctionFieldIsAlgClosed.lean`), whose
  statement hash is **identical** to the pin row's (`c6b91b55…`), so the row is accounted by hash over
  the import closure.
* **Transcribed although the port has a twin — `restrict`** (13 lines).  The port's
  `ModularForm.LevelOneBasis.restrict` (`ModularForms/IsArithmeticQExpansion.lean`) is the
  `ModularForm`-only binder variant; the pin's `restrict` is generic over `F` with
  `[ModularFormClass F Γ k]`, which is exactly what `Δ₀`/`Δ₁` need in order to consume the *bundled*
  `CuspForm.discriminant` without a coercion, and the two statements differ textually, so importing the
  port's copy would leave the pin's row unaccounted by hash.  Declaring the pin's own version keeps the
  engine diff at **0 unaccounted**.
* **Transcribed, because the checker diffs the statement textually:** `Gamma_le_Gamma1` (mathlib's
  `CongruenceSubgroup.Gamma_le_Gamma1` takes implicit `{n}`) and `natCast_pos` (1 line; the port's
  copies are `private` in `ModularCurve/LevelN/QExpBridge.lean`).
* One proof body is *not* the pin's: `one_mem_strictPeriods`.  The statement is the pin's; the pin's
  six-line `ext i j; fin_cases …; simp [ModularGroup.T, …]` does not close in this mathlib (the
  `mapGL` coercion stays folded), so the proof reads mathlib's
  `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem` instead — same row, same hash, three lines.
* **`Δ₀`/`Δ₁` are the discriminant, not `E₄³`.**  The scaffold's prose said "the pin's `Δ₀` is the
  port's `ModularCurve.JOneES.JOneESRat.A12`"; that substitution is wrong and is **not** made.
  `ModularCurve/X1/FunctionField.lean`'s `A12` is `restrictForm Γ ((E₄ ^ 3).mcast _)`, and
  `E₄³ ≠ Δ` (classically `E₄³ - E₆² = 1728·Δ`).  The engine needs `ModularForm.discriminant ^ m` —
  in `isBoundedAtImInfty_of_mul_eq`'s conclusion and in `coe_liftForm`/`qL_liftForm_mul` through
  `coe_Δ₀` — so the pin's two `def`s (`restrict (le_SL Γ) CuspForm.discriminant` and
  `restrict le_rfl CuspForm.discriminant`) and their two `rfl` lemmas are transcribed verbatim.
  (`port_plan`'s `Δ₀ → A12` is one of the *suspect* substitutions it flags itself: a parser type-only
  match, FR-0266.)

## The 550/532 split (measured)

The two pins are one proof written twice: **93 `S_` rows / 63 distinct statement hashes** (the two
`Theorems/` wrappers add 2 rows and **0** new hashes — they restate the pins' `solution` rows).

* Everything hash-identical is declared **once**, at the 550 pin's names, in
  `ModularCurve.IntegralGammaAux`: the `Analytic`/`CuspGrowth` engine (11 rows), `key_ineq`,
  `restrict`, `qL`, `one_mem_strictPeriods`, `le_SL`, `Δ₀`, `coe_Δ₀`, `Δ₁`, `coe_Δ₁`, `coe_ne_zero`,
  `eventually_ne_zero_coe`, `exists_F₀`, `slash_zero_eq`, `qL_ne_zero`, `T_mem_SL`, `Δ₀_ne_zero`,
  `qL_discriminant_ne_zero`, `cuspOrder`, `isIntegral_of_forall_isBoundedUnder` — 30 rows.
* The rows whose *statements* differ — the 550 ones carrying `(M : ℕ)` and `hM : Γ(M) ≤ Γ`, the 532
  ones carrying the level `wd Γ = Γ.normalCore.index` — stay **two declarations in two subject
  namespaces** (FR-0274): `ModularCurve.IntegralGammaAux` and `ModularCurve.IntegralFiniteIndex`, i.e.
  `Gamma_le_conj`/`normalCore_le_conj`, `translateSL`, `coe_translateSL`,
  `natCast_mem_strictPeriods_Gamma`/`wd_mem_strictPeriods`, `exists_qParam_pow_le_slash`,
  `cuspOrder`/`cuspOrder_spec`, `exists_forall_cuspOrder_le`, `isBoundedAtImInfty_of_mul_eq`,
  `liftForm`, `coe_liftForm'`, `coe_liftForm`, `qL_liftForm_mul`,
  `isIntegral_of_forall_isBoundedUnder`.  The 532-only `wd` family (`wd`, `wd_ne_zero`, `wd_pos`,
  `one_le_wd`) is in `IntegralFiniteIndex`.
* `isIntegral_of_forall_isBoundedUnder` is the one **deliberate** duplicate statement: the two pins
  write it with the same text but different elaborated signatures (the 550 one is generic over `M` and
  consumes `hM`; the 532 one has level `wd Γ` and consumes no `hM`), and neither generalises to the
  other — `CongruenceSubgroup.Gamma (wd Γ) ≤ Γ` does **not** hold, so the 550 engine cannot serve the
  532 headline.  `dedup --within` reports exactly this pair as one 22-line cluster; it is kept, with
  the reason here and in the gates block below.

## Gates measured for this module (AF102M2)

`check_port --force` **64 ok / 0 mismatch / 0 missing / 0 own / 0 kw**; engine diff 63 distinct pin
hashes ↔ 62 declared + 1 imported (`T_mem_Gamma1`) = 63, **0 unaccounted and 0 module rows outside the
pin** (by name: 52 distinct last names on each side, the only two differences being the pin's `solution`
→ the wrappers' published names and `T_mem_Gamma1` → the import); edit loop **silent** (`lake env lean
-DautoImplicit=false`, 12.8 s); `dedup --within --module JqModCIntegral` 1 cluster / 22 lines (the pair
above); `move_dead --dry-run` **0 declarations, 0 lines**; `#print axioms` on all 64 public
declarations = `[propext, Classical.choice, Quot.sound]` and nothing else, **no `sorryAx`**; one locked
`lake build` green.

**Heartbeat probe pair, recorded and never installed** (FR-0225): with `-DmaxHeartbeats=5000` the whole
module still elaborates with no output, and at `-DmaxHeartbeats=3000` it fails at `exists_qParam_pow_le`
(`…:175`, `whnf`); the default is 200000, so every declaration here has ≥ 40× headroom.  No
`set_option maxHeartbeats` is installed anywhere in the module, and the scaffold's
`set_option linter.unusedSectionVars false` is **dropped** (neither pin carries it; the engine is
silent without it).

**Not here:** the set's one-row insertion,
`ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion`, lives in
`ModularCurve/QExpansionDifferentialLift.lean`, not in `Period/QExpansionDiff.lean`: its first premise
is that file's own row, i.e. one import *above* `Period/QExpansionDiff.lean`, so declaring it there
would close a cycle (FR-0280's shape).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex.lean>

spec-pin: Theorems/Thm_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder.lean
spec-pin: Theorems/Thm_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex.lean
spec-pin: P2M/Sol/S_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder.lean
spec-pin: P2M/Sol/S_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex.lean
-/
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.QExpansionDifferentialLift
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.X1.FunctionField
import FLTForHuman.ModularCurve.X1.FunctionFieldIsAlgClosed
import FLTForHuman.ModularForms.IsArithmeticQExpansion
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularCurve Filter Function
open scoped MatrixGroups Topology Manifold ModularForm Pointwise

namespace ModularCurve

namespace IntegralGammaAux

section Analytic

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem analyticOnNhd_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) :
    AnalyticOnNhd ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet

theorem eq_zero_of_eventuallyEq_zero {f : ℍ → ℂ} (hf : MDiff f) {c : ℂ} (hc : 0 < c.im)
    (h : ∀ᶠ z in 𝓝 c, (f ∘ ofComplex) z = 0) : f = 0 := by
  have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have key := (analyticOnNhd_comp_ofComplex hf).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hU hc h
  funext τ
  have := key τ.im_pos
  simp only [comp_apply, ofComplex_apply] at this
  exact this

theorem eventually_ne_zero {f : ℍ → ℂ} (hf : MDiff f) (hf0 : f ≠ 0) {c : ℂ} (hc : 0 < c.im) :
    ∀ᶠ z in 𝓝[≠] c, f (ofComplex z) ≠ 0 := by
  rcases (analyticOnNhd_comp_ofComplex hf c hc).eventually_eq_zero_or_eventually_ne_zero with
    h | h
  · exact absurd (eq_zero_of_eventuallyEq_zero hf hc h) hf0
  · exact h

theorem continuousAt_ofComplex {c : ℂ} (hc : 0 < c.im) : ContinuousAt ofComplex c :=
  (mdifferentiableAt_ofComplex hc).continuousAt

theorem tendsto_ofComplex_nhdsNE (τ : ℍ) :
    Tendsto ofComplex (𝓝[≠] (τ : ℂ)) (𝓝[≠] τ) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h2 := (continuousAt_ofComplex τ.im_pos).tendsto
    rw [ofComplex_apply] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z hz hU
    intro h
    apply hz
    have hU' : 0 < z.im := hU
    have := congrArg UpperHalfPlane.coe (Set.mem_singleton_iff.mp h)
    simpa [ofComplex_apply_of_im_pos hU'] using this

theorem eq_of_eq_off_zeros {h u v : ℍ → ℂ}
    (hh : ∀ c : ℂ, 0 < c.im → ∀ᶠ z in 𝓝[≠] c, h (ofComplex z) ≠ 0)
    (hu : Continuous u) (hv : Continuous v) (huv : ∀ τ, h τ ≠ 0 → u τ = v τ) : u = v := by
  funext τ
  have hcu : ContinuousAt (u ∘ ofComplex) (τ : ℂ) :=
    hu.continuousAt.comp_of_eq (continuousAt_ofComplex τ.im_pos) (ofComplex_apply τ)
  have hcv : ContinuousAt (v ∘ ofComplex) (τ : ℂ) :=
    hv.continuousAt.comp_of_eq (continuousAt_ofComplex τ.im_pos) (ofComplex_apply τ)
  have hev : (u ∘ ofComplex) =ᶠ[𝓝[≠] (τ : ℂ)] (v ∘ ofComplex) :=
    (hh τ τ.im_pos).mono fun z hz => huv _ hz
  have := tendsto_nhds_unique_of_eventuallyEq (hcu.tendsto.mono_left nhdsWithin_le_nhds)
    (hcv.tendsto.mono_left nhdsWithin_le_nhds) hev
  simpa only [comp_apply, ofComplex_apply] using this

theorem exists_mdifferentiable_mul_eq {g h : ℍ → ℂ} (hg : MDiff g) (hh : MDiff h)
    (hh0 : ∀ c : ℂ, 0 < c.im → ∀ᶠ z in 𝓝[≠] c, h (ofComplex z) ≠ 0)
    (hb : ∀ τ : ℍ, ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] (τ : ℂ), ‖g (ofComplex z) / h (ofComplex z)‖ ≤ M) :
    ∃ F₀ : ℍ → ℂ, MDiff F₀ ∧ ∀ τ, F₀ τ * h τ = g τ := by
  set φ : ℂ → ℂ := fun z => g (ofComplex z) / h (ofComplex z) with hφ
  set ψ : ℂ → ℂ := fun c => limUnder (𝓝[≠] c) φ with hψ

  have hA : ∀ c : ℂ, ∀ hc : 0 < c.im, h (ofComplex c) ≠ 0 → DifferentiableAt ℂ φ c := by
    intro c hc hne
    have hg' : DifferentiableAt ℂ (g ∘ ofComplex) c := mdifferentiableAt_iff.mp (hg ⟨c, hc⟩)
    have hh' : DifferentiableAt ℂ (h ∘ ofComplex) c := mdifferentiableAt_iff.mp (hh ⟨c, hc⟩)
    exact hg'.div hh' hne

  have hB : ∀ c : ℂ, 0 < c.im → h (ofComplex c) ≠ 0 → ψ c = φ c := fun c hc hne =>
    ((hA c hc hne).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

  have hC : DifferentiableOn ℂ ψ {z : ℂ | 0 < z.im} := by
    intro c hc
    have hc' : 0 < c.im := hc
    obtain ⟨M, hM⟩ := hb ⟨c, hc'⟩
    have hev : ∀ᶠ z in 𝓝[≠] c, h (ofComplex z) ≠ 0 ∧ ‖φ z‖ ≤ M ∧ 0 < z.im :=
      (hh0 c hc').and (hM.and (mem_nhdsWithin_of_mem_nhds
        (isOpen_upperHalfPlaneSet.mem_nhds hc')))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    have hd : DifferentiableOn ℂ φ (Metric.ball c ε \ {c}) := fun z hz =>
      (hA z (hball z hz.1 hz.2).2.2 (hball z hz.1 hz.2).1).differentiableWithinAt
    have hbdd : BddAbove (norm ∘ φ '' (Metric.ball c ε \ {c})) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hball z hz.1 hz.2).2.1
    have R := Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds c hε)
      hd hbdd
    have heq : Set.EqOn ψ (update φ c (limUnder (𝓝[≠] c) φ)) (Metric.ball c ε) := by
      intro z hz
      by_cases hzc : z = c
      · subst hzc; simp [hψ]
      · rw [update_of_ne hzc]
        exact hB z (hball z hz hzc).2.2 (hball z hz hzc).1
    have hψs : DifferentiableOn ℂ ψ (Metric.ball c ε) := R.congr heq
    exact (hψs.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)))
      |>.differentiableWithinAt

  refine ⟨fun τ => ψ τ, ?_, ?_⟩
  · refine UpperHalfPlane.mdifferentiable_iff.mpr (hC.congr fun z hz => ?_)
    have hz' : 0 < z.im := hz
    simp only [comp_apply, ofComplex_apply_of_im_pos hz', UpperHalfPlane.coe_mk]
  · have hF : MDiff (fun τ : ℍ => ψ τ) := by
      refine UpperHalfPlane.mdifferentiable_iff.mpr (hC.congr fun z hz => ?_)
      have hz' : 0 < z.im := hz
      simp only [comp_apply, ofComplex_apply_of_im_pos hz', UpperHalfPlane.coe_mk]
    have key := eq_of_eq_off_zeros (u := fun τ => ψ τ * h τ) (v := g) hh0
      (hF.continuous.mul hh.continuous) hg.continuous (fun τ hτ => by
        have h1 : h (ofComplex (τ : ℂ)) ≠ 0 := by rwa [ofComplex_apply]
        have := hB τ τ.im_pos h1
        simp only [this, hφ, ofComplex_apply]
        exact div_mul_cancel₀ _ hτ)
    exact fun τ => congrFun key τ

end Analytic

section CuspGrowth

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem norm_qParam_lt_one' {h : ℝ} (hh : 0 < h) (τ : ℍ) : ‖Periodic.qParam h (τ : ℂ)‖ < 1 := by
  have := (Periodic.norm_qParam_lt_iff hh 0 (τ : ℂ)).mpr (by simpa using τ.im_pos)
  simpa using this

theorem exists_qParam_pow_le {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (f : ModularForm Γ k) (hf : f ≠ 0) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam h (τ : ℂ)‖ ^ n ≤ ‖f τ‖ := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hΦ : AnalyticAt ℂ (cuspFunction h f) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have hne : ¬ (∀ᶠ q in 𝓝 (0 : ℂ), cuspFunction h f q = 0) := by
    intro hev
    apply hf
    have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
    have hball : AnalyticOnNhd ℂ (cuspFunction h f) (Metric.ball 0 1) :=
      (differentiableOn_cuspFunction_ball hh hper (ModularFormClass.holo f)
        (ModularFormClass.bdd_at_infty f)).analyticOnNhd Metric.isOpen_ball
    have hz := hball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) 1).isPreconnected (Metric.mem_ball_self one_pos) hev
    ext τ
    have hq : Periodic.qParam h (τ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      simpa using norm_qParam_lt_one' hh τ
    have := hz hq
    rw [eq_cuspFunction τ hh.ne' hper] at this
    simpa using this
  obtain ⟨n, φ, hφ, hφ0, hev⟩ := hΦ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  refine ⟨n, ‖φ 0‖ / 2, by positivity, ?_⟩
  have hlow : ∀ᶠ q in 𝓝 (0 : ℂ), ‖φ 0‖ / 2 < ‖φ q‖ :=
    hφ.continuousAt.norm.eventually_const_lt (by simpa using hφ0)
  have hq0 : Tendsto (fun τ : ℍ => Periodic.qParam h (τ : ℂ)) atImInfty (𝓝 0) :=
    qParam_tendsto_atImInfty hh
  filter_upwards [hq0.eventually hlow, hq0.eventually hev] with τ h1 h2
  rw [← eq_cuspFunction τ hh.ne' hper, h2, norm_smul, norm_pow, mul_comm, sub_zero]
  gcongr

theorem exists_norm_discriminant_le :
    ∃ C : ℝ, ∀ᶠ τ : ℍ in atImInfty,
      ‖ModularForm.discriminant τ‖ ≤ C * ‖Periodic.qParam 1 (τ : ℂ)‖ := by
  have h := CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant one_pos
    (by simp)
  obtain ⟨C, hC⟩ := h.bound
  refine ⟨C, hC.mono fun τ hτ => ?_⟩
  rw [Periodic.norm_qParam]
  have : ‖Real.exp (-2 * Real.pi * τ.im / 1)‖ = Real.exp (-2 * Real.pi * (τ : ℂ).im / 1) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rfl
  rw [← this]
  exact hτ

theorem norm_qParam_one_le {N : ℝ} (hN : 1 ≤ N) (τ : ℍ) :
    ‖Periodic.qParam 1 (τ : ℂ)‖ ≤ ‖Periodic.qParam N (τ : ℂ)‖ := by
  rw [Periodic.norm_qParam, Periodic.norm_qParam, Real.exp_le_exp, div_one]
  rw [le_div_iff₀ (by linarith)]
  have h1 : 0 ≤ 2 * Real.pi * (τ : ℂ).im := by
    have := τ.im_pos
    have : (0 : ℝ) < (τ : ℂ).im := this
    positivity
  nlinarith

end CuspGrowth

theorem key_ineq {a b c d q q₁ C M D : ℝ} {n m : ℕ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hab : a * b = c) (hb : C * q ^ n ≤ b) (hc : c ≤ M) (hdq : d ≤ D * q₁) (hq₁ : q₁ ≤ q)
    (hq1 : q ≤ 1) (hq0 : 0 < q) (hq₁0 : 0 ≤ q₁) (hC : 0 < C) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hnm : n ≤ m) : a * d ^ m ≤ M * D ^ m / C := by
  have h1 : a * d ^ m * C * q ^ n ≤ M * D ^ m * q ^ n :=
    calc a * d ^ m * C * q ^ n = a * d ^ m * (C * q ^ n) := by ring
      _ ≤ a * d ^ m * b := by gcongr
      _ = c * d ^ m := by rw [← hab]; ring
      _ ≤ M * d ^ m := by gcongr
      _ ≤ M * (D * q₁) ^ m := by gcongr
      _ ≤ M * (D * q) ^ m := by gcongr
      _ = M * D ^ m * q ^ m := by ring
      _ ≤ M * D ^ m * q ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0.le hq1 hnm) (by positivity)
  rw [le_div_iff₀ hC]
  exact le_of_mul_le_mul_right h1 (pow_pos hq0 n)

section Level

variable (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (hM : CongruenceSubgroup.Gamma M ≤ Γ) {k : ℤ}

def restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ)
    {k : ℤ} (f : F) [ModularFormClass F Γ k] : ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono hle)

include hM in
theorem Gamma_le_conj (A : SL(2, ℤ)) :
    ((CongruenceSubgroup.Gamma M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ A)⁻¹ •
        ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨A * y * A⁻¹, hM ((CongruenceSubgroup.Gamma_normal M).conj_mem y hy A), ?_⟩
  simp [map_mul, map_inv]

def translateSL (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (A : SL(2, ℤ)) :
    ModularForm (CongruenceSubgroup.Gamma M) k :=
  restrict (Gamma_le_conj M Γ hM A) (ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ A))

@[scoped simp] theorem coe_translateSL (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (A : SL(2, ℤ)) : ⇑(translateSL M Γ hM f A) = ⇑f ∣[k] A := rfl

theorem natCast_mem_strictPeriods_Gamma :
    (M : ℝ) ∈ (CongruenceSubgroup.Gamma M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem natCast_pos [NeZero M] : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))

include hM in

theorem exists_qParam_pow_le_slash [NeZero M] (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hh : h ≠ 0) (A : SL(2, ℤ)) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam M (τ : ℂ)‖ ^ n ≤ ‖(⇑h ∣[k] A) τ‖ := by
  have hne : translateSL M Γ hM h A ≠ 0 := by
    intro h0
    apply hh
    have h1 : (⇑h ∣[k] A) = 0 := by
      rw [← coe_translateSL M Γ hM h A, h0]; rfl
    rw [SlashAction.slash_eq_zero_iff] at h1
    exact (FunLike.coe_zero_iff h).mp h1
  exact exists_qParam_pow_le (natCast_pos M) (natCast_mem_strictPeriods_Gamma M)
    (translateSL M Γ hM h A) hne

open scoped Classical in

def cuspOrder (φ : ℍ → ℂ) : ℕ :=
  if H : ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam M (τ : ℂ)‖ ^ n ≤ ‖φ τ‖
  then H.choose else 0

theorem cuspOrder_spec (φ : ℍ → ℂ)
    (H : ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam M (τ : ℂ)‖ ^ n ≤ ‖φ τ‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam M (τ : ℂ)‖ ^ (cuspOrder M φ) ≤ ‖φ τ‖ := by
  rw [cuspOrder, dite_eq_left H]
  exact H.choose_spec

theorem exists_forall_cuspOrder_le [Γ.FiniteIndex] (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ m : ℕ, ∀ A : SL(2, ℤ), cuspOrder M (⇑h ∣[k] A) ≤ m := by
  classical
  let ψ : SL(2, ℤ) ⧸ Γ → ℕ := fun q => cuspOrder M (⇑h ∣[k] (q.out)⁻¹)
  obtain ⟨m, hm⟩ := (Set.finite_range ψ).bddAbove
  refine ⟨m, fun A => ?_⟩
  set B : SL(2, ℤ) := ((A⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ).out with hB
  have hq : ((A⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ) = (B : _) := (QuotientGroup.out_eq' _).symm
  rw [QuotientGroup.eq, inv_inv] at hq
  have hslash : ⇑h ∣[k] (A * B) = ⇑h :=
    SlashInvariantFormClass.slash_action_eq h (Matrix.SpecialLinearGroup.mapGL ℝ (A * B))
      (Subgroup.mem_map_of_mem _ hq)
  have key : ⇑h ∣[k] A = ⇑h ∣[k] B⁻¹ :=
    calc ⇑h ∣[k] A = ⇑h ∣[k] ((A * B) * B⁻¹) := by rw [mul_inv_cancel_right]
      _ = (⇑h ∣[k] (A * B)) ∣[k] B⁻¹ := SlashAction.slash_mul _ _ _ _
      _ = ⇑h ∣[k] B⁻¹ := by rw [hslash]
  rw [key]
  exact hm ⟨_, rfl⟩

include hM in

theorem isBoundedAtImInfty_of_mul_eq [NeZero M] (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hh : h ≠ 0) (F₀ : ℍ → ℂ) (hF : ∀ τ, F₀ τ * h τ = g τ) (A : SL(2, ℤ)) {m : ℕ}
    (hm : cuspOrder M (⇑h ∣[k] A) ≤ m) :
    IsBoundedAtImInfty (fun τ : ℍ => F₀ (A • τ) * (ModularForm.discriminant τ) ^ m) := by
  obtain ⟨C, hC, hlow⟩ := cuspOrder_spec M _ (exists_qParam_pow_le_slash M Γ hM h hh A)
  have hgA : IsBoundedAtImInfty (⇑g ∣[k] A) := ModularFormClass.bdd_at_infty (translateSL M Γ hM g A)
  obtain ⟨D, hD⟩ := exists_norm_discriminant_le
  rw [IsBoundedAtImInfty, BoundedAtFilter] at hgA ⊢
  obtain ⟨M', hM'⟩ := hgA.bound
  refine Asymptotics.IsBigO.of_bound (max M' 0 * max D 0 ^ m / C) ?_
  filter_upwards [hlow, hM', hD] with τ h1 h2 h3
  simp only [Pi.one_apply, norm_one, mul_one] at h2 ⊢
  have hq0 : 0 < ‖Periodic.qParam M (τ : ℂ)‖ := by
    rw [Periodic.norm_qParam]; exact Real.exp_pos _
  have hq1 : ‖Periodic.qParam M (τ : ℂ)‖ ≤ 1 := (norm_qParam_lt_one' (natCast_pos M) τ).le
  have hq₁ : ‖Periodic.qParam 1 (τ : ℂ)‖ ≤ ‖Periodic.qParam M (τ : ℂ)‖ :=
    norm_qParam_one_le (Nat.one_le_cast.mpr NeZero.one_le) τ
  have hab : ‖F₀ (A • τ)‖ * ‖(⇑h ∣[k] A) τ‖ = ‖(⇑g ∣[k] A) τ‖ := by
    rw [← norm_mul, ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ← mul_assoc, hF]
  rw [norm_mul, norm_pow]
  exact key_ineq (norm_nonneg _) (norm_nonneg _) hab h1 (h2.trans (le_max_left _ _))
    (h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) hq₁ hq1 hq0
    (norm_nonneg _) hC (le_max_right _ _) (le_max_right _ _) hm

end Level

section Assembly

variable (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hM : CongruenceSubgroup.Gamma M ≤ Γ)
  (hT : ModularGroup.T ∈ Γ)

abbrev qL (f : ℍ → ℂ) : LaurentSeries ℂ := ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)

include hT in
omit [NeZero M] in
theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT, AddSubgroup.mem_zmultiples_iff]
  exact ⟨1, by norm_num⟩

omit [NeZero M] in
theorem le_SL : ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

def Δ₀ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrict (le_SL Γ) CuspForm.discriminant

omit [NeZero M] in
@[scoped simp] theorem coe_Δ₀ : ((Δ₀ Γ : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

def Δ₁ : ModularForm 𝒮ℒ 12 := restrict le_rfl CuspForm.discriminant

@[scoped simp] theorem coe_Δ₁ : ((Δ₁ : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

omit [NeZero M] in
theorem coe_ne_zero {k : ℤ} (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) :
    (h : ℍ → ℂ) ≠ 0 := fun e => hh ((FunLike.coe_zero_iff h).mp e)

omit [NeZero M] in
theorem eventually_ne_zero_coe {k : ℤ} (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hh : h ≠ 0) (c : ℂ) (hc : 0 < c.im) : ∀ᶠ z in 𝓝[≠] c, h (ofComplex z) ≠ 0 :=
  eventually_ne_zero h.holo' (coe_ne_zero Γ h hh) hc

omit [NeZero M] in

theorem exists_F₀ {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hb : ∀ τ : ℍ, IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖g z / h z‖)) :
    ∃ F₀ : ℍ → ℂ, MDiff F₀ ∧ ∀ τ, F₀ τ * h τ = g τ := by
  refine exists_mdifferentiable_mul_eq g.holo' h.holo' (eventually_ne_zero_coe Γ h hh)
    (fun τ => ?_)
  obtain ⟨M', hM'⟩ := hb τ
  refine ⟨M', ?_⟩
  have h1 : ∀ᶠ z : ℍ in 𝓝[≠] τ, ‖g z / h z‖ ≤ M' := hM'
  exact (tendsto_ofComplex_nhdsNE τ).eventually h1

omit [NeZero M] in

theorem slash_zero_eq {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Γ) : F₀ ∣[(0 : ℤ)] γ = F₀ := by
  refine eq_of_eq_off_zeros (eventually_ne_zero_coe Γ h hh)
    (hF₀.slash 0 (γ : GL (Fin 2) ℝ)).continuous hF₀.continuous (fun τ hτ => ?_)
  rw [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
  have eh : h (γ • τ) = denom γ τ ^ k * h τ := SlashInvariantForm.slash_action_eqn_SL'' h hγ τ
  have eg : g (γ • τ) = denom γ τ ^ k * g τ := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
  have hd : (denom γ τ) ^ k ≠ 0 := zpow_ne_zero _ (denom_ne_zero _ _)
  have e1 := hF (γ • τ)
  have e2 := hF τ
  rw [eh, eg] at e1
  have : F₀ (γ • τ) * (denom γ τ ^ k * h τ) = F₀ τ * (denom γ τ ^ k * h τ) := by
    rw [e1, ← e2]; ring
  exact mul_right_cancel₀ (mul_ne_zero hd hτ) this

include hM in

def liftForm [Γ.FiniteIndex] {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder M (⇑h ∣[k] A) ≤ m) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) ((m : ℤ) * 12) where
  toFun := F₀ * ⇑(Δ₁.pow m)
  slash_action_eq' γ hγ := by
    obtain ⟨γ, hγ', rfl⟩ := hγ
    have hΔ : (⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] γ = ⇑(Δ₁.pow m) :=
      SlashInvariantFormClass.slash_action_eq (Δ₁.pow m)
        (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩
    have e := ModularForm.mul_slash_SL2 0 ((m : ℤ) * 12) γ F₀ ⇑(Δ₁.pow m)
    rw [zero_add] at e
    show (F₀ * ⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] γ = F₀ * ⇑(Δ₁.pow m)
    rw [e, slash_zero_eq Γ g h hh F₀ hF₀ hF γ hγ', hΔ]
  holo' := hF₀.mul (Δ₁.pow m).holo'
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro A _
    have hΔ : (⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] A = ⇑(Δ₁.pow m) :=
      SlashInvariantFormClass.slash_action_eq (Δ₁.pow m)
        (Matrix.SpecialLinearGroup.mapGL ℝ A) ⟨A, rfl⟩
    have e := ModularForm.mul_slash_SL2 0 ((m : ℤ) * 12) A F₀ ⇑(Δ₁.pow m)
    rw [zero_add] at e
    show IsBoundedAtImInfty ((F₀ * ⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] A)
    rw [e, hΔ]
    have : (F₀ ∣[(0 : ℤ)] A * ⇑(Δ₁.pow m)) =
        fun τ => F₀ (A • τ) * ModularForm.discriminant τ ^ m := by
      funext τ
      simp [ModularForm.SL_slash_apply]
    rw [this]
    exact isBoundedAtImInfty_of_mul_eq M Γ hM g h hh F₀ hF A (hm A)

theorem coe_liftForm' [Γ.FiniteIndex] {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder M (⇑h ∣[k] A) ≤ m) :
    ⇑(liftForm M Γ hM g h hh F₀ hF₀ hF m hm) = F₀ * ⇑(Δ₁.pow m) := rfl

theorem coe_liftForm [Γ.FiniteIndex] {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder M (⇑h ∣[k] A) ≤ m) :
    (⇑(liftForm M Γ hM g h hh F₀ hF₀ hF m hm)) * ⇑h = ⇑g * ⇑((Δ₀ Γ).pow m) := by
  rw [coe_liftForm']
  funext τ
  simp only [Pi.mul_apply, ModularForm.coe_pow, Pi.pow_apply, coe_Δ₀, coe_Δ₁]
  rw [mul_right_comm, hF]

include hT in

theorem qL_liftForm_mul [Γ.FiniteIndex] {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder M (⇑h ∣[k] A) ≤ m) :
    qL ⇑(liftForm M Γ hM g h hh F₀ hF₀ hF m hm) * qL ⇑h =
      qL ⇑g * qL (ModularForm.discriminant) ^ m := by
  have h1 := ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods Γ hT)
    (liftForm M Γ hM g h hh F₀ hF₀ hF m hm) h
  have h2 := ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods Γ hT)
    g ((Δ₀ Γ).pow m)
  have h3 := ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods Γ hT) (Δ₀ Γ) m
  rw [coe_liftForm] at h1
  simp only [qL, ← PowerSeries.coe_mul, ← PowerSeries.coe_pow, ← h1, h2, h3, coe_Δ₀]

include hT in
omit [NeZero M] in
theorem qL_ne_zero {k : ℤ} (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) :
    qL ⇑h ≠ 0 := by
  intro e
  apply hh
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods Γ hT)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using e

theorem T_mem_SL : ModularGroup.T ∈ (⊤ : Subgroup SL(2, ℤ)) := Subgroup.mem_top _

theorem Δ₀_ne_zero : Δ₀ (⊤ : Subgroup SL(2, ℤ)) ≠ 0 := by
  intro e
  have := congrArg (fun f : ModularForm ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 =>
    (f : ℍ → ℂ) I) e
  exact ModularForm.discriminant_ne_zero I (by simpa using this)

theorem qL_discriminant_ne_zero : qL ModularForm.discriminant ≠ 0 := by
  rw [← coe_Δ₀ (⊤ : Subgroup SL(2, ℤ))]
  exact qL_ne_zero (⊤ : Subgroup SL(2, ℤ)) T_mem_SL (Δ₀ ⊤) Δ₀_ne_zero

include hM hT in

theorem isIntegral_of_forall_isBoundedUnder [Γ.FiniteIndex] {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hb : ∀ τ : ℍ, IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖g z / h z‖)) :
    IsIntegral (Algebra.adjoin ℂ ({jqModC ℂ} : Set (LaurentSeries ℂ))) (qL ⇑g / qL ⇑h) := by
  obtain ⟨F₀, hF₀, hF⟩ := exists_F₀ Γ g h hh hb
  obtain ⟨m, hm⟩ := exists_forall_cuspOrder_le M Γ h
  set F := liftForm M Γ hM g h hh F₀ hF₀ hF m hm with hFdef
  have hq : qL ⇑F * qL ⇑h = qL ⇑g * qL ModularForm.discriminant ^ m :=
    qL_liftForm_mul M Γ hM hT g h hh F₀ hF₀ hF m hm
  have hxF : qL ⇑F / qL ModularForm.discriminant ^ m = qL ⇑g / qL ⇑h := by
    rw [div_eq_div_iff (pow_ne_zero _ qL_discriminant_ne_zero) (qL_ne_zero Γ hT h hh)]
    rw [hq]
  have key := ModularForm.isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic
    (one_mem_strictPeriods Γ hT) m (k := (m : ℤ) * 12) (by ring) F
  rw [← jqModC_eq_qExpansion_E4_cube_div_discriminant] at key
  rw [← hxF]
  exact key

end Assembly

end IntegralGammaAux

theorem IntegralGammaAux.Gamma_le_Gamma1 (M : ℕ) :
    CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma1 M := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨hA.1, hA.2.2.2, hA.2.2.1⟩

open scoped Topology in
theorem isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hb : ∀ τ : UpperHalfPlane, Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : UpperHalfPlane => ‖g z / h z‖)) :
    IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) /
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑h)) := by
  have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  exact ModularCurve.IntegralGammaAux.isIntegral_of_forall_isBoundedUnder M Γ
    ((ModularCurve.IntegralGammaAux.Gamma_le_Gamma1 M).trans hΓ)
    (hΓ (ModularCurve.P2MKcSepQ.T_mem_Gamma1 M)) g h hh hb

namespace IntegralFiniteIndex

open IntegralGammaAux

section Level

variable (Γ : Subgroup SL(2, ℤ)) {k : ℤ}

def wd : ℕ := Γ.normalCore.index

theorem wd_ne_zero [Γ.FiniteIndex] : wd Γ ≠ 0 :=
  (Subgroup.FiniteIndex.index_ne_zero : Γ.normalCore.index ≠ 0)

theorem wd_pos [Γ.FiniteIndex] : (0 : ℝ) < wd Γ :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (wd_ne_zero Γ))

theorem one_le_wd [Γ.FiniteIndex] : (1 : ℝ) ≤ wd Γ :=
  Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (wd_ne_zero Γ))

theorem normalCore_le_conj (A : SL(2, ℤ)) :
    ((Γ.normalCore : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ A)⁻¹ •
        ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨A * y * A⁻¹, Γ.normalCore_le ((Subgroup.normalCore_normal Γ).conj_mem y hy A), ?_⟩
  simp [map_mul, map_inv]

def translateSL (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (A : SL(2, ℤ)) :
    ModularForm ((Γ.normalCore : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
  IntegralGammaAux.restrict (normalCore_le_conj Γ A)
    (ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ A))

@[scoped simp] theorem coe_translateSL (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (A : SL(2, ℤ)) : ⇑(translateSL Γ f A) = ⇑f ∣[k] A := rfl

theorem wd_mem_strictPeriods :
    ((wd Γ : ℕ) : ℝ) ∈ ((Γ.normalCore : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hmem : ModularGroup.T ^ ((wd Γ : ℕ) : ℤ) ∈ Γ.normalCore := by
    rw [zpow_natCast]
    exact Γ.normalCore.pow_index_mem ModularGroup.T
  simp only [Subgroup.mem_strictPeriods_iff, Subgroup.mem_map, Units.ext_iff,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  refine ⟨ModularGroup.T ^ ((wd Γ : ℕ) : ℤ), hmem, ?_⟩
  rw [ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom]

theorem exists_qParam_pow_le_slash [Γ.FiniteIndex] (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hh : h ≠ 0) (A : SL(2, ℤ)) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam (wd Γ) (τ : ℂ)‖ ^ n ≤ ‖(⇑h ∣[k] A) τ‖ := by
  have hne : translateSL Γ h A ≠ 0 := by
    intro h0
    apply hh
    have h1 : (⇑h ∣[k] A) = 0 := by
      rw [← coe_translateSL Γ h A, h0]; rfl
    rw [SlashAction.slash_eq_zero_iff] at h1
    exact (FunLike.coe_zero_iff h).mp h1
  exact IntegralGammaAux.exists_qParam_pow_le (wd_pos Γ) (wd_mem_strictPeriods Γ)
    (translateSL Γ h A) hne

open scoped Classical in

def cuspOrder (φ : ℍ → ℂ) : ℕ :=
  if H : ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam (wd Γ) (τ : ℂ)‖ ^ n ≤ ‖φ τ‖
  then H.choose else 0

theorem cuspOrder_spec (φ : ℍ → ℂ)
    (H : ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam (wd Γ) (τ : ℂ)‖ ^ n ≤ ‖φ τ‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam (wd Γ) (τ : ℂ)‖ ^ (cuspOrder Γ φ) ≤ ‖φ τ‖ := by
  rw [cuspOrder, dite_eq_left H]
  exact H.choose_spec

theorem exists_forall_cuspOrder_le [Γ.FiniteIndex] (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ m : ℕ, ∀ A : SL(2, ℤ), cuspOrder Γ (⇑h ∣[k] A) ≤ m := by
  classical
  let ψ : SL(2, ℤ) ⧸ Γ → ℕ := fun q => cuspOrder Γ (⇑h ∣[k] (q.out)⁻¹)
  obtain ⟨m, hm⟩ := (Set.finite_range ψ).bddAbove
  refine ⟨m, fun A => ?_⟩
  set B : SL(2, ℤ) := ((A⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ).out with hB
  have hq : ((A⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ) = (B : _) := (QuotientGroup.out_eq' _).symm
  rw [QuotientGroup.eq, inv_inv] at hq
  have hslash : ⇑h ∣[k] (A * B) = ⇑h :=
    SlashInvariantFormClass.slash_action_eq h (Matrix.SpecialLinearGroup.mapGL ℝ (A * B))
      (Subgroup.mem_map_of_mem _ hq)
  have key : ⇑h ∣[k] A = ⇑h ∣[k] B⁻¹ :=
    calc ⇑h ∣[k] A = ⇑h ∣[k] ((A * B) * B⁻¹) := by rw [mul_inv_cancel_right]
      _ = (⇑h ∣[k] (A * B)) ∣[k] B⁻¹ := SlashAction.slash_mul _ _ _ _
      _ = ⇑h ∣[k] B⁻¹ := by rw [hslash]
  rw [key]
  exact hm ⟨_, rfl⟩

theorem isBoundedAtImInfty_of_mul_eq [Γ.FiniteIndex] (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hh : h ≠ 0) (F₀ : ℍ → ℂ) (hF : ∀ τ, F₀ τ * h τ = g τ) (A : SL(2, ℤ)) {m : ℕ}
    (hm : cuspOrder Γ (⇑h ∣[k] A) ≤ m) :
    IsBoundedAtImInfty (fun τ : ℍ => F₀ (A • τ) * (ModularForm.discriminant τ) ^ m) := by
  obtain ⟨C, hC, hlow⟩ := cuspOrder_spec Γ _ (exists_qParam_pow_le_slash Γ h hh A)
  have hgA : IsBoundedAtImInfty (⇑g ∣[k] A) := ModularFormClass.bdd_at_infty (translateSL Γ g A)
  obtain ⟨D, hD⟩ := IntegralGammaAux.exists_norm_discriminant_le
  rw [IsBoundedAtImInfty, BoundedAtFilter] at hgA ⊢
  obtain ⟨M', hM'⟩ := hgA.bound
  refine Asymptotics.IsBigO.of_bound (max M' 0 * max D 0 ^ m / C) ?_
  filter_upwards [hlow, hM', hD] with τ h1 h2 h3
  simp only [Pi.one_apply, norm_one, mul_one] at h2 ⊢
  have hq0 : 0 < ‖Periodic.qParam (wd Γ) (τ : ℂ)‖ := by
    rw [Periodic.norm_qParam]; exact Real.exp_pos _
  have hq1 : ‖Periodic.qParam (wd Γ) (τ : ℂ)‖ ≤ 1 :=
    (IntegralGammaAux.norm_qParam_lt_one' (wd_pos Γ) τ).le
  have hq₁ : ‖Periodic.qParam 1 (τ : ℂ)‖ ≤ ‖Periodic.qParam (wd Γ) (τ : ℂ)‖ :=
    IntegralGammaAux.norm_qParam_one_le (one_le_wd Γ) τ
  have hab : ‖F₀ (A • τ)‖ * ‖(⇑h ∣[k] A) τ‖ = ‖(⇑g ∣[k] A) τ‖ := by
    rw [← norm_mul, ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ← mul_assoc, hF]
  rw [norm_mul, norm_pow]
  exact IntegralGammaAux.key_ineq (norm_nonneg _) (norm_nonneg _) hab h1
    (h2.trans (le_max_left _ _))
    (h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) hq₁ hq1 hq0
    (norm_nonneg _) hC (le_max_right _ _) (le_max_right _ _) hm

end Level

section Assembly

variable (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)

def liftForm [Γ.FiniteIndex] {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder Γ (⇑h ∣[k] A) ≤ m) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) ((m : ℤ) * 12) where
  toFun := F₀ * ⇑(Δ₁.pow m)
  slash_action_eq' γ hγ := by
    obtain ⟨γ, hγ', rfl⟩ := hγ
    have hΔ : (⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] γ = ⇑(Δ₁.pow m) :=
      SlashInvariantFormClass.slash_action_eq (Δ₁.pow m)
        (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩
    have e := ModularForm.mul_slash_SL2 0 ((m : ℤ) * 12) γ F₀ ⇑(Δ₁.pow m)
    rw [zero_add] at e
    show (F₀ * ⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] γ =
      F₀ * ⇑(Δ₁.pow m)
    rw [e, IntegralGammaAux.slash_zero_eq Γ g h hh F₀ hF₀ hF γ hγ', hΔ]
  holo' := hF₀.mul (Δ₁.pow m).holo'
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro A _
    have hΔ : (⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] A =
        ⇑(Δ₁.pow m) :=
      SlashInvariantFormClass.slash_action_eq (Δ₁.pow m)
        (Matrix.SpecialLinearGroup.mapGL ℝ A) ⟨A, rfl⟩
    have e := ModularForm.mul_slash_SL2 0 ((m : ℤ) * 12) A F₀ ⇑(Δ₁.pow m)
    rw [zero_add] at e
    show IsBoundedAtImInfty ((F₀ * ⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] A)
    rw [e, hΔ]
    have : (F₀ ∣[(0 : ℤ)] A * ⇑(Δ₁.pow m)) =
        fun τ => F₀ (A • τ) * ModularForm.discriminant τ ^ m := by
      funext τ
      simp [ModularForm.SL_slash_apply]
    rw [this]
    exact isBoundedAtImInfty_of_mul_eq Γ g h hh F₀ hF A (hm A)

theorem coe_liftForm' [Γ.FiniteIndex] {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder Γ (⇑h ∣[k] A) ≤ m) :
    ⇑(liftForm Γ g h hh F₀ hF₀ hF m hm) = F₀ * ⇑(Δ₁.pow m) := rfl

theorem coe_liftForm [Γ.FiniteIndex] {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder Γ (⇑h ∣[k] A) ≤ m) :
    (⇑(liftForm Γ g h hh F₀ hF₀ hF m hm)) * ⇑h = ⇑g * ⇑((Δ₀ Γ).pow m) := by
  rw [coe_liftForm']
  funext τ
  simp only [Pi.mul_apply, ModularForm.coe_pow, Pi.pow_apply, IntegralGammaAux.coe_Δ₀,
    IntegralGammaAux.coe_Δ₁]
  rw [mul_right_comm, hF]

include hT in

theorem qL_liftForm_mul [Γ.FiniteIndex] {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder Γ (⇑h ∣[k] A) ≤ m) :
    qL ⇑(liftForm Γ g h hh F₀ hF₀ hF m hm) * qL ⇑h =
      qL ⇑g * qL (ModularForm.discriminant) ^ m := by
  have h1 := ModularForm.qExpansion_mul_coe one_pos
    (IntegralGammaAux.one_mem_strictPeriods Γ hT)
    (liftForm Γ g h hh F₀ hF₀ hF m hm) h
  have h2 := ModularForm.qExpansion_mul_coe one_pos
    (IntegralGammaAux.one_mem_strictPeriods Γ hT) g ((Δ₀ Γ).pow m)
  have h3 := ModularForm.qExpansion_pow one_pos (IntegralGammaAux.one_mem_strictPeriods Γ hT)
    (Δ₀ Γ) m
  rw [coe_liftForm] at h1
  simp only [qL, ← PowerSeries.coe_mul, ← PowerSeries.coe_pow, ← h1, h2, h3,
    IntegralGammaAux.coe_Δ₀]

include hT in

theorem isIntegral_of_forall_isBoundedUnder [Γ.FiniteIndex] {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hb : ∀ τ : ℍ, IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖g z / h z‖)) :
    IsIntegral (Algebra.adjoin ℂ ({jqModC ℂ} : Set (LaurentSeries ℂ)))
      (qL ⇑g / qL ⇑h) := by
  obtain ⟨F₀, hF₀, hF⟩ := IntegralGammaAux.exists_F₀ Γ g h hh hb
  obtain ⟨m, hm⟩ := exists_forall_cuspOrder_le Γ h
  set F := liftForm Γ g h hh F₀ hF₀ hF m hm with hFdef
  have hq : qL ⇑F * qL ⇑h =
      qL ⇑g * qL ModularForm.discriminant ^ m :=
    qL_liftForm_mul Γ hT g h hh F₀ hF₀ hF m hm
  have hxF : qL ⇑F / qL ModularForm.discriminant ^ m =
      qL ⇑g / qL ⇑h := by
    rw [div_eq_div_iff (pow_ne_zero _ IntegralGammaAux.qL_discriminant_ne_zero)
      (IntegralGammaAux.qL_ne_zero Γ hT h hh)]
    rw [hq]
  have key := ModularForm.isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic
    (IntegralGammaAux.one_mem_strictPeriods Γ hT) m (k := (m : ℤ) * 12) (by ring) F
  rw [← jqModC_eq_qExpansion_E4_cube_div_discriminant] at key
  rw [← hxF]
  exact key

end Assembly

end IntegralFiniteIndex

theorem isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hb : ∀ τ : UpperHalfPlane, Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : UpperHalfPlane => ‖g z / h z‖)) :
    IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) /
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑h)) :=
  ModularCurve.IntegralFiniteIndex.isIntegral_of_forall_isBoundedUnder Γ hT g h hh hb

end ModularCurve
