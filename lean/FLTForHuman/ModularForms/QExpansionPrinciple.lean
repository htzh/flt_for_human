/-
  R1, the level-one q-expansion principle — the constancy kernel.

  A holomorphic `SL₂(ℤ)`-invariant `q`-series is constant: if `F : ℍ → ℂ` is
  presented everywhere by a power series `∑_{m ≥ 0} c_m q(τ)^m` and is invariant
  under `SL₂(ℤ)`, then `c_m = 0` for every `m ≠ 0`. This is the minimal named form
  of the one genuinely analytic input of the modular-equation argument (R1 of
  `base/013-riemann-existence-and-the-q-expansion-principle.md` §3, §6).

  The analytic content is mathlib's `ModularForm.eq_const_of_weight_zero`: the
  invariant `F` is packaged as a weight-zero level-one `ModularForm`, whose only
  instances are the constants. Everything else is the bookkeeping that turns a
  `HasSum` on `ℍ` into the `ModularForm` fields.

  ## Source

  The exported kernel is stated verbatim from its pin wrapper
  `Theorems/Thm_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean`
  (FLT `anthropics/fermats-last-theorem@aa2d8b3`), whose proof is the 186-line
  `P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean` under
  `namespace ModularCurve.Realized`. Nothing in the pin block comes from
  `P2M/Util`, so the port is mathlib-only for this part.

  ## The mathlib-first audit (pin helper → v4.34.0)

  Before transcribing anything the pin's block was looked up in our pinned
  mathlib; the private helpers below exist only where no public statement does.
  Of the pin's 14 helpers:

  | pin helper | replaced by |
  |---|---|
  | `norm_qParam_lt_one_of_pos` | public `Periodic.norm_qParam_lt_one` |
  | `hasSum_cuspFunction_punctured` | private in mathlib; re-derived (needed for `mdifferentiable`) |
  | `hasFPowerSeriesOnBall_update` | private in mathlib; re-derived (needed for `mdifferentiable`) |
  | `discFun`, `hasSum_discFun`, `discFun_zero`, `continuousAt_discFun` | dropped; the public `cuspFunction` API replaces them |
  | `apply_eq_discFun`, `differentiableOn_discFun` | dropped; `apply_eq_cuspFunction` / `differentiableAt_cuspFunction_of_hasSum` are the private forms the `mdifferentiable` route needs |
  | `mdifferentiable` | **ported** — no public mathlib lemma derives `MDiff` from a `HasSum` |
  | `tendsto_atImInfty` | public `UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion` |
  | `isBoundedAtImInfty` | public `UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion` |
  | `periodic` | dropped; public `UpperHalfPlane.periodic_comp_ofComplex` is the counterpart (topic 7 needs it) |
  | `coeff_unique` | public `UpperHalfPlane.qExpansion_coeff_unique` audited; unusable here (finding below), so the pin's argument is ported |
  | `solution` | this module's exported kernel |

  Two bridges are needed and are confined to the private block: mathlib's
  `*_of_hasSum_qExpansion` lemmas use `c_m • q^m` where the kernel states
  `c_m * q^m` (equal on `ℂ` via `smul_eq_mul`), and `UpperHalfPlane.mdifferentiable_iff`
  is the route from "power series on the disc" to `MDiff`.

  **Finding on `coeff_unique`.** The audit expected the pin's 26-line
  `coeff_unique` to drop for mathlib's one-line `UpperHalfPlane.qExpansion_coeff_unique`.
  It does state exactly the required fact, but its `{F : Type*} [FunLike F ℍ ℂ]`
  signature instantiates at the bare function type `ℍ → ℂ` in the kernel, and the
  resulting unification unfolds `DFunLike.coe` (and `FunLike`, `limUnder`,
  `cuspFunction`) millions of times: a deterministic `whnf` heartbeat timeout at
  the default 200 000 *and* at the package's 4 000 000, with
  `[reduction] DFunLike.coe ↦ 5143553` under `set_option diagnostics true`. The
  pin's `coeff_unique` (restated below, over `hasFPowerSeriesOnBall_update` and
  `tendsto_nhds_unique`) has no `FunLike` quantifier and compiles immediately, so
  it is ported rather than replaced. This is the one §2.1 substitution that did
  not go through.

  ## Assumptions

  `UpperHalfPlane`, `Function.Periodic.qParam`, `cuspFunction`, `ModularForm` and
  `MDiff` are mathlib's; `jq` and `PoleOrderLE` are the port's
  (`FLTForHuman/ModularCurve/Defs/`). The corollary
  `mem_adjoin_jq_of_poleOrderLE_zero` is ours: it has no FLT source and is the
  `n = 0` end of R1's Hauptmodul form (topic 7), used here as the wire test.
-/
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Defs.PhiGen

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function
open scoped MatrixGroups ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

/-! ## The private helper block

The pin's `Realized` block, reduced to what the `mdifferentiable` route actually
needs. `hasSum_cuspFunction_of_hasSum_punctured` and `hasFPowerSeriesOnBall_update`
are mathlib-private; `mdifferentiable` is the one genuinely missing step. -/

/-- The pin's `Realized.hasSum_cuspFunction_punctured` (mathlib-private in
`QExpansion.lean`): a `HasSum` on `ℍ` reads as a `HasSum` of the descended
`cuspFunction` value on the punctured disc. -/
private theorem hasSum_cuspFunction_of_hasSum_punctured {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hh : 0 < h) (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • 𝕢 h (τ : ℂ) ^ m) (f τ))
    {q : ℂ} (hq : ‖q‖ < 1) (hq1 : q ≠ 0) :
    HasSum (fun m : ℕ => c m • q ^ m) (cuspFunction h f q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := Periodic.cuspFunction_eq_of_nonzero h (f ∘ ofComplex) hq1
  have h3 : cuspFunction h f q = f τ := by
    simpa [τ, cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  have h4 : 𝕢 h (τ : ℂ) = q := Periodic.qParam_right_inv hh.ne' hq1
  rw [h3, ← h4]
  exact hf τ

/-- The pin's `Realized.hasFPowerSeriesOnBall_update` (mathlib-private): the
`HasSum` on `ℍ`, with the value at `q = 0` filled in by `c 0`, is a radius-`1`
power series. The radius bound is the summability read off
`hasSum_cuspFunction_of_hasSum_punctured` at real `q = r`. -/
private theorem hasFPowerSeriesOnBall_update {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • 𝕢 h (τ : ℂ) ^ m) (f τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      have : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [smul_eq_mul, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
        (hasSum_cuspFunction_of_hasSum_punctured hh hf (q := r) (by simpa using hr)
          (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm]
        using hasSum_cuspFunction_of_hasSum_punctured hh hf hy hy'

/-- The pin's `Realized.apply_eq_discFun`, in the public `cuspFunction` form:
`F` is the `cuspFunction` value at `q(τ)`. This is `HasSum.unique` against
`hasSum_cuspFunction_of_hasSum_punctured`, and it does not need `h`-periodicity. -/
private theorem apply_eq_cuspFunction {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • 𝕢 h (τ : ℂ) ^ m) (f τ)) (τ : ℍ) :
    f τ = cuspFunction h f (𝕢 h (τ : ℂ)) :=
  (hf τ).unique (hasSum_cuspFunction_of_hasSum_punctured hh hf
    (Periodic.norm_qParam_lt_one hh τ.im_pos) (Periodic.qParam_ne_zero _))

/-- The pin's `Realized.differentiableOn_discFun` at a punctured disc point: the
radius-`1` power series of `hasFPowerSeriesOnBall_update` is complex-differentiable,
and it agrees with `cuspFunction` away from `0`. -/
private theorem differentiableAt_cuspFunction_of_hasSum {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hh : 0 < h) (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • 𝕢 h (τ : ℂ) ^ m) (f τ))
    {q : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0) : DifferentiableAt ℂ (cuspFunction h f) q := by
  have h1 : DifferentiableOn ℂ (update (cuspFunction h f) 0 (c 0)) (Metric.ball 0 1) := by
    have h := (hasFPowerSeriesOnBall_update hh hf).differentiableOn
    rwa [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one] at h
  have hqball : q ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hq
  have h2 : DifferentiableAt ℂ (update (cuspFunction h f) 0 (c 0)) q :=
    h1.differentiableAt (Metric.isOpen_ball.mem_nhds hqball)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hq'] with y hy
  exact (update_of_ne hy (c 0) (cuspFunction h f)).symm

/-- The pin's `Realized.mdifferentiable` — the one helper the mathlib audit left
without a public counterpart: nothing public derives `MDiff` from a `HasSum`. The
power series on the disc composes with `q ↦ q(τ)`, and `apply_eq_cuspFunction`
identifies `F ∘ ofComplex` with that composite on `{Im > 0}`. -/
private theorem mdifferentiable {h : ℝ} {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (f τ)) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f := by
  have hf' : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • 𝕢 h (τ : ℂ) ^ m) (f τ) := fun τ => by
    simpa only [smul_eq_mul] using hf τ
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 : DifferentiableOn ℂ (fun z : ℂ => cuspFunction h f (𝕢 h z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hzq : ‖𝕢 h z‖ < 1 := Periodic.norm_qParam_lt_one hh hz
    have hzq' : 𝕢 h z ≠ 0 := Periodic.qParam_ne_zero _
    exact ((differentiableAt_cuspFunction_of_hasSum hh hf' hzq hzq').comp z
      ((Periodic.differentiable_qParam (h := h)) z)).differentiableWithinAt
  refine h1.congr fun z hz => ?_
  rw [Function.comp_apply, apply_eq_cuspFunction hh hf' (ofComplex z)]
  exact congrArg (fun w : ℍ => cuspFunction h f (𝕢 h (w : ℂ)))
    (UpperHalfPlane.ofComplex_apply_of_im_pos hz)

/-- The pin's `Realized.coeff_unique`: two `HasSum` presentations of the same `F`
have equal coefficients. Both presentations are power series at `0`
(`hasFPowerSeriesOnBall_update`); continuity forces the same value at `0`
(`tendsto_nhds_unique`), and then the formal multilinear series coincide.

Mathlib's `UpperHalfPlane.qExpansion_coeff_unique` states the same thing, but its
`FunLike`-generic `{F : Type*} [FunLike F ℍ ℂ]` signature makes the call at the
bare function type `ℍ → ℂ` unfold `DFunLike.coe` millions of times (a
deterministic `whnf` timeout), so the pin's own argument is kept. -/
private theorem coeff_unique {h : ℝ} {F : ℍ → ℂ} {c d : ℕ → ℂ} (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • 𝕢 h (τ : ℂ) ^ m) (F τ))
    (hF' : ∀ τ : ℍ, HasSum (fun m : ℕ => d m • 𝕢 h (τ : ℂ) ^ m) (F τ)) : c = d := by
  have hc := hasFPowerSeriesOnBall_update hh hF
  have hd := hasFPowerSeriesOnBall_update hh hF'
  have hlim : ∀ {e : ℕ → ℂ}, HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (e 0))
      (.ofScalars ℂ e) 0 1 → Tendsto (cuspFunction h F) (𝓝[≠] 0) (𝓝 (e 0)) := by
    intro e he
    have h1 : Tendsto (update (cuspFunction h F) 0 (e 0)) (𝓝[≠] 0) (𝓝 (e 0)) := by
      have h2 := he.hasFPowerSeriesAt.continuousAt.tendsto
      rw [update_self] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact update_of_ne hz (e 0) (cuspFunction h F)
  have h0 : c 0 = d 0 := tendsto_nhds_unique (hlim hc) (hlim hd)
  have hd' : HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (c 0)) (.ofScalars ℂ d) 0 1 :=
    h0 ▸ hd
  have heq := hc.hasFPowerSeriesAt.eq_formalMultilinearSeries hd'.hasFPowerSeriesAt
  funext m
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) heq

/-! ## R1: the constancy kernel -/

/-- R1, the level-one q-expansion principle, in kernel form: a holomorphic,
`SL₂(ℤ)`-invariant `q`-series is constant. `hF` is the realization on `ℍ`
(holomorphy at the cusp: the exponents are `m ≥ 0`), `hinv` is invariance of
weight zero, and the conclusion is the vanishing of every nonconstant Fourier
coefficient.

The analysis is mathlib's `ModularForm.eq_const_of_weight_zero`; the proof
packages `F` as a weight-zero level-one `ModularForm` and compares the two
`q`-series presentations of `F` with `coeff_unique`. -/
theorem coeff_eq_zero_of_hasSum_of_slash_invariant
    {F : UpperHalfPlane → ℂ} {c : ℕ → ℂ}
    (hF : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    {m : ℕ} (hm : m ≠ 0) : c m = 0 := by
  have hF' : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • 𝕢 1 (τ : ℂ) ^ m) (F τ) := fun τ => by
    simpa only [smul_eq_mul] using hF τ
  have hslash : ∀ γ : SL(2, ℤ), F ∣[(0 : ℤ)] γ = F := fun γ => by
    funext τ
    rw [ModularForm.SL_slash_apply, hinv, neg_zero, zpow_zero, mul_one]
  let f : ModularForm 𝒮ℒ 0 :=
    { toFun := F
      slash_action_eq' := fun A hA => by
        obtain ⟨γ, rfl⟩ := hA
        exact hslash γ
      holo' := mdifferentiable one_pos hF
      bdd_at_cusps' := fun {cusp} hc => by
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hslash γ]
        exact isBoundedAtImInfty_of_hasSum_qExpansion one_pos hF' }
  obtain ⟨κ, hκ⟩ := ModularForm.eq_const_of_weight_zero f
  have hFκ : ∀ τ : ℍ, F τ = κ := fun τ => congr_fun hκ τ
  have hF'' : ∀ τ : ℍ,
      HasSum (fun m : ℕ => (Pi.single (M := fun _ => ℂ) 0 κ m) • 𝕢 1 (τ : ℂ) ^ m) (F τ) := by
    intro τ
    rw [hFκ τ]
    have := hasSum_ite_eq 0 κ
    refine this.congr_fun fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  have heq : c = Pi.single (M := fun _ => ℂ) 0 κ := coeff_unique one_pos hF' hF''
  rw [heq, Pi.single_apply, ite_eq_right hm]

/-! ## The `n = 0` end of the Hauptmodul form, and the wire test -/

/-- Our corollary — the `n = 0` case of R1's Hauptmodul form (topic 7): a Laurent
series realized by an invariant `F` with no pole at `∞` is a *constant*, hence an
element of `ℚ[jq]`.

This statement has no FLT source. The pin reaches the Hauptmodul form through
`exists_aeval_jq_sub_holomorphicAtInfty` (pole killing, topic 7); here the pole
bound is an explicit hypothesis, and the proof is a genuine cross-module
composition: it restricts the `ℤ`-indexed `HasSum` to `ℕ`
(`Function.Injective.hasSum_iff`) using `PoleOrderLE f 0`, applies
`coeff_eq_zero_of_hasSum_of_slash_invariant` to kill the positive coefficients,
and reads the result off `HahnSeries.single 0 (f.coeff 0)` via the port's
`algebraMap_laurentSeries_eq_single`. -/
theorem mem_adjoin_jq_of_poleOrderLE_zero
    (f : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    (h0 : PoleOrderLE f 0) : f ∈ Algebra.adjoin ℚ {jq} := by
  have hneg : ∀ m : ℤ, m < 0 → f.coeff m = 0 := fun m hm => h0 m (by simpa using hm)
  have hF' : ∀ τ : ℍ,
      HasSum (fun m : ℕ => ((f.coeff (m : ℤ) : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ) := by
    intro τ
    have h := hF τ
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff] at h
    · exact h
    · intro m hm
      have hm' : m < 0 := by
        by_contra hge
        push Not at hge
        exact hm ⟨m.toNat, Int.toNat_of_nonneg hge⟩
      simp [hneg m hm']
  have hvan : ∀ n : ℕ, n ≠ 0 → f.coeff (n : ℤ) = 0 := fun n hn => by
    have := coeff_eq_zero_of_hasSum_of_slash_invariant (F := F)
      (c := fun n : ℕ => ((f.coeff (n : ℤ) : ℚ) : ℂ)) hF' hinv hn
    exact_mod_cast this
  have hfconst : f = HahnSeries.single 0 (f.coeff 0) := by
    ext m
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · rw [hneg m hm, HahnSeries.coeff_single_of_ne hm.ne]
    · rw [HahnSeries.coeff_single_same]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm.le
      rw [HahnSeries.coeff_single_of_ne (by exact_mod_cast hm.ne')]
      exact hvan n (by exact_mod_cast hm.ne')
  rw [hfconst, ← algebraMap_laurentSeries_eq_single]
  exact Subalgebra.algebraMap_mem _ _

/-! ## Non-vacuity -/

section Example

/-- The constant form `F = const κ`, `c = Pi.single 0 κ` satisfies both
hypotheses of the kernel, so the kernel's conclusion is not vacuous: its `m ≠ 0`
coefficients are `0`. (`hasSum_ite_eq` is the constant `q`-series; `const` is
trivially `SL₂(ℤ)`-invariant.) -/
example (κ : ℂ) {m : ℕ} (hm : m ≠ 0) :
    (Pi.single (M := fun _ => ℂ) 0 κ : ℕ → ℂ) m = 0 := by
  refine coeff_eq_zero_of_hasSum_of_slash_invariant (F := Function.const ℍ κ)
    (c := Pi.single (M := fun _ => ℂ) 0 κ) ?_ ?_ hm
  · intro τ
    have := hasSum_ite_eq 0 κ
    refine this.congr_fun fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · intro γ τ
    rfl

end Example

end ModularCurve

end
