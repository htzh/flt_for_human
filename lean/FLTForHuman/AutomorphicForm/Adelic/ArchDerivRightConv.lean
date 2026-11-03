/-
  Differentiating a right convolution along an archimedean flow — the **real** place.

  For a real place `w`, a direction `d : ArchDir`, continuous `φ` and a factorisable test
  function `α`, the right convolution `rightConv K φ α` is archimedean-smooth and its
  archimedean derivative is again a right convolution, the derivative having moved onto
  the test function along the **negative** flow (the integration variable is on the left):

    `archDerivAt hw d (rightConv K φ α)`
      `= rightConv K φ (fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0)`.

  The headline is the pin's triple conjunction: the identity above; the **tensor form** of
  that differentiated test factor (`∃ fa', IsArchTestFactor fa' ∧ …`, which is the
  left-derivative chart `leftDerivFactor`/`liftPhi'` of `FactorizableTestFnArchSmoothLeft`);
  and the **integration-by-parts** identity
  `rightConv φ (Dγ · ω) = -rightConv (Dφ) (γ · ω)` for `γ` compactly supported and `ω`
  invariant under the flow — the adjointness that makes `archDerivAt` skew-symmetric
  against the Haar measure, and the identity the Casimir/commutator family builds on.

  Transcribed from `P2M/Sol/S_…` (pinned `aa2d8b3`, 1,246 lines) with the pin's wrapper
  namespace dropped. Of the pin's 113 `private` prelude declarations, 72 are declarations
  the port already carries as the **left** half of the archimedean chart and its matrix
  vocabulary (`e8l5*`/`l5*` → `lift*`, `e8tc_*`/`tc_*` → `chart_*`, `e8leftDeriv` →
  `leftDerivFactor`, `l5Ent` → `liftEntry`, `Ent`/`tcDetSet` → `ArchEntry`/`nonsingEntries`,
  `leftDeriv` → `leftDerivFactor`); they are imported from
  `Adelic/FactorizableTestFnArchSmoothLeft.lean` and **not** restated here. The 41 that
  have no port twin keep the pin's own file-local names (`l5F`, `l5E`, `TcFamily`, `tc_*`,
  `af_*`), because the port has never carried them at another name and the pin↔port diff
  stays mechanical that way; they are `private`, so the module's public surface is the
  headline alone.

  spec-pin: Theorems/Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothLeft
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmooth
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
-- The Casimir engine (the `leftCasimir_eq_archCasimirAt_of_isArchSmoothAt` half): the two
-- Casimir rows of SET-AF9 are transcribed against it, and nothing below this module imports it.
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimir
-- The cusp/level vocabulary of the second Casimir row's statement
-- (`levelInvariantSubmodule`, `productionPinsOf`, `levelOne`, `heckeGen`, `adelicBox`).
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicHaar.MulRightInvariant

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal isometryEquivRealOfIsReal)
open scoped Topology

noncomputable section

namespace AutomorphicForm

open IsFactorizableTestFn

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

section TestData

open MeasureTheory
open scoped Pointwise

set_option linter.style.haveILetI false in
private theorem l5_integrable_conv_integrand {φ α : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hαc : Continuous α)
    (hαs : HasCompactSupport α) (g : AdelicGL2 (𝓞 K) K) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    Integrable (fun y => φ (g * y) * α y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  refine ((hφ.comp (continuous_const.mul continuous_id)).mul hαc).integrable_of_hasCompactSupport (hαs.mono ?_)
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by show φ (g * y) * α y = 0; rw [h0, mul_zero])

end TestData

section EngineBridge

open MeasureTheory Metric Set

section Engine

variable {X : Type} [MeasurableSpace X] (ν : Measure X)
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private structure TcFamily (F : X → ArchEntry → Y) : Prop where
  smooth : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (F x) nonsingEntries
  meas : ∀ m : ℕ, ∀ e ∈ nonsingEntries, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ m (F x) e) ν
  bound : ∀ e₀ ∈ nonsingEntries, ∀ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ball e₀ ρ ⊆ nonsingEntries ∧
    ∃ C : ℝ, ∀ᵐ x ∂ν, ∀ e ∈ ball e₀ ρ, ‖iteratedFDeriv ℝ m (F x) e‖ ≤ C

variable {ν}

private theorem tc_aesm_of_zero {g : X → ArchEntry → Y} {e : ArchEntry}
    (h : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ 0 (g x) e) ν) :
    AEStronglyMeasurable (fun x => g x e) ν := by
  have hfun : (fun x => g x e) =
      fun x => (continuousMultilinearCurryFin0 ℝ ArchEntry Y) (iteratedFDeriv ℝ 0 (g x) e) := by
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    simp
  rw [hfun]
  exact (continuousMultilinearCurryFin0 ℝ ArchEntry Y).continuous.comp_aestronglyMeasurable h

private theorem tc_aesm_fderiv_order {F : X → ArchEntry → Y} (hF : TcFamily ν F) (m : ℕ) {e : ArchEntry}
    (he : e ∈ nonsingEntries) :
    AEStronglyMeasurable (fun x => iteratedFDeriv ℝ m (fderiv ℝ (F x)) e) ν := by
  have hfun : (fun x => iteratedFDeriv ℝ m (fderiv ℝ (F x)) e) =
      fun x => (continuousMultilinearCurryRightEquiv' ℝ m ArchEntry Y) (iteratedFDeriv ℝ (m + 1) (F x) e) := by
    funext x
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
  rw [hfun]
  exact (continuousMultilinearCurryRightEquiv' ℝ m ArchEntry Y).continuous.comp_aestronglyMeasurable
    (hF.meas (m + 1) e he)

private theorem tc_norm_fderiv_eq (f : ArchEntry → Y) (e : ArchEntry) :
    ‖fderiv ℝ f e‖ = ‖iteratedFDeriv ℝ 1 f e‖ := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]

private theorem tc_differentiableAt {F : X → ArchEntry → Y} (hF : TcFamily ν F) (x : X) {e : ArchEntry}
    (he : e ∈ nonsingEntries) :
    DifferentiableAt ℝ (F x) e :=
  ((hF.smooth x).differentiableOn (by simp) e he).differentiableAt (chart_isOpen_nonsingEntries.mem_nhds he)

private theorem tc_integrable_fderiv [IsFiniteMeasure ν] {F : X → ArchEntry → Y} (hF : TcFamily ν F) {e₀ : ArchEntry}
    (he₀ : e₀ ∈ nonsingEntries) :
    Integrable (fun x => fderiv ℝ (F x) e₀) ν := by
  obtain ⟨ρ, hρ, -, C, hC⟩ := hF.bound e₀ he₀ 1
  refine Integrable.of_bound (tc_aesm_of_zero (tc_aesm_fderiv_order hF 0 he₀)) C (hC.mono fun x hx => ?_)
  rw [tc_norm_fderiv_eq]
  exact hx e₀ (mem_ball_self hρ)

private theorem tc_hasFDerivAt_integral [IsFiniteMeasure ν] {F : X → ArchEntry → Y} (hF : TcFamily ν F)
    {e₀ : ArchEntry} (he₀ : e₀ ∈ nonsingEntries) :
    HasFDerivAt (fun e => ∫ x, F x e ∂ν) (∫ x, fderiv ℝ (F x) e₀ ∂ν) e₀ := by
  obtain ⟨ρ, hρ, hball, C, hC⟩ := hF.bound e₀ he₀ 1
  obtain ⟨ρ₀, hρ₀, -, C₀, hC₀⟩ := hF.bound e₀ he₀ 0
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := ν) (F := fun e x => F x e)
    (F' := fun e x => fderiv ℝ (F x) e) (bound := fun _ => C) (ball_mem_nhds e₀ hρ)
    (Filter.eventually_of_mem (chart_isOpen_nonsingEntries.mem_nhds he₀) fun e he => tc_aesm_of_zero (hF.meas 0 e he))
    (Integrable.of_bound (tc_aesm_of_zero (hF.meas 0 e₀ he₀)) C₀ (hC₀.mono fun x hx => by
      have h0 := hx e₀ (mem_ball_self hρ₀)
      rwa [norm_iteratedFDeriv_zero] at h0))
    (tc_aesm_of_zero (tc_aesm_fderiv_order hF 0 he₀))
    (hC.mono fun x hx e he => by rw [tc_norm_fderiv_eq]; exact hx e he)
    (integrable_const C)
    (Filter.Eventually.of_forall fun x e he => (tc_differentiableAt hF x (hball he)).hasFDerivAt)
  exact h

private theorem tc_contDiffOn_integral_nat [IsFiniteMeasure ν] (n : ℕ) :
    ∀ {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : X → ArchEntry → Z),
      TcFamily ν F → ContDiffOn ℝ n (fun e => ∫ x, F x e ∂ν) nonsingEntries := by
  induction n with
  | zero =>
    intro Z _ _ F hF
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun e he => (tc_hasFDerivAt_integral hF he).continuousAt.continuousWithinAt
  | succ n ih =>
    intro Z _ _ F hF
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen chart_isOpen_nonsingEntries]
    refine ⟨fun e he => (tc_hasFDerivAt_integral hF he).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hF' : TcFamily ν fun x => fderiv ℝ (F x) :=
      { smooth := fun x => (hF.smooth x).fderiv_of_isOpen chart_isOpen_nonsingEntries (by simp)
        meas := fun m e he => tc_aesm_fderiv_order hF m he
        bound := fun e₀ he₀ m => by
          obtain ⟨ρ, hρ, hball, C, hC⟩ := hF.bound e₀ he₀ (m + 1)
          exact ⟨ρ, hρ, hball, C, hC.mono fun x hx e he => by rw [norm_iteratedFDeriv_fderiv]; exact hx e he⟩ }
    exact (ih _ hF').congr fun e he => (tc_hasFDerivAt_integral hF he).fderiv

private theorem tc_contDiffOn_integral [IsFiniteMeasure ν] {F : X → ArchEntry → Y} (hF : TcFamily ν F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e => ∫ x, F x e ∂ν) nonsingEntries :=
  contDiffOn_infty.mpr fun n => tc_contDiffOn_integral_nat n F hF

private theorem tc_deriv_integral_comp [IsFiniteMeasure ν] {F : X → ArchEntry → Y} (hF : TcFamily ν F)
    (γ : ℝ → ArchEntry) (hγ : DifferentiableAt ℝ γ 0) (h0 : γ 0 ∈ nonsingEntries) :
    deriv (fun t : ℝ => ∫ x, F x (γ t) ∂ν) 0 = ∫ x, deriv (fun t : ℝ => F x (γ t)) 0 ∂ν := by
  have hγ' := hγ.hasDerivAt
  have h1 := (tc_hasFDerivAt_integral hF h0).comp_hasDerivAt (0 : ℝ) hγ'
  have h2 : ∀ x, deriv (fun t : ℝ => F x (γ t)) 0 = fderiv ℝ (F x) (γ 0) (deriv γ 0) := fun x =>
    ((tc_differentiableAt hF x h0).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ').deriv
  change deriv ((fun e => ∫ x, F x e ∂ν) ∘ γ) 0 = _
  rw [h1.deriv, ContinuousLinearMap.integral_apply (tc_integrable_fderiv hF h0)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (h2 x).symm)

end Engine

section Affine

variable {X : Type} [MeasurableSpace X] {ν : Measure X}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem af_iteratedFDeriv {Φ : V → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (ξ : ℂ) (c : V)
    (L : ArchEntry →L[ℝ] V) (m : ℕ) (e : ArchEntry) :
    iteratedFDeriv ℝ m (fun e' => ξ • Φ (c + L e')) e =
      ξ • (iteratedFDeriv ℝ m Φ (c + L e)).compContinuousLinearMap fun _ : Fin m => L := by
  have hΦc : ContDiff ℝ (⊤ : ℕ∞) fun v : V => Φ (c + v) := hΦ.comp (contDiff_const.add contDiff_id)
  have hg : ContDiff ℝ (⊤ : ℕ∞) ((fun v : V => Φ (c + v)) ∘ ⇑L) := hΦc.comp L.contDiff
  show iteratedFDeriv ℝ m (ξ • ((fun v : V => Φ (c + v)) ∘ ⇑L)) e = _
  rw [iteratedFDeriv_const_smul_apply (hg.of_le (by exact_mod_cast le_top)).contDiffAt,
    L.iteratedFDeriv_comp_right hΦc e (by exact_mod_cast le_top), iteratedFDeriv_comp_add_left]

private theorem af_continuous_closedForm {Φ : V → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (m : ℕ) (e : ArchEntry) :
    Continuous fun p : V × (ArchEntry →L[ℝ] V) =>
      (iteratedFDeriv ℝ m Φ (p.1 + p.2 e)).compContinuousLinearMap fun _ : Fin m => p.2 := by
  have hL : Continuous fun p : V × (ArchEntry →L[ℝ] V) => p.2 := continuous_snd
  have hinner : Continuous fun p : V × (ArchEntry →L[ℝ] V) => iteratedFDeriv ℝ m Φ (p.1 + p.2 e) :=
    (hΦ.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).comp
      (continuous_fst.add (hL.clm_apply continuous_const))
  have houter : Continuous fun p : V × (ArchEntry →L[ℝ] V) =>
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ (fun _ : Fin m => ArchEntry)
        (fun _ : Fin m => V) ℂ fun _ : Fin m => p.2 :=
    (ContinuousMultilinearMap.coe_continuous (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin m => ArchEntry) (fun _ : Fin m => V) ℂ)).comp (continuous_pi fun _ => hL)
  have h := houter.clm_apply hinner
  simpa only [ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply] using h

private theorem af_family [FiniteDimensional ℝ V] {Φ : V → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {χ : X → ℂ}
    (hχ : AEStronglyMeasurable χ ν) {c : X → V} (hc : AEStronglyMeasurable c ν) {L : X → ArchEntry →L[ℝ] V}
    (hL : AEStronglyMeasurable L ν) {Cχ Cc CL : ℝ} (hχb : ∀ᵐ x ∂ν, ‖χ x‖ ≤ Cχ) (hcb : ∀ᵐ x ∂ν, ‖c x‖ ≤ Cc)
    (hLb : ∀ᵐ x ∂ν, ‖L x‖ ≤ CL) :
    TcFamily ν fun x e => χ x • Φ (c x + L x e) where
  smooth x := ((hΦ.comp (contDiff_const.add (L x).contDiff)).const_smul (χ x)).contDiffOn
  meas m e _ := by
    have hfun : (fun x => iteratedFDeriv ℝ m (fun e' => χ x • Φ (c x + L x e')) e) = fun x =>
        χ x • (fun p : V × (ArchEntry →L[ℝ] V) =>
          (iteratedFDeriv ℝ m Φ (p.1 + p.2 e)).compContinuousLinearMap fun _ : Fin m => p.2) (c x, L x) := by
      funext x
      exact af_iteratedFDeriv hΦ (χ x) (c x) (L x) m e
    rw [hfun]
    exact hχ.smul ((af_continuous_closedForm hΦ m e).comp_aestronglyMeasurable (hc.prodMk hL))
  bound e₀ he₀ m := by
    obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp chart_isOpen_nonsingEntries e₀ he₀

    have hρ : ∀ {x : X} {e : ArchEntry}, ‖c x‖ ≤ Cc → ‖L x‖ ≤ CL → e ∈ ball e₀ (min ε 1) →
        c x + L x e ∈ closedBall (0 : V) (|Cc| + |CL| * (‖e₀‖ + 1)) := by
      intro x e hcx hLx he
      rw [mem_ball_iff_norm] at he
      have he1 : ‖e‖ ≤ ‖e₀‖ + 1 := by
        have h1 := norm_sub_norm_le e e₀
        have h2 : ‖e - e₀‖ < 1 := he.trans_le (min_le_right _ _)
        linarith
      rw [mem_closedBall_zero_iff]
      calc ‖c x + L x e‖ ≤ ‖c x‖ + ‖L x e‖ := norm_add_le _ _
        _ ≤ ‖c x‖ + ‖L x‖ * ‖e‖ := add_le_add le_rfl ((L x).le_opNorm e)
        _ ≤ |Cc| + |CL| * (‖e₀‖ + 1) :=
          add_le_add (hcx.trans (le_abs_self _))
            (mul_le_mul (hLx.trans (le_abs_self _)) he1 (norm_nonneg _) (abs_nonneg _))
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V) (|Cc| + |CL| * (‖e₀‖ + 1))).exists_bound_of_continuousOn
      (hΦ.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).continuousOn
    refine ⟨min ε 1, lt_min hε one_pos, (ball_subset_ball (min_le_left _ _)).trans hεS,
      |Cχ| * (|M| * |CL| ^ m), ?_⟩
    filter_upwards [hχb, hcb, hLb] with x hχx hcx hLx
    intro e he
    rw [af_iteratedFDeriv hΦ (χ x) (c x) (L x) m e, norm_smul]
    have hΦb : ‖iteratedFDeriv ℝ m Φ (c x + L x e)‖ ≤ |M| := (hM _ (hρ hcx hLx he)).trans (le_abs_self _)
    have hcomp : ‖(iteratedFDeriv ℝ m Φ (c x + L x e)).compContinuousLinearMap fun _ : Fin m => L x‖ ≤
        |M| * |CL| ^ m := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul hΦb (pow_le_pow_left₀ (norm_nonneg _) (hLx.trans (le_abs_self _)) m) (by positivity)
        (abs_nonneg _)
    exact mul_le_mul (hχx.trans (le_abs_self _)) hcomp (norm_nonneg _) (abs_nonneg _)

end Affine

end EngineBridge

section Conv

open MeasureTheory Metric Set
open scoped Classical

private def l5F (φ : AdelicGL2 (𝓞 K) K → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ)
    (Φ : liftEntry K → ℂ) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K → ArchEntry → ℂ :=
  fun y e => (φ (g * y) * ff (glFin (𝓞 K) K y)) • Φ (liftCD w y + liftLD hw y e)

private theorem l5F_eq {φ α : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {Φ : liftEntry K → ℂ}
    (hfa : ∀ z, fa z = Φ (archEntries K z)) (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) {e : ArchEntry} (he : e ∈ nonsingEntries)
    (y : AdelicGL2 (𝓞 K) K) :
    l5F φ ff Φ hw g y e = φ (g * y) * α (archRealLiftAt hw e * y) := by
  rw [lift_factor_lift_mul hw hfa hα he y]
  simp only [l5F, IsFactorizableTestFn.liftCD, IsFactorizableTestFn.liftLD,
    IsFactorizableTestFn.liftM, ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

set_option linter.style.haveILetI false in
private theorem l5_tcFamily {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsLocallyConstant ff)
    {Φ : liftEntry K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K)
    {C : Set (AdelicGL2 (𝓞 K) K)} (hC : IsCompact C) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    TcFamily ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) (l5F φ ff Φ hw g) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hχ : Continuous fun y : AdelicGL2 (𝓞 K) K => φ (g * y) * ff (glFin (𝓞 K) K y) :=
    (hφ.comp (continuous_const.mul continuous_id)).mul (hff.continuous.comp (continuous_glFin (𝓞 K) K))
  obtain ⟨Cχ, hCχ⟩ := hC.exists_bound_of_continuousOn hχ.continuousOn
  obtain ⟨Cc, hCc⟩ := hC.exists_bound_of_continuousOn (lift_continuous_cD w).continuousOn
  obtain ⟨CL, hCL⟩ := hC.exists_bound_of_continuousOn (lift_continuous_LD hw).continuousOn
  exact af_family hΦ hχ.aestronglyMeasurable (lift_continuous_cD w).aestronglyMeasurable
    (lift_continuous_LD hw).aestronglyMeasurable (ae_restrict_of_forall_mem hCm hCχ)
    (ae_restrict_of_forall_mem hCm hCc) (ae_restrict_of_forall_mem hCm hCL)

set_option linter.style.haveILetI false in
private theorem l5_rightConv_lift_eq {φ α : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {Φ : liftEntry K → ℂ}
    (hfa : ∀ z, fa z = Φ (archEntries K z)) (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) {C : Set (AdelicGL2 (𝓞 K) K)} {S : Set ArchEntry}
    (hSd : S ⊆ nonsingEntries)
    (hCvan : ∀ e' ∈ S, ∀ y ∉ C, α (archRealLiftAt hw e' * y) = 0) {e' : ArchEntry} (he' : e' ∈ S) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    rightConv K φ (fun y => α (archRealLiftAt hw e' * y)) g =
      ∫ y, l5F φ ff Φ hw g y e' ∂((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  have hz : ∀ y, y ∉ C → φ (g * y) * α (archRealLiftAt hw e' * y) = 0 := fun y hy => by
    rw [hCvan e' he' y hy, mul_zero]
  show (∫ y, φ (g * y) * α (archRealLiftAt hw e' * y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => (l5F_eq hfa hα hw g (hSd he') y).symm)
set_option linter.style.haveILetI false in
private theorem l5_isArchSmoothAt_rightConv (hw : w.IsReal) {φ α : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hα : IsFactorizableTestFn K α) : IsArchSmoothAt hw (rightConv K φ α) := by
  obtain ⟨-, hαs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K α hα
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, -⟩, ⟨hff, -⟩, hαeq⟩ := hα
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  intro g
  refine contDiffOn_of_locally_contDiffOn fun e₀ he₀ => ?_
  have he₀' : invEntries e₀ ∈ nonsingEntries := chart_invEntries_mem he₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 chart_isOpen_nonsingEntries (invEntries e₀) he₀'
  have hSd : closedBall (invEntries e₀) (ρ / 2) ⊆ nonsingEntries :=
    (closedBall_subset_ball (half_lt_self hρ)).trans hball
  obtain ⟨C, hC, hCvan⟩ := lift_exists_compact_support hw hαs (isCompact_closedBall (invEntries e₀) (ρ / 2)) hSd
  haveI : IsFiniteMeasure ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hH := tc_contDiffOn_integral (l5_tcFamily hφ hff hΦ hw g hC)
  refine ⟨nonsingEntries ∩ invEntries ⁻¹' ball (invEntries e₀) (ρ / 2),
    chart_contDiffOn_invEntries.continuousOn.isOpen_inter_preimage chart_isOpen_nonsingEntries isOpen_ball,
    ⟨he₀, mem_ball_self (half_pos hρ)⟩, ?_⟩
  refine (hH.comp (chart_contDiffOn_invEntries.mono fun e he => he.1) fun e he => chart_invEntries_mem he.1).congr
    fun e he => ?_
  have hinS : invEntries e ∈ closedBall (invEntries e₀) (ρ / 2) := ball_subset_closedBall he.2.2
  show rightConv K φ α (g * archRealLiftAt hw e) = _
  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, lift_lift_inv hw he.1]
  exact l5_rightConv_lift_eq hfa hαeq hw g hSd hCvan hinS

set_option linter.style.haveILetI false in
private theorem l5_archDerivAt_rightConv (hw : w.IsReal) (d : ArchDir) {φ α : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hα : IsFactorizableTestFn K α) :
    archDerivAt hw d (rightConv K φ α) = rightConv K φ (leftDerivFactor hw d α) := by
  obtain ⟨-, hαs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K α hα
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, -⟩, ⟨hff, -⟩, hαeq⟩ := hα
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  funext g

  have hγ : HasDerivAt (fun t : ℝ => liftCurve d (-t))
      ((-1 : ℝ) • Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)) 0 := by
    have h := lift_hasDerivAt_curve d
    rw [← neg_zero] at h
    exact h.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have h0 : liftCurve d (-0) ∈ nonsingEntries := lift_curve_mem d _
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 chart_isOpen_nonsingEntries (liftCurve d (-0)) h0
  have hSd : closedBall (liftCurve d (-0)) (ρ / 2) ⊆ nonsingEntries :=
    (closedBall_subset_ball (half_lt_self hρ)).trans hball
  obtain ⟨C, hC, hCvan⟩ := lift_exists_compact_support hw hαs (isCompact_closedBall (liftCurve d (-0)) (ρ / 2)) hSd
  haveI : IsFiniteMeasure ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hF := l5_tcFamily hφ hff hΦ hw g hC

  have hev : ∀ᶠ t : ℝ in 𝓝 0, liftCurve d (-t) ∈ closedBall (liftCurve d (-0)) (ρ / 2) :=
    hγ.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ (half_pos hρ))

  have hL : archDerivAt hw d (rightConv K φ α) g =
      deriv (fun t : ℝ => ∫ y, l5F φ ff Φ hw g y (liftCurve d (-t))
        ∂((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C)) 0 := by
    show deriv (fun t : ℝ => rightConv K φ α (g * archFlowAt hw d t)) 0 = _
    refine Filter.EventuallyEq.deriv_eq (hev.mono fun t ht => ?_)
    show rightConv K φ α (g * archFlowAt hw d t) = _
    rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, lift_archFlowAt_inv, lift_archFlowAt_eq_lift]
    exact l5_rightConv_lift_eq hfa hαeq hw g hSd hCvan ht

  have hpt : ∀ y : AdelicGL2 (𝓞 K) K,
      deriv (fun t : ℝ => l5F φ ff Φ hw g y (liftCurve d (-t))) 0 =
      φ (g * y) * leftDerivFactor hw d α y := by
    intro y
    have hfun : (fun t : ℝ => l5F φ ff Φ hw g y (liftCurve d (-t))) =
        fun t : ℝ => φ (g * y) * α (archFlowAt hw d (-t) * y) := by
      funext t
      rw [l5F_eq hfa hαeq hw g (lift_curve_mem d (-t)) y, lift_archFlowAt_eq_lift]
    rw [hfun]
    show deriv (fun t : ℝ => φ (g * y) * α (archFlowAt hw d (-t) * y)) 0 =
      φ (g * y) * deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0
    exact deriv_const_mul_field _

  have hvan : ∀ y ∉ C, leftDerivFactor hw d α y = 0 := by
    intro y hy
    have h : (fun t : ℝ => α (archFlowAt hw d (-t) * y)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      refine hev.mono fun t ht => ?_
      show α (archFlowAt hw d (-t) * y) = 0
      rw [lift_archFlowAt_eq_lift]
      exact hCvan _ ht y hy
    show deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0 = 0
    rw [h.deriv_eq, deriv_const]
  rw [hL, tc_deriv_integral_comp hF (fun t => liftCurve d (-t)) hγ.differentiableAt h0]
  have hz : ∀ y, y ∉ C → φ (g * y) * leftDerivFactor hw d α y = 0 := fun y hy => by
    rw [hvan y hy, mul_zero]
  show _ = ∫ y, φ (g * y) * leftDerivFactor hw d α y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end Conv

section Parts

open MeasureTheory Metric Set
open scoped Classical

private theorem l5_continuous_archFlowAt (hw : w.IsReal) (d : ArchDir) :
    Continuous fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K) := by
  have h0 : ContinuousAt (fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)) 0 := by
    have hfun : (fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)) =
        fun t : ℝ => archRealLiftAt hw (liftCurve d t) := by
      funext t
      exact lift_archFlowAt_eq_lift hw d t
    rw [hfun]
    exact ((lift_continuousOn_lift hw).continuousAt
      (chart_isOpen_nonsingEntries.mem_nhds (lift_curve_mem d 0))).comp
      (lift_hasDerivAt_curve d).continuousAt
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have hfun : (fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)) =
      fun t : ℝ => archFlowAt hw d t₀ * archFlowAt hw d (t - t₀) := by
    funext t
    rw [← archFlowAt_add, show t₀ + (t - t₀) = t by ring]
  rw [hfun]
  have hsub : ContinuousAt (fun t : ℝ => t - t₀) t₀ := continuousAt_id.sub continuousAt_const
  have hshift : ContinuousAt (fun t : ℝ => (archFlowAt hw d (t - t₀) : AdelicGL2 (𝓞 K) K)) t₀ :=
    ContinuousAt.comp_of_eq (g := fun s : ℝ => (archFlowAt hw d s : AdelicGL2 (𝓞 K) K))
      (f := fun t : ℝ => t - t₀) h0 hsub (sub_self t₀)
  exact continuousAt_const.mul hshift

private theorem l5_hasDerivAt_orbit (hw : w.IsReal) (d : ArchDir) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsArchSmoothAt hw f) (x : AdelicGL2 (𝓞 K) K) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => f (x * archFlowAt hw d t)) (archDerivAt hw d f (x * archFlowAt hw d t₀)) t₀ := by
  have h0 : ∀ x' : AdelicGL2 (𝓞 K) K,
      HasDerivAt (fun s : ℝ => f (x' * archFlowAt hw d s)) (archDerivAt hw d f x') 0 := by
    intro x'
    have hfun : (fun s : ℝ => f (x' * archFlowAt hw d s)) =
        fun s : ℝ => f (x' * archRealLiftAt hw (liftCurve d s)) := by
      funext s
      rw [lift_archFlowAt_eq_lift]
    have hdiff : DifferentiableAt ℝ (fun s : ℝ => f (x' * archFlowAt hw d s)) 0 := by
      rw [hfun]
      exact (((hf x').differentiableOn (by simp) _ (lift_curve_mem d 0)).differentiableAt
        (chart_isOpen_nonsingEntries.mem_nhds (lift_curve_mem d 0))).comp (0 : ℝ)
        (lift_hasDerivAt_curve d).differentiableAt
    exact hdiff.hasDerivAt
  have hfun : (fun t : ℝ => f (x * archFlowAt hw d t)) =
      (fun s : ℝ => f (x * archFlowAt hw d t₀ * archFlowAt hw d s)) ∘ fun t : ℝ => t - t₀ := by
    funext t
    show f (x * archFlowAt hw d t) = f (x * archFlowAt hw d t₀ * archFlowAt hw d (t - t₀))
    rw [mul_assoc, ← archFlowAt_add, show t₀ + (t - t₀) = t by ring]
  have hpt : HasDerivAt (fun s : ℝ => f (x * archFlowAt hw d t₀ * archFlowAt hw d s))
      (archDerivAt hw d f (x * archFlowAt hw d t₀)) (t₀ - t₀) := by
    rw [sub_self]
    exact h0 _
  rw [hfun]
  have h := hpt.scomp (h := fun t : ℝ => t - t₀) t₀ ((hasDerivAt_sub_const_iff t₀).2 (hasDerivAt_id t₀))
  rw [one_smul] at h
  exact h

private theorem l5_archDerivAt_eq_zero_of_notMem (hw : w.IsReal) (d : ArchDir) {f : AdelicGL2 (𝓞 K) K → ℂ}
    {y : AdelicGL2 (𝓞 K) K} (hy : y ∉ tsupport f) : archDerivAt hw d f y = 0 := by
  have hmem : (tsupport f)ᶜ ∈ 𝓝 (y * archFlowAt hw d 0) := by
    rw [archFlowAt_zero, mul_one]
    exact (isClosed_tsupport f).isOpen_compl.mem_nhds hy
  have horbit : ContinuousAt (fun t : ℝ => y * archFlowAt hw d t) 0 :=
    continuousAt_const.mul (l5_continuous_archFlowAt hw d).continuousAt
  have heq : (fun t : ℝ => f (y * archFlowAt hw d t)) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
    filter_upwards [horbit.preimage_mem_nhds hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  show deriv (fun t : ℝ => f (y * archFlowAt hw d t)) 0 = 0
  rw [heq.deriv_eq, deriv_const]

private theorem l5_hasCompactSupport_archDerivAt (hw : w.IsReal) (d : ArchDir) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (archDerivAt hw d f) := by
  refine hf.mono' fun y hy => ?_
  by_contra hyt
  exact hy (l5_archDerivAt_eq_zero_of_notMem hw d hyt)

private theorem l5_hasCompactSupport_mul {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : HasCompactSupport f)
    (h : AdelicGL2 (𝓞 K) K → ℂ) : HasCompactSupport fun y => f y * h y := by
  refine hf.mono fun y hy => ?_
  simp only [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by rw [h0, zero_mul])

private def l5E (hw : w.IsReal) (d : ArchDir) (φ γ ω : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (t : ℝ)
    (y : AdelicGL2 (𝓞 K) K) : ℂ :=
  φ (g * y * archFlowAt hw d t) * (γ (y * archFlowAt hw d t) * ω y)

private def l5E' (hw : w.IsReal) (d : ArchDir) (φ γ ω : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (t : ℝ)
    (y : AdelicGL2 (𝓞 K) K) : ℂ :=
  archDerivAt hw d φ (g * y * archFlowAt hw d t) * (γ (y * archFlowAt hw d t) * ω y) +
    φ (g * y * archFlowAt hw d t) * (archDerivAt hw d γ (y * archFlowAt hw d t) * ω y)

private theorem l5_hasDerivAt_E (hw : w.IsReal) (d : ArchDir) {φ γ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφs : IsArchSmoothAt hw φ) (hγs : IsArchSmoothAt hw γ) (ω : AdelicGL2 (𝓞 K) K → ℂ)
    (g y : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => l5E hw d φ γ ω g t' y) (l5E' hw d φ γ ω g t y) t :=
  (l5_hasDerivAt_orbit hw d hφs (g * y) t).mul ((l5_hasDerivAt_orbit hw d hγs y t).mul_const (ω y))

private theorem l5_continuous_E' (hw : w.IsReal) (d : ArchDir) {φ γ ω : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hφ' : Continuous (archDerivAt hw d φ)) (hγ : Continuous γ)
    (hγ' : Continuous (archDerivAt hw d γ)) (hω : Continuous ω) (g : AdelicGL2 (𝓞 K) K) :
    Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => l5E' hw d φ γ ω g p.1 p.2 := by
  have hflow : Continuous fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K) := l5_continuous_archFlowAt hw d
  unfold l5E'
  fun_prop

private theorem l5_E'_eq_zero (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    {γ : AdelicGL2 (𝓞 K) K → ℂ} (ω : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) {t : ℝ}
    {y : AdelicGL2 (𝓞 K) K} (hy : y * archFlowAt hw d t ∉ tsupport γ) : l5E' hw d φ γ ω g t y = 0 := by
  rw [l5E', image_eq_zero_of_notMem_tsupport hy, l5_archDerivAt_eq_zero_of_notMem hw d hy]
  ring

set_option linter.style.haveILetI false in
private theorem l5_integral_E_eq (hw : w.IsReal) (d : ArchDir) (φ γ : AdelicGL2 (𝓞 K) K → ℂ)
    {ω : AdelicGL2 (𝓞 K) K → ℂ} (hωinv : ∀ y t, ω (y * archFlowAt hw d t) = ω y) (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    (∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
      ∫ y, φ (g * y) * (γ y * ω y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isMulRightInvariant_adelicGLHaar K
  rw [← integral_mul_right_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    (fun y => φ (g * y) * (γ y * ω y)) (archFlowAt hw d t)]
  congr 1
  funext y
  rw [l5E, hωinv, mul_assoc]

private theorem l5_continuous_E (hw : w.IsReal) (d : ArchDir) {φ γ ω : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hγ : Continuous γ) (hω : Continuous ω) (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    Continuous fun y => l5E hw d φ γ ω g t y := by
  unfold l5E
  exact (hφ.comp ((continuous_const.mul continuous_id).mul continuous_const)).mul
    ((hγ.comp (continuous_id.mul continuous_const)).mul hω)

private theorem l5_exists_segment_compact (hw : w.IsReal) (d : ArchDir) {γ : AdelicGL2 (𝓞 K) K → ℂ}
    (hγc : HasCompactSupport γ) : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧
      ∀ y, y ∉ C → ∀ t ∈ ball (0 : ℝ) 1, y * archFlowAt hw d t ∉ tsupport γ := by
  refine ⟨(fun p : ℝ × AdelicGL2 (𝓞 K) K => p.2 * archFlowAt hw d (-p.1)) ''
      (closedBall (0 : ℝ) 1 ×ˢ tsupport γ),
    ((isCompact_closedBall (0 : ℝ) 1).prod (hγc : IsCompact (tsupport γ))).image
      (continuous_snd.mul ((l5_continuous_archFlowAt hw d).comp continuous_fst.neg)), ?_⟩
  intro y hy t ht hmem
  apply hy
  refine ⟨(t, y * archFlowAt hw d t), ⟨ball_subset_closedBall ht, hmem⟩, ?_⟩
  show y * archFlowAt hw d t * archFlowAt hw d (-t) = y
  rw [mul_assoc, ← archFlowAt_add, add_neg_cancel, archFlowAt_zero, mul_one]

set_option linter.style.haveILetI false in
private theorem l5_hasDerivAt_integral_E (hw : w.IsReal) (d : ArchDir) {φ γ ω : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hφs : IsArchSmoothAt hw φ) (hφ' : Continuous (archDerivAt hw d φ)) (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (hγs : IsArchSmoothAt hw γ) (hγ' : Continuous (archDerivAt hw d γ))
    (hω : Continuous ω) (g : AdelicGL2 (𝓞 K) K) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    HasDerivAt (fun t : ℝ => ∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      (∫ y, l5E' hw d φ γ ω g 0 y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) 0 := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨C, hC, hCout⟩ := l5_exists_segment_compact hw d (γ := γ) hγc
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hC).exists_bound_of_continuousOn
    (l5_continuous_E' hw d hφ hφ' hγ hγ' hω g).continuousOn
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hbound : Integrable (fun y => if y ∈ C then M else 0) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (integrableOn_const (C := M) hC.measure_lt_top.ne).integrable_indicator hCm
  have hint0 : Integrable (fun y => l5E hw d φ γ ω g 0 y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    have hE0 : (fun y => l5E hw d φ γ ω g 0 y) = fun y => φ (g * y) * (γ y * ω y) := by
      funext y
      rw [l5E, archFlowAt_zero, mul_one, mul_one]
    rw [hE0]
    exact l5_integrable_conv_integrand hφ (hγ.mul hω) (l5_hasCompactSupport_mul hγc ω) g
  have hE'0m : AEStronglyMeasurable (fun y => l5E' hw d φ γ ω g 0 y)
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    ((l5_continuous_E' hw d hφ hφ' hγ hγ' hω g).comp
      ((continuous_const : Continuous fun _ : AdelicGL2 (𝓞 K) K => (0 : ℝ)).prodMk continuous_id)).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K), ∀ t ∈ ball (0 : ℝ) 1,
      ‖l5E' hw d φ γ ω g t y‖ ≤ if y ∈ C then M else 0 := by
    refine Filter.Eventually.of_forall fun y t ht => ?_
    by_cases hy : y ∈ C
    · rw [ite_eq_left hy]
      exact hM (t, y) ⟨ball_subset_closedBall ht, hy⟩
    · rw [ite_eq_right hy, l5_E'_eq_zero hw d φ ω g (hCout y hy t ht), norm_zero]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    (F := l5E hw d φ γ ω g) (F' := l5E' hw d φ γ ω g) (ball_mem_nhds (0 : ℝ) one_pos)
    (Filter.Eventually.of_forall fun t => (l5_continuous_E hw d hφ hγ hω g t).aestronglyMeasurable) hint0 hE'0m
    h_bound hbound (Filter.Eventually.of_forall fun y t _ => l5_hasDerivAt_E hw d hφs hγs ω g y t)).2

set_option linter.style.haveILetI false in
private theorem l5_rightConv_archDerivAt_mul (hw : w.IsReal) (d : ArchDir) {φ γ ω : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hφs : IsArchSmoothAt hw φ) (hφ' : Continuous (archDerivAt hw d φ)) (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (hγs : IsArchSmoothAt hw γ) (hγ' : Continuous (archDerivAt hw d γ))
    (hω : Continuous ω) (hωinv : ∀ y t, ω (y * archFlowAt hw d t) = ω y) :
    rightConv K φ (fun y => archDerivAt hw d γ y * ω y) =
      -rightConv K (archDerivAt hw d φ) fun y => γ y * ω y := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  funext g

  have hA : Integrable (fun y => archDerivAt hw d φ (g * y) * (γ y * ω y))
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    l5_integrable_conv_integrand hφ' (hγ.mul hω) (l5_hasCompactSupport_mul hγc ω) g
  have hB : Integrable (fun y => φ (g * y) * (archDerivAt hw d γ y * ω y))
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    l5_integrable_conv_integrand hφ (hγ'.mul hω)
      (l5_hasCompactSupport_mul (l5_hasCompactSupport_archDerivAt hw d hγc) ω) g
  have hD : HasDerivAt (fun t : ℝ => ∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      (∫ y, l5E' hw d φ γ ω g 0 y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) 0 :=
    l5_hasDerivAt_integral_E hw d hφ hφs hφ' hγ hγc hγs hγ' hω g

  have hconst : HasDerivAt (fun t : ℝ => ∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      0 0 := by
    have hfun : (fun t : ℝ => ∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
        fun _ => ∫ y, φ (g * y) * (γ y * ω y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
      funext t
      exact l5_integral_E_eq hw d φ γ hωinv g t
    rw [hfun]
    exact hasDerivAt_const (0 : ℝ) _
  have hzero := hD.unique hconst
  have hE'0 : (fun y => l5E' hw d φ γ ω g 0 y) =
      fun y => archDerivAt hw d φ (g * y) * (γ y * ω y) + φ (g * y) * (archDerivAt hw d γ y * ω y) := by
    funext y
    rw [l5E', archFlowAt_zero, mul_one, mul_one]
  rw [hE'0, integral_add hA hB] at hzero
  show (∫ y, φ (g * y) * (archDerivAt hw d γ y * ω y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    -∫ y, archDerivAt hw d φ (g * y) * (γ y * ω y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  linear_combination hzero

end Parts

section Head

open NumberField NumberField.AdelicLevel AutomorphicForm

/-- **Differentiating a right convolution along an archimedean flow, at a real place.** The
triple conjunction of the pin's row: `rightConv φ α` is archimedean-smooth with the
derivative pushed onto the test function along the negative flow; the differentiated test
factor is again a tensor with the same finite factor; and the integration-by-parts identity
`rightConv φ (Dγ · ω) = -rightConv (Dφ) (γ · ω)` holds for `γ` compactly supported and `ω`
invariant under the flow. -/
theorem archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) :
    (∀ φ α : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsFactorizableTestFn K α →
      IsArchSmoothAt hw (rightConv K φ α) ∧
        archDerivAt hw d (rightConv K φ α) =
          rightConv K φ (fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0)) ∧
    (∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa →
        ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
          (fun y : AdelicGL2 (𝓞 K) K =>
              deriv (fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) *
                ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y))) 0) =
            fun y => fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
    (∀ φ γ ω : AdelicGL2 (𝓞 K) K → ℂ,
      Continuous φ → IsArchSmoothAt hw φ → Continuous (archDerivAt hw d φ) →
      Continuous γ → HasCompactSupport γ → IsArchSmoothAt hw γ → Continuous (archDerivAt hw d γ) →
      Continuous ω → (∀ (y : AdelicGL2 (𝓞 K) K) (t : ℝ), ω (y * archFlowAt hw d t) = ω y) →
        rightConv K φ (fun y => archDerivAt hw d γ y * ω y) =
          -rightConv K (archDerivAt hw d φ) fun y => γ y * ω y) := by
  refine ⟨fun φ α hφ hα => ⟨l5_isArchSmoothAt_rightConv hw hφ hα, l5_archDerivAt_rightConv hw d hφ hα⟩,
    fun fa ff hfa => lift_leftDeriv_tensor hw d hfa ff, ?_⟩
  intro φ γ ω hφ hφs hφ' hγ hγc hγs hγ' hω hωinv
  exact l5_rightConv_archDerivAt_mul hw d hφ hφs hφ' hγ hγc hγs hγ' hω hωinv

end Head

/-! ### The Casimir bridge into right convolution

Two rows, both headlines: the bridge `archCasimirAt (rightConv x f) = rightConv (archCasimirAt x) f`
for an arch-smooth `x` with continuous first and second derivatives (the Casimir analogue of
`archDerivAt_rightConv_eq_rightConv_deriv`, using `leftCasimir_eq_archCasimirAt_of_isArchSmoothAt` for
the left-acting element), and the row that keeps a character-typed test function's Casimir
factorisable, bi-finite, and inside `levelInvariantSubmodule ⊓ archCutSubmodule`. -/

section CasimirBridge

open MeasureTheory

open AutomorphicForm.CuspidalConstituent
open NumberField.AdelicBox

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

namespace CommConv17

open CasCore17

variable (hw : w.IsReal)

private def Lf (d : ArchDir) (β : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => β (archFlowAt hw d (-t) * y)) 0

private theorem isFactorizableTestFn_Lf (d : ArchDir) {β : AdelicGL2 (𝓞 K) K → ℂ}
    (hβ : IsFactorizableTestFn K β) :
    IsFactorizableTestFn K (Lf hw d β) := by
  obtain ⟨fa, ff, hfa, hff, hβeq⟩ := hβ
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', ff, hfa', hff, fun y => ?_⟩
  have h1 : Lf hw d β y = deriv (fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) *
      ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y))) 0 := by
    simp only [Lf, hβeq]
  rw [h1]
  exact congrFun heq y

private theorem conv_smooth_and_deriv {x : AdelicGL2 (𝓞 K) K → ℂ} (hx : Continuous x) (d : ArchDir)
    {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : IsFactorizableTestFn K β) :
    IsArchSmoothAt hw (rightConv K x β) ∧ archDerivAt hw d (rightConv K x β) = rightConv K x (Lf hw d β) :=
  (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).1 x β hx hβ

private theorem continuous_conv {x : AdelicGL2 (𝓞 K) K → ℂ} (hx : Continuous x) {β : AdelicGL2 (𝓞 K) K → ℂ}
    (hβ : IsFactorizableTestFn K β) : Continuous (rightConv K x β) :=
  (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K x hx β hβ).1

section Lin

variable {x : AdelicGL2 (𝓞 K) K → ℂ}

set_option linter.style.haveILetI false in
private theorem integrable_integrand (hx : Continuous x) {β : AdelicGL2 (𝓞 K) K → ℂ} (hβ : Continuous β)
    (hβc : HasCompactSupport β) (g : AdelicGL2 (𝓞 K) K) :
    Integrable (fun y => x (g * y) * β y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hc : Continuous fun y : AdelicGL2 (𝓞 K) K => x (g * y) * β y := (hx.comp (continuous_const.mul continuous_id)).mul hβ
  exact hc.integrable_of_hasCompactSupport hβc.mul_left

private theorem rightConv_add_right (hx : Continuous x) {β₁ β₂ : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : Continuous β₁)
    (h₁c : HasCompactSupport β₁) (h₂ : Continuous β₂) (h₂c : HasCompactSupport β₂) :
    rightConv K x (β₁ + β₂) = rightConv K x β₁ + rightConv K x β₂ := by
  funext g
  simp only [rightConv_apply, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand hx h₁ h₁c g) (integrable_integrand hx h₂ h₂c g)

private theorem rightConv_sub_right (hx : Continuous x) {β₁ β₂ : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : Continuous β₁)
    (h₁c : HasCompactSupport β₁) (h₂ : Continuous β₂) (h₂c : HasCompactSupport β₂) :
    rightConv K x (β₁ - β₂) = rightConv K x β₁ - rightConv K x β₂ := by
  funext g
  simp only [rightConv_apply, Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_integrand hx h₁ h₁c g) (integrable_integrand hx h₂ h₂c g)

omit hw in
private theorem rightConv_smul_right (x β : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) :
    rightConv K x (c • β) = c • rightConv K x β := by
  funext g
  simp only [rightConv_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

omit hw in
private theorem rightConv_neg_right (x β : AdelicGL2 (𝓞 K) K → ℂ) : rightConv K x (-β) = -rightConv K x β := by
  rw [← neg_one_smul ℂ β, rightConv_smul_right, neg_one_smul]

omit hw in
private theorem rightConv_smul_left' (x β : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) :
    rightConv K (c • x) β = c • rightConv K x β :=
  convOp_smul K β c x

omit hw in
private theorem rightConv_neg_left (x β : AdelicGL2 (𝓞 K) K → ℂ) : rightConv K (-x) β = -rightConv K x β := by
  rw [← neg_one_smul ℂ x, rightConv_smul_left', neg_one_smul]

omit hw in
private theorem rightConv_sub_left {u v β : AdelicGL2 (𝓞 K) K → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hβ : Continuous β) (hβc : HasCompactSupport β) :
    rightConv K (u - v) β = rightConv K u β - rightConv K v β := by
  rw [sub_eq_add_neg, rightConv_add_left K (u := u) (w := -v) hu hv.neg hβ hβc, rightConv_neg_left, ← sub_eq_add_neg]

omit hw in
private theorem hcs_smul (c : ℂ) {β : AdelicGL2 (𝓞 K) K → ℂ} (h : HasCompactSupport β) :
    HasCompactSupport (c • β) :=
  h.mono fun y hy => by
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or] at hy ⊢
    exact hy.2

end Lin

private theorem main (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x)))
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAt hw (rightConv K x α) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x α))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x α)))) ∧
    archCasimirAt hw (rightConv K x α) = rightConv K (archCasimirAt hw x) α := by
  obtain ⟨hαs, fa, ff, hfa, hff, hαeq, hDα⟩ :=
    AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor K w hw α hα
  have hfactD : ∀ d : ArchDir, IsFactorizableTestFn K (archDerivAt hw d α) := by
    intro d
    obtain ⟨fa', hfa', h⟩ := hDα d
    exact ⟨fa', ff, hfa', hff, h⟩
  have hreg : ∀ {β : AdelicGL2 (𝓞 K) K → ℂ}, IsFactorizableTestFn K β → Continuous β ∧ HasCompactSupport β :=
    fun hβ => AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ hβ
  have hfactDD : ∀ d d' : ArchDir, IsFactorizableTestFn K (archDerivAt hw d (archDerivAt hw d' α)) := by
    intro d d'
    obtain ⟨-, fa₁, ff₁, hfa₁, hff₁, -, hD⟩ :=
      AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor K w hw _ (hfactD d')
    obtain ⟨fa', hfa', h⟩ := hD d
    exact ⟨fa', ff₁, hfa', hff₁, h⟩

  have hLfact : ∀ d, IsFactorizableTestFn K (Lf hw d α) := fun d => isFactorizableTestFn_Lf hw d hα
  have hLLfact : ∀ d d', IsFactorizableTestFn K (Lf hw d (Lf hw d' α)) := fun d d' => isFactorizableTestFn_Lf hw d (hLfact d')
  have hDconv : ∀ d, archDerivAt hw d (rightConv K x α) = rightConv K x (Lf hw d α) := fun d => (conv_smooth_and_deriv hw hxc d hα).2
  have hDDconv : ∀ d d', archDerivAt hw d (archDerivAt hw d' (rightConv K x α)) =
      rightConv K x (Lf hw d (Lf hw d' α)) := by
    intro d d'
    rw [hDconv d', (conv_smooth_and_deriv hw hxc d (hLfact d')).2]
  refine ⟨(conv_smooth_and_deriv hw hxc .H hα).1, fun d => ?_, fun d d' => ?_, ?_⟩
  · rw [hDconv d]; exact continuous_conv hxc (hLfact d)
  · rw [hDDconv d d']; exact continuous_conv hxc (hLLfact d d')

  have hΩL : archCasimirAt hw (rightConv K x α) =
      rightConv K x (-((1 / 4 : ℂ) • Lf hw .H (Lf hw .H α) - (1 / 2 : ℂ) • Lf hw .H α + Lf hw .E (Lf hw .Fm α))) := by
    have c1 : Continuous ((1 / 4 : ℂ) • Lf hw .H (Lf hw .H α) - (1 / 2 : ℂ) • Lf hw .H α) :=
      ((hreg (hLLfact .H .H)).1.const_smul (1 / 4 : ℂ)).sub ((hreg (hLfact .H)).1.const_smul (1 / 2 : ℂ))
    have s1 : HasCompactSupport ((1 / 4 : ℂ) • Lf hw .H (Lf hw .H α) - (1 / 2 : ℂ) • Lf hw .H α) :=
      (hcs_smul _ (hreg (hLLfact .H .H)).2).sub (hcs_smul _ (hreg (hLfact .H)).2)
    have c2 : Continuous ((1 / 4 : ℂ) • Lf hw .H (Lf hw .H α)) := (hreg (hLLfact .H .H)).1.const_smul (1 / 4 : ℂ)
    have s2 : HasCompactSupport ((1 / 4 : ℂ) • Lf hw .H (Lf hw .H α)) := hcs_smul _ (hreg (hLLfact .H .H)).2
    have c3 : Continuous ((1 / 2 : ℂ) • Lf hw .H α) := (hreg (hLfact .H)).1.const_smul (1 / 2 : ℂ)
    have s3 : HasCompactSupport ((1 / 2 : ℂ) • Lf hw .H α) := hcs_smul _ (hreg (hLfact .H)).2
    rw [archCasimirAt, hDDconv, hDconv, hDDconv, rightConv_neg_right,
      rightConv_add_right hxc (β₁ := (1 / 4 : ℂ) • Lf hw .H (Lf hw .H α) - (1 / 2 : ℂ) • Lf hw .H α)
        (β₂ := Lf hw .E (Lf hw .Fm α)) c1 s1 (hreg (hLLfact _ _)).1 (hreg (hLLfact _ _)).2,
      rightConv_sub_right hxc (β₁ := (1 / 4 : ℂ) • Lf hw .H (Lf hw .H α)) (β₂ := (1 / 2 : ℂ) • Lf hw .H α) c2 s2 c3 s3,
      rightConv_smul_right, rightConv_smul_right]

  have hLR : -((1 / 4 : ℂ) • Lf hw .H (Lf hw .H α) - (1 / 2 : ℂ) • Lf hw .H α + Lf hw .E (Lf hw .Fm α)) =
      archCasimirAt hw α := by
    funext y
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact AutomorphicForm.leftCasimir_eq_archCasimirAt_of_isArchSmoothAt K w hw α hαs y

  have hIBP : ∀ (d : ArchDir) {φ γ : AdelicGL2 (𝓞 K) K → ℂ}, Continuous φ → IsArchSmoothAt hw φ →
      Continuous (archDerivAt hw d φ) → Continuous γ → HasCompactSupport γ → IsArchSmoothAt hw γ →
      Continuous (archDerivAt hw d γ) →
      rightConv K (archDerivAt hw d φ) γ = -rightConv K φ (archDerivAt hw d γ) := by
    intro d φ γ hφ hφs hφ' hγ hγc hγs hγ'
    have h := (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.2 φ γ
      (fun _ => 1) hφ hφs hφ' hγ hγc hγs hγ' continuous_const (fun _ _ => rfl)
    simp only [mul_one] at h
    rw [h, neg_neg]
  have hα1 := hreg hα
  have hDα1 : ∀ d, Continuous (archDerivAt hw d α) ∧ HasCompactSupport (archDerivAt hw d α) := fun d => hreg (hfactD d)
  have hDDα1 : ∀ d d', Continuous (archDerivAt hw d (archDerivAt hw d' α)) := fun d d' => (hreg (hfactDD d d')).1

  have e1 : rightConv K (archDerivAt hw .H (archDerivAt hw .H x)) α =
      rightConv K x (archDerivAt hw .H (archDerivAt hw .H α)) := by
    rw [hIBP .H (hD1 .H) (hxs.archDerivAt .H) (hD2 .H .H) hα1.1 hα1.2 hαs (hDα1 .H).1,
      hIBP .H hxc hxs (hD1 .H) (hDα1 .H).1 (hDα1 .H).2 (hαs.archDerivAt .H) (hDDα1 .H .H), neg_neg]

  have e2 : rightConv K (archDerivAt hw .H x) α = -rightConv K x (archDerivAt hw .H α) :=
    hIBP .H hxc hxs (hD1 .H) hα1.1 hα1.2 hαs (hDα1 .H).1

  have e3 : rightConv K (archDerivAt hw .E (archDerivAt hw .Fm x)) α =
      rightConv K x (archDerivAt hw .Fm (archDerivAt hw .E α)) := by
    rw [hIBP .E (hD1 .Fm) (hxs.archDerivAt .Fm) (hD2 .E .Fm) hα1.1 hα1.2 hαs (hDα1 .E).1,
      hIBP .Fm hxc hxs (hD1 .Fm) (hDα1 .E).1 (hDα1 .E).2 (hαs.archDerivAt .E) (hDDα1 .Fm .E), neg_neg]
  have hΩR : rightConv K (archCasimirAt hw x) α =
      rightConv K x (-((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H α) + (1 / 2 : ℂ) • archDerivAt hw .H α +
        archDerivAt hw .Fm (archDerivAt hw .E α))) := by
    have c4 : Continuous ((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H x) - (1 / 2 : ℂ) • archDerivAt hw .H x) :=
      ((hD2 .H .H).const_smul (1 / 4 : ℂ)).sub ((hD1 .H).const_smul (1 / 2 : ℂ))
    have c5 : Continuous ((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H x)) := (hD2 .H .H).const_smul (1 / 4 : ℂ)
    have c6 : Continuous ((1 / 2 : ℂ) • archDerivAt hw .H x) := (hD1 .H).const_smul (1 / 2 : ℂ)
    have c7 : Continuous ((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H α) + (1 / 2 : ℂ) • archDerivAt hw .H α) :=
      ((hDDα1 .H .H).const_smul (1 / 4 : ℂ)).add ((hDα1 .H).1.const_smul (1 / 2 : ℂ))
    have s7 : HasCompactSupport ((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H α) + (1 / 2 : ℂ) • archDerivAt hw .H α) :=
      (hcs_smul _ (hreg (hfactDD .H .H)).2).add (hcs_smul _ (hDα1 .H).2)
    have c8 : Continuous ((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H α)) := (hDDα1 .H .H).const_smul (1 / 4 : ℂ)
    have s8 : HasCompactSupport ((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H α)) := hcs_smul _ (hreg (hfactDD .H .H)).2
    have c9 : Continuous ((1 / 2 : ℂ) • archDerivAt hw .H α) := (hDα1 .H).1.const_smul (1 / 2 : ℂ)
    have s9 : HasCompactSupport ((1 / 2 : ℂ) • archDerivAt hw .H α) := hcs_smul _ (hDα1 .H).2
    rw [archCasimirAt, rightConv_neg_left, rightConv_neg_right,
      rightConv_add_left K (u := (1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H x) - (1 / 2 : ℂ) • archDerivAt hw .H x)
        (w := archDerivAt hw .E (archDerivAt hw .Fm x)) c4 (hD2 .E .Fm) hα1.1 hα1.2,
      rightConv_sub_left (u := (1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H x)) (v := (1 / 2 : ℂ) • archDerivAt hw .H x)
        c5 c6 hα1.1 hα1.2,
      rightConv_smul_left', rightConv_smul_left', e1, e2, e3,
      rightConv_add_right hxc (β₁ := (1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H α) + (1 / 2 : ℂ) • archDerivAt hw .H α)
        (β₂ := archDerivAt hw .Fm (archDerivAt hw .E α)) c7 s7 (hDDα1 .Fm .E) (hreg (hfactDD .Fm .E)).2,
      rightConv_add_right hxc (β₁ := (1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H α)) (β₂ := (1 / 2 : ℂ) • archDerivAt hw .H α)
        c8 s8 c9 s9,
      rightConv_smul_right, rightConv_smul_right, smul_neg, sub_neg_eq_add]

  have hnat : -((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H α) + (1 / 2 : ℂ) • archDerivAt hw .H α +
        archDerivAt hw .Fm (archDerivAt hw .E α)) = archCasimirAt hw α := by
    funext y
    show _ = (-((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H α) - (1 / 2 : ℂ) • archDerivAt hw .H α +
      archDerivAt hw .E (archDerivAt hw .Fm α))) y
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, CasCore17.rel_Fm_E hw hαs y]
    ring
  rw [hΩL, hLR, hΩR, hnat]

end CommConv17

/-- **Headline (the bridge).** If `x` is archimedean-smooth with continuous first and second flow
derivatives and `f` is a factorizable test function, then `rightConv x f` is arch-smooth with the
same, and its Casimir is the right convolution of the Casimir: `archCasimirAt (rightConv x f) =
rightConv (archCasimirAt x) f`. -/
theorem archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAt hw (rightConv K x f) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x f)))) ∧
        archCasimirAt hw (rightConv K x f) = rightConv K (archCasimirAt hw x) f := by
  intro f tys hf _
  exact CommConv17.main hw x hxc hxs hD1 hD2 f hf

namespace CasLeft2

open CasCore17

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)

private def Tens (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ)
    (γ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∃ fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa ∧
    ∀ y, γ y = fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)

private theorem tens_Ld {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {γ : AdelicGL2 (𝓞 K) K → ℂ} (hγ : Tens ff γ) (d : ArchDir) : Tens ff (CommConv17.Lf hw d γ) := by
  obtain ⟨fa, hfa, hγeq⟩ := hγ
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', hfa', fun y => ?_⟩
  have hfun : (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) =
      fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) *
        ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y)) := by
    funext t; exact hγeq _
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0 = _
  rw [hfun]
  exact congrFun heq y

private theorem isFactorizableTestFn_of_tens {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hff : IsFinTestFactor K ff) {γ : AdelicGL2 (𝓞 K) K → ℂ} (hγ : Tens ff γ) : IsFactorizableTestFn K γ := by
  obtain ⟨fa, hfa, hγeq⟩ := hγ
  exact ⟨fa, ff, hfa, hff, hγeq⟩

private theorem Ld_right_law {γ : AdelicGL2 (𝓞 K) K → ℂ} {k : AdelicGL2 (𝓞 K) K} {c : ℂ}
    (h : ∀ g, γ (g * k) = c * γ g) (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    CommConv17.Lf hw d γ (g * k) = c * CommConv17.Lf hw d γ g := by
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * (g * k))) 0 =
    c * deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * g)) 0
  have hfun : (fun t : ℝ => γ (archFlowAt hw d (-t) * (g * k))) =
      fun t => c * γ (archFlowAt hw d (-t) * g) := by
    funext t; rw [← mul_assoc, h]
  rw [hfun]
  exact deriv_const_mul_field c

private theorem Ld_left_inv {γ : AdelicGL2 (𝓞 K) K → ℂ} {k : AdelicGL2 (𝓞 K) K}
    (hk : glArch (𝓞 K) K k = 1) (h : ∀ y, γ (k * y) = γ y) (d : ArchDir) (y : AdelicGL2 (𝓞 K) K) :
    CommConv17.Lf hw d γ (k * y) = CommConv17.Lf hw d γ y := by
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * (k * y))) 0 =
    deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
  congr 1
  funext t
  rw [← mul_assoc, archFlowAt_mul_comm_of_glArch_eq_one hw d (-t) hk, mul_assoc, h]

end CasLeft2

open CasLeft2 MeasureTheory in
set_option linter.unusedVariables false in
set_option linter.style.haveILetI false in
/-- **Headline.** The Casimir of a character-typed test function is again factorisable and
arch-bi-finite of the same type, its right convolution is linear in the three `L`-summands, and right
convolution by it preserves `levelInvariantSubmodule ⊓ archCutSubmodule`. -/
theorem isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K (ArchTypeFamily.ofChar K χ) α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    let L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
    let β : AdelicGL2 (𝓞 K) K → ℂ :=
      fun y => -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y)
    (IsFactorizableTestFn K β ∧ IsArchBiFinite K (ArchTypeFamily.ofChar K χ) β) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      rightConv K x' β = fun g => -((1 / 4 : ℂ) * rightConv K x' (L .H (L .H α)) g
        - (1 / 2 : ℂ) * rightConv K x' (L .H α) g + rightConv K x' (L .E (L .Fm α)) g)) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ) →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ)) := by
  classical
  intro L β
  obtain ⟨fa, ff, hfa, hff, hαeq⟩ := hαf
  have hT0 : CasLeft2.Tens ff α := ⟨fa, hfa, hαeq⟩
  have hT1 : CasLeft2.Tens ff (L .H α) := CasLeft2.tens_Ld hw hT0 .H
  have hT2 : CasLeft2.Tens ff (L .H (L .H α)) := CasLeft2.tens_Ld hw hT1 .H
  have hT3 : CasLeft2.Tens ff (L .Fm α) := CasLeft2.tens_Ld hw hT0 .Fm
  have hT4 : CasLeft2.Tens ff (L .E (L .Fm α)) := CasLeft2.tens_Ld hw hT3 .E
  obtain ⟨fa1, ⟨⟨Φ1, hΦ1, hfa1⟩, hs1⟩, h1⟩ := hT1
  obtain ⟨fa2, ⟨⟨Φ2, hΦ2, hfa2⟩, hs2⟩, h2⟩ := hT2
  obtain ⟨fa4, ⟨⟨Φ4, hΦ4, hfa4⟩, hs4⟩, h4⟩ := hT4

  have hβeq : ∀ y, β y = (fun z => (-(1 / 4 : ℂ)) * fa2 z + (1 / 2 : ℂ) * fa1 z + (-1 : ℂ) * fa4 z) (glArch (𝓞 K) K y) *
      ff (glFin (𝓞 K) K y) := by
    intro y
    show -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y) = _
    rw [h1, h2, h4]
    ring
  have hβf : IsFactorizableTestFn K β := by
    refine ⟨fun z => (-(1 / 4 : ℂ)) * fa2 z + (1 / 2 : ℂ) * fa1 z + (-1 : ℂ) * fa4 z, ff,
      ⟨⟨fun m => (-(1 / 4 : ℂ)) * Φ2 m + (1 / 2 : ℂ) * Φ1 m + (-1 : ℂ) * Φ4 m, ?_, fun z => ?_⟩, ?_⟩, hff, hβeq⟩
    · exact ((contDiff_const.mul hΦ2).add (contDiff_const.mul hΦ1)).add (contDiff_const.mul hΦ4)
    · show (-(1 / 4 : ℂ)) * fa2 z + (1 / 2 : ℂ) * fa1 z + (-1 : ℂ) * fa4 z = _
      rw [hfa2, hfa1, hfa4]
    · exact (hs2.mul_left.add hs1.mul_left).add hs4.mul_left

  have hαs : IsArchSmoothAt hw α :=
    (AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor K w hw α ⟨fa, ff, hfa, hff, hαeq⟩).1
  have hβΩ : ∀ y, β y = archCasimirAt hw α y :=
    AutomorphicForm.leftCasimir_eq_archCasimirAt_of_isArchSmoothAt K w hw α hαs

  have hαL : ∀ (v : InfinitePlace K) (k : rowIsometrySubgroup₀ v.Completion) (y : AdelicGL2 (𝓞 K) K),
      α (rowIsometryInclAt₀ K v k * y) = ((χ v k⁻¹ : ℂˣ) : ℂ) * α y := by
    intro v
    have h := (mem_archCutSubmodule_ofChar_iff K χ _).mp hαb.1 v
    exact (comp_inv_mem_archTypeSubmoduleAt_ofChar_iff K v (χ v) α).mp
      ((mem_archTypeSubmoduleAt_ofChar_iff K v (χ v) _).mpr h)
  have hαR : ∀ (v : InfinitePlace K) (k : rowIsometrySubgroup₀ v.Completion) (g : AdelicGL2 (𝓞 K) K),
      α (g * rowIsometryInclAt₀ K v k) = ((χ v k⁻¹ : ℂˣ) : ℂ) * α g := by
    intro v
    have h : α ∈ ⨅ v : InfinitePlace K, ⨆ _ : Fin 1, archDualTypeSubmoduleAt K v (ArchRepAt.ofChar K (χ v)) := hαb.2
    simp only [iSup_const, Submodule.mem_iInf] at h
    exact (mem_archDualTypeSubmoduleAt_ofChar_iff K v (χ v) α).mp (h v)

  have hβL : ∀ (v : InfinitePlace K) (k : rowIsometrySubgroup₀ v.Completion) (y : AdelicGL2 (𝓞 K) K),
      β (rowIsometryInclAt₀ K v k * y) = ((χ v k⁻¹ : ℂˣ) : ℂ) * β y := by
    intro v k y
    rw [hβΩ, hβΩ]
    have hfun : (fun g => α (rowIsometryInclAt₀ K v k * g)) = ((χ v k⁻¹ : ℂˣ) : ℂ) • α := by
      funext g; rw [hαL, Pi.smul_apply, smul_eq_mul]
    have h := congrFun (archCasimirAt_comp_mul_left hw α (rowIsometryInclAt₀ K v k)) y
    rw [hfun, archCasimirAt_smul, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hβR : ∀ (v : InfinitePlace K) (k : rowIsometrySubgroup₀ v.Completion) (g : AdelicGL2 (𝓞 K) K),
      β (g * rowIsometryInclAt₀ K v k) = ((χ v k⁻¹ : ℂˣ) : ℂ) * β g := by
    intro v k g
    have e1 := CasLeft2.Ld_right_law hw (hαR v k) .H g
    have e2 := CasLeft2.Ld_right_law hw (fun g' => CasLeft2.Ld_right_law hw (hαR v k) .H g') .H g
    have e3 := CasLeft2.Ld_right_law hw (fun g' => CasLeft2.Ld_right_law hw (hαR v k) .Fm g') .E g
    show -((1 / 4 : ℂ) * L .H (L .H α) (g * _) - (1 / 2 : ℂ) * L .H α (g * _) + L .E (L .Fm α) (g * _)) =
      _ * -((1 / 4 : ℂ) * L .H (L .H α) g - (1 / 2 : ℂ) * L .H α g + L .E (L .Fm α) g)
    change -((1 / 4 : ℂ) * CommConv17.Lf hw .H (CommConv17.Lf hw .H α) (g * _) - (1 / 2 : ℂ) * CommConv17.Lf hw .H α (g * _) +
        CommConv17.Lf hw .E (CommConv17.Lf hw .Fm α) (g * _)) =
      _ * -((1 / 4 : ℂ) * CommConv17.Lf hw .H (CommConv17.Lf hw .H α) g - (1 / 2 : ℂ) * CommConv17.Lf hw .H α g +
        CommConv17.Lf hw .E (CommConv17.Lf hw .Fm α) g)
    rw [e1, e2, e3]
    ring
  have hβLmem : ∀ v : InfinitePlace K, (fun x => β x⁻¹) ∈ archTypeSubmoduleAt K v (ArchRepAt.ofChar K (χ v)) :=
    fun v => (comp_inv_mem_archTypeSubmoduleAt_ofChar_iff K v (χ v) β).mpr (hβL v)
  have hβb : IsArchBiFinite K (ArchTypeFamily.ofChar K χ) β := by
    refine ⟨(mem_archCutSubmodule_ofChar_iff K χ _).mpr fun v =>
      (mem_archTypeSubmoduleAt_ofChar_iff K v (χ v) _).mp (hβLmem v), ?_⟩
    show β ∈ ⨅ v : InfinitePlace K, ⨆ _ : Fin 1, archDualTypeSubmoduleAt K v (ArchRepAt.ofChar K (χ v))
    simp only [iSup_const, Submodule.mem_iInf]
    exact fun v => (mem_archDualTypeSubmoduleAt_ofChar_iff K v (χ v) β).mpr (hβR v)

  have hfac1 : IsFactorizableTestFn K (L .H α) :=
    CasLeft2.isFactorizableTestFn_of_tens hff ⟨fa1, ⟨⟨Φ1, hΦ1, hfa1⟩, hs1⟩, h1⟩
  have hfac2 : IsFactorizableTestFn K (L .H (L .H α)) :=
    CasLeft2.isFactorizableTestFn_of_tens hff ⟨fa2, ⟨⟨Φ2, hΦ2, hfa2⟩, hs2⟩, h2⟩
  have hfac4 : IsFactorizableTestFn K (L .E (L .Fm α)) :=
    CasLeft2.isFactorizableTestFn_of_tens hff ⟨fa4, ⟨⟨Φ4, hΦ4, hfa4⟩, hs4⟩, h4⟩
  have hlin : ∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      rightConv K x' β = fun g => -((1 / 4 : ℂ) * rightConv K x' (L .H (L .H α)) g
        - (1 / 2 : ℂ) * rightConv K x' (L .H α) g + rightConv K x' (L .E (L .Fm α)) g) := by
    intro x' hx'
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
    haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
    have hint : ∀ {γ : AdelicGL2 (𝓞 K) K → ℂ}, IsFactorizableTestFn K γ → ∀ g : AdelicGL2 (𝓞 K) K,
        Integrable (fun y => x' (g * y) * γ y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
      intro γ hγ g
      obtain ⟨hγc, hγs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ hγ
      exact ((hx'.comp (continuous_const.mul continuous_id)).mul hγc).integrable_of_hasCompactSupport hγs.mul_left
    funext g
    rw [rightConv_apply, rightConv_apply, rightConv_apply, rightConv_apply]
    have hfun : (fun y => x' (g * y) * β y) = fun y => -((1 / 4 : ℂ) * (x' (g * y) * L .H (L .H α) y) -
        (1 / 2 : ℂ) * (x' (g * y) * L .H α y) + x' (g * y) * L .E (L .Fm α) y) := by
      funext y
      show x' (g * y) * -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y) = _
      ring
    have hA : Integrable (fun y => (1 / 4 : ℂ) * (x' (g * y) * L .H (L .H α) y))
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := (hint hfac2 g).const_mul _
    have hB : Integrable (fun y => (1 / 2 : ℂ) * (x' (g * y) * L .H α y))
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := (hint hfac1 g).const_mul _
    have hAB : Integrable (fun y => (1 / 4 : ℂ) * (x' (g * y) * L .H (L .H α) y) -
        (1 / 2 : ℂ) * (x' (g * y) * L .H α y)) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := hA.sub hB
    rw [hfun, integral_neg, integral_add hAB (hint hfac4 g), integral_sub hA hB, integral_const_mul,
      integral_const_mul]

  have hβU : ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K, β (k * y) = β y := by
    intro k hk y
    have hk1 : glArch (𝓞 K) K k = 1 := (mem_finiteAdelicGL2Subgroup_iff K k).mp (Subgroup.mem_inf.mp hk).2
    have hα' : ∀ y, α (k * y) = α y := fun y => (hαU y k hk).1
    have e1 : ∀ y, L .H α (k * y) = L .H α y := fun y => CasLeft2.Ld_left_inv hw hk1 hα' .H y
    have e2 : ∀ y, L .H (L .H α) (k * y) = L .H (L .H α) y := fun y => CasLeft2.Ld_left_inv hw hk1 e1 .H y
    have e3 : ∀ y, L .Fm α (k * y) = L .Fm α y := fun y => CasLeft2.Ld_left_inv hw hk1 hα' .Fm y
    have e4 : ∀ y, L .E (L .Fm α) (k * y) = L .E (L .Fm α) y := fun y => CasLeft2.Ld_left_inv hw hk1 e3 .E y
    show -((1 / 4 : ℂ) * L .H (L .H α) (k * y) - (1 / 2 : ℂ) * L .H α (k * y) + L .E (L .Fm α) (k * y)) =
      -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y)
    rw [e1, e2, e4]
  refine ⟨⟨hβf, hβb⟩, hlin, fun x' hx' _ _ => Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
  · intro g u hu
    rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
    have hfun : (fun y => β (u⁻¹ * y)) = β := funext fun y => hβU u⁻¹ (Subgroup.inv_mem _ hu) y
    rw [hfun]
  · exact (mem_archCutSubmodule_ofChar_iff K χ _).mpr fun v =>
      (mem_archTypeSubmoduleAt_ofChar_iff K v (χ v) _).mp
        (rightConv_mem_archTypeSubmoduleAt_ofChar K v (χ v) x' β (hβLmem v))

end CasimirBridge

/-! #### SET-AF10 — the Casimir commutes with a right translate by a row isometry and with right
convolution

Two headlines: the Casimir of a right translate by a row isometry at any place (and of a right
convolution by a factorisable test function) is the translate/convolve of the Casimir; and for a
character-typed factorisable test function, `rightConv x' α` is arch-smooth, its Casimir is again a
right convolution by a factorisable bi-finite function, and it stays in
`levelInvariantSubmodule ⊓ archCutSubmodule`. -/

-- The pin's `attribute [-ext]` (pin `:5`): `subst` must not use `Completion.ext` on `w' = w`.
attribute [-ext] NumberField.InfinitePlace.Completion.ext

open AutomorphicForm.CuspidalConstituent

/-- **Headline.** The Casimir commutes with right translation by a row isometry (every place) and with
right convolution by a factorisable test function; smoothness and the first/second derivative
continuities are preserved. -/
theorem archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAt hw x)) ∧
    (∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAt hw (rightConv K x f) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x f)))) ∧
        archCasimirAt hw (rightConv K x f) = rightConv K (archCasimirAt hw x) f) := by
  classical
  refine ⟨?_, AutomorphicForm.archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt K w hw x hxc hxs hD1 hD2⟩
  intro w' k
  by_cases hw' : w' = w
  · subst hw'

    set e := ringEquivRealOfIsReal hw with he
    let m : GL (Fin 2) ℝ := glEquivOfRingEquiv e (k : GL (Fin 2) w'.Completion)
    have hkm : rowIsometryInclAt₀ K w' k = archRealGLAt hw m := by
      show adelicArchGLInclAt K w' (k : GL (Fin 2) w'.Completion) =
        adelicArchGLInclAt K w' (glEquivOfRingEquiv e.symm (glEquivOfRingEquiv e (k : GL (Fin 2) w'.Completion)))
      congr 1
      apply Units.ext; ext i j
      show ((k : GL (Fin 2) w'.Completion) : Matrix (Fin 2) (Fin 2) w'.Completion) i j =
        e.symm (e (((k : GL (Fin 2) w'.Completion) : Matrix (Fin 2) (Fin 2) w'.Completion) i j))
      exact (e.symm_apply_apply _).symm
    rw [hkm]
    exact AutomorphicForm.archCasimirAt_rightTranslate_archRealGLAt K w' hw x hxc hxs hD1 hD2 m
  · exact AutomorphicForm.archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne K w hw x hxc hxs hD1 hD2 w' hw' k

/-- **Headline.** For a character-typed factorisable test function `α`, `rightConv x' α` is
arch-smooth with continuous first and second derivatives, its Casimir is `rightConv x' β` for a
factorisable `β` that is arch-bi-finite of the same type, and the Casimir stays in
`levelInvariantSubmodule ⊓ archCutSubmodule`. -/
theorem isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x')
    (hxl : x' ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N)
    (hxt : x' ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ))
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K (ArchTypeFamily.ofChar K χ) α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    IsArchSmoothAt hw (rightConv K x' α) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x' α))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x' α)))) ∧
    (∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsArchBiFinite K (ArchTypeFamily.ofChar K χ) β ∧
        archCasimirAt hw (rightConv K x' α) = rightConv K x' β) ∧
    archCasimirAt hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
      archCutSubmodule K (ArchTypeFamily.ofChar K χ) := by
  classical

  set L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
    fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0 with hL
  have hcalc := fun d : ArchDir =>
    AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d
  have hLfact : ∀ (d : ArchDir) (γ : AdelicGL2 (𝓞 K) K → ℂ), IsFactorizableTestFn K γ → IsFactorizableTestFn K (L d γ) := by
    intro d γ hγ
    obtain ⟨fa, ff, hfa, hff, hγ'⟩ := hγ
    obtain ⟨fa', hfa', heq⟩ := (hcalc d).2.1 fa ff hfa
    refine ⟨fa', ff, hfa', hff, fun y => ?_⟩
    have hfun : (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) =
        fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) * ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y)) := by
      funext t; rw [hγ']
    show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0 = fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)
    rw [hfun]
    exact congrFun heq y

  have hD1 : ∀ d : ArchDir, IsArchSmoothAt hw (rightConv K x' α) ∧
      archDerivAt hw d (rightConv K x' α) = rightConv K x' (L d α) := fun d => (hcalc d).1 x' α hxc hαf
  have hcontL : ∀ γ : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K γ → Continuous (rightConv K x' γ) := fun γ hγ =>
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K x' hxc γ hγ).1
  have hsmooth : IsArchSmoothAt hw (rightConv K x' α) := (hD1 .H).1
  have hder1 : ∀ d : ArchDir, archDerivAt hw d (rightConv K x' α) = rightConv K x' (L d α) := fun d => (hD1 d).2
  have hder2 : ∀ d d' : ArchDir, archDerivAt hw d (archDerivAt hw d' (rightConv K x' α)) = rightConv K x' (L d (L d' α)) := by
    intro d d'
    rw [hder1 d']
    exact ((hcalc d).1 x' (L d' α) hxc (hLfact d' α hαf)).2

  obtain ⟨⟨hβf, hβb⟩, hlin, hmem⟩ :=
    AutomorphicForm.isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar K D w hw hreal N χ α hαf hαb hαU
  have hΩ : archCasimirAt hw (rightConv K x' α) =
      rightConv K x' (fun y => -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y)) := by
    rw [hlin x' hxc]
    funext g
    simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hder2 .H .H, hder1 .H, hder2 .E .Fm]
  refine ⟨hsmooth, fun d => ?_, fun d d' => ?_, ⟨_, hβf, hβb, hΩ⟩, ?_⟩
  · rw [hder1 d]; exact hcontL _ (hLfact d α hαf)
  · rw [hder2 d d']; exact hcontL _ (hLfact d _ (hLfact d' α hαf))
  · rw [hΩ]; exact hmem x' hxc hxl hxt

end AutomorphicForm

end
