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
-/
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothLeft
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmooth
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
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

open NumberField AutomorphicForm NumberField.AdelicLevel
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

end AutomorphicForm

end
