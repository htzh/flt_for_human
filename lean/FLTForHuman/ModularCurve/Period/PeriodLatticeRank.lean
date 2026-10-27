/-
  Nondegeneracy of the real periods of a weight-2 cusp form.

  If every period `ModularCurve.periodOf Γ γ f` of `f : CuspForm Γ 2` has vanishing
  real part, then `f = 0`: the real parts of the periods separate cusp forms, i.e.
  no nonzero cusp form has all of its periods purely imaginary.

  The proof passes to an equivariant primitive `F` of `f`
  (`ModularCurve.exists_hasEquivariantPrimitiveOf`) and studies the
  nowhere-vanishing holomorphic function `cexp ∘ F`, whose logarithmic derivative is
  `f`. The hypothesis says `re (F (γ • z)) = re (F z)` for every `γ ∈ Γ`, so
  `‖cexp (F z)‖` depends only on the `Γ`-orbit of `z` (`re_apply_smul`,
  `norm_exp_apply_smul`). Choosing, for each coset of `Γ`, a representative at which
  `im ≥ 1/2`, one bounds `‖cexp (F z)‖` by the maximum of the `q`-function
  `Φ M F ρ` on the compact closed disc of radius `e ^ (-π / M)` (`exp_F_const`).
  That maximum is attained inside the open unit disc, so the maximum-modulus
  principle makes `cexp ∘ F` constant; then
  `f = (cexp ∘ F)' / (cexp ∘ F) = 0` (`apply_eq_zero`).

  Transcribed from
  `P2M/Sol/S_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.lean` (pinned
  `aa2d8b3`, 310 lines); the statement is the `Theorems/` wrapper's. Two shared
  blocks are imported rather than transcribed: the derivative pair
  `hasDerivAt_smul_ofComplex` / `hasDerivAt_comp_smul` from
  `ModularForms/EichlerShimura/EichlerIntegral.lean`, and the convergence pair
  `tendsto_vadd_atImInfty` / `const_eq_zero_of_tendsto_sub` from
  `ModularCurve/Period/ParabolicHoms.lean`. Every helper below is `private`, so the
  statement checker diffs only the headline.

  References (public mirror, pinned):
  <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.lean>,
  <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.lean>

  spec-pin: Theorems/Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.lean
  spec-pin: P2M/Sol/S_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.Period.ParabolicHoms
import FLTForHuman.ModularForms.EichlerShimura.EichlerIntegral
import FLTForHuman.ModularForms.EichlerShimura.ExistsEquivariantPrimitive
import FLTForHuman.ModularForms.EichlerShimura.PeriodOf

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups Real Manifold ModularForm

open UpperHalfPlane Filter Topology Complex Function Metric

namespace ModularCurve

namespace PeriodRealInjectivityOf

open ModularCurve.Period

local notation "𝕢" => Function.Periodic.qParam

/-- A `T`-power conjugated into `Γ` has vanishing period: the two translates of `F`
differ by a constant, and both tend to the same limit at `i∞`. -/
private theorem apply_smul_T_zpow_smul {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : IsEquivariantPrimitive Γ F) (δ : SL(2, ℤ)) {L : ℂ}
    (hlim : Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) (n : ℤ)
    (hγ : δ * ModularGroup.T ^ n * δ⁻¹ ∈ Γ) (w : ℍ) :
    F (δ • (ModularGroup.T ^ n • w)) = F (δ • w) := by
  have hkey : ∀ w : ℍ, (δ * ModularGroup.T ^ n * δ⁻¹ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w)
      = δ • (ModularGroup.T ^ n • w) := by
    intro w
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  have hc' : ∀ w : ℍ, F (δ • (ModularGroup.T ^ n • w)) - F (δ • w) = hF.period ⟨_, hγ⟩ := by
    intro w
    rw [← hkey]
    exact hF.sub_eq_period ⟨_, hγ⟩ (δ • w)
  have hc0 : hF.period ⟨_, hγ⟩ = 0 := by
    refine PeriodMapParabolicOf.const_eq_zero_of_tendsto_sub
      (g := fun w : ℍ => F (δ • (ModularGroup.T ^ n • w)))
      (h := fun w : ℍ => F (δ • w)) (L := L) ?_ hlim hc'
    have hfun : (fun w : ℍ => F (δ • (ModularGroup.T ^ n • w)))
        = (fun w : ℍ => F (δ • w)) ∘ fun w : ℍ => ((n : ℤ) : ℝ) +ᵥ w := by
      funext w
      simp only [Function.comp_apply, UpperHalfPlane.modular_T_zpow_smul]
    rw [hfun]
    exact hlim.comp (PeriodMapParabolicOf.tendsto_vadd_atImInfty ((n : ℤ) : ℝ))
  have := hc' w
  rwa [hc0, sub_eq_zero] at this

/-- Some positive `M` has every conjugate `δ * T ^ M * δ⁻¹` inside `Γ`. -/
private theorem exists_conj_T_zpow_mem (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ M : ℕ, 0 < M ∧ ∀ δ : SL(2, ℤ), δ * ModularGroup.T ^ (M : ℤ) * δ⁻¹ ∈ Γ := by
  obtain ⟨M, hM, -, hTM⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := Γ.normalCore)) ModularGroup.T
  refine ⟨M, hM, fun δ => Γ.normalCore_le ?_⟩
  rw [zpow_natCast]
  exact Γ.normalCore_normal.conj_mem _ hTM δ

section Main

variable {Γ : Subgroup SL(2, ℤ)} {M : ℕ} {f : CuspForm Γ 2} {F : ℍ → ℂ}

/-- The exponential of the `ρ`-translate of the primitive. -/
private noncomputable def K (F : ℍ → ℂ) (ρ : SL(2, ℤ)) : ℍ → ℂ :=
  fun w => cexp (F (ρ⁻¹ • w))

/-- `K F ρ` is periodic in the `q`-variable, with period `M`. -/
private theorem K_periodic (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F)
    (hTM : ∀ δ : SL(2, ℤ), δ * ModularGroup.T ^ (M : ℤ) * δ⁻¹ ∈ Γ) (ρ : SL(2, ℤ)) :
    Periodic (K F ρ ∘ ofComplex) (M : ℝ) := by
  obtain ⟨L, hL⟩ := hF.2.2.2 ρ⁻¹
  intro z
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + (M : ℝ)).im := by simpa using hz
    simp only [Function.comp_apply, K]
    rw [ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hz]
    have hT : (⟨z + (M : ℝ), hz'⟩ : ℍ) = ModularGroup.T ^ (M : ℤ) • (⟨z, hz⟩ : ℍ) := by
      rw [UpperHalfPlane.modular_T_zpow_smul]
      ext1
      simp [UpperHalfPlane.coe_vadd, add_comm]
    rw [hT, apply_smul_T_zpow_smul hF.2.2.1 ρ⁻¹ hL (M : ℤ) (by
      simpa using hTM ρ⁻¹)]
  · have hz : z.im ≤ 0 := not_lt.mp hz
    have hz' : (z + (M : ℝ)).im ≤ 0 := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_eq_of_im_nonpos hz' hz]

/-- `K F ρ` is holomorphic. -/
private theorem K_mdifferentiable (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F)
    (ρ : SL(2, ℤ)) : MDiff (K F ρ) := by
  intro τ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have h1 : DifferentiableAt ℂ (fun z : ℂ => F (ρ⁻¹ • ofComplex z)) ↑τ :=
    (HeckeEis.hasDerivAt_comp_smul hF.1 ρ⁻¹ τ).differentiableAt
  exact h1.cexp

/-- `K F ρ` has a limit at `i∞`. -/
private theorem K_tendsto (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F)
    (ρ : SL(2, ℤ)) : ∃ M : ℂ, Tendsto (K F ρ) atImInfty (𝓝 M) := by
  obtain ⟨L, hL⟩ := hF.2.2.2 ρ⁻¹
  exact ⟨cexp L, hL.cexp⟩

/-- `K F ρ` is bounded at `i∞`. -/
private theorem K_bounded (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F)
    (ρ : SL(2, ℤ)) : IsBoundedAtImInfty (K F ρ) := by
  obtain ⟨M, hM⟩ := K_tendsto hF ρ
  have := hM.isBigO_one ℝ
  exact this

/-- The `M`-th `q`-function of `K F ρ`, a scalar function on the `q`-disc. It is
unrelated to the linear map `Φ` from regular differentials to cusp forms. -/
private noncomputable def Φ (N : ℕ) (F : ℍ → ℂ) (ρ : SL(2, ℤ)) : ℂ → ℂ :=
  UpperHalfPlane.cuspFunction (N : ℝ) (K F ρ)

variable (hM : 0 < M) (hTM : ∀ δ : SL(2, ℤ), δ * ModularGroup.T ^ (M : ℤ) * δ⁻¹ ∈ Γ)

include hM in
private theorem hNpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM

include hM hTM in
private theorem Φ_differentiableOn (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F)
    (ρ : SL(2, ℤ)) : DifferentiableOn ℂ (Φ M F ρ) (ball 0 1) :=
  differentiableOn_cuspFunction_ball (hNpos hM) (K_periodic hF hTM ρ) (K_mdifferentiable hF ρ)
    (K_bounded hF ρ)

include hM hTM in
private theorem Φ_qParam (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F) (ρ : SL(2, ℤ))
    (w : ℍ) : Φ M F ρ (𝕢 (M : ℝ) ↑w) = cexp (F (ρ⁻¹ • w)) :=
  UpperHalfPlane.eq_cuspFunction w (hNpos hM).ne' (K_periodic hF hTM ρ)

private theorem qParam_mem_ball (w : ℍ) : 𝕢 (M : ℝ) ↑w ∈ ball (0 : ℂ) 1 ∨ (M : ℝ) ≤ 0 := by
  by_cases hN : (0 : ℝ) < M
  · left
    rw [mem_ball_zero_iff, Function.Periodic.norm_qParam]
    have him : (0:ℝ) < Complex.im ↑w := w.2
    calc Real.exp (-2 * π * Complex.im ↑w / M) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by
            apply div_neg_of_neg_of_pos _ hN
            nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero
  · right; exact not_lt.mp hN

include hM in
private theorem qParam_mem_ball' (w : ℍ) : 𝕢 (M : ℝ) ↑w ∈ ball (0 : ℂ) 1 := by
  rcases qParam_mem_ball (M := M) w with h | h
  · exact h
  · exact absurd (hNpos hM) (not_lt.mpr h)

include hM in
private theorem qParam_mem_closedBall {w : ℍ} (hw : 1 / 2 ≤ w.im) :
    𝕢 (M : ℝ) ↑w ∈ closedBall (0 : ℂ) (Real.exp (-π / M)) := by
  rw [mem_closedBall_zero_iff, Function.Periodic.norm_qParam, Real.exp_le_exp, UpperHalfPlane.coe_im]
  rw [div_le_div_iff_of_pos_right (hNpos hM)]
  nlinarith [Real.pi_pos]

/-- The hypothesis on the real parts of the periods: `F` is `Γ`-equivariant in real
part. -/
private theorem re_apply_smul (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0)
    (γ : Γ) (z : ℍ) :
    (F ((γ : SL(2, ℤ)) • z)).re = (F z).re := by
  have h1 := hF.2.2.1.sub_eq_period γ z
  have h2 : hF.2.2.1.period γ = ModularCurve.periodOf Γ γ f := by
    rw [ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf Γ f hF γ]
    rfl
  have h3 : (F ((γ : SL(2, ℤ)) • z) - F z).re = 0 := by rw [h1, h2, h γ]
  rw [Complex.sub_re, sub_eq_zero] at h3
  exact h3

/-- Hence `‖cexp (F z)‖` is invariant under `Γ`. -/
private theorem norm_exp_apply_smul (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) :
    ‖cexp (F (γ • z))‖ = ‖cexp (F z)‖ := by
  rw [Complex.norm_exp, Complex.norm_exp, ← re_apply_smul hF h ⟨γ, hγ⟩ z]

include hM hTM in
private theorem exp_F_const [Γ.FiniteIndex]
    (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0) :
    ∃ c : ℂ, ∀ z : ℍ, cexp (F z) = c := by
  classical
  -- The pin writes `haveI` here; instance search also reads a local hypothesis of class
  -- type, and `Finset.univ` below needs the quotient's `Fintype`.
  have hfin : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  set r : ℝ := Real.exp (-π / M) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (hNpos hM)

  have hmax : ∀ j : SL(2, ℤ) ⧸ Γ, ∃ q ∈ closedBall (0 : ℂ) r,
      IsMaxOn (norm ∘ Φ M F j.out) (closedBall (0 : ℂ) r) q := fun j =>
    (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn (nonempty_closedBall.mpr hr0)
      (((Φ_differentiableOn hM hTM hF j.out).continuousOn.mono (closedBall_subset_ball hr1)).norm)
  choose q hq hqmax using hmax
  set m : SL(2, ℤ) ⧸ Γ → ℝ := fun j => ‖Φ M F j.out (q j)‖ with hm
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ m ⟨(1 : SL(2, ℤ)), Finset.mem_univ _⟩
  set B : ℝ := m j₀ with hB

  have hbound : ∀ z : ℍ, ‖cexp (F z)‖ ≤ B := by
    intro z
    obtain ⟨g, hg⟩ := ModularGroup.exists_one_half_le_im_smul z
    obtain ⟨g0, hg0⟩ := QuotientGroup.mk_out_eq_mul Γ g
    set j : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk g with hj
    have h1 : ‖cexp (F z)‖ = ‖Φ M F j.out (𝕢 (M : ℝ) ↑(g • z))‖ := by
      rw [Φ_qParam hM hTM hF, hg0, mul_inv_rev, mul_smul, inv_smul_smul]
      exact (norm_exp_apply_smul hF h (inv_mem g0.2) z).symm
    rw [h1]
    exact (hqmax j (qParam_mem_closedBall hM hg)).trans (hj₀ j (Finset.mem_univ _))

  set ρ₀ : SL(2, ℤ) := j₀.out with hρ₀
  have hΦd : DifferentiableOn ℂ (Φ M F ρ₀) (ball 0 1) := Φ_differentiableOn hM hTM hF ρ₀
  have hnonzero : ∀ p ∈ ball (0 : ℂ) 1, p ≠ 0 → ‖Φ M F ρ₀ p‖ ≤ B := by
    intro p hp hp0
    have him : 0 < (Function.Periodic.invQParam (M : ℝ) p).im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (hNpos hM) (mem_ball_zero_iff.mp hp) hp0
    have : Φ M F ρ₀ p = cexp (F (ρ₀⁻¹ • ⟨_, him⟩)) := by
      rw [Φ, UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hp0,
        Function.comp_apply, K, ofComplex_apply_of_im_pos him]
    rw [this]
    exact hbound _
  have hall : ∀ p ∈ ball (0 : ℂ) 1, ‖Φ M F ρ₀ p‖ ≤ B := by
    intro p hp
    rcases eq_or_ne p 0 with rfl | hp0
    · have hcont : ContinuousAt (Φ M F ρ₀) 0 :=
        (hΦd.differentiableAt (ball_mem_nhds 0 one_pos)).continuousAt
      have ht : Tendsto (fun p => ‖Φ M F ρ₀ p‖) (𝓝[≠] 0) (𝓝 ‖Φ M F ρ₀ 0‖) :=
        (hcont.tendsto.mono_left nhdsWithin_le_nhds).norm
      refine le_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) one_pos)] with p hp0 hp1
      exact hnonzero p hp1 hp0
    · exact hnonzero p hp hp0
  have hq₀ball : q j₀ ∈ ball (0 : ℂ) 1 := closedBall_subset_ball hr1 (hq j₀)
  have hismax : IsMaxOn (norm ∘ Φ M F ρ₀) (ball 0 1) (q j₀) := by
    intro p hp
    exact hall p hp
  have hconst := Complex.eq_const_of_exists_max hΦd hq₀ball hismax

  refine ⟨Φ M F ρ₀ (q j₀), fun z => ?_⟩
  have h1 : cexp (F z) = Φ M F ρ₀ (𝕢 (M : ℝ) ↑(ρ₀ • z)) := by
    rw [Φ_qParam hM hTM hF, inv_smul_smul]
  rw [h1]
  exact hconst (qParam_mem_ball' hM _)

include hM hTM in
private theorem apply_eq_zero [Γ.FiniteIndex] (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0) (τ : ℍ) :
    f τ = 0 := by
  obtain ⟨c, hc⟩ := exp_F_const hM hTM hF h
  have h1 : HasDerivAt (fun z : ℂ => cexp ((F ∘ ofComplex) z)) (cexp ((F ∘ ofComplex) ↑τ) * f τ) ↑τ :=
    (hF.1 τ).cexp
  have h2 : HasDerivAt (fun z : ℂ => cexp ((F ∘ ofComplex) z)) 0 ↑τ := by
    refine (hasDerivAt_const (↑τ : ℂ) c).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz]
    exact hc _
  have h3 := h1.unique h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (Complex.exp_ne_zero _)
  · exact h4

end Main

private theorem main (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (f : CuspForm Γ 2)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0) : f = 0 := by
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ f
  obtain ⟨M, hM, hTM⟩ := exists_conj_T_zpow_mem Γ
  exact DFunLike.ext f 0 fun τ => by simpa using apply_eq_zero hM hTM hF h τ

end PeriodRealInjectivityOf

/-- **Nondegeneracy of the real periods.** A weight-2 cusp form of finite level whose
periods are all purely imaginary vanishes. -/
theorem eq_zero_of_forall_re_periodOf_eq_zero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0) : f = 0 :=
  PeriodRealInjectivityOf.main Γ f h

end ModularCurve
