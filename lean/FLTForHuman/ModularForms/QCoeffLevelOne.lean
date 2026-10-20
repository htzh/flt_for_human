/-
  Level-one `q`-expansion coefficients and the Rankin–Cohen bracket.

  Five leaves of the `ModularForm` q-expansion family, transcribed from their
  pinned `Theorems/` wrappers with the proofs of their `P2M/Sol/` files, whole
  (`aa2d8b3`):

  * `ModularForm.exists_gamma0_qExpansion_eq_of_levelOne` (36 pin lines) — every
    level-one form is the identity of a level-`N` form;
  * `ModularForm.levelOne_weight_four_qCoeff_one` (24) and
    `ModularForm.levelOne_weight_six_qCoeff_one` (24) — the weight-`4`/`6` spaces
    are one-dimensional, so `a₁ = 240 a₀` and `a₁ = -504 a₀`;
  * `ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant`
    (52) — a weight-twelve form vanishing at the cusp is a multiple of `Δ`,
    coefficientwise;
  * `ModularForm.exists_rankinCohen_one_qExpansion_eq` (301) — the rankin-Cohen
    bracket `k₁ g h' - k₂ g' h` of two forms at level `Γ` is a form of weight
    `k₁ + k₂ + 2` whose q-expansion is the `θ`-expression in the statement.

  Home by subject (playbook §3.1): these are the `ModularForm` q-expansion facts
  the `omegaRow_T2` node consumes, so they sit together in one module and the
  `ModularCurve` `θ`/omega-row material lives in `ModularCurve/OmegaRowT2.lean`.

  Faithfulness and drift.  Statements are the wrappers' verbatim; proofs are the
  `S_` files' bodies with the pin's `p2m_export`/`p2m_open`/`p2m_open_scoped`
  scaffolding dropped (they export definitions the port already has) and the
  pin's private helper blocks kept `private` under their own inner namespaces
  (`SolRESTRAux`, `WL12Pen`, `RankinCohenOne`).  The pin's `attribute [-simp]`
  and `attribute [-instance]` blocks on the wrappers are **not** transcribed: they
  prune the pin's global simp/instance sets (hundreds of hub declarations, most of
  them not imported here) to make its proofs elaborate in the giant `import
  Mathlib` environment; they are not part of any statement, and the port's
  targeted imports reproduce the pin's elaboration without them.  The one
  `set_option Elab.async false` of the twelve-node's `S_` file is dropped for the
  same reason (nothing here needs the pin's async workaround).  The pin's
  `import Mathlib` becomes the named modules below.

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_levelOne_weight_four_qCoeff_one.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_levelOne_weight_six_qCoeff_one.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq.lean>

  spec-pin: Theorems/Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne.lean
  spec-pin: P2M/Sol/S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne.lean
  spec-pin: Theorems/Thm_ModularForm_levelOne_weight_four_qCoeff_one.lean
  spec-pin: P2M/Sol/S_ModularForm_levelOne_weight_four_qCoeff_one.lean
  spec-pin: Theorems/Thm_ModularForm_levelOne_weight_six_qCoeff_one.lean
  spec-pin: P2M/Sol/S_ModularForm_levelOne_weight_six_qCoeff_one.lean
  spec-pin: Theorems/Thm_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant.lean
  spec-pin: P2M/Sol/S_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant.lean
  spec-pin: Theorems/Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq.lean
  spec-pin: P2M/Sol/S_ModularForm_exists_rankinCohen_one_qExpansion_eq.lean
-/

import FLTForHuman.ModularForms.Level.Degeneracy
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularCurve.Period.QExpansionDerivative
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.RingTheory.LaurentSeries

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Manifold Topology Real

/-! ### Level-one forms are level-`N` forms -/

namespace SolRESTRAux

private theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [gamma0_one_eq_top, MonoidHom.range_eq_map]

private theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  simp [Matrix.one_fin_two]

end SolRESTRAux

namespace ModularForm

theorem exists_gamma0_qExpansion_eq_of_levelOne (N : ℕ) [NeZero N] {k : ℤ}
    (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm (CongruenceSubgroup.Gamma0 N) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
  obtain ⟨G, hG⟩ := ModularForm.exists_degeneracy_Gamma0 (show 1 * 1 ∣ N by simp)
    (ModularForm.mcast rfl F SolRESTRAux.gamma0_one_coe)
  refine ⟨G, ?_⟩
  rw [hG, SolRESTRAux.heckeDiagMatrix_one]
  funext τ
  rw [one_smul]
  rfl

/-! ### The weight-`4` and weight-`6` one-dimensional spaces -/

theorem levelOne_weight_four_qCoeff_one (Y : ModularForm 𝒮ℒ 4) :
    ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₄ = Y :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₄ (EisensteinSeries.E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_four_rank_one) Y
  have hq : UpperHalfPlane.qExpansion 1 ⇑Y = c • UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c ModularForm.E₄,
      show (c • ⇑ModularForm.E₄) = ⇑Y from congrArg DFunLike.coe hc]
  have h0 : (UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  show (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 1 = _ * (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 0
  rw [hq, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul, h0,
    ModularForm.E₄_qExpansion_coeff_one]
  ring

theorem levelOne_weight_six_qCoeff_one (Y : ModularForm 𝒮ℒ 6) :
    ModularFormClass.qCoeff ⇑Y 1 = -504 * ModularFormClass.qCoeff ⇑Y 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₆ = Y :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₆ (EisensteinSeries.E_ne_zero _ ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_six_rank_one) Y
  have hq : UpperHalfPlane.qExpansion 1 ⇑Y = c • UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c ModularForm.E₆,
      show (c • ⇑ModularForm.E₆) = ⇑Y from congrArg DFunLike.coe hc]
  have h0 : (UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  show (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 1 = _ * (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 0
  rw [hq, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul, h0,
    ModularForm.E₆_qExpansion_coeff_one]
  ring

/-! ### Weight twelve: a form vanishing at the cusp is a multiple of `Δ` -/

namespace WL12Pen

private theorem exists_coe_eq_smul_discriminant (Z : ModularForm 𝒮ℒ 12)
    (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) :
    ∃ c : ℂ, (⇑Z : UpperHalfPlane → ℂ) = c • ⇑CuspForm.discriminant := by
  obtain ⟨c, hc⟩ :=
    CuspForm.exists_smul_discriminant_of_weight_eq_twelve (ModularForm.toCuspForm Z h0)
  exact ⟨c, (show (c • ⇑CuspForm.discriminant : UpperHalfPlane → ℂ)
    = ⇑(ModularForm.toCuspForm Z h0) from congrArg DFunLike.coe hc).symm⟩

private theorem qExpansion_eq_smul (Z : ModularForm 𝒮ℒ 12) (c : ℂ)
    (hZ : (⇑Z : UpperHalfPlane → ℂ) = c • ⇑CuspForm.discriminant) :
    UpperHalfPlane.qExpansion 1 ⇑Z = c • UpperHalfPlane.qExpansion 1 ModularForm.discriminant := by
  rw [hZ, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c CuspForm.discriminant,
    CuspForm.coe_discriminant]

private theorem qCoeff_eq_mul (Z : ModularForm 𝒮ℒ 12) (c : ℂ)
    (hq : UpperHalfPlane.qExpansion 1 ⇑Z
      = c • UpperHalfPlane.qExpansion 1 ModularForm.discriminant) (n : ℕ) :
    ModularFormClass.qCoeff ⇑Z n = c * ModularFormClass.qCoeff ModularForm.discriminant n := by
  unfold ModularFormClass.qCoeff
  rw [hq, PowerSeries.coeff_smul, smul_eq_mul]

private theorem qCoeff_one_eq (Z : ModularForm 𝒮ℒ 12) (c : ℂ)
    (hq : UpperHalfPlane.qExpansion 1 ⇑Z
      = c • UpperHalfPlane.qExpansion 1 ModularForm.discriminant) :
    ModularFormClass.qCoeff ⇑Z 1 = c := by
  have h1 : ModularFormClass.qCoeff ModularForm.discriminant 1 = 1 := by
    unfold ModularFormClass.qCoeff
    exact ModularForm.discriminant_qExpansion_coeff_one
  rw [qCoeff_eq_mul Z c hq 1, h1, mul_one]

end WL12Pen

theorem levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant (Z : ModularForm 𝒮ℒ 12)
    (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n =
      ModularFormClass.qCoeff ⇑Z 1 * ModularFormClass.qCoeff ModularForm.discriminant n := by
  obtain ⟨c, hZ⟩ := WL12Pen.exists_coe_eq_smul_discriminant Z h0
  have hq := WL12Pen.qExpansion_eq_smul Z c hZ
  intro n
  rw [WL12Pen.qCoeff_eq_mul Z c hq n, WL12Pen.qCoeff_one_eq Z c hq]

/-! ### The Rankin–Cohen bracket -/

namespace RankinCohenOne

theorem det_coe_SL (γ : SL(2, ℤ)) :
    ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe (γ.map (Int.castRingHom ℝ))
  simpa using this

theorem denom_SL (γ : SL(2, ℤ)) (z : ℂ) :
    denom (γ : GL (Fin 2) ℝ) z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem hasDerivAt_comp_smul {F : ℍ → ℂ} (hF : MDiff F) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => F (γ • ofComplex z))
      (deriv (F ∘ ofComplex) ↑(γ • τ) * (1 / denom (γ : GL (Fin 2) ℝ) τ ^ 2)) τ := by
  have hs := (hasStrictDerivAt_smul (g := (γ : GL (Fin 2) ℝ))
    (by rw [det_coe_SL]; exact one_pos) τ).hasDerivAt
  have hF' : HasDerivAt (F ∘ ofComplex) (deriv (F ∘ ofComplex) ↑(γ • τ))
      ↑((γ : GL (Fin 2) ℝ) • ofComplex (τ : ℂ)) := by
    rw [ofComplex_apply]
    exact (mdifferentiableAt_iff.mp (hF _)).hasDerivAt
  have := hF'.comp (τ : ℂ) hs
  convert this using 1 <;> first
    | with_reducible_and_instances rfl
    | rfl
    | (ext z; simp only [Function.comp_apply, ofComplex_apply]; done)
    | (ext z; simp only [Function.comp_apply, ofComplex_apply]; rfl)
    | (rw [det_coe_SL]; push_cast; ring)

theorem hasDerivAt_denom_zpow (k : ℤ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => denom (γ : GL (Fin 2) ℝ) z ^ (-k))
      ((-k : ℂ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k - 1) * ((γ 1 0 : ℤ) : ℂ)) τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hlin : HasDerivAt (fun z : ℂ => denom (γ : GL (Fin 2) ℝ) z) ((γ 1 0 : ℤ) : ℂ) τ := by
    simp_rw [denom_SL]
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  have hz := (hasDerivAt_zpow (-k) (denom (γ : GL (Fin 2) ℝ) τ) (Or.inl hden)).comp (τ : ℂ) hlin
  push_cast at hz
  exact hz

theorem D_slash {F : ℍ → ℂ} (hF : MDiff F) (k : ℤ) (γ : SL(2, ℤ)) (τ : ℍ) :
    Derivative.normalizedDerivOfComplex (F ∣[k] γ) τ =
      (Derivative.normalizedDerivOfComplex F (γ • τ) * (denom (γ : GL (Fin 2) ℝ) τ)⁻¹ ^ 2
        - k * (2 * π * Complex.I)⁻¹ * ((γ 1 0 : ℤ) : ℂ) * (denom (γ : GL (Fin 2) ℝ) τ)⁻¹ * F (γ • τ))
        * denom (γ : GL (Fin 2) ℝ) τ ^ (-k) := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hprod := (hasDerivAt_comp_smul hF γ τ).mul (hasDerivAt_denom_zpow k γ τ)
  have hev : ((F ∣[k] γ) ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      fun z : ℂ => F (γ • ofComplex z) * denom (γ : GL (Fin 2) ℝ) z ^ (-k) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    rw [Function.comp_apply, SL_slash_apply, ofComplex_apply_of_im_pos hz]
  have hD := hprod.congr_of_eventuallyEq hev
  simp only [Derivative.normalizedDerivOfComplex]
  rw [hD.deriv]
  have e1 : denom (γ : GL (Fin 2) ℝ) τ ^ (-k - 1) =
      denom (γ : GL (Fin 2) ℝ) τ ^ (-k) * (denom (γ : GL (Fin 2) ℝ) τ)⁻¹ := by
    rw [sub_eq_add_neg, zpow_add₀ hden, zpow_neg_one]
  rw [e1]
  simp only [ofComplex_apply]
  field_simp
  ring

local notation "D" => Derivative.normalizedDerivOfComplex

def bracket (k₁ k₂ : ℤ) (g h : ℍ → ℂ) : ℍ → ℂ :=
  (k₁ : ℂ) • (g * D h) - (k₂ : ℂ) • (D g * h)

theorem bracket_apply (k₁ k₂ : ℤ) (g h : ℍ → ℂ) (τ : ℍ) :
    bracket k₁ k₂ g h τ = k₁ * (g τ * D h τ) - k₂ * (D g τ * h τ) := rfl

theorem bracket_slash {g h : ℍ → ℂ} (hg : MDiff g) (hh : MDiff h) (k₁ k₂ : ℤ)
    (γ : SL(2, ℤ)) :
    bracket k₁ k₂ (g ∣[k₁] γ) (h ∣[k₂] γ) = (bracket k₁ k₂ g h) ∣[k₁ + k₂ + 2] γ := by
  funext τ
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [SL_slash_apply, bracket_apply, bracket_apply, D_slash hg, D_slash hh, SL_slash_apply,
    SL_slash_apply]
  have e : denom (γ : GL (Fin 2) ℝ) τ ^ (-(k₁ + k₂ + 2)) =
      denom (γ : GL (Fin 2) ℝ) τ ^ (-k₁) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k₂) *
        (denom (γ : GL (Fin 2) ℝ) τ)⁻¹ ^ 2 := by
    rw [show (-(k₁ + k₂ + 2) : ℤ) = -k₁ + -k₂ + -2 by ring, zpow_add₀ hden, zpow_add₀ hden,
      zpow_neg _ 2, zpow_ofNat, inv_pow]
  rw [e]
  ring

theorem isBoundedAtImInfty_D {F : ℍ → ℂ} (hF : MDiff F) (hb : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (D F) := by
  rw [isBoundedAtImInfty_iff] at hb ⊢
  obtain ⟨M, A, hMA⟩ := hb
  refine ⟨‖(2 * π * Complex.I)⁻¹‖ * M, max A 0 + 2, fun z hz => ?_⟩
  have hzA : max A 0 + 2 ≤ (z : ℂ).im := by rwa [coe_im]

  have hdisc : ∀ w : ℂ, dist w z ≤ 1 → 0 < w.im ∧ A ≤ w.im := by
    intro w hw
    have h1 : |(w - z).im| ≤ ‖w - (z : ℂ)‖ := Complex.abs_im_le_norm _
    rw [dist_eq_norm] at hw
    have h2 := (abs_le.mp (h1.trans hw)).1
    simp only [Complex.sub_im] at h2
    constructor
    · linarith [le_max_right A 0]
    · linarith [le_max_left A 0]
  have key : ‖deriv (F ∘ ofComplex) z‖ ≤ M / 1 := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos
    · apply DifferentiableOn.diffContOnCl
      refine (UpperHalfPlane.mdifferentiable_iff.mp hF).mono ?_
      rw [closure_ball _ one_ne_zero]
      intro w hw
      exact (hdisc w (Metric.mem_closedBall.mp hw)).1
    · intro w hw
      have hw' : dist w z ≤ 1 := (Metric.mem_sphere.mp hw).le
      obtain ⟨hwpos, hwA⟩ := hdisc w hw'
      have := hMA ⟨w, hwpos⟩ hwA
      simpa [Function.comp_apply, ofComplex_apply_of_im_pos hwpos] using this
  rw [div_one] at key
  simp only [Derivative.normalizedDerivOfComplex, norm_mul]
  gcongr

theorem periodic_D {F : ℍ → ℂ} (hper : Function.Periodic (F ∘ ofComplex) 1) :
    Function.Periodic (D F ∘ ofComplex) 1 := by
  intro w
  simp only [Function.comp_apply, Derivative.normalizedDerivOfComplex]
  congr 1
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    rw [ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos hw']
    change deriv (F ∘ ofComplex) (w + 1) = deriv (F ∘ ofComplex) w
    have hfun : (F ∘ ofComplex) = fun x => (F ∘ ofComplex) (x + 1) := (funext hper).symm
    conv_rhs => rw [hfun]
    rw [deriv_comp_add_const]
  · have hw' : (w + 1).im ≤ 0 := by simpa using not_lt.mp hw
    rw [ofComplex_apply_eq_of_im_nonpos hw' (not_lt.mp hw)]

theorem mdifferentiable_bracket {g h : ℍ → ℂ} (hg : MDiff g) (hh : MDiff h) (k₁ k₂ : ℤ) :
    MDiff (bracket k₁ k₂ g h) :=
  ((hg.mul (Derivative.normalizedDerivOfComplex_mdifferentiable hh)).const_smul _).sub
    (((Derivative.normalizedDerivOfComplex_mdifferentiable hg).mul hh).const_smul _)

theorem isBoundedAtImInfty_bracket {g h : ℍ → ℂ} (hg : MDiff g) (hh : MDiff h)
    (hgb : IsBoundedAtImInfty g) (hhb : IsBoundedAtImInfty h) (k₁ k₂ : ℤ) :
    IsBoundedAtImInfty (bracket k₁ k₂ g h) := by
  rw [bracket, sub_eq_add_neg]
  exact ((hgb.mul (isBoundedAtImInfty_D hh hhb)).smul _).add
    (((isBoundedAtImInfty_D hg hgb).mul hhb).smul _).neg

theorem periodic_bracket {g h : ℍ → ℂ} (hg : Function.Periodic (g ∘ ofComplex) 1)
    (hh : Function.Periodic (h ∘ ofComplex) 1) (k₁ k₂ : ℤ) :
    Function.Periodic (bracket k₁ k₂ g h ∘ ofComplex) 1 := by
  intro w
  have h1 := hg w
  have h2 := hh w
  have h3 := periodic_D hg w
  have h4 := periodic_D hh w
  simp only [Function.comp_apply] at h1 h2 h3 h4 ⊢
  rw [bracket_apply, bracket_apply, h1, h2, h3, h4]

variable {Γ : Subgroup SL(2, ℤ)} {k₁ k₂ : ℤ}

def rankinCohen [Γ.FiniteIndex] (g : ModularForm Γ k₁) (h : ModularForm Γ k₂) :
    ModularForm Γ (k₁ + k₂ + 2) where
  toFun := bracket k₁ k₂ g h
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hA
    have hγ' : (γ : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := Subgroup.mem_map_of_mem _ hγ
    change bracket k₁ k₂ g h ∣[k₁ + k₂ + 2] (γ : GL (Fin 2) ℝ) = _
    rw [← SL_slash, ← bracket_slash (ModularFormClass.holo g) (ModularFormClass.holo h), SL_slash,
      SL_slash, SlashInvariantForm.slash_action_eqn g _ hγ',
      SlashInvariantForm.slash_action_eqn h _ hγ']
  holo' := mdifferentiable_bracket (ModularFormClass.holo g) (ModularFormClass.holo h) k₁ k₂
  bdd_at_cusps' {c} hc := by
    have hc' : IsCusp c (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* _).range :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
    intro γ _
    rw [← bracket_slash (ModularFormClass.holo g) (ModularFormClass.holo h)]
    exact isBoundedAtImInfty_bracket ((ModularFormClass.holo g).slash k₁ (γ : GL (Fin 2) ℝ))
      ((ModularFormClass.holo h).slash k₂ (γ : GL (Fin 2) ℝ))
      (ModularFormClass.bdd_at_infty_slash g γ) (ModularFormClass.bdd_at_infty_slash h γ) k₁ k₂

theorem rankinCohen_apply [Γ.FiniteIndex] (g : ModularForm Γ k₁) (h : ModularForm Γ k₂) (τ : ℍ) :
    rankinCohen g h τ = k₁ * g τ * D h τ - k₂ * D g τ * h τ := by
  change bracket k₁ k₂ g h τ = _
  rw [bracket_apply]; ring

theorem coe_rankinCohen [Γ.FiniteIndex] (g : ModularForm Γ k₁) (h : ModularForm Γ k₂) :
    (rankinCohen g h : ℍ → ℂ) = bracket k₁ k₂ g h := rfl

open ModularCurve in
theorem coeff_nat_thetaL_ofPowerSeries (φ : PowerSeries ℂ) (n : ℕ) :
    (thetaL ℂ (HahnSeries.ofPowerSeries ℤ ℂ φ)).coeff (n : ℤ) = (n : ℂ) * PowerSeries.coeff n φ := by
  rw [thetaL_apply, show ((n : ℤ)) = ((n : ℤ) - 1) + 1 by ring, HahnSeries.coeff_single_mul_add,
    one_mul, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, Nat.cast_one,
    sub_add_cancel, Ring.choose_one_right, HahnSeries.ofPowerSeries_apply_coeff, zsmul_eq_mul,
    Int.cast_natCast]

theorem qExpansion_D {F : ℍ → ℂ} (hper : Function.Periodic (F ∘ ofComplex) 1) (hhol : MDiff F)
    (hbdd : IsBoundedAtImInfty F) :
    qExpansion 1 (D F) =
      PowerSeries.mk fun n : ℕ => (n : ℂ) * (qExpansion 1 F).coeff n := by
  ext n
  have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (n : ℤ))
    (ModularCurve.coe_qExpansion_normalizedDerivOfComplex F hper hhol hbdd)
  beta_reduce at h
  rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_nat_thetaL_ofPowerSeries] at h
  rw [h, PowerSeries.coeff_mk]

section

variable (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
include h1

theorem periodic_coe {k : ℤ} (f : ModularForm Γ k) : Function.Periodic (⇑f ∘ ofComplex) 1 := by
  simpa using SlashInvariantFormClass.periodic_comp_ofComplex f h1

theorem analyticAt_cuspFunction {k : ℤ} (f : ModularForm Γ k) :
    AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos h1

theorem analyticAt_cuspFunction_D [Γ.FiniteIndex] {k : ℤ} (f : ModularForm Γ k) :
    AnalyticAt ℂ (cuspFunction 1 (D (f : ℍ → ℂ))) 0 := by
  have := analyticAt_cuspFunction_zero (h := 1) (f := D (f : ℍ → ℂ)) one_pos
    (by simpa using periodic_D (periodic_coe h1 f))
    (Derivative.normalizedDerivOfComplex_mdifferentiable (ModularFormClass.holo f))
    (isBoundedAtImInfty_D (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f))
  exact this

theorem qExpansion_D_coe [Γ.FiniteIndex] {k : ℤ} (f : ModularForm Γ k) :
    qExpansion 1 (D (f : ℍ → ℂ)) =
      PowerSeries.mk fun n : ℕ => (n : ℂ) * (qExpansion 1 (f : ℍ → ℂ)).coeff n :=
  qExpansion_D (by simpa using periodic_coe h1 f) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f)

theorem qExpansion_rankinCohen [Γ.FiniteIndex] (g : ModularForm Γ k₁) (h : ModularForm Γ k₂) :
    qExpansion 1 (rankinCohen g h : ℍ → ℂ) =
      PowerSeries.C (k₁ : ℂ) * qExpansion 1 (g : ℍ → ℂ) *
          PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (h : ℍ → ℂ)).coeff n)
        - PowerSeries.C (k₂ : ℂ) *
          PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (g : ℍ → ℂ)).coeff n) *
            qExpansion 1 (h : ℍ → ℂ) := by
  have ag := analyticAt_cuspFunction h1 g
  have ah := analyticAt_cuspFunction h1 h
  have aDg := analyticAt_cuspFunction_D h1 g
  have aDh := analyticAt_cuspFunction_D h1 h
  have a1 : AnalyticAt ℂ (cuspFunction 1 ((g : ℍ → ℂ) * D (h : ℍ → ℂ))) 0 := by
    rw [cuspFunction_mul ag.continuousAt aDh.continuousAt]; exact ag.mul aDh
  have a2 : AnalyticAt ℂ (cuspFunction 1 (D (g : ℍ → ℂ) * (h : ℍ → ℂ))) 0 := by
    rw [cuspFunction_mul aDg.continuousAt ah.continuousAt]; exact aDg.mul ah
  have a1' : AnalyticAt ℂ (cuspFunction 1 ((k₁ : ℂ) • ((g : ℍ → ℂ) * D (h : ℍ → ℂ)))) 0 := by
    rw [cuspFunction_smul a1.continuousAt]; exact analyticAt_const.smul a1
  have a2' : AnalyticAt ℂ (cuspFunction 1 ((k₂ : ℂ) • (D (g : ℍ → ℂ) * (h : ℍ → ℂ)))) 0 := by
    rw [cuspFunction_smul a2.continuousAt]; exact analyticAt_const.smul a2
  rw [coe_rankinCohen, bracket, qExpansion_sub a1' a2', qExpansion_smul a1, qExpansion_smul a2,
    qExpansion_mul ag aDh, qExpansion_mul aDg ah, qExpansion_D_coe h1 g, qExpansion_D_coe h1 h,
    PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, mul_assoc, mul_assoc]

end

end RankinCohenOne

open RankinCohenOne in
theorem exists_rankinCohen_one_qExpansion_eq
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    {k₁ k₂ : ℤ} (g : ModularForm Γ k₁) (h : ModularForm Γ k₂) :
    ∃ B : ModularForm Γ (k₁ + k₂ + 2),
      (∀ τ : ℍ, B τ = k₁ * g τ * Derivative.normalizedDerivOfComplex h τ
                     - k₂ * Derivative.normalizedDerivOfComplex g τ * h τ) ∧
      qExpansion 1 (B : ℍ → ℂ) =
        PowerSeries.C (k₁ : ℂ) * qExpansion 1 (g : ℍ → ℂ) *
            PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (h : ℍ → ℂ)).coeff n)
          - PowerSeries.C (k₂ : ℂ) *
            PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (g : ℍ → ℂ)).coeff n) *
              qExpansion 1 (h : ℍ → ℂ) :=
  ⟨rankinCohen g h, rankinCohen_apply g h, qExpansion_rankinCohen h1 g h⟩

end ModularForm

end
