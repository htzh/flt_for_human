/-
  Phase A2 of `topics/modularCurve/WORKORDER-A-levelN-field.md`: the places of the
  level-`N` function field `K` of `X(N)` and their valuations.

  The four headlines are the pin's `Theorems/` wrappers verbatim; the proofs are the
  matching `P2M/Sol/S_ModularCurve_LevelN_*` files, adapted to mathlib `v4.34.0`.  The
  shared blocks (`Good`, `Q`, the `ring N` action lemmas, `PB`, `qParam_pow_mul`,
  `Q_natCast_eq_qExpand`) are imported from `LevelN/Prelude.lean`; every other
  declaration the pin carries is re-derived `private` in the pin's own sub-namespace,
  so this module's public surface is exactly the four headlines.

  FLT provenance, pinned `aa2d8b3`:
  * `S_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq.lean:224-866`
  * `S_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq.lean:24-489`
  * `S_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord.lean:315-384`
  * `S_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul.lean:412-643`
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul.lean

  Two families of the same pin names live here (`ordFun`, `ordValuation`,
  `ordValuationK`, `ordFunction`, ...): the cusp-at-`i∞` one of `CuspPlaces` and the
  point-`τ₀` one of `AnalyticPlaces` (the pin's own namespace split; the two differ
  only in the order function they are built from).  The pin's
  `set_option linter.unusedSectionVars false` / `linter.unusedVariables false` and its
  local `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` bumps are not
  transcribed; where Lean auto-includes an unused section instance that `omit` refuses
  to remove (its *value* uses it), the suppression is narrowed to that declaration.
  The `Real` scope is **not** opened file-wide: it carries the `π` token notation, and
  three pin declarations use `π` as a binder name (`obtain ⟨π, hπ⟩`), which is a parse
  error under that scope.  The one place the pin's `π` term is needed (`zetaInv`'s
  body, a `def` whose body the checker ignores) spells `Real.pi`.
-/
import FLTForHuman.ModularCurve.LevelN.Prelude
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.ModularCurve.Defs.JqCoeff
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter Topology Function

open scoped MatrixGroups Manifold ModularForm

namespace ModularCurve

namespace LevelN

variable {h : ℝ}

variable {G : ℍ → ℂ}


private theorem norm_qParam_lt_one (hh : 0 < h) (τ : ℍ) : ‖Periodic.qParam h τ‖ < 1 := by
  have := (Periodic.norm_qParam_lt_iff hh 0 (τ : ℂ)).mpr (by simpa using τ.im_pos)
  simpa using this
theorem Good.eq_zero_of_analyticOrderAt_eq_top (hG : Good h G) (hh : 0 < h)
    (htop : analyticOrderAt (cuspFunction h G) 0 = ⊤) : G = 0 := by
  have han : AnalyticOnNhd ℂ (cuspFunction h G) (Metric.ball 0 1) :=
    (differentiableOn_cuspFunction_ball hh hG.periodic hG.mdiff hG.bdd).analyticOnNhd
      Metric.isOpen_ball
  have hzero : Set.EqOn (cuspFunction h G) 0 (Metric.ball 0 1) :=
    han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) 1).isPreconnected (Metric.mem_ball_self one_pos)
      (analyticOrderAt_eq_top.mp htop)
  funext τ
  have hq : Periodic.qParam h τ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_qParam_lt_one hh τ
  have := hzero hq
  rw [eq_cuspFunction τ hh.ne' hG.periodic] at this
  simpa using this
theorem Good.analyticOrderAt_ne_top (hG : Good h G) (hh : 0 < h) (hG0 : G ≠ 0) :
    analyticOrderAt (cuspFunction h G) 0 ≠ ⊤ :=
  fun htop => hG0 (hG.eq_zero_of_analyticOrderAt_eq_top hh htop)
namespace CuspPlaces

variable {h : ℝ}

variable {G G₁ G₂ : ℍ → ℂ}

private def ordB (h : ℝ) (G : ℍ → ℂ) : ℕ := (analyticOrderAt (cuspFunction h G) 0).toNat
private theorem ordB_cast (hG : Good h G) (hh : 0 < h) (hG0 : G ≠ 0) :
    (ordB h G : ℕ∞) = analyticOrderAt (cuspFunction h G) 0 :=
  ENat.natCast_toNat (hG.analyticOrderAt_ne_top hh hG0)
private theorem ordB_mul (hh : 0 < h) (h₁ : Good h G₁) (h₂ : Good h G₂) (h₁0 : G₁ ≠ 0) (h₂0 : G₂ ≠ 0) :
    ordB h (G₁ * G₂) = ordB h G₁ + ordB h G₂ := by
  have hmul := analyticOrderAt_mul (h₁.analyticAt hh) (h₂.analyticAt hh)
  unfold ordB
  rw [cuspFunction_mul_of_good hh h₁ h₂, hmul]
  exact ENat.toNat_add (h₁.analyticOrderAt_ne_top hh h₁0) (h₂.analyticOrderAt_ne_top hh h₂0)
private theorem min_ordB_le_ordB_add (hh : 0 < h) (h₁ : Good h G₁) (h₂ : Good h G₂) (h₁0 : G₁ ≠ 0)
    (h₂0 : G₂ ≠ 0) (h0 : G₁ + G₂ ≠ 0) :
    min (ordB h G₁) (ordB h G₂) ≤ ordB h (G₁ + G₂) := by
  have hle := le_analyticOrderAt_add (f := cuspFunction h G₁) (g := cuspFunction h G₂) (z₀ := 0)
  rw [← cuspFunction_add_of_good hh h₁ h₂, ← ordB_cast h₁ hh h₁0, ← ordB_cast h₂ hh h₂0,
    ← ordB_cast (h₁.add h₂) hh h0] at hle
  rcases le_total (ordB h G₁) (ordB h G₂) with hle' | hle'
  · rw [min_eq_left hle']
    rw [min_eq_left (by exact_mod_cast hle')] at hle
    exact_mod_cast hle
  · rw [min_eq_right hle']
    rw [min_eq_right (by exact_mod_cast hle')] at hle
    exact_mod_cast hle
private theorem ordB_eq_zero_of_apply_ne_zero (h0 : cuspFunction h G 0 ≠ 0) : ordB h G = 0 := by
  unfold ordB
  rw [analyticOrderAt_eq_zero.mpr (Or.inr h0)]
  rfl
private theorem ordB_pos (hG : Good h G) (hh : 0 < h) (hG0 : G ≠ 0) (h0 : cuspFunction h G 0 = 0) :
    0 < ordB h G := by
  have hne : analyticOrderAt (cuspFunction h G) 0 ≠ 0 :=
    (hG.analyticAt hh).analyticOrderAt_ne_zero.mpr h0
  have hcast := ordB_cast hG hh hG0
  by_contra hle
  push Not at hle
  rw [Nat.le_zero.mp hle, Nat.cast_zero] at hcast
  exact hne hcast.symm
private theorem T_inv_smul_eq_vadd (τ : ℍ) : ModularGroup.T⁻¹ • τ = (-1 : ℝ) +ᵥ τ := by
  have := modular_T_zpow_smul τ (-1)
  rw [zpow_neg_one] at this
  rw [this]
  norm_num
private theorem coe_T_inv_smul (τ : ℍ) : ((ModularGroup.T⁻¹ • τ : ℍ) : ℂ) = (τ : ℂ) - 1 := by
  rw [T_inv_smul_eq_vadd, coe_vadd]
  push_cast
  ring
private def zetaInv (h : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I / h))
private theorem zetaInv_ne_zero (h : ℝ) : zetaInv h ≠ 0 := Complex.exp_ne_zero _
private theorem qParam_sub_one (h : ℝ) (z : ℂ) :
    Periodic.qParam h (z - 1) = zetaInv h * Periodic.qParam h z := by
  simp only [Periodic.qParam, zetaInv, ← Complex.exp_add]
  congr 1
  ring
private theorem cuspFunction_comp_T_inv_eventuallyEq_nhdsNE (hh : 0 < h) (hG : Good h G) :
    cuspFunction h (fun τ : ℍ => G (ModularGroup.T⁻¹ • τ)) =ᶠ[𝓝[≠] 0]
      (fun q => cuspFunction h G (zetaInv h * q)) := by
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with q hq hq1
  have hq0 : q ≠ 0 := hq
  rw [Metric.mem_ball, dist_zero_right] at hq1
  rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  set z := Periodic.invQParam h q with hz
  have hzim : 0 < z.im := Periodic.im_invQParam_pos_of_norm_lt_one hh hq1 hq0
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hzim]
  have hpt : ModularGroup.T⁻¹ • (⟨z, hzim⟩ : ℍ) = ofComplex (z - 1) := by
    have hzim' : 0 < (z - 1).im := by simpa using hzim
    rw [ofComplex_apply_of_im_pos hzim']
    ext1
    rw [coe_T_inv_smul]
  rw [hpt]
  have := eq_cuspFunction (f := G) (ofComplex (z - 1)) hh.ne' hG.periodic
  rw [← Function.comp_apply (f := G) (g := ofComplex), show ((ofComplex (z - 1) : ℍ) : ℂ) = z - 1 by
    rw [ofComplex_apply_of_im_pos (by simpa using hzim : 0 < (z - 1).im)]] at this
  rw [Function.comp_apply] at this
  rw [← this, qParam_sub_one, hz, Periodic.qParam_right_inv hh.ne' hq0]
private theorem cuspFunction_comp_T_inv_eventuallyEq (hh : 0 < h) (hG : Good h G)
    (hG₁ : Good h (fun τ : ℍ => G (ModularGroup.T⁻¹ • τ))) :
    cuspFunction h (fun τ : ℍ => G (ModularGroup.T⁻¹ • τ)) =ᶠ[𝓝 0]
      (fun q => cuspFunction h G (zetaInv h * q)) := by
  have hc1 : ContinuousAt (cuspFunction h (fun τ : ℍ => G (ModularGroup.T⁻¹ • τ))) 0 :=
    hG₁.continuousAt hh
  have hc2 : ContinuousAt (fun q => cuspFunction h G (zetaInv h * q)) 0 := by
    have h1 : ContinuousAt (cuspFunction h G) (zetaInv h * 0) := by
      rw [mul_zero]; exact hG.continuousAt hh
    exact ContinuousAt.comp (g := cuspFunction h G) h1 (continuous_const.mul continuous_id).continuousAt
  exact (hc1.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hc2).mp
    (cuspFunction_comp_T_inv_eventuallyEq_nhdsNE hh hG)
private theorem ordB_comp_T_inv (hh : 0 < h) (hG : Good h G)
    (hG₁ : Good h (fun τ : ℍ => G (ModularGroup.T⁻¹ • τ))) :
    ordB h (fun τ : ℍ => G (ModularGroup.T⁻¹ • τ)) = ordB h G := by
  unfold ordB
  rw [analyticOrderAt_congr (cuspFunction_comp_T_inv_eventuallyEq hh hG hG₁),
    show (fun q => cuspFunction h G (zetaInv h * q)) = cuspFunction h G ∘ (fun q => zetaInv h * q)
      from rfl,
    analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_const.mul analyticAt_id) (by
      rw [show (fun q : ℂ => zetaInv h * q) = fun q => q * zetaInv h from funext fun q => mul_comm _ _,
        deriv_mul_const_field, deriv_id'', one_mul]
      exact zetaInv_ne_zero h),
    mul_zero]
section LevelOne

local notation "Δ" => ModularForm.discriminant




private theorem discriminant_ne_zero' : (Δ : ℍ → ℂ) ≠ 0 := by
  intro h0
  have := congrFun h0 UpperHalfPlane.I
  exact ModularForm.discriminant_ne_zero _ this


private theorem cuspFunction_discriminant_zero (N : ℕ) [NeZero N] :
    cuspFunction N Δ 0 = 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [cuspFunction_apply_zero hN ((good_discriminant N).analyticAt hN) (good_discriminant N).periodic]
  exact ModularForm.discriminant_isZeroAtImInfty.valueAtInfty_eq_zero
private theorem ordB_discriminant_pos (N : ℕ) [NeZero N] : 0 < ordB N Δ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  exact ordB_pos (good_discriminant N) hN discriminant_ne_zero' (cuspFunction_discriminant_zero N)
private theorem cuspFunction_E₄_zero (N : ℕ) [NeZero N] :
    cuspFunction N (ModularForm.E₄ : ℍ → ℂ) 0 = 1 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [cuspFunction_apply_zero hN ((good_E₄ N).analyticAt hN) (good_E₄ N).periodic]
  have h1 := qExpansion_coeff_zero (f := (ModularForm.E₄ : ℍ → ℂ)) one_pos
    (by simpa using (good_E₄ 1).analyticAt (by exact_mod_cast one_pos))
    (by simpa using (good_E₄ 1).periodic)
  rw [← h1]
  exact EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by decide)
private theorem ordB_E₄_pow (N : ℕ) [NeZero N] (n : ℕ) : ordB N ((ModularForm.E₄ : ℍ → ℂ) ^ n) = 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  apply ordB_eq_zero_of_apply_ne_zero
  induction n with
  | zero =>
    rw [pow_zero]
    have : cuspFunction (N : ℝ) (1 : ℍ → ℂ) 0 = 1 := by
      rw [cuspFunction_apply_zero hN ((Good.one (N : ℝ)).analyticAt hN) (Good.one (N : ℝ)).periodic]
      exact tendsto_const_nhds.limUnder_eq
    rw [this]; exact one_ne_zero
  | succ n ih =>
    rw [pow_succ, cuspFunction_mul_of_good hN ((good_E₄ N).pow n) (good_E₄ N), Pi.mul_apply,
      cuspFunction_E₄_zero]
    simpa using ih
private theorem discriminant_T_inv_smul (τ : ℍ) : Δ (ModularGroup.T⁻¹ • τ) = Δ τ := by
  have hper : Periodic (ModularForm.discriminant ∘ ofComplex) 1 := by
    simpa using (good_discriminant 1).periodic
  have him : 0 < ((τ : ℂ) - 1).im := by simpa using τ.im_pos
  have h1 : (ModularGroup.T⁻¹ • τ : ℍ) = ofComplex ((τ : ℂ) - 1) := by
    rw [ofComplex_apply_of_im_pos him]
    ext1
    rw [coe_T_inv_smul]
  rw [h1]
  have h2 := hper ((τ : ℂ) - 1)
  rw [Function.comp_apply, Function.comp_apply, sub_add_cancel, ofComplex_apply] at h2
  exact h2.symm

end LevelOne
section OrdInf

local notation "Δ" => ModularForm.discriminant

variable (N : ℕ) [NeZero N]

private theorem castN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
private def PB (F : ℍ → ℂ) (m : ℕ) : Prop := IsBoundedAtImInfty (F * (Δ : ℍ → ℂ) ^ m)
omit [NeZero N] in
private theorem PB.add_right {F : ℍ → ℂ} {m : ℕ} (hm : PB F m) (k : ℕ) : PB F (m + k) := by
  unfold PB at hm ⊢
  rw [pow_add, ← mul_assoc]
  exact hm.mul ((good_discriminant 1).pow k).bdd
private theorem good_of_PB {F : ℍ → ℂ} (hF : F ∈ ring N) {m : ℕ} (hm : PB F m) :
    Good N (F * (Δ : ℍ → ℂ) ^ m) where
  periodic := by
    have : (F * (Δ : ℍ → ℂ) ^ m) ∘ ofComplex = (F ∘ ofComplex) * (((Δ : ℍ → ℂ) ^ m) ∘ ofComplex) := rfl
    rw [this]
    exact (periodic_of_mem N hF).mul ((good_discriminant N).pow m).periodic
  mdiff := (mdifferentiable_of_mem N hF).mul ((good_discriminant N).pow m).mdiff
  bdd := hm
private def ordAux (F : ℍ → ℂ) (m : ℕ) : ℤ :=
  (ordB N (F * (Δ : ℍ → ℂ) ^ m) : ℤ) - m * (ordB N (Δ : ℍ → ℂ) : ℤ)
private theorem ordB_one : ordB N (1 : ℍ → ℂ) = 0 :=
  ordB_eq_zero_of_apply_ne_zero (by
    rw [cuspFunction_apply_zero (castN_pos N) ((Good.one (N : ℝ)).analyticAt (castN_pos N))
      (Good.one (N : ℝ)).periodic]
    rw [show valueAtInfty (1 : ℍ → ℂ) = 1 from tendsto_const_nhds.limUnder_eq]
    exact one_ne_zero)
private theorem ordB_discriminant_pow (k : ℕ) : ordB N ((Δ : ℍ → ℂ) ^ k) = k * ordB N (Δ : ℍ → ℂ) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_mul]
    exact ordB_one N
  | succ k ih =>
    rw [pow_succ, ordB_mul (castN_pos N) ((good_discriminant N).pow k) (good_discriminant N)
      (discriminant_pow_ne_zero k) discriminant_ne_zero', ih]
    ring
private theorem ordAux_add_right {F : ℍ → ℂ} (hF : F ∈ ring N) (hF0 : F ≠ 0) {m : ℕ} (hm : PB F m)
    (k : ℕ) : ordAux N F (m + k) = ordAux N F m := by
  unfold ordAux
  rw [pow_add, ← mul_assoc, ordB_mul (castN_pos N) (good_of_PB N hF hm)
    ((good_discriminant N).pow k) (by rwa [Ne, mul_discriminant_pow_eq_zero_iff])
    (discriminant_pow_ne_zero k), ordB_discriminant_pow]
  push_cast
  ring
private theorem ordAux_eq_ordAux {F : ℍ → ℂ} (hF : F ∈ ring N) (hF0 : F ≠ 0) {m m' : ℕ} (hm : PB F m)
    (hm' : PB F m') : ordAux N F m = ordAux N F m' := by
  rw [← ordAux_add_right N hF hF0 hm m', ← ordAux_add_right N hF hF0 hm' m, add_comm]
open Classical in

private def ordInf (F : ℍ → ℂ) : ℤ :=
  if hex : ∃ m : ℕ, PB F m then ordAux N F (Nat.find hex) else 0
private theorem ordInf_eq {F : ℍ → ℂ} (hF : F ∈ ring N) (hF0 : F ≠ 0) {m : ℕ} (hm : PB F m) :
    ordInf N F = ordAux N F m := by
  classical
  have hex : ∃ m : ℕ, PB F m := ⟨m, hm⟩
  rw [ordInf, dite_eq_left hex]
  exact ordAux_eq_ordAux N hF hF0 (Nat.find_spec hex) hm
private theorem ordInf_mul {F G : ℍ → ℂ} (hF : F ∈ ring N) (hG : G ∈ ring N) (hF0 : F ≠ 0) (hG0 : G ≠ 0) :
    ordInf N (F * G) = ordInf N F + ordInf N G := by
  obtain ⟨m, hm⟩ := exists_isBoundedAtImInfty_mul_pow N hF
  obtain ⟨n, hn⟩ := exists_isBoundedAtImInfty_mul_pow N hG
  have hFG0 : F * G ≠ 0 := by
    intro h0
    rcases eq_zero_or_eq_zero_of_mul_eq_zero N hF hG h0 with h | h
    · exact hF0 h
    · exact hG0 h
  have hprod : (F * G) * (Δ : ℍ → ℂ) ^ (m + n) = (F * (Δ : ℍ → ℂ) ^ m) * (G * (Δ : ℍ → ℂ) ^ n) := by
    ring
  have hmn : PB (F * G) (m + n) := by
    unfold PB
    rw [hprod]
    exact hm.mul hn
  rw [ordInf_eq N ((ring N).mul_mem hF hG) hFG0 hmn, ordInf_eq N hF hF0 hm, ordInf_eq N hG hG0 hn]
  unfold ordAux
  rw [hprod, ordB_mul (castN_pos N) (good_of_PB N hF hm) (good_of_PB N hG hn)
    (by rwa [Ne, mul_discriminant_pow_eq_zero_iff]) (by rwa [Ne, mul_discriminant_pow_eq_zero_iff])]
  push_cast
  ring
private theorem min_ordInf_le_ordInf_add {F G : ℍ → ℂ} (hF : F ∈ ring N) (hG : G ∈ ring N) (hF0 : F ≠ 0)
    (hG0 : G ≠ 0) (hFG : F + G ≠ 0) : min (ordInf N F) (ordInf N G) ≤ ordInf N (F + G) := by
  obtain ⟨m, hm⟩ := exists_isBoundedAtImInfty_mul_pow N hF
  obtain ⟨n, hn⟩ := exists_isBoundedAtImInfty_mul_pow N hG
  have hmM : PB F (m + n) := PB.add_right hm n
  have hnM : PB G (m + n) := by rw [add_comm]; exact PB.add_right hn m
  have hsum : (F + G) * (Δ : ℍ → ℂ) ^ (m + n) = F * (Δ : ℍ → ℂ) ^ (m + n) + G * (Δ : ℍ → ℂ) ^ (m + n) := by
    ring
  have hM : PB (F + G) (m + n) := by
    unfold PB
    rw [hsum]
    exact hmM.add hnM
  rw [ordInf_eq N ((ring N).add_mem hF hG) hFG hM, ordInf_eq N hF hF0 hmM, ordInf_eq N hG hG0 hnM]
  unfold ordAux
  have hle := min_ordB_le_ordB_add (castN_pos N) (good_of_PB N hF hmM) (good_of_PB N hG hnM)
    (by rwa [Ne, mul_discriminant_pow_eq_zero_iff]) (by rwa [Ne, mul_discriminant_pow_eq_zero_iff])
    (by rw [← hsum]; rwa [Ne, mul_discriminant_pow_eq_zero_iff])
  rw [hsum]
  rw [min_sub_sub_right]
  gcongr
  exact_mod_cast hle
private theorem ordInf_one : ordInf N (1 : ℍ → ℂ) = 0 := by
  have h1 : PB (1 : ℍ → ℂ) 0 := by
    unfold PB
    rw [pow_zero, mul_one]
    exact Filter.const_boundedAtFilter _ _
  rw [ordInf_eq N (ring N).one_mem one_ne_zero h1]
  unfold ordAux
  rw [pow_zero, mul_one, Nat.cast_zero, zero_mul, sub_zero, ordB_one N]
  simp
private theorem ordInf_jAnalytic : ordInf N jAnalytic = -(ordB N (Δ : ℍ → ℂ) : ℤ) := by
  have hjΔ : jAnalytic * (Δ : ℍ → ℂ) ^ 1 = (ModularForm.E₄ : ℍ → ℂ) ^ 3 := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_one, jAnalytic]
    field_simp [ModularForm.discriminant_ne_zero τ]
  have h1 : PB jAnalytic 1 := by
    unfold PB
    rw [hjΔ]
    exact ((good_E₄ N).pow 3).bdd
  have hj0 : jAnalytic ≠ 0 := by
    intro h0
    have hpkg := WLight.levelN_structure_package N PeriodPair.ofTau (fun _ => ⟨rfl, rfl⟩) (wp N)
      (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
    have := hpkg.2.2.2.1 Polynomial.X (fun τ => by
      rw [Polynomial.eval_X, h0]; rfl)
    exact Polynomial.X_ne_zero this
  rw [ordInf_eq N (jAnalytic_mem N) hj0 h1]
  unfold ordAux
  rw [hjΔ, ordB_E₄_pow N 3]
  simp
private theorem ordInf_comp_T_inv {F : ℍ → ℂ} (hF : F ∈ ring N)
    (hF₁ : (fun τ : ℍ => F (ModularGroup.T⁻¹ • τ)) ∈ ring N) :
    ordInf N (fun τ : ℍ => F (ModularGroup.T⁻¹ • τ)) = ordInf N F := by
  by_cases hF0 : F = 0
  · subst hF0
    rfl
  obtain ⟨m, hm⟩ := exists_isBoundedAtImInfty_mul_pow N hF
  set F₁ : ℍ → ℂ := fun τ : ℍ => F (ModularGroup.T⁻¹ • τ) with hF₁def
  have hfun : F₁ * (Δ : ℍ → ℂ) ^ m = fun τ : ℍ => (F * (Δ : ℍ → ℂ) ^ m) (ModularGroup.T⁻¹ • τ) := by
    funext τ
    simp only [hF₁def, Pi.mul_apply, Pi.pow_apply, discriminant_T_inv_smul]
  have hF₁0 : F₁ ≠ 0 := by
    intro h0
    apply hF0
    funext τ
    have := congrFun h0 (ModularGroup.T • τ)
    simpa [hF₁def] using this

  have htend : Tendsto (fun τ : ℍ => ModularGroup.T⁻¹ • τ) atImInfty atImInfty := by
    rw [atImInfty, Filter.tendsto_comap_iff]
    have : UpperHalfPlane.im ∘ (fun τ : ℍ => ModularGroup.T⁻¹ • τ) = UpperHalfPlane.im := by
      funext τ
      simp only [Function.comp_apply, T_inv_smul_eq_vadd, vadd_im]
    rw [this]
    exact Filter.tendsto_comap
  have hm₁ : PB F₁ m := by
    unfold PB
    rw [hfun]
    exact hm.comp_tendsto htend
  rw [ordInf_eq N hF₁ hF₁0 hm₁, ordInf_eq N hF hF0 hm]
  unfold ordAux
  congr 2
  rw [hfun]
  have hG := good_of_PB N hF hm
  have hG₁ : Good N (fun τ : ℍ => (F * (Δ : ℍ → ℂ) ^ m) (ModularGroup.T⁻¹ • τ)) := by
    rw [← hfun]
    exact good_of_PB N hF₁ hm₁
  exact_mod_cast ordB_comp_T_inv (castN_pos N) hG hG₁

end OrdInf
section Valuation

local notation "Δ" => ModularForm.discriminant

variable (N : ℕ) [NeZero N]

open Classical in

private def ordFun (F : ring N) : WithZero (Multiplicative ℤ) :=
  if (F : ℍ → ℂ) = 0 then 0 else WithZero.exp (-ordInf N (F : ℍ → ℂ))
set_option linter.unusedSectionVars false in
private theorem ordFun_of_ne_zero {F : ring N} (hF : (F : ℍ → ℂ) ≠ 0) :
    ordFun N F = WithZero.exp (-ordInf N (F : ℍ → ℂ)) := by
  simp [ordFun, hF]
set_option linter.unusedSectionVars false in
private theorem ordFun_zero' {F : ring N} (hF : (F : ℍ → ℂ) = 0) : ordFun N F = 0 := by
  simp [ordFun, hF]
private def ordValuation : Valuation (ring N) (WithZero (Multiplicative ℤ)) where
  toFun := ordFun N
  map_zero' := ordFun_zero' N rfl
  map_one' := by
    rw [ordFun_of_ne_zero N (by simp)]
    simp [ordInf_one]
  map_mul' F G := by
    by_cases hF : (F : ℍ → ℂ) = 0
    · rw [ordFun_zero' N hF, ordFun_zero' N (by simp [hF]), zero_mul]
    by_cases hG : (G : ℍ → ℂ) = 0
    · rw [ordFun_zero' N hG, ordFun_zero' N (by simp [hG]), mul_zero]
    have hFG : ((F * G : ring N) : ℍ → ℂ) ≠ 0 := by
      intro h
      rcases eq_zero_or_eq_zero_of_mul_eq_zero N F.2 G.2 (by simpa using h) with h' | h'
      · exact hF h'
      · exact hG h'
    rw [ordFun_of_ne_zero N hF, ordFun_of_ne_zero N hG, ordFun_of_ne_zero N hFG,
      ← WithZero.exp_add]
    congr 1
    rw [show ((F * G : ring N) : ℍ → ℂ) = (F : ℍ → ℂ) * (G : ℍ → ℂ) from rfl,
      ordInf_mul N F.2 G.2 hF hG]
    ring
  map_add_le_max' F G := by
    by_cases hFG : ((F + G : ring N) : ℍ → ℂ) = 0
    · rw [ordFun_zero' N hFG]; exact zero_le
    by_cases hF : (F : ℍ → ℂ) = 0
    · have : F + G = G := by
        have hF' : F = 0 := Subtype.ext hF
        rw [hF', zero_add]
      rw [this, ordFun_zero' N hF]
      exact le_max_right _ _
    by_cases hG : (G : ℍ → ℂ) = 0
    · have : F + G = F := by
        have hG' : G = 0 := Subtype.ext hG
        rw [hG', add_zero]
      rw [this, ordFun_zero' N hG]
      exact le_max_left _ _
    rw [ordFun_of_ne_zero N hF, ordFun_of_ne_zero N hG, ordFun_of_ne_zero N hFG]
    have hmin := min_ordInf_le_ordInf_add N F.2 G.2 hF hG (by simpa using hFG)
    rw [show ((F + G : ring N) : ℍ → ℂ) = (F : ℍ → ℂ) + (G : ℍ → ℂ) from rfl]
    rcases le_total (ordInf N (F : ℍ → ℂ)) (ordInf N (G : ℍ → ℂ)) with h | h
    · rw [min_eq_left h] at hmin
      refine le_trans ?_ (le_max_left _ _)
      rw [WithZero.exp_le_exp]
      omega
    · rw [min_eq_right h] at hmin
      refine le_trans ?_ (le_max_right _ _)
      rw [WithZero.exp_le_exp]
      omega
@[scoped simp]
private theorem ordValuation_apply (F : ring N) : ordValuation N F = ordFun N F := rfl
private theorem ordValuation_ne_zero {F : ring N} (hF : F ≠ 0) : ordValuation N F ≠ 0 := by
  have hF' : (F : ℍ → ℂ) ≠ 0 := fun h => hF (Subtype.ext h)
  rw [ordValuation_apply, ordFun_of_ne_zero N hF']
  exact WithZero.exp_ne_zero
private theorem nonZeroDivisors_le_supp_primeCompl :
    nonZeroDivisors (ring N) ≤ (ordValuation N).supp.primeCompl := by
  intro s hs
  change s ∉ (ordValuation N).supp
  rw [Valuation.mem_supp_iff]
  apply ordValuation_ne_zero
  intro h
  rw [h] at hs
  exact zero_notMem_nonZeroDivisors hs

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring N) K] [IsScalarTower ℂ (ring N) K]
  [IsFractionRing (ring N) K]
private def ordValuationK : Valuation K (WithZero (Multiplicative ℤ)) :=
  (ordValuation N).extendToLocalization (S := nonZeroDivisors (ring N))
    (nonZeroDivisors_le_supp_primeCompl N) K
set_option linter.unusedSectionVars false in
private theorem ordValuationK_algebraMap (F : ring N) :
    ordValuationK N K (algebraMap (ring N) K F) = ordFun N F :=
  Valuation.extendToLocalization_apply_map_apply _ _ K F
private theorem ordValuationK_jK :
    ordValuationK N K (algebraMap (ring N) K (jGen N)) = WithZero.exp (ordB N (Δ : ℍ → ℂ) : ℤ) := by
  have hj0 : ((jGen N : ring N) : ℍ → ℂ) ≠ 0 := by
    intro h0
    have hpkg := WLight.levelN_structure_package N PeriodPair.ofTau (fun _ => ⟨rfl, rfl⟩) (wp N)
      (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
    have := hpkg.2.2.2.1 Polynomial.X (fun τ => by
      rw [Polynomial.eval_X, ← coe_jGen N, h0]; rfl)
    exact Polynomial.X_ne_zero this
  rw [ordValuationK_algebraMap, ordFun_of_ne_zero N hj0, coe_jGen, ordInf_jAnalytic, neg_neg]
private theorem one_lt_ordValuationK_jK : 1 < ordValuationK N K (algebraMap (ring N) K (jGen N)) := by
  rw [ordValuationK_jK, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  exact_mod_cast ordB_discriminant_pos N
private theorem isNontrivial_ordValuationK : (ordValuationK N K).IsNontrivial := by
  refine ⟨algebraMap (ring N) K (jGen N), ?_, ?_⟩
  · rw [ordValuationK_jK]; exact WithZero.exp_ne_zero
  · exact (one_lt_ordValuationK_jK N K).ne'
private theorem nontrivial_valueGroup :
    Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass <| ordValuationK N K)) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  have hne : ordValuationK N K (algebraMap (ring N) K (jGen N)) ≠ 0 := by
    rw [ordValuationK_jK]; exact WithZero.exp_ne_zero
  refine ⟨Units.mk0 _ hne, ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨_, rfl⟩
  · intro h
    have h' := congrArg (fun u : (WithZero (Multiplicative ℤ))ˣ => (u : WithZero (Multiplicative ℤ))) h
    simp only [Units.val_mk0, Units.val_one] at h'
    exact (one_lt_ordValuationK_jK N K).ne' h'
private def cuspPlace : AlgebraicCurve.Place ℂ K :=
  haveI := nontrivial_valueGroup N K
  { toValuationSubring := (ordValuationK N K).valuationSubring
    algebraMap_mem' := fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      by_cases ha : a = 0
      · simp [ha]
      · rw [IsScalarTower.algebraMap_apply ℂ (ring N) K, ordValuationK_algebraMap]
        have hne : ((algebraMap ℂ (ring N) a : ring N) : ℍ → ℂ) ≠ 0 := by
          intro h
          have := congrFun h UpperHalfPlane.I
          simp [Algebra.algebraMap_eq_smul_one, ha] at this
        rw [ordFun_of_ne_zero N hne, ← WithZero.exp_zero, WithZero.exp_le_exp]

        have hPB : PB ((algebraMap ℂ (ring N) a : ring N) : ℍ → ℂ) 0 := by
          unfold PB
          rw [pow_zero, mul_one]
          have : ((algebraMap ℂ (ring N) a : ring N) : ℍ → ℂ) = fun _ => a := by
            funext τ; simp [Algebra.algebraMap_eq_smul_one]
          rw [this]
          exact Filter.const_boundedAtFilter _ _
        rw [ordInf_eq N (algebraMap ℂ (ring N) a).2 hne hPB]
        unfold ordAux
        rw [pow_zero, mul_one, Nat.cast_zero, zero_mul, sub_zero, neg_nonpos]
        exact_mod_cast Nat.zero_le _
    ne_top' := by
      rw [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
      exact isNontrivial_ordValuationK N K
    isPrincipalIdealRing' :=
      (Valuation.valuationSubring_isDiscreteValuationRing
        (ordValuationK N K)).toIsPrincipalIdealRing }
@[scoped simp]
private theorem cuspPlace_toValuationSubring :
    (cuspPlace N K).toValuationSubring = (ordValuationK N K).valuationSubring := rfl
private theorem mem_cuspPlace_iff (x : K) :
    x ∈ (cuspPlace N K).toValuationSubring ↔ ordValuationK N K x ≤ 1 := by
  rw [cuspPlace_toValuationSubring, Valuation.mem_valuationSubring_iff]
private theorem ord_jK_neg : (cuspPlace N K).ord (algebraMap (ring N) K (jGen N)) < 0 := by
  set W := cuspPlace N K
  set y := algebraMap (ring N) K (jGen N) with hy
  have hyW : y ∉ W.toValuationSubring := by
    rw [mem_cuspPlace_iff, not_le]
    exact one_lt_ordValuationK_jK N K
  have hy0 : y ≠ 0 := fun h => hyW (h ▸ W.toValuationSubring.zero_mem)

  have hmem : y⁻¹ ∈ W.toValuationSubring.nonunits :=
    (ValuationSubring.inv_mem_nonunits_iff W.toValuationSubring).mpr (Or.inr hyW)
  obtain ⟨hyiW, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hmem
  have hval : W.adicValuation y⁻¹ < 1 := by
    rw [W.adicValuation_coe ⟨y⁻¹, hyiW⟩,
      IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hmax
  have hne : W.adicValuation y⁻¹ ≠ 0 := W.adicValuation_ne_zero (inv_ne_zero hy0)
  have hpos : 0 < W.ord y⁻¹ := by
    rw [AlgebraicCurve.Place.ord, neg_pos, WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]
    exact hval
  rw [W.ord_inv] at hpos
  omega
private theorem ordFun_comp_T_inv (F : ring N)
    (hF₁ : (fun τ : ℍ => (F : ℍ → ℂ) (ModularGroup.T⁻¹ • τ)) ∈ ring N) :
    ordFun N ⟨fun τ : ℍ => (F : ℍ → ℂ) (ModularGroup.T⁻¹ • τ), hF₁⟩ = ordFun N F := by
  have hiff : (fun τ : ℍ => (F : ℍ → ℂ) (ModularGroup.T⁻¹ • τ)) = 0 ↔ (F : ℍ → ℂ) = 0 := by
    constructor
    · intro h
      funext τ
      have := congrFun h (ModularGroup.T • τ)
      simpa using this
    · intro h
      funext τ
      simp [h]
  by_cases hF : (F : ℍ → ℂ) = 0
  · rw [ordFun_zero' N hF, ordFun_zero' N (by
      change (fun τ : ℍ => (F : ℍ → ℂ) (ModularGroup.T⁻¹ • τ)) = 0
      exact hiff.mpr hF)]
  · have hF' : (fun τ : ℍ => (F : ℍ → ℂ) (ModularGroup.T⁻¹ • τ)) ≠ 0 := by
      rw [Ne, hiff]; exact hF
    rw [ordFun_of_ne_zero N hF, ordFun_of_ne_zero N (F := ⟨_, hF₁⟩) hF']
    congr 2
    exact ordInf_comp_T_inv N F.2 hF₁
private theorem ordValuationK_algEquiv
    (hst : ∀ F ∈ ring N, (fun τ : ℍ => F (ModularGroup.T⁻¹ • τ)) ∈ ring N) (φ : K ≃ₐ[ℂ] K)
    (hφ : ∀ (F : ℍ → ℂ) (hF : F ∈ ring N),
      φ (algebraMap (ring N) K ⟨F, hF⟩) =
        algebraMap (ring N) K ⟨fun τ : ℍ => F (ModularGroup.T⁻¹ • τ), hst F hF⟩)
    (x : K) : ordValuationK N K (φ x) = ordValuationK N K x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ring N) x
  rw [map_div₀, map_div₀, map_div₀]
  have ha := hφ (a : ℍ → ℂ) a.2
  have hb' := hφ (b : ℍ → ℂ) b.2
  simp only [Subtype.coe_eta] at ha hb'
  rw [ha, hb', ordValuationK_algebraMap, ordValuationK_algebraMap, ordValuationK_algebraMap,
    ordValuationK_algebraMap, ordFun_comp_T_inv N a, ordFun_comp_T_inv N b]
private theorem smul_cuspPlace_eq
    (hst : ∀ F ∈ ring N, (fun τ : ℍ => F (ModularGroup.T⁻¹ • τ)) ∈ ring N) (φ : K ≃ₐ[ℂ] K)
    (hφ : ∀ (F : ℍ → ℂ) (hF : F ∈ ring N),
      φ (algebraMap (ring N) K ⟨F, hF⟩) =
        algebraMap (ring N) K ⟨fun τ : ℍ => F (ModularGroup.T⁻¹ • τ), hst F hF⟩) :
    AlgebraicCurve.SemilinearAut.ofAlgAut φ • cuspPlace N K = cuspPlace N K := by
  apply AlgebraicCurve.Place.ext
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    AlgebraicCurve.SemilinearAut.ofAlgAut_smul, mem_cuspPlace_iff, mem_cuspPlace_iff]
  have h := ordValuationK_algEquiv N K hst φ hφ (φ⁻¹ x)
  rw [show φ (φ⁻¹ x) = x from φ.apply_symm_apply x] at h
  rw [h]

end Valuation
end CuspPlaces

/-- Pin `ModularCurve.LevelN.exists_place_ord_neg_forall_smul_eq`
(`S_..._exists_place_ord_neg_forall_smul_eq.lean:874`), at the wrapper's statement. -/
theorem exists_place_ord_neg_forall_smul_eq (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K]
    (hst : ∀ F ∈ ModularCurve.LevelN.ring N,
      (fun τ : UpperHalfPlane => F (ModularGroup.T⁻¹ • τ)) ∈ ModularCurve.LevelN.ring N) :
    ∃ W : AlgebraicCurve.Place ℂ K,
      W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) < 0 ∧
      ∀ φ : K ≃ₐ[ℂ] K,
        (∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N),
            φ (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) =
              algebraMap (ModularCurve.LevelN.ring N) K
                ⟨fun τ : UpperHalfPlane => F (ModularGroup.T⁻¹ • τ), hst F hF⟩) →
        AlgebraicCurve.SemilinearAut.ofAlgAut φ • W = W :=
  ⟨CuspPlaces.cuspPlace N K, CuspPlaces.ord_jK_neg N K,
    fun φ hφ => CuspPlaces.smul_cuspPlace_eq N K hst φ hφ⟩

namespace AnalyticPlaces

variable (N : ℕ) [NeZero N]



private abbrev ext (F : ℍ → ℂ) : ℂ → ℂ := F ∘ ofComplex
private theorem ext_apply_coe (F : ℍ → ℂ) (τ : ℍ) : ext F τ = F τ := by
  simp [ext, ofComplex_apply]
private theorem analyticOnNhd_ext {F : ℍ → ℂ} (hF : F ∈ ring N) :
    AnalyticOnNhd ℂ (ext F) upperHalfPlaneSet := by
  intro z hz
  have hd : DifferentiableOn ℂ (ext F) upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_of_mem N hF)
  exact hd.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hz)
private theorem analyticAt_ext {F : ℍ → ℂ} (hF : F ∈ ring N) (τ₀ : ℍ) : AnalyticAt ℂ (ext F) τ₀ :=
  analyticOnNhd_ext N hF τ₀ τ₀.im_pos
private theorem analyticOrderAt_ne_top {F : ℍ → ℂ} (hF : F ∈ ring N) (hF0 : F ≠ 0) (τ₀ : ℍ) :
    analyticOrderAt (ext F) τ₀ ≠ ⊤ := by
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : ℍ, F τ₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (funext h)
  have h1 : analyticOrderAt (ext F) τ₁ ≠ ⊤ := by
    have : analyticOrderAt (ext F) τ₁ = 0 := by
      rw [analyticOrderAt_eq_zero]
      right
      rwa [ext_apply_coe]
    rw [this]
    exact ENat.zero_ne_top
  exact (analyticOnNhd_ext N hF).analyticOrderAt_ne_top_of_isPreconnected
    ((convex_halfSpace_im_gt 0).isPreconnected) τ₁.im_pos τ₀.im_pos h1
private def ordAt (τ₀ : ℍ) (F : ℍ → ℂ) : ℕ := (analyticOrderAt (ext F) τ₀).toNat
private theorem ordAt_cast {F : ℍ → ℂ} (hF : F ∈ ring N) (hF0 : F ≠ 0) (τ₀ : ℍ) :
    (ordAt τ₀ F : ℕ∞) = analyticOrderAt (ext F) τ₀ :=
  ENat.natCast_toNat (analyticOrderAt_ne_top N hF hF0 τ₀)
private theorem ordAt_mul {F G : ℍ → ℂ} (hF : F ∈ ring N) (hG : G ∈ ring N) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (τ₀ : ℍ) : ordAt τ₀ (F * G) = ordAt τ₀ F + ordAt τ₀ G := by
  have h := analyticOrderAt_mul (analyticAt_ext N hF τ₀) (analyticAt_ext N hG τ₀)
  unfold ordAt
  rw [show ext (F * G) = ext F * ext G from rfl, h]
  exact ENat.toNat_add (analyticOrderAt_ne_top N hF hF0 τ₀) (analyticOrderAt_ne_top N hG hG0 τ₀)
private theorem min_ordAt_le_ordAt_add {F G : ℍ → ℂ} (hF : F ∈ ring N) (hG : G ∈ ring N) (hF0 : F ≠ 0)
    (hG0 : G ≠ 0) (hFG : F + G ≠ 0) (τ₀ : ℍ) :
    min (ordAt τ₀ F) (ordAt τ₀ G) ≤ ordAt τ₀ (F + G) := by
  have h := le_analyticOrderAt_add (f := ext F) (g := ext G) (z₀ := (τ₀ : ℂ))
  rw [show ext F + ext G = ext (F + G) from rfl, ← ordAt_cast N hF hF0, ← ordAt_cast N hG hG0,
    ← ordAt_cast N ((ring N).add_mem hF hG) hFG] at h
  rcases le_total (ordAt τ₀ F) (ordAt τ₀ G) with hle | hle
  · rw [min_eq_left hle]
    rw [min_eq_left (by exact_mod_cast hle)] at h
    exact_mod_cast h
  · rw [min_eq_right hle]
    rw [min_eq_right (by exact_mod_cast hle)] at h
    exact_mod_cast h
private theorem ordAt_one (τ₀ : ℍ) : ordAt τ₀ (1 : ℍ → ℂ) = 0 := by
  unfold ordAt
  have : analyticOrderAt (ext (1 : ℍ → ℂ)) τ₀ = 0 := by
    rw [analyticOrderAt_eq_zero]
    right
    simp [ext]
  rw [this]
  rfl
open Classical in

private def ordFun (τ₀ : ℍ) (F : ring N) : WithZero (Multiplicative ℤ) :=
  if (F : ℍ → ℂ) = 0 then 0 else WithZero.exp (-(ordAt τ₀ (F : ℍ → ℂ) : ℤ))
set_option linter.unusedSectionVars false in
private theorem ordFun_of_ne_zero (τ₀ : ℍ) {F : ring N} (hF : (F : ℍ → ℂ) ≠ 0) :
    ordFun N τ₀ F = WithZero.exp (-(ordAt τ₀ (F : ℍ → ℂ) : ℤ)) := by
  simp [ordFun, hF]
set_option linter.unusedSectionVars false in
private theorem ordFun_zero' (τ₀ : ℍ) {F : ring N} (hF : (F : ℍ → ℂ) = 0) : ordFun N τ₀ F = 0 := by
  simp [ordFun, hF]
private def ordValuation (τ₀ : ℍ) : Valuation (ring N) (WithZero (Multiplicative ℤ)) where
  toFun := ordFun N τ₀
  map_zero' := ordFun_zero' N τ₀ rfl
  map_one' := by
    rw [ordFun_of_ne_zero N τ₀ (by simp)]
    simp [ordAt_one]
  map_mul' F G := by
    by_cases hF : (F : ℍ → ℂ) = 0
    · rw [ordFun_zero' N τ₀ hF, ordFun_zero' N τ₀ (by simp [hF]), zero_mul]
    by_cases hG : (G : ℍ → ℂ) = 0
    · rw [ordFun_zero' N τ₀ hG, ordFun_zero' N τ₀ (by simp [hG]), mul_zero]
    have hFG : ((F * G : ring N) : ℍ → ℂ) ≠ 0 := by
      intro h
      rcases eq_zero_or_eq_zero_of_mul_eq_zero N F.2 G.2 (by simpa using h) with h' | h'
      · exact hF h'
      · exact hG h'
    rw [ordFun_of_ne_zero N τ₀ hF, ordFun_of_ne_zero N τ₀ hG, ordFun_of_ne_zero N τ₀ hFG,
      ← WithZero.exp_add]
    congr 1
    rw [show ((F * G : ring N) : ℍ → ℂ) = (F : ℍ → ℂ) * (G : ℍ → ℂ) from rfl,
      ordAt_mul N F.2 G.2 hF hG]
    push_cast
    ring
  map_add_le_max' F G := by
    by_cases hFG : ((F + G : ring N) : ℍ → ℂ) = 0
    · rw [ordFun_zero' N τ₀ hFG]; exact zero_le
    by_cases hF : (F : ℍ → ℂ) = 0
    · have : F + G = G := by
        have hF' : F = 0 := Subtype.ext hF
        rw [hF', zero_add]
      rw [this, ordFun_zero' N τ₀ hF]
      exact le_max_right _ _
    by_cases hG : (G : ℍ → ℂ) = 0
    · have : F + G = F := by
        have hG' : G = 0 := Subtype.ext hG
        rw [hG', add_zero]
      rw [this, ordFun_zero' N τ₀ hG]
      exact le_max_left _ _
    rw [ordFun_of_ne_zero N τ₀ hF, ordFun_of_ne_zero N τ₀ hG, ordFun_of_ne_zero N τ₀ hFG]
    have hmin := min_ordAt_le_ordAt_add N F.2 G.2 hF hG (by simpa using hFG) τ₀
    rw [show ((F + G : ring N) : ℍ → ℂ) = (F : ℍ → ℂ) + (G : ℍ → ℂ) from rfl]

    rcases le_total (ordAt τ₀ (F : ℍ → ℂ)) (ordAt τ₀ (G : ℍ → ℂ)) with h | h
    · rw [min_eq_left h] at hmin
      refine le_trans ?_ (le_max_left _ _)
      rw [WithZero.exp_le_exp]
      omega
    · rw [min_eq_right h] at hmin
      refine le_trans ?_ (le_max_right _ _)
      rw [WithZero.exp_le_exp]
      omega
@[scoped simp]
private theorem ordValuation_apply (τ₀ : ℍ) (F : ring N) : ordValuation N τ₀ F = ordFun N τ₀ F := rfl
private theorem ordValuation_ne_zero (τ₀ : ℍ) {F : ring N} (hF : F ≠ 0) : ordValuation N τ₀ F ≠ 0 := by
  have hF' : (F : ℍ → ℂ) ≠ 0 := fun h => hF (Subtype.ext h)
  rw [ordValuation_apply, ordFun_of_ne_zero N τ₀ hF']
  exact WithZero.exp_ne_zero
private theorem nonZeroDivisors_le_supp_primeCompl (τ₀ : ℍ) :
    nonZeroDivisors (ring N) ≤ (ordValuation N τ₀).supp.primeCompl := by
  intro s hs
  change s ∉ (ordValuation N τ₀).supp
  rw [Valuation.mem_supp_iff]
  apply ordValuation_ne_zero
  intro h
  rw [h] at hs
  exact zero_notMem_nonZeroDivisors hs

section FractionField

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring N) K] [IsScalarTower ℂ (ring N) K]
  [IsFractionRing (ring N) K]
private def ordValuationK (τ₀ : ℍ) : Valuation K (WithZero (Multiplicative ℤ)) :=
  (ordValuation N τ₀).extendToLocalization (S := nonZeroDivisors (ring N))
    (nonZeroDivisors_le_supp_primeCompl N τ₀) K
set_option linter.unusedSectionVars false in
private theorem ordValuationK_algebraMap (τ₀ : ℍ) (F : ring N) :
    ordValuationK N K τ₀ (algebraMap (ring N) K F) = ordFun N τ₀ F :=
  Valuation.extendToLocalization_apply_map_apply _ _ K F
private def jSub (τ₀ : ℍ) : ring N := jGen N - algebraMap ℂ (ring N) (jAnalytic τ₀)
set_option linter.unusedSectionVars false in
private theorem coe_jSub (τ₀ : ℍ) : ((jSub N τ₀ : ring N) : ℍ → ℂ) = fun τ => jAnalytic τ - jAnalytic τ₀ := by
  funext τ
  simp [jSub, jGen, Algebra.algebraMap_eq_smul_one]
private theorem jSub_ne_zero (τ₀ : ℍ) : (jSub N τ₀ : ring N) ≠ 0 := by
  intro h
  have h' := congrArg (fun F : ring N => (F : ℍ → ℂ)) h
  simp only [coe_jSub, ZeroMemClass.coe_zero] at h'

  have hpkg := WLight.levelN_structure_package N PeriodPair.ofTau (fun _ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  have htr := hpkg.2.2.2.1 (Polynomial.X - Polynomial.C (jAnalytic τ₀)) (fun τ => by
    have := congrFun h' τ
    simp only [Pi.zero_apply] at this
    simp [this])
  have := congrArg (Polynomial.eval (jAnalytic τ₀ + 1)) htr
  simp at this
private theorem ordAt_jSub_pos (τ₀ : ℍ) : 0 < ordAt τ₀ ((jSub N τ₀ : ring N) : ℍ → ℂ) := by
  have hne : ((jSub N τ₀ : ring N) : ℍ → ℂ) ≠ 0 := fun h => jSub_ne_zero N τ₀ (Subtype.ext h)
  have hcast := ordAt_cast N (jSub N τ₀).2 hne τ₀
  by_contra h0
  push Not at h0
  have h0' : ordAt τ₀ ((jSub N τ₀ : ring N) : ℍ → ℂ) = 0 := Nat.le_zero.mp h0
  rw [h0', Nat.cast_zero, eq_comm, analyticOrderAt_eq_zero] at hcast
  rcases hcast with h | h
  · exact h (analyticAt_ext N (jSub N τ₀).2 τ₀)
  · apply h
    rw [ext_apply_coe, coe_jSub]
    simp
private theorem ordValuationK_jSub_lt_one (τ₀ : ℍ) :
    ordValuationK N K τ₀ (algebraMap (ring N) K (jSub N τ₀)) < 1 := by
  rw [ordValuationK_algebraMap, ordFun_of_ne_zero N τ₀ (fun h => jSub_ne_zero N τ₀ (Subtype.ext h)),
    ← WithZero.exp_zero, WithZero.exp_lt_exp]
  have := ordAt_jSub_pos N τ₀
  omega
private theorem isNontrivial_ordValuationK (τ₀ : ℍ) : (ordValuationK N K τ₀).IsNontrivial := by
  refine ⟨algebraMap (ring N) K (jSub N τ₀), ?_, ?_⟩
  · rw [ordValuationK_algebraMap]
    exact ordValuation_ne_zero N τ₀ (jSub_ne_zero N τ₀)
  · exact (ordValuationK_jSub_lt_one N K τ₀).ne
private theorem nontrivial_valueGroup (τ₀ : ℍ) :
    Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass <| ordValuationK N K τ₀)) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  have hne : ordValuationK N K τ₀ (algebraMap (ring N) K (jSub N τ₀)) ≠ 0 := by
    rw [ordValuationK_algebraMap]
    exact ordValuation_ne_zero N τ₀ (jSub_ne_zero N τ₀)
  refine ⟨Units.mk0 _ hne, ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨_, rfl⟩
  · intro h
    have h' := congrArg (fun u : (WithZero (Multiplicative ℤ))ˣ => (u : WithZero (Multiplicative ℤ))) h
    simp only [Units.val_mk0, Units.val_one] at h'
    exact (ordValuationK_jSub_lt_one N K τ₀).ne h'
private def analyticPlace (τ₀ : ℍ) : AlgebraicCurve.Place ℂ K :=
  haveI := nontrivial_valueGroup N K τ₀
  { toValuationSubring := (ordValuationK N K τ₀).valuationSubring
    algebraMap_mem' := fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      by_cases ha : a = 0
      · simp [ha]
      · rw [IsScalarTower.algebraMap_apply ℂ (ring N) K, ordValuationK_algebraMap,
          ordFun_of_ne_zero N τ₀ (by
            intro h
            have := congrFun h UpperHalfPlane.I
            simp [Algebra.algebraMap_eq_smul_one, ha] at this)]
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        have : ordAt τ₀ ((algebraMap ℂ (ring N) a : ring N) : ℍ → ℂ) = 0 := by
          unfold ordAt
          have : analyticOrderAt (ext ((algebraMap ℂ (ring N) a : ring N) : ℍ → ℂ)) τ₀ = 0 := by
            rw [analyticOrderAt_eq_zero]
            right
            simp [ext, Algebra.algebraMap_eq_smul_one, ha]
          rw [this]; rfl
        omega
    ne_top' := by
      rw [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
      exact isNontrivial_ordValuationK N K τ₀
    isPrincipalIdealRing' :=
      (Valuation.valuationSubring_isDiscreteValuationRing
        (ordValuationK N K τ₀)).toIsPrincipalIdealRing }
@[scoped simp]
private theorem analyticPlace_toValuationSubring (τ₀ : ℍ) :
    (analyticPlace N K τ₀).toValuationSubring = (ordValuationK N K τ₀).valuationSubring := rfl
private theorem mem_analyticPlace_iff (τ₀ : ℍ) (x : K) :
    x ∈ (analyticPlace N K τ₀).toValuationSubring ↔ ordValuationK N K τ₀ x ≤ 1 := by
  rw [analyticPlace_toValuationSubring, Valuation.mem_valuationSubring_iff]
private theorem inv_jSub_notMem (τ₀ : ℍ) :
    (algebraMap (ring N) K (jSub N τ₀))⁻¹ ∉ (analyticPlace N K τ₀).toValuationSubring := by
  rw [mem_analyticPlace_iff, map_inv₀, not_le, one_lt_inv₀]
  · exact ordValuationK_jSub_lt_one N K τ₀
  · rw [ordValuationK_algebraMap]
    exact (zero_le.lt_of_ne (ordValuation_ne_zero N τ₀ (jSub_ne_zero N τ₀)).symm)
private theorem jSub_mem_nonunits (τ₀ : ℍ) :
    algebraMap (ring N) K (jSub N τ₀) ∈ (analyticPlace N K τ₀).toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  exact Or.inr (inv_jSub_notMem N K τ₀)
private theorem algebraMap_mem_analyticPlace (τ₀ : ℍ) (F : ring N) :
    algebraMap (ring N) K F ∈ (analyticPlace N K τ₀).toValuationSubring := by
  rw [mem_analyticPlace_iff, ordValuationK_algebraMap]
  by_cases hF : (F : ℍ → ℂ) = 0
  · rw [ordFun_zero' N τ₀ hF]; exact zero_le
  · rw [ordFun_of_ne_zero N τ₀ hF, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

end FractionField
omit [NeZero N] in

private def moeb (δ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (((δ 0 0 : ℤ) : ℂ) * z + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * z + ((δ 1 1 : ℤ) : ℂ))
omit [NeZero N] in
private theorem coe_smul_eq_moeb (δ : SL(2, ℤ)) (τ : ℍ) : ((δ • τ : ℍ) : ℂ) = moeb δ τ := by
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp [moeb]
omit [NeZero N] in
private theorem moeb_denom_ne_zero (δ : SL(2, ℤ)) (τ : ℍ) :
    ((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.zero_im] at him

  have hc : ((δ 1 0 : ℤ) : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact h1
    · exact absurd h1 τ.im_pos.ne'
  have hc' : (δ 1 0 : ℤ) = 0 := by exact_mod_cast hc
  have hre := congrArg Complex.re h
  simp only [Complex.intCast_re, zero_mul, Complex.zero_re, hc', Int.cast_zero, zero_add] at hre
  have hd' : (δ 1 1 : ℤ) = 0 := by exact_mod_cast hre
  have hdet := δ.2
  rw [Matrix.det_fin_two, hc', hd'] at hdet
  simp at hdet
omit [NeZero N] in
private theorem analyticAt_moeb (δ : SL(2, ℤ)) (τ : ℍ) : AnalyticAt ℂ (moeb δ) τ := by
  unfold moeb
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const) (moeb_denom_ne_zero δ τ)
omit [NeZero N] in
private theorem hasDerivAt_moeb (δ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (moeb δ) ((((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) ^ 2)⁻¹ τ := by
  have hden := moeb_denom_ne_zero δ τ
  have hnum : HasDerivAt (fun z : ℂ => ((δ 0 0 : ℤ) : ℂ) * z + ((δ 0 1 : ℤ) : ℂ))
      ((δ 0 0 : ℤ) : ℂ) (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((δ 0 0 : ℤ) : ℂ)).add_const ((δ 0 1 : ℤ) : ℂ)
  have hden' : HasDerivAt (fun z : ℂ => ((δ 1 0 : ℤ) : ℂ) * z + ((δ 1 1 : ℤ) : ℂ))
      ((δ 1 0 : ℤ) : ℂ) (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((δ 1 0 : ℤ) : ℂ)).add_const ((δ 1 1 : ℤ) : ℂ)
  have h := hnum.div hden' hden
  have hdet : ((δ 0 0 : ℤ) : ℂ) * ((δ 1 1 : ℤ) : ℂ) - ((δ 0 1 : ℤ) : ℂ) * ((δ 1 0 : ℤ) : ℂ) = 1 := by
    have := δ.2
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  convert h using 1 <;> try rfl
  rw [inv_eq_one_div]
  congr 1
  linear_combination -hdet
omit [NeZero N] in
private theorem deriv_moeb_ne_zero (δ : SL(2, ℤ)) (τ : ℍ) : deriv (moeb δ) τ ≠ 0 := by
  rw [(hasDerivAt_moeb δ τ).deriv]
  exact inv_ne_zero (pow_ne_zero _ (moeb_denom_ne_zero δ τ))
omit [NeZero N] in

private theorem ext_comp_smul_eventuallyEq (δ : SL(2, ℤ)) (F : ℍ → ℂ) (τ₀ : ℍ) :
    ext (fun τ : ℍ => F (δ • τ)) =ᶠ[𝓝 (τ₀ : ℂ)] (ext F ∘ moeb δ) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ₀.im_pos] with z hz
  have hz' : 0 < z.im := hz
  simp only [ext, Function.comp_apply, ofComplex_apply_of_im_pos hz']
  have hmem : 0 < (moeb δ z).im := by
    have := (δ • (⟨z, hz'⟩ : ℍ)).im_pos
    rwa [show ((δ • (⟨z, hz'⟩ : ℍ) : ℍ).im) = (moeb δ z).im by
      rw [← UpperHalfPlane.coe_im, coe_smul_eq_moeb]] at this
  rw [ofComplex_apply_of_im_pos hmem]
  congr 1
  ext1
  simpa using coe_smul_eq_moeb δ ⟨z, hz'⟩
omit [NeZero N] in

private theorem analyticOrderAt_ext_comp_smul (δ : SL(2, ℤ)) (F : ℍ → ℂ) (τ₀ : ℍ) :
    analyticOrderAt (ext (fun τ : ℍ => F (δ • τ))) τ₀ = analyticOrderAt (ext F) ((δ • τ₀ : ℍ) : ℂ) := by
  rw [analyticOrderAt_congr (ext_comp_smul_eventuallyEq δ F τ₀),
    analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_moeb δ τ₀) (deriv_moeb_ne_zero δ τ₀),
    coe_smul_eq_moeb]
omit [NeZero N] in
private theorem ordAt_comp_smul (δ : SL(2, ℤ)) (F : ℍ → ℂ) (τ₀ : ℍ) :
    ordAt τ₀ (fun τ : ℍ => F (δ • τ)) = ordAt (δ • τ₀) F := by
  unfold ordAt
  rw [analyticOrderAt_ext_comp_smul]
omit [NeZero N] in
private theorem comp_smul_eq_zero_iff (δ : SL(2, ℤ)) (F : ℍ → ℂ) :
    (fun τ : ℍ => F (δ • τ)) = 0 ↔ F = 0 := by
  constructor
  · intro h
    funext τ
    have := congrFun h (δ⁻¹ • τ)
    simpa using this
  · rintro rfl
    rfl
private theorem ordFun_comp_smul (τ₀ : ℍ) (δ : SL(2, ℤ)) (hδ : δ • τ₀ = τ₀) (F : ring N)
    (hFδ : (fun τ : ℍ => (F : ℍ → ℂ) (δ • τ)) ∈ ring N) :
    ordFun N τ₀ ⟨fun τ : ℍ => (F : ℍ → ℂ) (δ • τ), hFδ⟩ = ordFun N τ₀ F := by
  by_cases hF : (F : ℍ → ℂ) = 0
  · rw [ordFun_zero' N τ₀ hF, ordFun_zero' N τ₀ (by
      change (fun τ : ℍ => (F : ℍ → ℂ) (δ • τ)) = 0
      rw [comp_smul_eq_zero_iff]; exact hF)]
  · have hF' : (fun τ : ℍ => (F : ℍ → ℂ) (δ • τ)) ≠ 0 := by
      rw [Ne, comp_smul_eq_zero_iff]; exact hF
    rw [ordFun_of_ne_zero N τ₀ hF, ordFun_of_ne_zero N τ₀ (F := ⟨_, hFδ⟩) hF']
    congr 2
    change ((ordAt τ₀ (fun τ : ℍ => (F : ℍ → ℂ) (δ • τ)) : ℕ) : ℤ) = _
    rw [ordAt_comp_smul, hδ]

section Stabiliser

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring N) K] [IsScalarTower ℂ (ring N) K]
  [IsFractionRing (ring N) K]
private theorem ordValuationK_algEquiv (τ₀ : ℍ) (δ : SL(2, ℤ)) (hδ : δ • τ₀ = τ₀)
    (hst : ∀ F ∈ ring N, (fun τ : ℍ => F (δ • τ)) ∈ ring N) (φ : K ≃ₐ[ℂ] K)
    (hφ : ∀ (F : ℍ → ℂ) (hF : F ∈ ring N),
      φ (algebraMap (ring N) K ⟨F, hF⟩) = algebraMap (ring N) K ⟨fun τ : ℍ => F (δ • τ), hst F hF⟩)
    (x : K) : ordValuationK N K τ₀ (φ x) = ordValuationK N K τ₀ x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ring N) x
  rw [map_div₀, map_div₀, map_div₀]
  have ha := hφ (a : ℍ → ℂ) a.2
  have hb' := hφ (b : ℍ → ℂ) b.2
  simp only [Subtype.coe_eta] at ha hb'
  rw [ha, hb', ordValuationK_algebraMap, ordValuationK_algebraMap, ordValuationK_algebraMap,
    ordValuationK_algebraMap, ordFun_comp_smul N τ₀ δ hδ a, ordFun_comp_smul N τ₀ δ hδ b]
private theorem smul_analyticPlace_eq (τ₀ : ℍ) (δ : SL(2, ℤ)) (hδ : δ • τ₀ = τ₀)
    (hst : ∀ F ∈ ring N, (fun τ : ℍ => F (δ • τ)) ∈ ring N) (φ : K ≃ₐ[ℂ] K)
    (hφ : ∀ (F : ℍ → ℂ) (hF : F ∈ ring N),
      φ (algebraMap (ring N) K ⟨F, hF⟩) = algebraMap (ring N) K ⟨fun τ : ℍ => F (δ • τ), hst F hF⟩) :
    AlgebraicCurve.SemilinearAut.ofAlgAut φ • analyticPlace N K τ₀ = analyticPlace N K τ₀ := by
  apply AlgebraicCurve.Place.ext
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    AlgebraicCurve.SemilinearAut.ofAlgAut_smul, mem_analyticPlace_iff, mem_analyticPlace_iff]
  have h := ordValuationK_algEquiv N K τ₀ δ hδ hst φ hφ (φ⁻¹ x)
  rw [show φ (φ⁻¹ x) = x from φ.apply_symm_apply x] at h
  rw [h]
private theorem ord_jSub_pos (τ₀ : ℍ) :
    0 < (analyticPlace N K τ₀).ord (algebraMap (ring N) K (jGen N) - algebraMap ℂ K (jAnalytic τ₀)) := by
  have hmem := jSub_mem_nonunits N K τ₀
  have heq : algebraMap (ring N) K (jSub N τ₀) =
      algebraMap (ring N) K (jGen N) - algebraMap ℂ K (jAnalytic τ₀) := by
    rw [jSub, map_sub, ← IsScalarTower.algebraMap_apply]
  rw [← heq]
  set W := analyticPlace N K τ₀
  set y := algebraMap (ring N) K (jSub N τ₀) with hy
  have hy0 : y ≠ 0 := by
    rw [hy]
    intro h
    exact jSub_ne_zero N τ₀ ((IsFractionRing.injective (ring N) K)
      (by rw [h, map_zero]))
  obtain ⟨hyW, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hmem

  have hval : W.adicValuation y < 1 := by
    rw [W.adicValuation_coe ⟨y, hyW⟩,
      IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hmax
  have hne : W.adicValuation y ≠ 0 := W.adicValuation_ne_zero hy0
  rw [AlgebraicCurve.Place.ord, neg_pos, WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]
  exact hval

end Stabiliser
section FractionFieldExtra

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring N) K] [IsScalarTower ℂ (ring N) K]
  [IsFractionRing (ring N) K]

private theorem exists_pos_neg_log_eq_mul_ord (τ₀ : ℍ) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : K, x ≠ 0 →
      -(WithZero.log (ordValuationK N K τ₀ x)) = (e : ℤ) * (analyticPlace N K τ₀).ord x := by
  set W := analyticPlace N K τ₀ with hW
  set v := ordValuationK N K τ₀ with hv
  have hmem : ∀ x : K, x ∈ W.toValuationSubring ↔ v x ≤ 1 := fun x => mem_analyticPlace_iff N K τ₀ x
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  have hπ0 : (π : K) ≠ 0 := by
    intro h; exact hπ.ne_zero (Subtype.ext h)
  have hvπ0 : v (π : K) ≠ 0 := (Valuation.ne_zero_iff v).mpr hπ0
  have hvπle : v (π : K) ≤ 1 := (hmem _).mp π.2
  have hvπlt : v (π : K) < 1 := by
    rcases hvπle.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hπ.not_isUnit
      have hinv : (π : K)⁻¹ ∈ W.toValuationSubring := by
        rw [hmem, map_inv₀, h, inv_one]
      refine ⟨⟨π, ⟨(π : K)⁻¹, hinv⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
      · change (π : K) * (π : K)⁻¹ = 1; exact mul_inv_cancel₀ hπ0
      · change (π : K)⁻¹ * (π : K) = 1; exact inv_mul_cancel₀ hπ0

  have hlogπ : WithZero.log (v (π : K)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hvπ0, WithZero.exp_zero]; exact hvπlt
  refine ⟨(-(WithZero.log (v (π : K)))).toNat, by omega, fun x hx0 => ?_⟩
  have he : (((-(WithZero.log (v (π : K)))).toNat : ℕ) : ℤ) = -(WithZero.log (v (π : K))) :=
    Int.toNat_of_nonneg (by omega)
  rw [he]
  obtain ⟨u, hux⟩ := W.exists_unit_mul_zpow hx0 hπ

  have hu0 : ((u : W.toValuationSubring) : K) ≠ 0 := by
    simp [ne_eq, ZeroMemClass.coe_eq_zero]
  have hvu : v ((u : W.toValuationSubring) : K) = 1 := by
    apply le_antisymm ((hmem _).mp (u : W.toValuationSubring).2)
    have hinv : v (((u⁻¹ : W.toValuationSubringˣ) : W.toValuationSubring) : K) ≤ 1 :=
      (hmem _).mp ((u⁻¹ : W.toValuationSubringˣ) : W.toValuationSubring).2
    have hprod : ((u : W.toValuationSubring) : K) *
        (((u⁻¹ : W.toValuationSubringˣ) : W.toValuationSubring) : K) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    have hvinv : v (((u⁻¹ : W.toValuationSubringˣ) : W.toValuationSubring) : K) =
        (v ((u : W.toValuationSubring) : K))⁻¹ := by
      have := congrArg v hprod
      rw [map_mul, map_one] at this
      exact eq_inv_of_mul_eq_one_right this
    rw [hvinv] at hinv
    have hpos : 0 < v ((u : W.toValuationSubring) : K) := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hu0)
    exact (inv_le_one₀ hpos).mp hinv

  have hvx : v x = v ((u : W.toValuationSubring) : K) * v (π : K) ^ W.ord x := by
    conv_lhs => rw [hux]
    rw [map_mul, map_zpow₀]
  rw [hvx, hvu, one_mul, WithZero.log_zpow, smul_eq_mul]
  ring
private theorem exists_place_ordAt_eq_mul_ord (τ₀ : ℍ) :
    ∃ (W : AlgebraicCurve.Place ℂ K) (e : ℕ), 0 < e ∧
      ∀ (F : ℍ → ℂ) (hF : F ∈ ring N), F ≠ 0 →
        analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ) ≠ ⊤ ∧
        ((analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ)).toNat : ℤ) =
          e * W.ord (algebraMap (ring N) K ⟨F, hF⟩) := by
  obtain ⟨e, he, hlog⟩ := exists_pos_neg_log_eq_mul_ord N K τ₀
  refine ⟨analyticPlace N K τ₀, e, he, fun F hF hF0 => ⟨analyticOrderAt_ne_top N hF hF0 τ₀, ?_⟩⟩
  have hne : (algebraMap (ring N) K ⟨F, hF⟩) ≠ 0 := by
    intro h
    have : (⟨F, hF⟩ : ring N) = 0 := (IsFractionRing.injective (ring N) K) (by rw [h, map_zero])
    exact hF0 (congrArg Subtype.val this)
  have h := hlog _ hne
  rw [ordValuationK_algebraMap, ordFun_of_ne_zero N τ₀ (by exact hF0), WithZero.log_exp, neg_neg] at h
  rw [← h]
  rfl
end FractionFieldExtra

end AnalyticPlaces

/-- Pin `ModularCurve.LevelN.exists_place_ord_sub_pos_forall_smul_eq`
(`S_..._exists_place_ord_sub_pos_forall_smul_eq.lean:497`), at the wrapper's statement. -/
theorem exists_place_ord_sub_pos_forall_smul_eq (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] (τ₀ : UpperHalfPlane) :
    ∃ W : AlgebraicCurve.Place ℂ K,
      0 < W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) -
          algebraMap ℂ K (ModularCurve.LevelN.jAnalytic τ₀)) ∧
      ∀ (γ : SL(2, ℤ)) (_ : γ • τ₀ = τ₀)
        (hst : ∀ F ∈ ModularCurve.LevelN.ring N,
          (fun τ : UpperHalfPlane => F (γ⁻¹ • τ)) ∈ ModularCurve.LevelN.ring N)
        (φ : K ≃ₐ[ℂ] K),
        (∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N),
            φ (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) =
              algebraMap (ModularCurve.LevelN.ring N) K
                ⟨fun τ : UpperHalfPlane => F (γ⁻¹ • τ), hst F hF⟩) →
        AlgebraicCurve.SemilinearAut.ofAlgAut φ • W = W := by
  refine ⟨AnalyticPlaces.analyticPlace N K τ₀, AnalyticPlaces.ord_jSub_pos N K τ₀, ?_⟩
  intro γ hγ hst φ hφ
  have hδ : γ⁻¹ • τ₀ = τ₀ := by
    conv_lhs => rw [← hγ]
    rw [inv_smul_smul]
  exact AnalyticPlaces.smul_analyticPlace_eq N K τ₀ γ⁻¹ hδ hst φ hφ

/-- Pin `ModularCurve.LevelN.exists_place_analyticOrderAt_eq_mul_ord`
(`S_..._exists_place_analyticOrderAt_eq_mul_ord.lean:396`), at the wrapper's
statement. -/
theorem exists_place_analyticOrderAt_eq_mul_ord (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] (τ₀ : UpperHalfPlane) :
    ∃ (W : AlgebraicCurve.Place ℂ K) (e : ℕ), 0 < e ∧
      ∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N), F ≠ 0 →
        analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ) ≠ ⊤ ∧
        ((analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ)).toNat : ℤ) =
          e * W.ord (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) :=
  AnalyticPlaces.exists_place_ordAt_eq_mul_ord N K τ₀

namespace CuspExpChi

section Chart

private theorem exists_chart {N : ℕ} [NeZero N] {F : ℍ → ℂ} (hF : Good N F)
    (hF0 : qExpansion N F ≠ 0) :
    ∃ u : ℂ → ℂ, ContinuousAt u 0 ∧
      u 0 = (qExpansion N F).coeff ((qExpansion N F).order.toNat) ∧ u 0 ≠ 0 ∧
      ∀ τ : ℍ, F τ = Periodic.qParam N τ ^ ((qExpansion N F).order.toNat) *
        u (Periodic.qParam N τ) := by
  have pF := hF.periodic
  have dF := hF.mdiff
  have bF := hF.bdd
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set P := qExpansion N F with hP

  have hsummN : Summable fun n : ℕ => ‖P.coeff n‖ * (1 / 2 : ℝ) ^ n := by
    have : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
    have h1 : HasSum (fun n : ℕ => P.coeff n • ((1 / 2 : ℝ) : ℂ) ^ n)
        (cuspFunction N F ((1 / 2 : ℝ) : ℂ)) :=
      hasSum_qExpansion_of_norm_lt hN pF dF bF (by
        rw [Complex.norm_real]
        norm_num)
    refine (summable_norm_iff.mpr h1.summable).congr fun n => ?_
    rw [norm_smul, norm_pow, Complex.norm_real]
    norm_num
  have hsummShift : Summable fun j : ℕ => ‖P.coeff ((P.order.toNat) + j)‖ * (1 / 2 : ℝ) ^ j := by
    have h1 : Summable fun j : ℕ =>
        ‖P.coeff (j + P.order.toNat)‖ * (1 / 2 : ℝ) ^ (j + P.order.toNat) :=
      (summable_nat_add_iff (f := fun n : ℕ => ‖P.coeff n‖ * (1 / 2 : ℝ) ^ n)
        (P.order.toNat)).mpr hsummN
    have h2 := h1.mul_right ((2 : ℝ) ^ P.order.toNat)
    refine h2.congr fun j => ?_
    have hpow : ((1 : ℝ) / 2) ^ P.order.toNat * (2 : ℝ) ^ P.order.toNat = 1 := by
      rw [← mul_pow]
      norm_num
    rw [pow_add, add_comm j P.order.toNat]
    linear_combination ‖P.coeff (P.order.toNat + j)‖ * ((1 : ℝ) / 2) ^ j * hpow

  set u : ℂ → ℂ := fun z => ∑' j : ℕ, P.coeff (P.order.toNat + j) * z ^ j with hu
  have hucont : ContinuousOn u (Metric.ball (0 : ℂ) (1 / 2)) := by
    refine continuousOn_tsum (fun j => ?_) hsummShift fun j z hz => ?_
    · exact (continuous_const.mul (continuous_pow j)).continuousOn
    · rw [norm_mul, norm_pow]
      gcongr
      exact le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  have huCA : ContinuousAt u 0 :=
    hucont.continuousAt (Metric.ball_mem_nhds _ (by norm_num))
  have hu0 : u 0 = P.coeff (P.order.toNat) := by
    have hval : u 0 = ∑' j : ℕ, P.coeff (P.order.toNat + j) * (0 : ℂ) ^ j := rfl
    rw [hval, tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
    simp
  have hum : P.coeff (P.order.toNat) ≠ 0 := PowerSeries.coeff_order hF0
  refine ⟨u, huCA, hu0, by rw [hu0]; exact hum, fun τ => ?_⟩
  set z := Periodic.qParam (N : ℝ) (τ : ℂ) with hz
  have hz1 : ‖z‖ < 1 := UpperHalfPlane.norm_qParam_lt_one N τ
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hsum : HasSum (fun n : ℕ => P.coeff n • z ^ n) (F τ) :=
    hasSum_qExpansion hN pF dF bF τ
  have hshift : HasSum (fun j : ℕ => P.coeff (j + P.order.toNat) • z ^ (j + P.order.toNat))
      (F τ) := by
    have hvan : ∑ i ∈ Finset.range (P.order.toNat), P.coeff i • z ^ i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [PowerSeries.coeff_of_lt_order_toNat i (Finset.mem_range.mp hi), zero_smul]
    have h4 := (hasSum_nat_add_iff' (P.order.toNat)).mpr hsum
    rwa [hvan, sub_zero] at h4
  have husum : HasSum (fun j : ℕ => P.coeff (P.order.toNat + j) * z ^ j)
      (F τ / z ^ P.order.toNat) := by
    have h2 : HasSum (fun j : ℕ => (P.coeff (P.order.toNat + j) * z ^ j) * z ^ P.order.toNat)
        (F τ) := by
      have heq : (fun j : ℕ => (P.coeff (P.order.toNat + j) * z ^ j) * z ^ P.order.toNat) =
          fun j : ℕ => P.coeff (j + P.order.toNat) • z ^ (j + P.order.toNat) := by
        funext j
        rw [smul_eq_mul, pow_add, add_comm j (P.order.toNat)]
        ring
      rw [heq]
      exact hshift
    have h3 := h2.div_const (z ^ P.order.toNat)
    have heq2 : (fun j : ℕ => P.coeff (P.order.toNat + j) * z ^ j * z ^ P.order.toNat /
        z ^ P.order.toNat) = fun j : ℕ => P.coeff (P.order.toNat + j) * z ^ j := by
      funext j
      rw [mul_div_assoc, div_self (pow_ne_zero _ hz0), mul_one]
    rwa [heq2] at h3
  have huz : u z = F τ / z ^ P.order.toNat := husum.tsum_eq
  rw [huz, mul_div_cancel₀ _ (pow_ne_zero _ hz0)]
private theorem eventually_ne_zero_atImInfty {N : ℕ} [NeZero N] {F : ℍ → ℂ} (hF : Good N F)
    (hF0 : qExpansion N F ≠ 0) : ∀ᶠ τ : ℍ in atImInfty, F τ ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨u, hu, -, hu0, hid⟩ := exists_chart hF hF0
  have h1 : Tendsto (fun τ : ℍ => u (Periodic.qParam N τ)) atImInfty (𝓝 (u 0)) :=
    hu.tendsto.comp (qParam_tendsto_atImInfty hN)
  filter_upwards [h1.eventually_ne hu0] with τ hτ
  rw [hid τ]
  exact mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _)) hτ
private theorem order_eq_of_tendsto_div {N : ℕ} [NeZero N] {G H : ℍ → ℂ} (hG : Good N G) (hH : Good N H)
    (hG0 : qExpansion N G ≠ 0) (hH0 : qExpansion N H ≠ 0) {L : ℂ} (hL : L ≠ 0)
    (hlim : Tendsto (fun τ : ℍ => G τ / H τ) atImInfty (𝓝 L)) :
    (qExpansion N G).order = (qExpansion N H).order := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨uG, cG, -, nG, idG⟩ := exists_chart hG hG0
  obtain ⟨uH, cH, -, nH, idH⟩ := exists_chart hH hH0
  set a := (qExpansion (N : ℝ) G).order.toNat with ha
  set b := (qExpansion (N : ℝ) H).order.toNat with hb
  have hq : Tendsto (fun τ : ℍ => Periodic.qParam (N : ℝ) (τ : ℂ)) atImInfty (𝓝 0) :=
    qParam_tendsto_atImInfty hN
  have hTG : Tendsto (fun τ : ℍ => uG (Periodic.qParam N τ)) atImInfty (𝓝 (uG 0)) :=
    cG.tendsto.comp hq
  have hTH : Tendsto (fun τ : ℍ => uH (Periodic.qParam N τ)) atImInfty (𝓝 (uH 0)) :=
    cH.tendsto.comp hq
  have hquot : ∀ τ : ℍ, G τ / H τ =
      Periodic.qParam (N : ℝ) (τ : ℂ) ^ a / Periodic.qParam (N : ℝ) (τ : ℂ) ^ b *
        (uG (Periodic.qParam N τ) / uH (Periodic.qParam N τ)) := by
    intro τ
    rw [idG τ, idH τ, mul_div_mul_comm]

  have hab : a = b := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    ·
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
      have hinv : Tendsto (fun τ : ℍ => H τ / G τ) atImInfty (𝓝 L⁻¹) := by
        have := hlim.inv₀ hL
        refine this.congr fun τ => ?_
        exact inv_div _ _
      have hzero : Tendsto (fun τ : ℍ => H τ / G τ) atImInfty (𝓝 0) := by
        have hform : ∀ τ : ℍ, H τ / G τ =
            Periodic.qParam (N : ℝ) (τ : ℂ) ^ (d + 1) *
              (uH (Periodic.qParam N τ) / uG (Periodic.qParam N τ)) := by
          intro τ
          have hz0 : Periodic.qParam (N : ℝ) (τ : ℂ) ≠ 0 := Complex.exp_ne_zero _
          rw [idG τ, idH τ, hd, mul_div_mul_comm, show a + d + 1 = (d + 1) + a by ring, pow_add,
            mul_div_cancel_right₀ _ (pow_ne_zero _ hz0)]
        have h1 : Tendsto (fun τ : ℍ => Periodic.qParam (N : ℝ) (τ : ℂ) ^ (d + 1)) atImInfty (𝓝 0) := by
          have := hq.pow (d + 1)
          rwa [zero_pow (Nat.succ_ne_zero d)] at this
        have h2 := h1.mul (hTH.div hTG nG)
        rw [zero_mul] at h2
        exact h2.congr fun τ => (hform τ).symm
      have := tendsto_nhds_unique hinv hzero
      exact (inv_ne_zero hL) this
    ·
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hgt
      have hzero : Tendsto (fun τ : ℍ => G τ / H τ) atImInfty (𝓝 0) := by
        have hform : ∀ τ : ℍ, G τ / H τ =
            Periodic.qParam (N : ℝ) (τ : ℂ) ^ (d + 1) *
              (uG (Periodic.qParam N τ) / uH (Periodic.qParam N τ)) := by
          intro τ
          have hz0 : Periodic.qParam (N : ℝ) (τ : ℂ) ≠ 0 := Complex.exp_ne_zero _
          rw [idG τ, idH τ, hd, mul_div_mul_comm, show b + d + 1 = (d + 1) + b by ring, pow_add,
            mul_div_cancel_right₀ _ (pow_ne_zero _ hz0)]
        have h1 : Tendsto (fun τ : ℍ => Periodic.qParam (N : ℝ) (τ : ℂ) ^ (d + 1)) atImInfty (𝓝 0) := by
          have := hq.pow (d + 1)
          rwa [zero_pow (Nat.succ_ne_zero d)] at this
        have h2 := h1.mul (hTG.div hTH nH)
        rw [zero_mul] at h2
        exact h2.congr fun τ => (hform τ).symm
      exact hL (tendsto_nhds_unique hlim hzero)

  have hfinG : (qExpansion (N : ℝ) G).order ≠ ⊤ := fun h => hG0 (PowerSeries.order_eq_top.mp h)
  have hfinH : (qExpansion (N : ℝ) H).order ≠ ⊤ := fun h => hH0 (PowerSeries.order_eq_top.mp h)
  rw [← ENat.natCast_toNat hfinG, ← ENat.natCast_toNat hfinH]
  exact congrArg _ hab

end Chart
section Orders

private theorem order_inv_laurent {x : LaurentSeries ℂ} (hx : x ≠ 0) : (x⁻¹).order = -x.order := by
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  omega
private theorem order_eq_of_coeff {x : LaurentSeries ℂ} {m : ℤ}
    (hm : x.coeff m ≠ 0) (hlt : ∀ k < m, x.coeff k = 0) : x.order = m := by
  have hx : x ≠ 0 := fun h => hm (by simp [h])
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hm)
  by_contra hlt'
  exact (fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)) (hlt _ (not_le.mp hlt'))
private theorem order_ofPowerSeries {p : PowerSeries ℂ} (hp : p ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ ℂ p).order = p.order.toNat := by
  apply order_eq_of_coeff
  · rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact PowerSeries.coeff_order hp
  · intro k hk
    rcases lt_or_ge k 0 with hk0 | hk0
    · exact ModularCurve.ofPowerSeries_coeff_of_neg _ hk0
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      exact PowerSeries.coeff_of_lt_order_toNat n (by exact_mod_cast hk)

end Orders
section Assembly

local notation "Δ" => ModularForm.discriminant

private theorem eq_of_Q_eq {w : ℝ} (hw : 0 < w) {P P' : ℍ → ℂ} (hP : Good w P) (hP' : Good w P')
    (hQ : Q w P = Q w P') : P = P' := by
  have hneg : Good w ((fun _ : ℍ => (-1 : ℂ)) * P') := (Good.const w (-1)).mul hP'
  have hsum : Good w (P + (fun _ : ℍ => (-1 : ℂ)) * P') := hP.add hneg
  have h0 : Q w (P + (fun _ : ℍ => (-1 : ℂ)) * P') = 0 := by
    rw [Q_add hw hP hneg, Q_mul hw (Good.const w (-1)) hP', Q_const hw, hQ, map_neg, map_one]
    ring
  have h1 := (Q_eq_zero_iff hw hsum).mp h0
  funext τ
  have := congrFun h1 τ
  simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply] at this
  linear_combination this
private theorem good_one_modularForm {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : Good 1 (f : ℍ → ℂ) := by
  have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
    exact AddSubgroup.mem_zmultiples _
  have : Fact (IsCusp OnePoint.infty (Γ : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact
    { periodic := SlashInvariantFormClass.periodic_comp_ofComplex f h1
      mdiff := f.holo'
      bdd := ModularFormClass.bdd_at_infty f }
private theorem good_nat_modularForm (M : ℕ) {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : Good M (f : ℍ → ℂ) :=
  { periodic := by simpa using (good_one_modularForm hT f).periodic.nat_mul M
    mdiff := (good_one_modularForm hT f).mdiff
    bdd := (good_one_modularForm hT f).bdd }
private theorem qExpansion_ne_zero_of_Q_ne_zero {w : ℝ} {F : ℍ → ℂ} (hF : Q w F ≠ 0) : qExpansion w F ≠ 0 :=
  fun hp => hF (by rw [Q, hp, map_zero])

end Assembly
end CuspExpChi

set_option linter.unusedVariables false in
open CuspExpChi in
/-- Pin `ModularCurve.LevelN.valuation_apply_smul_le_one_of_tendsto_div_smul`
(`S_..._valuation_apply_smul_le_one_of_tendsto_div_smul.lean:655`), at the wrapper's
statement. -/
theorem valuation_apply_smul_le_one_of_tendsto_div_smul
    (M : ℕ) [NeZero M]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K]
    (hst : ∀ γ : SL(2, ℤ), ∀ F ∈ ModularCurve.LevelN.ring M,
      (fun τ : UpperHalfPlane => F (γ • τ)) ∈ ModularCurve.LevelN.ring M)
    (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K))
    (hσ : ∀ (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring M),
      σ γ (algebraMap (ModularCurve.LevelN.ring M) K ⟨F, hF⟩) =
        algebraMap (ModularCurve.LevelN.ring M) K
          ⟨fun τ : UpperHalfPlane => F (γ⁻¹ • τ), hst γ⁻¹ F hF⟩)
    (E : K →ₐ[ℂ] LaurentSeries ℂ)
    (hEj : E (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) =
      ModularCurve.qExpand ℂ M (ModularCurve.jqModC ℂ))
    (hEq : ∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring M) (m : ℕ),
      UpperHalfPlane.IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) →
        E (algebraMap (ModularCurve.LevelN.ring M) K ⟨F, hF⟩) *
            HahnSeries.ofPowerSeries ℤ ℂ
              (UpperHalfPlane.qExpansion M (ModularForm.discriminant : UpperHalfPlane → ℂ)) ^ m =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion M (F * ModularForm.discriminant ^ m)))
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (z : K)
    (hz : E z * ModularCurve.qExpand ℂ M
        ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ModularCurve.qExpand ℂ M
        ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (γ : SL(2, ℤ)) (L : ℂ) (hL : L ≠ 0)
    (hlim : Filter.Tendsto
      (fun τ : UpperHalfPlane => (g : UpperHalfPlane → ℂ) (γ⁻¹ • τ) / (h : UpperHalfPlane → ℂ) (γ⁻¹ • τ))
      atImInfty (𝓝 L)) :
    Valued.v (E (σ γ z)) ≤ 1 := by
  classical
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)

  suffices key : ∀ n : ℤ, n < 0 → (E (σ γ z)).coeff n = 0 by
    have := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero ℂ (D := 0)).mpr key
    simpa using this

  obtain ⟨a, b, hbnz, hzab⟩ := IsFractionRing.div_surjective (A := ModularCurve.LevelN.ring M) z
  have hb0 : ((b : ModularCurve.LevelN.ring M) : UpperHalfPlane → ℂ) ≠ 0 := by
    intro h0
    apply nonZeroDivisors.ne_zero hbnz
    exact Subtype.ext (by rw [h0]; rfl)
  set af : UpperHalfPlane → ℂ := ((a : ModularCurve.LevelN.ring M) : UpperHalfPlane → ℂ) with haf
  set bf : UpperHalfPlane → ℂ := ((b : ModularCurve.LevelN.ring M) : UpperHalfPlane → ℂ) with hbf
  have haA : af ∈ ModularCurve.LevelN.ring M := (a : ModularCurve.LevelN.ring M).2
  have hbA : bf ∈ ModularCurve.LevelN.ring M := (b : ModularCurve.LevelN.ring M).2
  have ha'A : (fun τ : UpperHalfPlane => af (γ⁻¹ • τ)) ∈ ModularCurve.LevelN.ring M := hst γ⁻¹ af haA
  have hb'A : (fun τ : UpperHalfPlane => bf (γ⁻¹ • τ)) ∈ ModularCurve.LevelN.ring M := hst γ⁻¹ bf hbA
  set a' : UpperHalfPlane → ℂ := fun τ : UpperHalfPlane => af (γ⁻¹ • τ) with ha'
  set b' : UpperHalfPlane → ℂ := fun τ : UpperHalfPlane => bf (γ⁻¹ • τ) with hb'

  have hσa : σ γ (algebraMap (ModularCurve.LevelN.ring M) K a) =
      algebraMap (ModularCurve.LevelN.ring M) K ⟨a', ha'A⟩ := hσ γ af haA
  have hσb : σ γ (algebraMap (ModularCurve.LevelN.ring M) K b) =
      algebraMap (ModularCurve.LevelN.ring M) K ⟨b', hb'A⟩ := hσ γ bf hbA
  have hzσ : σ γ z = algebraMap (ModularCurve.LevelN.ring M) K ⟨a', ha'A⟩ /
      algebraMap (ModularCurve.LevelN.ring M) K ⟨b', hb'A⟩ := by
    rw [← hzab, map_div₀, hσa, hσb]

  obtain ⟨m₁, hm₁⟩ := exists_isBoundedAtImInfty_mul_pow M ha'A
  obtain ⟨m₂, hm₂⟩ := exists_isBoundedAtImInfty_mul_pow M hb'A
  have hPa : PB a' (m₁ + m₂) := PB.add_right hm₁ m₂
  have hPb : PB b' (m₁ + m₂) := by
    have := PB.add_right hm₂ m₁
    rwa [add_comm] at this
  set m : ℕ := m₁ + m₂ with hm
  have gd1 : Good M (a' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) := good_of_PB M ha'A hPa
  have gd2 : Good M (b' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) := good_of_PB M hb'A hPb

  have hQΔ : Q M (ModularForm.discriminant : UpperHalfPlane → ℂ) ≠ 0 := Q_discriminant_ne_zero M
  have hEa : E (algebraMap (ModularCurve.LevelN.ring M) K ⟨a', ha'A⟩) * Q M (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m =
      Q M (a' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) := hEq a' ha'A m hPa
  have hEb : E (algebraMap (ModularCurve.LevelN.ring M) K ⟨b', hb'A⟩) * Q M (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m =
      Q M (b' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) := hEq b' hb'A m hPb
  have hb'ne : b' ≠ 0 := by
    intro h0
    apply hb0
    funext τ
    have := congrFun h0 (γ • τ)
    simpa [hb'] using this
  have hQb : Q M (b' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) ≠ 0 := by
    rw [ne_eq, Q_eq_zero_iff hMpos gd2, mul_discriminant_pow_eq_zero_iff]
    exact hb'ne
  have hEz : E (σ γ z) = Q M (a' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) / Q M (b' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) := by
    rw [hzσ, map_div₀, ← hEa, ← hEb, mul_div_mul_right _ _ (pow_ne_zero _ hQΔ)]

  obtain ⟨n₁, hn₁⟩ := exists_isBoundedAtImInfty_mul_pow M haA
  obtain ⟨n₂, hn₂⟩ := exists_isBoundedAtImInfty_mul_pow M hbA
  have hPa0 : PB af (n₁ + n₂) := PB.add_right hn₁ n₂
  have hPb0 : PB bf (n₁ + n₂) := by
    have := PB.add_right hn₂ n₁
    rwa [add_comm] at this
  set n : ℕ := n₁ + n₂ with hn
  have gda : Good M (af * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n) := good_of_PB M haA hPa0
  have gdb : Good M (bf * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n) := good_of_PB M hbA hPb0
  have hEa0 : E (algebraMap (ModularCurve.LevelN.ring M) K a) * Q M (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n =
      Q M (af * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n) := hEq af haA n hPa0
  have hEb0 : E (algebraMap (ModularCurve.LevelN.ring M) K b) * Q M (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n =
      Q M (bf * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n) := hEq bf hbA n hPb0
  have hQb0 : Q M (bf * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n) ≠ 0 := by
    rw [ne_eq, Q_eq_zero_iff hMpos gdb, mul_discriminant_pow_eq_zero_iff]
    exact hb0
  have gdh : Good M (h : UpperHalfPlane → ℂ) := good_nat_modularForm M hT h
  have gdg : Good M (g : UpperHalfPlane → ℂ) := good_nat_modularForm M hT g
  have hQh : Q M (h : UpperHalfPlane → ℂ) = ModularCurve.qExpand ℂ M (Q 1 (h : UpperHalfPlane → ℂ)) :=
    Q_natCast_eq_qExpand M (good_one_modularForm hT h)
  have hQg : Q M (g : UpperHalfPlane → ℂ) = ModularCurve.qExpand ℂ M (Q 1 (g : UpperHalfPlane → ℂ)) :=
    Q_natCast_eq_qExpand M (good_one_modularForm hT g)
  have hz' : E z * Q M (h : UpperHalfPlane → ℂ) = Q M (g : UpperHalfPlane → ℂ) := by
    rw [hQh, hQg]
    exact hz
  have hEz0 : E z = Q M (af * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n) / Q M (bf * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n) := by
    rw [← hzab, map_div₀, ← hEa0, ← hEb0, mul_div_mul_right _ _ (pow_ne_zero _ hQΔ)]
  have hfun : af * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n * (h : UpperHalfPlane → ℂ) =
      bf * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ n * (g : UpperHalfPlane → ℂ) := by
    apply CuspExpChi.eq_of_Q_eq hMpos (gda.mul gdh) (gdb.mul gdg)
    rw [Q_mul hMpos gda gdh, Q_mul hMpos gdb gdg, ← hz', hEz0]
    field_simp
  have hrel : ∀ τ : UpperHalfPlane, af τ * (h : UpperHalfPlane → ℂ) τ = bf τ * (g : UpperHalfPlane → ℂ) τ := by
    intro τ
    have := congrFun hfun τ
    simp only [Pi.mul_apply, Pi.pow_apply] at this
    have hΔ : (ModularForm.discriminant : UpperHalfPlane → ℂ) τ ^ n ≠ 0 := pow_ne_zero _ (ModularForm.discriminant_ne_zero τ)
    have := mul_right_cancel₀ hΔ (by
      calc af τ * (h : UpperHalfPlane → ℂ) τ * (ModularForm.discriminant : UpperHalfPlane → ℂ) τ ^ n
          = af τ * (ModularForm.discriminant : UpperHalfPlane → ℂ) τ ^ n * (h : UpperHalfPlane → ℂ) τ := by ring
        _ = bf τ * (ModularForm.discriminant : UpperHalfPlane → ℂ) τ ^ n * (g : UpperHalfPlane → ℂ) τ := this
        _ = bf τ * (g : UpperHalfPlane → ℂ) τ * (ModularForm.discriminant : UpperHalfPlane → ℂ) τ ^ n := by ring)
    exact this

  have hev1 : ∀ᶠ τ : UpperHalfPlane in atImInfty,
      (g : UpperHalfPlane → ℂ) (γ⁻¹ • τ) / (h : UpperHalfPlane → ℂ) (γ⁻¹ • τ) ≠ 0 :=
    hlim.eventually_ne hL
  have hev2 : ∀ᶠ τ : UpperHalfPlane in atImInfty, (b' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) τ ≠ 0 :=
    CuspExpChi.eventually_ne_zero_atImInfty gd2 (CuspExpChi.qExpansion_ne_zero_of_Q_ne_zero hQb)
  have hlim' : Tendsto (fun τ : UpperHalfPlane =>
      (a' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) τ / (b' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) τ) atImInfty (𝓝 L) := by
    refine hlim.congr' ?_
    filter_upwards [hev1, hev2] with τ h1 h2
    have hh' : (h : UpperHalfPlane → ℂ) (γ⁻¹ • τ) ≠ 0 := fun h0 => h1 (by rw [h0, div_zero])
    have hb'τ : b' τ ≠ 0 := by
      intro h0
      apply h2
      simp only [Pi.mul_apply, Pi.pow_apply, h0, zero_mul]
    have hr := hrel (γ⁻¹ • τ)
    have hΔ : (ModularForm.discriminant : UpperHalfPlane → ℂ) τ ^ m ≠ 0 := pow_ne_zero _ (ModularForm.discriminant_ne_zero τ)
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_div_mul_right _ _ hΔ, div_eq_div_iff hh' hb'τ]
    show (g : UpperHalfPlane → ℂ) (γ⁻¹ • τ) * bf (γ⁻¹ • τ) = af (γ⁻¹ • τ) * (h : UpperHalfPlane → ℂ) (γ⁻¹ • τ)
    linear_combination -hr

  by_cases hQa : Q M (a' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) = 0
  · intro n hn
    rw [hEz, hQa, zero_div, HahnSeries.coeff_zero]
  · have hord := CuspExpChi.order_eq_of_tendsto_div gd1 gd2 (CuspExpChi.qExpansion_ne_zero_of_Q_ne_zero hQa)
      (CuspExpChi.qExpansion_ne_zero_of_Q_ne_zero hQb) hL hlim'
    have horder : (Q M (a' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m) / Q M (b' * (ModularForm.discriminant : UpperHalfPlane → ℂ) ^ m)).order = 0 := by
      rw [div_eq_mul_inv, HahnSeries.order_mul hQa (inv_ne_zero hQb), CuspExpChi.order_inv_laurent hQb, Q, Q,
        CuspExpChi.order_ofPowerSeries (CuspExpChi.qExpansion_ne_zero_of_Q_ne_zero hQa),
        CuspExpChi.order_ofPowerSeries (CuspExpChi.qExpansion_ne_zero_of_Q_ne_zero hQb), hord]
      omega
    intro n hn
    rw [hEz]
    exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [horder]; exact hn)


end LevelN

end ModularCurve

end
