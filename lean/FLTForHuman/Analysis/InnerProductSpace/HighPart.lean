/-
  The spectral theory of a compact self-adjoint operator: the high part of the spectrum, and the
  orthogonal decomposition of the range.

  * `ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq`: an element orthogonal to the
    set `{x − r • x}` of symmetric differences for every real `r` is zero (`SymmetricRangeDensity`).
  * `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal`: for a compact
    symmetric operator `T` and a subspace `X` whose intersection with each
    `(⨆_{r ≤ ‖μ‖} eigenspace μ)ᗮ` is either zero or contains `X`, one has `X ≤ ker T` or `X` is finite
    dimensional (`ContinuousLinearMap.HighPart`).
  * `ContinuousLinearMap.map_highPart_orthogonal_le_of_commute`: an operator commuting with `T` maps the
    orthogonal complement of the high part into itself.
  * `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker`: the orthogonal complement of the
    span of the nonzero eigenspaces of a compact symmetric operator is its kernel.
  * `CuspForm`-free linear algebra: `ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute`: an
    operator commuting with `T` maps each eigenspace's orthogonal complement into itself.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal.lean` (276
  lines), `S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute.lean` (275),
  `S_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker.lean` (275),
  `S_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq.lean` (385) and
  `S_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute.lean` (40), with the statements from the
  wrappers of the same names.  The first three files carry the same 14-declaration `highPart` prelude; it
  is written **once**, in the sub-namespace `ContinuousLinearMap.HighPart`, and the pin's `_pf` suffix (the
  `highPart`-spelled form of a headline result) is dropped there.  The pin label namespace
  `SymmetricRangeDensity` is a word name and is kept.

  spec-pin: Theorems/Thm_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal.lean
  spec-pin: P2M/Sol/S_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal.lean
  spec-pin: Theorems/Thm_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute.lean
  spec-pin: P2M/Sol/S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute.lean
  spec-pin: Theorems/Thm_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker.lean
  spec-pin: P2M/Sol/S_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker.lean
  spec-pin: Theorems/Thm_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq.lean
  spec-pin: P2M/Sol/S_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq.lean
  spec-pin: Theorems/Thm_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute.lean
  spec-pin: P2M/Sol/S_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute.lean
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open MeasureTheory Set


namespace SymmetricRangeDensity

private def bump (c r : ℝ) : ℝ → ℝ := fun x => max 0 (min 1 (2 - |x - c| / r))

private theorem bump_continuous (c r : ℝ) : Continuous (bump c r) := by
  unfold bump
  fun_prop

private theorem bump_nonneg (c r x : ℝ) : 0 ≤ bump c r x := by
  exact le_max_left _ _

private theorem bump_le_one (c r x : ℝ) : bump c r x ≤ 1 := by
  exact max_le zero_le_one (min_le_left _ _)

private theorem bump_eq_one {c r x : ℝ} (hr : 0 < r) (hx : |x - c| ≤ r) : bump c r x = 1 := by
  unfold bump
  have h1 : |x - c| / r ≤ 1 := (div_le_one hr).mpr hx
  have h2 : (1 : ℝ) ≤ 2 - |x - c| / r := by linarith
  rw [min_eq_left h2, max_eq_right zero_le_one]

private theorem bump_eq_zero {c r x : ℝ} (hr : 0 < r) (hx : 2 * r ≤ |x - c|) : bump c r x = 0 := by
  unfold bump
  have h1 : (2 : ℝ) ≤ |x - c| / r := by
    rw [le_div_iff₀ hr]
    exact hx
  have h2 : min 1 (2 - |x - c| / r) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
  exact le_antisymm (max_le le_rfl h2) (le_max_left _ _)

private theorem bump_hasCompactSupport {c r : ℝ} (hr : 0 < r) : HasCompactSupport (bump c r) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c (2 * r)) ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, Real.dist_eq]
  by_contra h
  exact hx (bump_eq_zero hr (le_of_lt (not_le.mp h)))

private def bumpC (c r : ℝ) (hr : 0 < r) : CompactlySupportedContinuousMap ℝ ℝ :=
  ⟨⟨bump c r, bump_continuous c r⟩, bump_hasCompactSupport hr⟩

private theorem bumpC_apply (c r : ℝ) (hr : 0 < r) (x : ℝ) : bumpC c r hr x = bump c r x := by
  rfl

private theorem measure_eq_zero_of_forall_measure_closedBall_le_ofReal_mul_sq
    (μ : Measure ℝ) (K : ℝ → ℝ)
    (h : ∀ c r : ℝ, 0 < r → μ (Metric.closedBall c r) ≤ ENNReal.ofReal (K c * r ^ 2)) :
    μ = 0 := by
  have piece : ∀ (n : ℕ) (r a : ℝ), 0 < r →
      μ ({c | K c ≤ n} ∩ Icc a (a + r)) ≤ ENNReal.ofReal (n * r ^ 2) := by
    intro n r a hr
    rcases ({c | K c ≤ n} ∩ Icc a (a + r)).eq_empty_or_nonempty with hE | ⟨c, hcK, hcI⟩
    · rw [hE, measure_empty]
      exact zero_le
    · calc μ ({c | K c ≤ n} ∩ Icc a (a + r))
          ≤ μ (Metric.closedBall c r) := by
            apply measure_mono
            intro x hx
            rw [Metric.mem_closedBall]
            have hd := Real.dist_le_of_mem_Icc hx.2 hcI
            linarith
        _ ≤ ENNReal.ofReal (K c * r ^ 2) := h c r hr
        _ ≤ ENNReal.ofReal (n * r ^ 2) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcK (sq_nonneg r))

  have block : ∀ n R : ℕ, μ ({c | K c ≤ n} ∩ Icc (-(R : ℝ)) R) = 0 := by
    intro n R
    refine le_antisymm ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    rw [zero_add]
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨m, hm⟩ := exists_nat_gt ((2 * (R : ℝ) * n + n) / ε)
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    set r : ℝ := ((m : ℝ) + 1)⁻¹ with hr_def
    have hr : 0 < r := inv_pos.mpr hm1
    have hr_mul : r * ((m : ℝ) + 1) = 1 := inv_mul_cancel₀ hm1.ne'
    have cover : {c | K c ≤ n} ∩ Icc (-(R : ℝ)) R ⊆
        ⋃ j ∈ Finset.range (2 * R * (m + 1) + 1),
          ({c | K c ≤ n} ∩ Icc (-(R : ℝ) + j * r) (-(R : ℝ) + j * r + r)) := by
      intro c hc
      obtain ⟨hcK, hcR⟩ := hc
      have hc1 : -(R : ℝ) ≤ c := hcR.1
      have hc2 : c ≤ R := hcR.2
      set t : ℝ := (c + R) * ((m : ℝ) + 1) with ht_def
      have ht0 : 0 ≤ t := mul_nonneg (by linarith) hm1.le
      have htr : t * r = c + R := by
        rw [ht_def, mul_assoc, mul_comm ((m : ℝ) + 1) r, hr_mul, mul_one]
      have hj1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
      have hj2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have hjN : ⌊t⌋₊ < 2 * R * (m + 1) + 1 := by
        have ht_le : t ≤ ((2 * R * (m + 1) : ℕ) : ℝ) := by
          rw [ht_def]; push_cast; nlinarith
        exact Nat.lt_succ_of_le (Nat.floor_le_of_le ht_le)
      refine mem_iUnion₂.mpr ⟨⌊t⌋₊, Finset.mem_range.mpr hjN, hcK, ?_, ?_⟩
      ·
        have : (⌊t⌋₊ : ℝ) * r ≤ t * r := mul_le_mul_of_nonneg_right hj1 hr.le
        linarith
      ·
        have : t * r ≤ ((⌊t⌋₊ : ℝ) + 1) * r := mul_le_mul_of_nonneg_right hj2.le hr.le
        linarith
    calc μ ({c | K c ≤ n} ∩ Icc (-(R : ℝ)) R)
        ≤ μ (⋃ j ∈ Finset.range (2 * R * (m + 1) + 1),
            ({c | K c ≤ n} ∩ Icc (-(R : ℝ) + j * r) (-(R : ℝ) + j * r + r))) := measure_mono cover
      _ ≤ ∑ j ∈ Finset.range (2 * R * (m + 1) + 1),
            μ ({c | K c ≤ n} ∩ Icc (-(R : ℝ) + j * r) (-(R : ℝ) + j * r + r)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ Finset.range (2 * R * (m + 1) + 1), ENNReal.ofReal (n * r ^ 2) :=
          Finset.sum_le_sum fun j _ => piece n r _ hr
      _ = ENNReal.ofReal (((2 * R * (m + 1) + 1 : ℕ) : ℝ) * (n * r ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ (ε : ENNReal) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          apply ENNReal.ofReal_le_ofReal
          have hm' : 2 * (R : ℝ) * n + n < ε * m := by
            have := (div_lt_iff₀ hε').mp hm
            linarith
          have hr2 : r ^ 2 * ((m : ℝ) + 1) ^ 2 = 1 := by
            rw [← mul_pow, hr_mul, one_pow]
          have key : (((2 * R * (m + 1) + 1 : ℕ) : ℝ) * n) ≤ (ε : ℝ) * ((m : ℝ) + 1) ^ 2 := by
            push_cast
            nlinarith [hm', (Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
              (Nat.cast_nonneg R : (0 : ℝ) ≤ R), hε']
          calc ((2 * R * (m + 1) + 1 : ℕ) : ℝ) * (n * r ^ 2)
              = (((2 * R * (m + 1) + 1 : ℕ) : ℝ) * n) * r ^ 2 := by ring
            _ ≤ ((ε : ℝ) * ((m : ℝ) + 1) ^ 2) * r ^ 2 :=
                mul_le_mul_of_nonneg_right key (sq_nonneg r)
            _ = (ε : ℝ) := by
                rw [mul_assoc, mul_comm (((m : ℝ) + 1) ^ 2) (r ^ 2), hr2, mul_one]

  have huniv : (univ : Set ℝ) ⊆ ⋃ p : ℕ × ℕ, ({c | K c ≤ p.1} ∩ Icc (-(p.2 : ℝ)) p.2) := by
    intro c _
    refine mem_iUnion.mpr ⟨(⌈K c⌉₊, ⌈|c|⌉₊), Nat.le_ceil (K c), ?_, ?_⟩
    · have := Nat.le_ceil |c|
      have := neg_abs_le c
      linarith
    · have := Nat.le_ceil |c|
      have := le_abs_self c
      linarith
  refine Measure.measure_univ_eq_zero.1 (le_antisymm ?_ zero_le)
  calc μ univ ≤ μ (⋃ p : ℕ × ℕ, ({c | K c ≤ p.1} ∩ Icc (-(p.2 : ℝ)) p.2)) := measure_mono huniv
    _ = 0 := measure_iUnion_null_iff.2 fun p => block p.1 p.2

variable {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]

private theorem inner_apply_comm {B : S →L[ℂ] S} (hB : IsSelfAdjoint B) (x y : S) :
    ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ := by
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB) x y

private def quadForm (A : S →L[ℂ] S) (u : S) (f : CompactlySupportedContinuousMap ℝ ℝ) : ℝ :=
  (⟪cfc (⇑f) A u, u⟫_ℂ).re

private theorem quadForm_add (A : S →L[ℂ] S) (u : S) (f g : CompactlySupportedContinuousMap ℝ ℝ) :
    quadForm A u (f + g) = quadForm A u f + quadForm A u g := by
  unfold quadForm
  have hfg : cfc (⇑(f + g)) A = cfc (⇑f) A + cfc (⇑g) A := by
    rw [CompactlySupportedContinuousMap.coe_add]
    exact cfc_add (a := A) (⇑f) (⇑g) (hf := f.continuous.continuousOn)
      (hg := g.continuous.continuousOn)
  rw [hfg, add_apply, inner_add_left, Complex.add_re]

private theorem quadForm_smul (A : S →L[ℂ] S) (u : S) (a : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ) :
    quadForm A u (a • f) = a * quadForm A u f := by
  unfold quadForm
  have haf : cfc (⇑(a • f)) A = a • cfc (⇑f) A := by
    rw [CompactlySupportedContinuousMap.coe_smul]
    exact cfc_smul (a := A) a (⇑f) (hf := f.continuous.continuousOn)
  rw [haf, smul_apply, ← Complex.coe_smul, inner_smul_left,
    Complex.conj_ofReal, Complex.re_ofReal_mul]

private theorem quadForm_nonneg {A : S →L[ℂ] S} (u : S) {f : CompactlySupportedContinuousMap ℝ ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ quadForm A u f := by
  unfold quadForm
  set g : ℝ → ℝ := fun x => Real.sqrt (f x) with hg
  have hgc : Continuous g := f.continuous.sqrt
  have hfgg : cfc (⇑f) A = cfc g A * cfc g A := by
    rw [← cfc_mul (a := A) g g (hf := hgc.continuousOn) (hg := hgc.continuousOn)]
    refine cfc_congr (fun x _ => ?_)
    exact (Real.mul_self_sqrt (hf x)).symm
  have hB : IsSelfAdjoint (cfc g A) := cfc_predicate g A
  rw [hfgg, mul_apply_eq_comp, inner_apply_comm hB]
  simpa using (inner_self_nonneg (𝕜 := ℂ) (x := cfc g A u))

private def quadFormP (A : S →L[ℂ] S) (u : S) : CompactlySupportedContinuousMap ℝ ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := quadForm A u
      map_add' := quadForm_add A u
      map_smul' := fun a f => by simpa using quadForm_smul A u a f }
    (fun f hf => quadForm_nonneg u (fun x => by simpa using (CompactlySupportedContinuousMap.le_def.mp hf) x))

private theorem quadFormP_apply (A : S →L[ℂ] S) (u : S) (f : CompactlySupportedContinuousMap ℝ ℝ) :
    quadFormP A u f = quadForm A u f := by
  rfl

private theorem quadForm_le {A : S →L[ℂ] S} (hA : IsSelfAdjoint A) {u w : S} {c r : ℝ} (hr : 0 ≤ r)
    (hw : A w - (c : ℂ) • w = u) (f : ℝ → ℝ) (hfc : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (hfz : ∀ x, r < |x - c| → f x = 0) :
    (⟪cfc f A u, u⟫_ℂ).re ≤ r ^ 2 * ‖w‖ ^ 2 := by
  have hdc : Continuous (fun x : ℝ => x - c) := by fun_prop
  have hD : ∀ y : S, cfc (fun x : ℝ => x - c) A y = A y - (c : ℂ) • y := by
    intro y
    have h1 : cfc (fun x : ℝ => x - c) A = cfc (fun x : ℝ => x) A - cfc (fun _ : ℝ => c) A :=
      cfc_sub (a := A) (fun x : ℝ => x) (fun _ : ℝ => c)
    rw [h1, cfc_id' (R := ℝ) (a := A) (ha := hA), cfc_const (a := A) c (ha := hA),
      sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self, Complex.coe_smul]
  have hDsa : IsSelfAdjoint (cfc (fun x : ℝ => x - c) A) := cfc_predicate _ A
  have hDw : cfc (fun x : ℝ => x - c) A w = u := by rw [hD, hw]

  have hgc : Continuous (fun x : ℝ => (x - c) * f x * (x - c)) := by fun_prop
  have hcfcg : cfc (fun x : ℝ => (x - c) * f x * (x - c)) A
      = cfc (fun x : ℝ => x - c) A * cfc f A * cfc (fun x : ℝ => x - c) A := by
    rw [← cfc_mul (a := A) (fun x : ℝ => x - c) f (hf := hdc.continuousOn) (hg := hfc.continuousOn),
      ← cfc_mul (a := A) (fun x : ℝ => (x - c) * f x) (fun x : ℝ => x - c)
        (hf := (hdc.mul hfc).continuousOn) (hg := hdc.continuousOn)]
  have hinner : ⟪cfc f A u, u⟫_ℂ = ⟪cfc (fun x : ℝ => (x - c) * f x * (x - c)) A w, w⟫_ℂ := by
    rw [← hDw, ← inner_apply_comm hDsa, hcfcg, mul_apply_eq_comp,
      mul_apply_eq_comp]

  have hgb : ∀ x ∈ spectrum ℝ A, ‖(x - c) * f x * (x - c)‖ ≤ r ^ 2 := by
    intro x _
    by_cases hx : r < |x - c|
    · rw [hfz x hx, mul_zero, zero_mul, norm_zero]
      positivity
    · have hx' : |x - c| ≤ r := not_lt.mp hx
      have hfx : |f x| ≤ 1 := abs_le.mpr ⟨by linarith [hf0 x], hf1 x⟩
      have hxc : 0 ≤ |x - c| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |x - c| * |f x| * |x - c| ≤ r * 1 * r := by
            gcongr
        _ = r ^ 2 := by ring
  have hnorm : ‖cfc (fun x : ℝ => (x - c) * f x * (x - c)) A‖ ≤ r ^ 2 := norm_cfc_le (sq_nonneg r) hgb
  calc (⟪cfc f A u, u⟫_ℂ).re = (⟪cfc (fun x : ℝ => (x - c) * f x * (x - c)) A w, w⟫_ℂ).re := by
        rw [hinner]
    _ ≤ ‖⟪cfc (fun x : ℝ => (x - c) * f x * (x - c)) A w, w⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ‖cfc (fun x : ℝ => (x - c) * f x * (x - c)) A w‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖cfc (fun x : ℝ => (x - c) * f x * (x - c)) A‖ * ‖w‖ * ‖w‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ w
    _ ≤ r ^ 2 * ‖w‖ * ‖w‖ := by gcongr
    _ = r ^ 2 * ‖w‖ ^ 2 := by ring

private theorem core {A : S →L[ℂ] S} (hA : IsSelfAdjoint A) (u : S)
    (hu : ∀ c : ℝ, ∃ w : S, A w - (c : ℂ) • w = u) : u = 0 := by
  classical
  choose w hw using hu

  set Λ := quadFormP A u with hΛ
  set μ : Measure ℝ := RealRMK.rieszMeasure Λ with hμ
  have hint : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, ∫ x, f x ∂μ = quadForm A u f :=
    fun f => RealRMK.integral_rieszMeasure Λ f

  have hball : ∀ c : ℝ, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall c r) ≤ ENNReal.ofReal (4 * ‖w c‖ ^ 2 * r ^ 2) := by
    intro c r hr
    have h2r : (0 : ℝ) ≤ 2 * r := by linarith
    set f := bumpC c r hr with hf
    have hfi : Integrable (fun x => f x) μ := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    have hlt : μ (Metric.closedBall c r) < ⊤ := measure_closedBall_lt_top

    have hlow : (μ (Metric.closedBall c r)).toReal ≤ ∫ x, f x ∂μ := by
      have h1 : ∫ x in Metric.closedBall c r, f x ∂μ ≤ ∫ x, f x ∂μ :=
        setIntegral_le_integral hfi (Filter.Eventually.of_forall (fun x => bump_nonneg c r x))
      have h2 : ∫ x in Metric.closedBall c r, f x ∂μ = ∫ x in Metric.closedBall c r, (1 : ℝ) ∂μ := by
        refine setIntegral_congr_fun measurableSet_closedBall (fun x hx => ?_)
        rw [Metric.mem_closedBall, Real.dist_eq] at hx
        exact bump_eq_one hr hx
      rw [h2, setIntegral_const, smul_eq_mul, mul_one] at h1
      simpa [Measure.real] using h1

    have hup : ∫ x, f x ∂μ ≤ (2 * r) ^ 2 * ‖w c‖ ^ 2 := by
      rw [hint f]
      exact quadForm_le hA h2r (hw c) (bump c r) (bump_continuous c r) (bump_nonneg c r)
        (bump_le_one c r) (fun x hx => bump_eq_zero hr (le_of_lt hx))
    have h4 : (2 * r) ^ 2 * ‖w c‖ ^ 2 = 4 * ‖w c‖ ^ 2 * r ^ 2 := by ring
    have hreal : (μ (Metric.closedBall c r)).toReal ≤ 4 * ‖w c‖ ^ 2 * r ^ 2 := by
      linarith [hlow, hup]
    exact (ENNReal.le_ofReal_iff_toReal_le hlt.ne (by positivity)).mpr hreal

  have hμ0 : μ = 0 := measure_eq_zero_of_forall_measure_closedBall_le_ofReal_mul_sq μ (fun c => 4 * ‖w c‖ ^ 2) hball

  obtain ⟨R₀, hR₀⟩ := (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) A).isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 0 + 1 with hR
  have hRpos : 0 < R := by positivity
  have hspec : ∀ x ∈ spectrum ℝ A, bump 0 R x = 1 := by
    intro x hx
    have hx' : |x - 0| ≤ R := by
      have := hR₀ hx
      rw [Metric.mem_closedBall, Real.dist_eq] at this
      linarith [le_max_left R₀ 0]
    exact bump_eq_one hRpos hx'
  have hone : cfc (bump 0 R) A = 1 := by
    rw [cfc_congr (g := fun _ : ℝ => (1 : ℝ)) (fun x hx => hspec x hx)]
    exact cfc_const_one (R := ℝ) (a := A)
  have hmass : ‖u‖ ^ 2 = ∫ x, bumpC 0 R hRpos x ∂μ := by
    rw [hint, quadForm]
    show ‖u‖ ^ 2 = (⟪cfc (bump 0 R) A u, u⟫_ℂ).re
    rw [hone, one_apply_eq_self]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm
  rw [hμ0, integral_zero_measure] at hmass
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hmass)

end SymmetricRangeDensity

open scoped InnerProductSpace

theorem ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (E : Submodule ℂ H)
    (hsym : ∀ x ∈ E, ∀ y ∈ E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (v : H) (hsurj : ∀ c : ℝ, ∃ w ∈ E, T w - (c : ℂ) • w = v) :
    v = 0 := by
  classical

  set S := E.topologicalClosure with hS
  have : CompleteSpace S :=
    completeSpace_coe_iff_isComplete.mpr E.isClosed_topologicalClosure.isComplete
  set A : S →L[ℂ] S := S.orthogonalProjectionOnto.comp (T.comp S.subtypeL) with hAdef
  have hA_apply : ∀ x : S, A x = S.orthogonalProjectionOnto (T x) := fun x => rfl

  have hES : (E : Set H) ⊆ (S : Set H) := E.le_topologicalClosure
  have hScl : (S : Set H) = closure (E : Set H) := E.topologicalClosure_coe
  have hsym1 : ∀ y ∈ E, ∀ x ∈ S, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
    intro y hy x hx
    have hcl : IsClosed {x : H | ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ} :=
      isClosed_eq (T.continuous.inner continuous_const) (continuous_id.inner continuous_const)
    have hsub : (E : Set H) ⊆ {x : H | ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ} := fun x hx => hsym x hx y hy
    have hx' : (x : H) ∈ closure (E : Set H) := by rw [← hScl]; exact hx
    exact closure_minimal hsub hcl hx'
  have hsymS : ∀ x ∈ S, ∀ y ∈ S, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
    intro x hx y hy
    have hcl : IsClosed {y : H | ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ} :=
      isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner T.continuous)
    have hsub : (E : Set H) ⊆ {y : H | ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ} := fun y hy => hsym1 y hy x hx
    have hy' : (y : H) ∈ closure (E : Set H) := by rw [← hScl]; exact hy
    exact closure_minimal hsub hcl hy'

  have hA : IsSelfAdjoint A := by
    refine LinearMap.IsSymmetric.isSelfAdjoint (fun x y => ?_)
    show ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ
    rw [hA_apply, hA_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact hsymS x x.2 y y.2

  choose w hwE hw using hsurj
  have hwS : ∀ c, w c ∈ S := fun c => hES (hwE c)
  have hPv : ∀ c : ℝ, A ⟨w c, hwS c⟩ - (c : ℂ) • ⟨w c, hwS c⟩ = S.orthogonalProjectionOnto v := by
    intro c
    have h1 : S.orthogonalProjectionOnto (w c) = ⟨w c, hwS c⟩ :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨w c, hwS c⟩ : S)
    show S.orthogonalProjectionOnto (T (w c)) - (c : ℂ) • (⟨w c, hwS c⟩ : S) =
      S.orthogonalProjectionOnto v
    rw [← h1, ← map_smul, ← map_sub, hw c]

  have hPv0 : S.orthogonalProjectionOnto v = 0 :=
    SymmetricRangeDensity.core hA (S.orthogonalProjectionOnto v) (fun c => ⟨⟨w c, hwS c⟩, hPv c⟩)

  set c₀ : ℝ := ‖A‖ + 1 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have heig : A ⟨w c₀, hwS c₀⟩ = (c₀ : ℂ) • ⟨w c₀, hwS c₀⟩ := by
    rw [← sub_eq_zero, hPv c₀, hPv0]
  have hw0 : (⟨w c₀, hwS c₀⟩ : S) = 0 := by
    by_contra hne
    have hpos : 0 < ‖(⟨w c₀, hwS c₀⟩ : S)‖ := norm_pos_iff.mpr hne
    have h1 : ‖A ⟨w c₀, hwS c₀⟩‖ ≤ ‖A‖ * ‖(⟨w c₀, hwS c₀⟩ : S)‖ := A.le_opNorm _
    rw [heig, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₀pos] at h1
    have : c₀ ≤ ‖A‖ := le_of_mul_le_mul_right h1 hpos
    linarith
  have hw0' : w c₀ = 0 := by
    have := congrArg Subtype.val hw0
    simpa using this
  have := hw c₀
  rw [hw0', map_zero, smul_zero, sub_zero] at this
  exact this.symm

open Module.End

namespace ContinuousLinearMap

namespace HighPart
open ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

def highPart (T : E →L[𝕜] E) (r : ℝ) : Submodule 𝕜 E :=
  ⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), eigenspace (T : Module.End 𝕜 E) μ


omit [CompleteSpace E] in
theorem le_norm_sub_of_mem_eigenspace {T : E →L[𝕜] E} (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    {μ ν : 𝕜} (hμν : μ ≠ ν) {r : ℝ} (hr : 0 ≤ r) (hμ : r ≤ ‖μ‖) (hν : r ≤ ‖ν‖)
    {e e' : E} (he : e ∈ eigenspace (T : Module.End 𝕜 E) μ) (he' : e' ∈ eigenspace (T : Module.End 𝕜 E) ν)
    (hne : ‖e‖ = 1) (hne' : ‖e'‖ = 1) : r ≤ ‖T e - T e'‖ := by
  have h0 : inner 𝕜 e e' = 0 := hT'.orthogonalFamily_eigenspaces hμν ⟨e, he⟩ ⟨e', he'⟩
  have horth : inner 𝕜 (μ • e) (ν • e') = 0 := by
    rw [inner_smul_left, inner_smul_right, h0]; simp
  have hTe : T e = μ • e := mem_eigenspace_iff.mp he
  have hTe' : T e' = ν • e' := mem_eigenspace_iff.mp he'
  rw [hTe, hTe']
  have hpy : ‖μ • e - ν • e'‖ * ‖μ • e - ν • e'‖ = ‖μ • e‖ * ‖μ • e‖ + ‖ν • e'‖ * ‖ν • e'‖ := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) (μ • e) (-(ν • e'))
      (by rw [inner_neg_right, horth, neg_zero])
    rwa [← sub_eq_add_neg, norm_neg] at this
  rw [norm_smul, norm_smul, hne, hne', mul_one, mul_one] at hpy
  have h2r : r * r + r * r ≤ ‖μ‖ * ‖μ‖ + ‖ν‖ * ‖ν‖ :=
    add_le_add (mul_self_le_mul_self hr hμ) (mul_self_le_mul_self hr hν)
  have h1 : r * r ≤ ‖μ • e - ν • e'‖ * ‖μ • e - ν • e'‖ := by
    rw [hpy]; nlinarith [norm_nonneg μ, norm_nonneg ν, h2r]
  nlinarith [norm_nonneg (μ • e - ν • e'), h1]

theorem finite_setOf_hasEigenvalue_le_norm {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {r : ℝ} (hr : 0 < r) :
    {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ r ≤ ‖μ‖}.Finite := by
  by_contra hinf
  have hinf' : {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ r ≤ ‖μ‖}.Infinite := hinf

  let μ : ℕ → 𝕜 := fun n => (hinf'.natEmbedding _ n : 𝕜)
  have hμmem : ∀ n, HasEigenvalue (T : Module.End 𝕜 E) (μ n) ∧ r ≤ ‖μ n‖ := fun n => (hinf'.natEmbedding _ n).2
  have hμinj : Function.Injective μ := fun a b h =>
    (hinf'.natEmbedding _).injective (Subtype.ext h)
  have hex : ∀ n, ∃ e : E, e ∈ eigenspace (T : Module.End 𝕜 E) (μ n) ∧ ‖e‖ = 1 := by
    intro n
    obtain ⟨v, hv, hv0⟩ := (hμmem n).1.exists_hasEigenvector
    refine ⟨(‖v‖⁻¹ : 𝕜) • v, Submodule.smul_mem _ _ hv, ?_⟩
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  choose e he hne using hex

  have hsep : ∀ n m, n ≠ m → r ≤ ‖T (e n) - T (e m)‖ := fun n m hnm =>
    le_norm_sub_of_mem_eigenspace hT' (fun h => hnm (hμinj h)) hr.le (hμmem n).2 (hμmem m).2 (he n) (he m)
      (hne n) (hne m)
  have hK : IsCompact (closure (T '' Metric.closedBall (0 : E) 1)) := hT.isCompact_closure_image_closedBall 1
  have hin : ∀ n, T (e n) ∈ closure (T '' Metric.closedBall (0 : E) 1) := fun n =>
    subset_closure ⟨e n, by simp [hne n], rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hin
  have hc : CauchySeq (fun n => T (e (φ n))) := hlim.cauchySeq
  -- the section's `CompleteSpace E` is spent here, to extract the limit of the Cauchy sequence
  obtain ⟨a', ha'⟩ := cauchySeq_tendsto_of_complete hc
  rw [Metric.tendsto_atTop] at ha'
  obtain ⟨N₀, hN₀⟩ := ha' (r / 2) (by linarith)
  have h1 : ‖T (e (φ N₀)) - a'‖ < r / 2 := by
    have := hN₀ N₀ le_rfl
    rwa [dist_eq_norm] at this
  have h2 : ‖T (e (φ (N₀ + 1))) - a'‖ < r / 2 := by
    have := hN₀ (N₀ + 1) (by omega)
    rwa [dist_eq_norm] at this
  have hsep' : r ≤ ‖T (e (φ N₀)) - T (e (φ (N₀ + 1)))‖ :=
    hsep (φ N₀) (φ (N₀ + 1)) (fun h => by have := hφ.injective h; omega)
  have htri : ‖T (e (φ N₀)) - T (e (φ (N₀ + 1)))‖ ≤
      ‖T (e (φ N₀)) - a'‖ + ‖T (e (φ (N₀ + 1))) - a'‖ := by
    have hxy : T (e (φ N₀)) - T (e (φ (N₀ + 1))) =
        (T (e (φ N₀)) - a') - (T (e (φ (N₀ + 1))) - a') := by abel
    rw [hxy]
    exact norm_sub_le _ _
  linarith

theorem finiteDimensional_highPart {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {r : ℝ} (hr : 0 < r) :
    FiniteDimensional 𝕜 ↥(highPart T r) := by
  set M := {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ r ≤ ‖μ‖} with hM
  have hfin : M.Finite := finite_setOf_hasEigenvalue_le_norm hT hT' hr
  have : ∀ μ : 𝕜, μ ∈ hfin.toFinset → FiniteDimensional 𝕜 ↥(eigenspace (T : Module.End 𝕜 E) μ) := by
    intro μ hμ
    rw [Set.Finite.mem_toFinset] at hμ
    exact finite_dimensional_eigenspace hT μ (fun h => by
      have h2 : r ≤ ‖μ‖ := hμ.2
      rw [h, norm_zero] at h2; exact absurd h2 (not_le.mpr hr))
  have hle : highPart T r ≤ hfin.toFinset.sup fun μ => eigenspace (T : Module.End 𝕜 E) μ := by
    refine iSup₂_le fun μ hμ => ?_
    by_cases h : HasEigenvalue (T : Module.End 𝕜 E) μ
    · exact Finset.le_sup (f := fun μ => eigenspace (T : Module.End 𝕜 E) μ)
        (hfin.mem_toFinset.mpr ⟨h, hμ⟩)
    · rw [hasEigenvalue_iff, not_ne_iff] at h
      rw [h]; exact bot_le
  have : ∀ i : { x // x ∈ hfin.toFinset }, FiniteDimensional 𝕜 ↥(eigenspace (T : Module.End 𝕜 E) i) :=
    fun i => this i i.2
  have : FiniteDimensional 𝕜 ↥(hfin.toFinset.sup fun μ => eigenspace (T : Module.End 𝕜 E) μ) := by
    rw [Finset.sup_eq_iSup]
    have e : (⨆ μ ∈ hfin.toFinset, eigenspace (T : Module.End 𝕜 E) μ)
        = ⨆ i : { x // x ∈ hfin.toFinset }, eigenspace (T : Module.End 𝕜 E) i := by
      rw [iSup_subtype']
    rw [e]
    exact Submodule.finiteDimensional_iSup _
  exact Submodule.finiteDimensional_of_le hle

theorem apply_mem_iSup_eigenspace_ne_zero {T : E →L[𝕜] E} {u : E}
    (hu : u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ) :
    T u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ := by
  -- FR-0208: the section's `CompleteSpace E` is dead in the pin's proof; spend it.
  have hcomp : CompleteSpace E := inferInstance
  refine Submodule.iSup_induction _
    (motive := fun u => T u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ) hu
    (fun μ x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · by_cases hμ : μ = 0
    · simp [hμ] at hx; simp [hx]
    · rw [iSup_pos hμ, mem_eigenspace_iff] at hx
      have hx' : T x = μ • x := hx
      rw [hx']
      refine Submodule.smul_mem _ μ (Submodule.mem_iSup_of_mem μ ?_)
      rw [iSup_pos hμ, mem_eigenspace_iff]
      show T x = μ • x
      exact hx'
  · rw [map_add]; exact Submodule.add_mem _ hx hy

theorem orthogonal_iSup_eigenspace_ne_zero_eq_ker {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) := by
  set K : Submodule 𝕜 E := ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ with hK
  apply le_antisymm
  · intro v hv
    have hinv : ∀ w ∈ Kᗮ, T w ∈ Kᗮ := by
      intro w hw
      rw [Submodule.mem_orthogonal] at hw ⊢
      intro u hu
      have e : inner 𝕜 u (T w) = inner 𝕜 ((T : E →ₗ[𝕜] E) u) w := (hT' u w).symm
      rw [e]
      exact hw _ (apply_mem_iSup_eigenspace_ne_zero hu)
    let S : ↥Kᗮ →L[𝕜] ↥Kᗮ := T.restrict hinv
    have hS_compact : IsCompactOperator S := hT.restrict' hinv
    have hS_symm : (S : ↥Kᗮ →ₗ[𝕜] ↥Kᗮ).IsSymmetric := hT'.restrict_invariant hinv
    have hS0 : S = 0 := by
      rw [← eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact hS_symm]
      intro μ hμ
      by_contra hμ0
      rw [hasEigenvalue_iff] at hμ
      apply hμ
      rw [eq_bot_iff]
      intro w hw
      rw [mem_eigenspace_iff] at hw
      have hw' : ((S w : Kᗮ) : E) = ((μ • w : Kᗮ) : E) := congrArg Subtype.val hw
      have hwE : (w : E) ∈ eigenspace (T : Module.End 𝕜 E) μ := by
        rw [mem_eigenspace_iff]
        exact hw'
      have hwK : (w : E) ∈ K := by
        refine Submodule.mem_iSup_of_mem μ ?_
        rw [iSup_pos hμ0]; exact hwE
      have hw0 : (w : E) ∈ K ⊓ Kᗮ := ⟨hwK, w.2⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hw0
      rw [Submodule.mem_bot]
      exact Subtype.ext hw0
    have h1 : ((S ⟨v, hv⟩ : Kᗮ) : E) = 0 := by rw [hS0]; rfl
    exact h1
  ·
    intro v hv
    have hv0 : v ∈ eigenspace (T : Module.End 𝕜 E) 0 := by
      rw [mem_eigenspace_iff, zero_smul]; exact hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.iSup_induction _ (motive := fun u => inner 𝕜 u v = 0) hu
      (fun μ x hx => ?_) (by simp) (fun x y hx hy => ?_)
    · by_cases hμ : μ = 0
      · simp [hμ] at hx; simp [hx]
      · rw [iSup_pos hμ] at hx
        exact hT'.orthogonalFamily_eigenspaces hμ ⟨x, hx⟩ ⟨v, hv0⟩
    · rw [inner_add_left, hx, hy, add_zero]

theorem highPart_sup_orthogonal_eq_top {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {r : ℝ} (hr : 0 < r) :
    highPart T r ⊔ (highPart T r)ᗮ = ⊤ := by
  have := finiteDimensional_highPart hT hT' hr
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

theorem map_highPart_le_of_commute {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (highPart T r) ≤ highPart T r := by
  -- FR-0208: the section's `CompleteSpace E` and the symmetry `hT'` are dead in the pin's
  -- proof; spend both.
  have hcomp : CompleteSpace E := inferInstance
  have hTsa : IsSelfAdjoint T := hT'.isSelfAdjoint
  unfold highPart
  rw [Submodule.map_iSup]
  refine iSup_mono fun μ => ?_
  rw [Submodule.map_iSup]
  refine iSup_mono fun hμ => ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_eigenspace_iff] at hx
  rw [mem_eigenspace_iff]
  have h := congrArg (fun A : E →L[𝕜] E => A x) hST
  simp only [coe_comp, Function.comp_apply] at h
  show (T : E →ₗ[𝕜] E) (S x) = μ • S x
  have : T (S x) = S (T x) := h.symm
  rw [ContinuousLinearMap.coe_coe, this, show (T x) = μ • x from hx, map_smul]

theorem adjoint_comp_eq_of_isSymmetric {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) :
    (adjoint S).comp T = T.comp (adjoint S) := by
  have hT : adjoint T = T := hT'.isSelfAdjoint.adjoint_eq
  have := congrArg adjoint hST
  rw [adjoint_comp, adjoint_comp, hT] at this
  exact this.symm

theorem map_highPart_orthogonal_le_of_commute {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (highPart T r)ᗮ ≤ (highPart T r)ᗮ := by
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal] at hy
  rw [Submodule.mem_orthogonal]
  intro x hx
  have hx' : adjoint S x ∈ highPart T r :=
    map_highPart_le_of_commute hT' (adjoint_comp_eq_of_isSymmetric hT' hST) r ⟨x, hx, rfl⟩
  rw [ContinuousLinearMap.coe_coe, ← adjoint_inner_left]
  exact hy _ hx'

theorem iInf_highPart_orthogonal_eq_ker {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨅ (r : ℝ) (_ : 0 < r), (highPart T r)ᗮ) = LinearMap.ker (T : E →ₗ[𝕜] E) := by
  rw [← orthogonal_iSup_eigenspace_ne_zero_eq_ker hT hT']
  have e : (⨅ (r : ℝ) (_ : 0 < r), (highPart T r)ᗮ) = (⨆ (r : ℝ) (_ : 0 < r), highPart T r)ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    refine iInf_congr fun r => ?_
    by_cases hr : 0 < r
    · simp only [iInf_pos hr, iSup_pos hr]
    · simp only [iInf_neg hr, iSup_neg hr, Submodule.bot_orthogonal_eq_top]
  rw [e]
  congr 1
  apply le_antisymm
  · refine iSup₂_le fun r hr => iSup₂_le fun μ hμ => ?_
    have hμ0 : μ ≠ 0 := fun h => by rw [h, norm_zero] at hμ; exact absurd hμ (not_le.mpr hr)
    exact le_iSup₂_of_le μ hμ0 le_rfl
  · refine iSup₂_le fun μ hμ => ?_
    have hr : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
    exact le_iSup₂_of_le ‖μ‖ hr (le_iSup₂_of_le μ le_rfl le_rfl)

theorem exists_inf_highPart_orthogonal_eq_bot_of_not_le_ker {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
    (hX : ∀ r : ℝ, 0 < r → X ⊓ (highPart T r)ᗮ = ⊥ ∨ X ≤ (highPart T r)ᗮ)
    (hTX : ¬ X ≤ LinearMap.ker (T : E →ₗ[𝕜] E)) :
    ∃ r : ℝ, 0 < r ∧ X ⊓ (highPart T r)ᗮ = ⊥ ∧
      ∃ L : ↥X →ₗ[𝕜] ↥(highPart T r), Function.Injective L := by
  by_contra hcon
  push Not at hcon
  apply hTX
  rw [← iInf_highPart_orthogonal_eq_ker hT hT']
  refine le_iInf₂ fun r hr => ?_
  rcases hX r hr with h | h
  · exfalso
    have := finiteDimensional_highPart hT hT' hr

    have hinj : Function.Injective
        (((highPart T r).orthogonalProjectionOnto : E →ₗ[𝕜] ↥(highPart T r)).comp X.subtype) := by
      intro a b hab
      apply Subtype.ext
      have h2 : (a : E) - b ∈ (highPart T r)ᗮ := by
        rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff, map_sub, sub_eq_zero]
        exact hab
      have hmem : (a : E) - b ∈ X ⊓ (highPart T r)ᗮ := ⟨X.sub_mem a.2 b.2, h2⟩
      rw [h, Submodule.mem_bot, sub_eq_zero] at hmem
      exact hmem
    exact hcon r hr h _ hinj
  · exact h

theorem le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
    (hX : ∀ r : ℝ, 0 < r → X ⊓ (highPart T r)ᗮ = ⊥ ∨ X ≤ (highPart T r)ᗮ) :
    X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) ∨ FiniteDimensional 𝕜 ↥X := by
  by_cases hTX : X ≤ LinearMap.ker (T : E →ₗ[𝕜] E)
  · exact Or.inl hTX
  obtain ⟨r, hr, -, L, hL⟩ := exists_inf_highPart_orthogonal_eq_bot_of_not_le_ker hT hT' X hX hTX
  have := finiteDimensional_highPart hT hT' hr
  exact Or.inr (Module.Finite.of_injective L hL)

end HighPart

end ContinuousLinearMap

open Module.End

theorem ContinuousLinearMap.map_highPart_orthogonal_le_of_commute {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by
  exact ContinuousLinearMap.HighPart.map_highPart_orthogonal_le_of_commute hT' hST r

open Module.End

theorem ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) := by
  exact ContinuousLinearMap.HighPart.orthogonal_iSup_eigenspace_ne_zero_eq_ker hT hT'

open Module.End

theorem ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
    (hX : ∀ r : ℝ, 0 < r → X ⊓ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ ∨ X ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ) :
    X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) ∨ FiniteDimensional 𝕜 ↥X := by
  exact ContinuousLinearMap.HighPart.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal hT hT' X hX

open Module.End
open scoped InnerProductSpace

theorem ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    (S : E →L[𝕜] E) (hST : S.comp T = T.comp S) (μ : 𝕜) (hμ : μ ≠ 0) :
    (eigenspace (T : Module.End 𝕜 E) μ).map (S : Module.End 𝕜 E) ≤ eigenspace (T : Module.End 𝕜 E) μ ∧
    ((eigenspace (T : Module.End 𝕜 E) μ)ᗮ).map (S : Module.End 𝕜 E) ≤ (eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by
  -- FR-0208: compactness and `hμ : μ ≠ 0` are dead in the pin's proof; spend both on the
  -- finite dimensionality of the eigenspace.
  have hfd : FiniteDimensional 𝕜 ↥(eigenspace (T : Module.End 𝕜 E) μ) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ
  have hTsa : IsSelfAdjoint T := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hT'
  have hadj : ContinuousLinearMap.adjoint T = T := hTsa.adjoint_eq
  have hST' : (ContinuousLinearMap.adjoint S).comp T = T.comp (ContinuousLinearMap.adjoint S) := by
    have h := congrArg ContinuousLinearMap.adjoint hST
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hadj] at h
    exact h.symm

  have hpres : ∀ R : E →L[𝕜] E, R.comp T = T.comp R →
      ∀ v ∈ eigenspace (T : Module.End 𝕜 E) μ, R v ∈ eigenspace (T : Module.End 𝕜 E) μ := by
    intro R hR v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : T v = μ • v := hv
    show T (R v) = μ • R v
    have h := congrArg (fun f : E →L[𝕜] E => f v) hR
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← h, hv', map_smul]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hpres S hST v hv
  · rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_orthogonal]
    intro e he
    show ⟪e, S v⟫_𝕜 = 0
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (Submodule.mem_orthogonal _ _).mp hv _ (hpres _ hST' e he)


end
