/-
  Landau's theorem for L-series with non-negative coefficients.

  `abscissaOfAbsConv_lt_of_differentiableOn_ball` — the ball form of Landau's theorem: if a
  series with non-negative coefficients agrees with a function holomorphic on a ball centred
  at a real point `x` on or to the right of its abscissa of absolute convergence, then that
  abscissa is strictly smaller than `x` (equivalently, the real point of the line of absolute
  convergence is a singularity). `abscissaOfAbsConv_lt_of_differentiableOn_ball'` is the same
  statement under its engine name; `not_exists_extension_of_abscissaOfAbsConv_eq` and
  `not_differentiableOn_ball_abscissaOfAbsConv` are the immediate contrapositive corollaries.
  The proof is the pin's: a Taylor expansion about `x₁ = x + r/4` at the interior point
  `x₂ = x₁ - 3r/8`, whose non-negative double series is summed in the other order (the
  `term`/`logMul` computation `re_term_logMul_pow`).

  Transcribed from the pin
  `P2M/Sol/S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.lean` (pinned `aa2d8b3`),
  **section `P2M_Landau` only** (pin lines 1659–1838); its headline is the pin
  `Theorems/Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.lean` wrapper. The
  same `S_` file also carries a ~2,960-line Landau–Siegel (Siegel zero) development in
  sections `P2M_CharacterSum` … `P2M_Siegel` and `P2M_ZeroFactorization` … `P2M_Page`; that
  material is used nowhere — not by this headline (the section below references none of its
  17 local definitions) and, by `grep` and by the pin's citation graph, by no other pin node
  or port module either — so it is deliberately unported (playbook §2.3, "content with no
  consumer anywhere").

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3` (Lean `v4.33.1` / mathlib
  `db584cd6`); port mathlib `v4.34.0`. The pin namespaces (`LSeries`) are kept; no `p2m_*`
  scaffolding is transcribed.
-/
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false

open scoped ComplexOrder
open Complex Filter Topology Set Metric Finset LSeries

noncomputable section

namespace LSeries

section

variable {a : ℕ → ℂ}

lemma re_term_logMul_pow (m : ℕ) (x : ℝ) (n : ℕ) :
    (term (logMul^[m] a) x n).re
      = if n = 0 then 0 else (Real.log n) ^ m * ((a n).re * (n:ℝ) ^ (-x)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [hn, ↓reduceIte, term_of_ne_zero hn]
  have hlog : (logMul^[m] a) n = (Real.log n : ℂ) ^ m * a n := by
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', logMul, ih, pow_succ, ← natCast_log]; ring
  rw [hlog, show (n:ℂ) ^ (x:ℂ) = (((n:ℝ) ^ x : ℝ) : ℂ) by
      rw [ofReal_cpow (Nat.cast_nonneg n)]; norm_cast,
    ← ofReal_pow, div_eq_mul_inv, ← ofReal_inv, mul_assoc, mul_comm (a n), ← mul_assoc,
    ← ofReal_mul, re_ofReal_mul, mul_assoc]
  congr 1
  rw [Real.rpow_neg (Nat.cast_nonneg n), mul_comm]

theorem abscissaOfAbsConv_lt_of_differentiableOn_ball' (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a ≤ x) {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball (x:ℂ) r))
    (hfa : ∀ s ∈ ball (x:ℂ) r, x < s.re → f s = LSeries a s) :
    abscissaOfAbsConv a < x := by

  set x₁ : ℝ := x + r/4 with hx₁
  set δ : ℝ := 3 * r / 8 with hδ
  set x₂ : ℝ := x₁ - δ with hx₂
  have hδ0 : 0 < δ := by positivity
  have hx₂x : x₂ < x := by rw [hx₂, hx₁, hδ]; linarith
  have habs₁ : abscissaOfAbsConv a < (x₁:ℂ).re := by
    rw [ofReal_re]; exact hx.trans_lt (by exact_mod_cast (by rw [hx₁]; linarith : x < x₁))

  have hsub : ball (x₁:ℂ) (r/2) ⊆ ball (x:ℂ) r := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs ⊢
    have hx₁x : ‖(x₁:ℂ) - x‖ = r/4 := by
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs, hx₁, add_sub_cancel_left, abs_of_pos]
      positivity
    calc ‖s - x‖ = ‖(s - x₁) + ((x₁:ℂ) - x)‖ := by ring_nf
      _ ≤ ‖s - x₁‖ + ‖(x₁:ℂ) - x‖ := norm_add_le _ _
      _ < r/2 + r/4 := by rw [hx₁x]; linarith
      _ ≤ r := by linarith
  have hf₁ : DifferentiableOn ℂ f (ball (x₁:ℂ) (r/2)) := hf.mono hsub
  have hx₂mem : (x₂:ℂ) ∈ ball (x₁:ℂ) (r/2) := by
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, hx₂, sub_sub_cancel_left,
      abs_neg, abs_of_pos hδ0, hδ]
    linarith

  have hT := Complex.hasSum_taylorSeries_on_ball hf₁ hx₂mem

  have hev : f =ᶠ[𝓝 (x₁:ℂ)] LSeries a := by
    have ho : IsOpen (ball (x:ℂ) r ∩ {s : ℂ | x < s.re}) :=
      isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
    have hmem : (x₁:ℂ) ∈ ball (x:ℂ) r ∩ {s : ℂ | x < s.re} := by
      refine ⟨?_, by simp [hx₁, hr]⟩
      rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, hx₁, add_sub_cancel_left,
        abs_of_pos (by positivity)]
      linarith
    filter_upwards [ho.mem_nhds hmem] with s hs using hfa s hs.1 hs.2
  have hderiv : ∀ m, iteratedDeriv m f x₁ = (-1) ^ m * LSeries (logMul^[m] a) x₁ := fun m ↦ by
    rw [hev.iteratedDeriv_eq, LSeries_iteratedDeriv m habs₁]

  let T : ℕ → ℕ → ℝ := fun n m ↦
    if n = 0 then 0 else (Real.log n) ^ m * δ ^ m / m.factorial * ((a n).re * (n:ℝ) ^ (-x₁))
  have ha_re : ∀ n, 0 ≤ (a n).re := fun n ↦ (Complex.le_def.mp (ha n)).1
  have hT0 : ∀ n m, 0 ≤ T n m := by
    intro n m
    simp only [T]
    split_ifs with hn
    · exact le_rfl
    · have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      exact mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg this m) (pow_nonneg hδ0.le m))
        (Nat.cast_nonneg _)) (mul_nonneg (ha_re n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

  have hrow : ∀ m, HasSum (fun n ↦ T n m)
      (((m.factorial : ℂ)⁻¹ • ((x₂:ℂ) - x₁) ^ m • iteratedDeriv m f x₁).re) := by
    intro m
    have hs : LSeriesSummable (logMul^[m] a) x₁ :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (by rwa [absicssaOfAbsConv_logPowMul])
    have hval : ((m.factorial : ℂ)⁻¹ • ((x₂:ℂ) - x₁) ^ m • iteratedDeriv m f x₁).re
        = δ ^ m / m.factorial * (LSeries (logMul^[m] a) x₁).re := by
      have hxd : (x₂:ℂ) - x₁ = -(δ:ℂ) := by rw [hx₂]; push_cast; ring
      rw [hderiv, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, hxd,
        mul_assoc ((m.factorial:ℂ)⁻¹), ← mul_pow, show -(δ:ℂ) * -1 = δ by ring,
        show (m.factorial : ℂ)⁻¹ * (δ:ℂ) ^ m = ((δ ^ m / m.factorial : ℝ) : ℂ) by push_cast; ring,
        re_ofReal_mul]
    rw [hval]
    have h2 := (Complex.hasSum_re hs.hasSum).mul_left (δ ^ m / m.factorial)
    convert h2 using 1
    all_goals first | rfl | skip
    ext n
    rw [re_term_logMul_pow]
    simp only [T]
    split_ifs with hn
    · simp
    · ring

  have hcol : HasSum (fun m ↦ ((m.factorial : ℂ)⁻¹ • ((x₂:ℂ) - x₁) ^ m • iteratedDeriv m f x₁).re)
      (f x₂).re := Complex.hasSum_re hT

  have hexp : ∀ n, n ≠ 0 → HasSum (fun m ↦ T n m) ((a n).re * (n:ℝ) ^ (-x₂)) := by
    intro n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have he := (NormedSpace.expSeries_div_hasSum_exp (δ * Real.log n)).mul_right
      ((a n).re * (n:ℝ) ^ (-x₁))
    convert he using 1
    · ext m
      simp only [T, hn, ↓reduceIte, mul_pow]
      ring
    · rw [show NormedSpace.exp (δ * Real.log n) = Real.exp (δ * Real.log n) from
          (congrFun Real.exp_eq_exp_ℝ _).symm, mul_comm δ, ← Real.rpow_def_of_pos hnpos, hx₂,
        show -(x₁ - δ) = δ + (-x₁) by ring, Real.rpow_add hnpos]
      ring

  let g : ℕ → ℝ := fun n ↦ if n = 0 then 0 else (a n).re * (n:ℝ) ^ (-x₂)
  have hg0 : ∀ n, 0 ≤ g n := fun n ↦ by
    simp only [g]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (ha_re n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hgT : ∀ n, HasSum (fun m ↦ T n m) (g n) := fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [g, T, ↓reduceIte]; exact hasSum_zero
    · simp only [g, hn, ↓reduceIte]; exact hexp n hn

  have hbound : ∀ N, ∑ n ∈ range N, g n ≤ (f x₂).re := by
    intro N
    calc ∑ n ∈ range N, g n = ∑ n ∈ range N, ∑' m, T n m :=
          sum_congr rfl fun n _ ↦ (hgT n).tsum_eq.symm
      _ = ∑' m, ∑ n ∈ range N, T n m :=
          (Summable.tsum_finsetSum fun n _ ↦ (hgT n).summable).symm
      _ ≤ ∑' m, ((m.factorial : ℂ)⁻¹ • ((x₂:ℂ) - x₁) ^ m • iteratedDeriv m f x₁).re :=
          Summable.tsum_le_tsum (fun m ↦ ((hrow m).summable.sum_le_tsum (range N)
            (fun n _ ↦ hT0 n m)).trans_eq (hrow m).tsum_eq)
            (summable_sum fun n _ ↦ (hgT n).summable) hcol.summable
      _ = (f x₂).re := hcol.tsum_eq
  have hsum : Summable g := summable_of_sum_range_le hg0 hbound

  have hL : LSeriesSummable a x₂ := by
    refine Summable.of_norm ?_
    convert hsum using 1
    ext n
    rw [norm_term_eq]
    simp only [g, ofReal_re]
    split_ifs with hn
    · rfl
    · obtain ⟨hre, him⟩ := Complex.le_def.mp (ha n)
      have : a n = ((a n).re : ℂ) := Complex.ext (by simp) (by simpa using him.symm)
      rw [this, norm_real, Real.norm_eq_abs, abs_of_nonneg (ha_re n), ofReal_re,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  exact hL.abscissaOfAbsConv_le.trans_lt (by simpa using hx₂x)

theorem not_exists_extension_of_abscissaOfAbsConv_eq (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a = x) {r : ℝ} (hr : 0 < r) :
    ¬ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball (x:ℂ) r) ∧
        ∀ s ∈ ball (x:ℂ) r, x < s.re → f s = LSeries a s := by
  rintro ⟨f, hf, hfa⟩
  have := abscissaOfAbsConv_lt_of_differentiableOn_ball' ha hx.le hr hf hfa
  rw [hx] at this
  exact lt_irrefl _ this

theorem not_differentiableOn_ball_abscissaOfAbsConv (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a = x) {r : ℝ} (hr : 0 < r) :
    ¬ DifferentiableOn ℂ (LSeries a) (ball (x:ℂ) r) := fun h ↦
  not_exists_extension_of_abscissaOfAbsConv_eq ha hx hr ⟨LSeries a, h, fun _ _ _ ↦ rfl⟩

end

theorem abscissaOfAbsConv_lt_of_differentiableOn_ball {a : ℕ → ℂ} (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a ≤ x) {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball (x:ℂ) r))
    (hfa : ∀ s ∈ ball (x:ℂ) r, x < s.re → f s = LSeries a s) :
    abscissaOfAbsConv a < x :=
  abscissaOfAbsConv_lt_of_differentiableOn_ball' ha hx hr hf hfa

end LSeries

end
