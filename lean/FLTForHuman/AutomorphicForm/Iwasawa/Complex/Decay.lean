/-
  The complex-place Iwasawa engine -- decay (tier 3, unlisted).

  The archimedean integrability and Fourier-decay half of the complex Iwasawa
  development of the pinned FLT repository `anthropics/fermats-last-theorem@aa2d8b3`.
  It rests on `Core.lean`'s `CplxIwasawa`/`CplxSmooth` blocks and writes once:

  * `B2bCL2` -- away from `det g = 0`, `radC g z ^ 2` grows like `1 + ‖z‖ ^ 2`
    uniformly on compacta, so `radC g z ^ (-κ)` is integrable for `κ > 2`;
  * `CplxDecay` -- the symbol estimate for `radC ^ (-u)` and the integration by
    parts that gives faster-than-polynomial decay of the Fourier transform;
  * `Engine` -- the two decay kernels.

  The pin's `B2bCL2` re-carries `botNormSqC`/`centerC` and the `radC` prelude that
  `CplxIwasawa` already has (byte-identical statements); they are dropped and the
  `CplxIwasawa`/`KCUnif` copies imported, so the block is written once. Every
  transcribed declaration carries a `-- pin:` provenance comment. The pin's
  `M4aP3B.FourierDecay` block is homed at
  `FLTForHuman/MeasureTheory/FourierDecay.lean` (imported through `Core`).

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import FLTForHuman.AutomorphicForm.Iwasawa.Complex.Core

set_option autoImplicit false
-- The pin is written for Lean v4.33.1; in v4.34.0 `simp` already carries several
-- of the arguments the pin lists explicitly.  Keeping the pin's proof text
-- verbatim (playbook section 4) leaves those arguments redundant, so the linter
-- that would flag them is off for this file.
set_option linter.unusedSimpArgs false

noncomputable section

open ComplexConjugate
open scoped ContDiff

namespace AutomorphicForm.ComplexIwasawa


open MeasureTheory CplxSmooth Real VectorFourier Complex
open scoped ContDiff FourierTransform

namespace B2bCL2

open ComplexConjugate
open CplxIwasawa KCUnif
open scoped Nat

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

-- pin: main (S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean:134)
theorem main (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (κ₀ κ₁ : ℝ) (hκ₀ : 2 < κ₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ g ∈ 𝒢, ∀ κ : ℝ, κ₀ ≤ κ → κ ≤ κ₁ →
      Integrable (fun z : ℂ => radC g z ^ (-κ)) ∧ ∫ z : ℂ, radC g z ^ (-κ) ≤ M := by

  obtain ⟨A₀, hA₀⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => botNormSqC g)
    continuous_botNormSqC.continuousOn
  obtain ⟨cA, hcA⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => (botNormSqC g)⁻¹)
    ((continuous_botNormSqC.continuousOn).inv₀ fun g hg => (botNormSqC_pos (hdet g hg)).ne')
  obtain ⟨cD, hcD⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => ‖g.det‖⁻¹)
    (continuous_detC.continuousOn.norm.inv₀ fun g hg => (norm_pos_iff.2 (hdet g hg)).ne')
  set A₁ : ℝ := max 1 A₀ with hA₁def
  set a : ℝ := max 1 cA with hadef
  set d : ℝ := max 1 cD with hddef
  have hA₁1 : 1 ≤ A₁ := le_max_left _ _
  have ha1 : 1 ≤ a := le_max_left _ _
  have hd1 : 1 ≤ d := le_max_left _ _
  set μ₀ : ℝ := min a⁻¹ ((d ^ 2)⁻¹ * A₁⁻¹) with hμ₀def
  have hμ₀ : 0 < μ₀ := by positivity
  have hμ₀1 : μ₀ ≤ 1 := (min_le_left _ _).trans (inv_le_one_of_one_le₀ ha1)

  set h : ℂ → ℝ := fun z => ((1 : ℝ) + ‖z‖ ^ 2) ^ (-κ₀ / 2) with hhdef
  have hfinr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < κ₀ := by
    rw [Complex.finrank_real_complex]; exact_mod_cast hκ₀
  have hh_int : Integrable h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) hfinr
  have hh_nonneg : ∀ z, 0 ≤ h z := fun z => Real.rpow_nonneg (by positivity) _
  set B : ℝ := μ₀⁻¹ ^ (κ₁ / 2) with hBdef
  have hB : 0 < B := Real.rpow_pos_of_pos (inv_pos.2 hμ₀) _
  have hIh : 0 ≤ ∫ z, h z := integral_nonneg hh_nonneg
  refine ⟨B * (∫ z, h z) + 1, by positivity, fun g hg κ hκ hκ1 => ?_⟩
  have hg' : g.det ≠ 0 := hdet g hg
  have hApos := botNormSqC_pos hg'
  have hdet0 : 0 < ‖g.det‖ := norm_pos_iff.2 hg'
  have h1 : (botNormSqC g)⁻¹ ≤ a := by
    have := hcA g hg; rw [norm_inv, Real.norm_of_nonneg hApos.le] at this
    exact this.trans (le_max_right _ _)
  have h2 : ‖g.det‖⁻¹ ≤ d := by
    have := hcD g hg; rw [norm_inv, norm_norm] at this
    exact this.trans (le_max_right _ _)
  have hAup : botNormSqC g ≤ A₁ := by
    have := hA₀ g hg; rw [Real.norm_of_nonneg hApos.le] at this
    exact this.trans (le_max_right _ _)
  have hb1 : a⁻¹ ≤ botNormSqC g := by
    rw [inv_le_comm₀ (by positivity) hApos]; exact h1
  have hb2 : (d ^ 2)⁻¹ * A₁⁻¹ ≤ Complex.normSq g.det / botNormSqC g := by
    rw [Complex.normSq_eq_norm_sq, div_eq_mul_inv]
    refine mul_le_mul ?_ ((inv_le_inv₀ (by positivity) hApos).mpr hAup) (by positivity) (sq_nonneg _)
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) ((inv_le_comm₀ (by positivity) hdet0).mpr h2) 2
  have hμA : μ₀ ≤ botNormSqC g := (min_le_left _ _).trans hb1
  have hμM : μ₀ ≤ Complex.normSq g.det / botNormSqC g := (min_le_right _ _).trans hb2

  have hcmp : ∀ z : ℂ, radC g z ^ (-κ) ≤ B * h (z - centerC g) := by
    intro z
    have hrad0 : 0 < radC g z := radC_pos hg' z
    have hκ0 : 0 < κ := by linarith
    have hW : (1:ℝ) ≤ 1 + ‖z - centerC g‖ ^ 2 := by nlinarith [sq_nonneg ‖z - centerC g‖]
    have hlb : μ₀ * (1 + ‖z - centerC g‖ ^ 2) ≤ radC g z ^ 2 := by
      rw [radC_sq_eq hg' z, Complex.normSq_eq_norm_sq]
      nlinarith [mul_le_mul_of_nonneg_right hμA (sq_nonneg ‖z - centerC g‖)]
    have hMn : 0 < μ₀ * (1 + ‖z - centerC g‖ ^ 2) := mul_pos hμ₀ (by positivity)
    calc radC g z ^ (-κ) = (radC g z ^ 2) ^ (-κ / 2) := by
          rw [← Real.rpow_natCast (radC g z) 2, ← Real.rpow_mul hrad0.le]; ring_nf
      _ ≤ (μ₀ * (1 + ‖z - centerC g‖ ^ 2)) ^ (-κ / 2) :=
          Real.rpow_le_rpow_of_nonpos hMn hlb (by linarith)
      _ = μ₀ ^ (-κ / 2) * ((1 : ℝ) + ‖z - centerC g‖ ^ 2) ^ (-κ / 2) := by
          rw [Real.mul_rpow hμ₀.le (by positivity)]
      _ ≤ B * ((1 : ℝ) + ‖z - centerC g‖ ^ 2) ^ (-κ₀ / 2) := by
          refine mul_le_mul ?_ ?_ (Real.rpow_nonneg (by positivity) _) hB.le
          · rw [hBdef, show -κ / 2 = -(κ / 2) from by ring, Real.rpow_neg hμ₀.le, ← Real.inv_rpow hμ₀.le]
            exact Real.rpow_le_rpow_of_exponent_le (one_le_inv_iff₀.2 ⟨hμ₀, hμ₀1⟩) (by linarith)
          · exact Real.rpow_le_rpow_of_exponent_le hW (by linarith)
      _ = B * h (z - centerC g) := by rw [hhdef]
  have hmaj_int : Integrable (fun z : ℂ => B * h (z - centerC g)) :=
    (hh_int.comp_sub_right (centerC g)).const_mul B
  have hmeas : AEStronglyMeasurable (fun z : ℂ => radC g z ^ (-κ)) volume :=
    ((contDiff_radC hg').continuous.rpow_const
      (fun z => Or.inl (radC_pos hg' z).ne')).aestronglyMeasurable
  have hnn : ∀ z : ℂ, 0 ≤ radC g z ^ (-κ) := fun z => Real.rpow_nonneg (radC_pos hg' z).le _
  have hint : Integrable (fun z : ℂ => radC g z ^ (-κ)) :=
    hmaj_int.mono' hmeas (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hnn z)]; exact hcmp z)
  refine ⟨hint, ?_⟩
  calc ∫ z : ℂ, radC g z ^ (-κ) ≤ ∫ z : ℂ, B * h (z - centerC g) :=
        integral_mono hint hmaj_int hcmp
    _ = B * ∫ z : ℂ, h (z - centerC g) := integral_const_mul _ _
    _ = B * ∫ z : ℂ, h z := by rw [integral_sub_right_eq_self h (centerC g)]
    _ ≤ B * (∫ z, h z) + 1 := by linarith
end B2bCL2

namespace CplxDecay

open CplxIwasawa (botNormSqC botNormSqC_pos centerC radC_pos radC_sq_eq
  norm_det_div_sqrt_le_radC contDiff_radC)

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

-- pin: radC_pos' (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1585)
private theorem radC_pos' (hg : g.det ≠ 0) (z : ℂ) : 0 < radC g z := radC_pos hg z

-- pin: radC_sq_eq' (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1587)
private theorem radC_sq_eq' (hg : g.det ≠ 0) (z : ℂ) :
    radC g z ^ 2 = botNormSqC g * Complex.normSq (z - centerC g)
      + Complex.normSq g.det / botNormSqC g := radC_sq_eq hg z

-- pin: norm_det_div_sqrt_le_radC' (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1591)
private theorem norm_det_div_sqrt_le_radC' (hg : g.det ≠ 0) (z : ℂ) :
    ‖g.det‖ / Real.sqrt (botNormSqC g) ≤ radC g z := norm_det_div_sqrt_le_radC hg z

-- pin: contDiff_radC' (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1594)
private theorem contDiff_radC' (hg : g.det ≠ 0) : ContDiff ℝ ∞ (radC g) := contDiff_radC hg

-- pin: exists_decay_bound_iteratedFDeriv_radC' (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1596)
private theorem exists_decay_bound_iteratedFDeriv_radC' (hg : g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (radC g) z‖
        ≤ C * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n :=
  exists_decay_bound_iteratedFDeriv_radC hg n

-- pin: iteratedDerivWithin_ofReal_cpow (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1602)
theorem iteratedDerivWithin_ofReal_cpow {c : ℝ} (hc : 0 < c) (u : ℂ) (k : ℕ) :
    Set.EqOn (iteratedDerivWithin k (fun y : ℝ => ((y : ℂ)) ^ u) (Set.Ioi c))
      (fun y => (∏ j ∈ Finset.range k, (u - (j : ℂ))) * ((y : ℂ)) ^ (u - (k : ℂ)))
      (Set.Ioi c) := by
  induction k with
  | zero => intro y hy; simp
  | succ k ih =>
    intro y hy
    rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih hy),
      derivWithin_of_isOpen isOpen_Ioi hy]
    have hy0 : (y : ℝ) ≠ 0 := (lt_trans hc (Set.mem_Ioi.1 hy)).ne'
    have hd : HasDerivAt (fun t : ℝ => ((t : ℂ)) ^ (u - (k : ℂ)))
        ((u - (k : ℂ)) * ((y : ℂ)) ^ (u - (k : ℂ) - 1)) y := by
      rcases eq_or_ne (u - (k : ℂ)) 0 with hu0 | hu0
      · rw [hu0, zero_mul]
        exact (hasDerivAt_const y (1 : ℂ)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun t => by simp only [Complex.cpow_zero])
      · exact hasDerivAt_ofReal_cpow_const hy0 hu0
    rw [(HasDerivAt.const_mul _ hd).deriv, Finset.prod_range_succ, Nat.cast_succ]
    ring_nf

-- pin: norm_iteratedDerivWithin_ofReal_cpow_le (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1623)
theorem norm_iteratedDerivWithin_ofReal_cpow_le {c : ℝ} (hc : 0 < c) (u : ℂ) (k : ℕ)
    {y : ℝ} (hy : y ∈ Set.Ioi c) :
    ‖iteratedDerivWithin k (fun t : ℝ => ((t : ℂ)) ^ (-u)) (Set.Ioi c) y‖
      ≤ (∏ j ∈ Finset.range k, (‖u‖ + (j : ℝ))) * y ^ (-u.re - (k : ℝ)) := by
  have hy0 : 0 < y := lt_trans hc (Set.mem_Ioi.1 hy)
  rw [iteratedDerivWithin_ofReal_cpow hc (-u) k hy, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.sub_re, Complex.neg_re,
    show ((k : ℂ)).re = (k : ℝ) from by exact_mod_cast Complex.natCast_re k]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy0.le _)
  rw [show ‖∏ j ∈ Finset.range k, (-u - (j : ℂ))‖
        = ∏ j ∈ Finset.range k, ‖-u - (j : ℂ)‖ from norm_prod _ _]
  refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => ?_)
  calc ‖-u - (j : ℂ)‖ ≤ ‖-u‖ + ‖(j : ℂ)‖ := norm_sub_le _ _
    _ = ‖u‖ + (j : ℝ) := by rw [norm_neg, Complex.norm_natCast]

-- pin: contDiffOn_ofReal_cpow_neg (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1638)
theorem contDiffOn_ofReal_cpow_neg {c : ℝ} (hc : 0 < c) (u : ℂ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => ((y : ℂ)) ^ (-u)) (Set.Ioi c) := by
  intro y hy
  have hy0 : (0:ℝ) < y := lt_trans hc (Set.mem_Ioi.1 hy)
  have hslit : ((y:ℝ):ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hy0
  have hana : AnalyticAt ℂ (fun z : ℂ => z ^ (-u)) ↑y :=
    analyticAt_id.cpow analyticAt_const hslit
  exact ((hana.contDiffAt.restrict_scalars ℝ).comp y
    Complex.ofRealCLM.contDiff.contDiffAt).contDiffWithinAt

-- pin: exists_bound_iteratedFDeriv_cpow_neg_radC (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1648)
theorem exists_bound_iteratedFDeriv_cpow_neg_radC (hg : g.det ≠ 0) (u : ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun w => ((radC g w : ℂ)) ^ (-u)) z‖ ≤ C * radC g z ^ (-u.re) := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hm : (0:ℝ) < ‖g.det‖ / Real.sqrt (botNormSqC g) :=
    div_pos (norm_pos_iff.2 hg) (Real.sqrt_pos.2 hA)
  have htow : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ (k + 1) (radC g) z‖ ≤ C := by
    intro k
    obtain ⟨C, hC, hB⟩ := exists_decay_bound_iteratedFDeriv_radC' hg (k + 1)
    refine ⟨C, hC, fun z => (hB z).trans ?_⟩
    have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
    have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
    have h1 : (1:ℝ) ≤ (1 + ‖z - centerC g‖) ^ k := one_le_pow₀ hW1
    rw [pow_succ, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hC.le hW0.le)]
  choose CR hCR using htow
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hP : (0:ℝ) < (‖u‖ + n + 1) ^ n := pow_pos (by positivity) n
  have hMx : (0:ℝ) < max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g))) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hDsum : (0:ℝ) ≤ ∑ k ∈ Finset.range n, CR k :=
    Finset.sum_nonneg fun k _ => (hCR k).1.le
  have hD1 : (1:ℝ) ≤ 1 + ∑ k ∈ Finset.range n, CR k := by linarith
  refine ⟨(n.factorial : ℝ) * (((‖u‖ + n + 1) ^ n)
      * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n)
      * (1 + ∑ k ∈ Finset.range n, CR k) ^ n,
    mul_pos (mul_pos hfac (mul_pos hP (pow_pos hMx n))) (pow_pos (by linarith) n),
    fun z => ?_⟩
  have hrad := radC_pos' hg z
  have hradm := norm_det_div_sqrt_le_radC' hg z
  have hm2 : ‖g.det‖ / Real.sqrt (botNormSqC g) / 2 < radC g z := by nlinarith
  have hrange : Set.range (radC g)
      ⊆ Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) := by
    rintro y ⟨w, rfl⟩
    have h1 := norm_det_div_sqrt_le_radC' hg w
    exact Set.mem_Ioi.2 (by nlinarith [radC_pos' hg w])
  have hgOn : ContDiffOn ℝ ∞ (fun y : ℝ => ((y : ℂ)) ^ (-u))
      (Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2)) :=
    contDiffOn_ofReal_cpow_neg (by linarith) u
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ => ((y : ℂ)) ^ (-u))
          (Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2)) (radC g z)‖
        ≤ ((‖u‖ + n + 1) ^ n)
          * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n * radC g z ^ (-u.re) := by
    intro i hi
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    refine (norm_iteratedDerivWithin_ofReal_cpow_le (by linarith) u i
      (Set.mem_Ioi.2 hm2)).trans ?_
    have hsplit : radC g z ^ (-u.re - (i:ℝ))
        = radC g z ^ (-u.re) * (radC g z ^ ((i:ℝ)))⁻¹ := by
      rw [show -u.re - (i:ℝ) = -u.re + -(i:ℝ) from by ring, Real.rpow_add hrad,
        Real.rpow_neg hrad.le ((i:ℝ))]
    have hpowinv : (radC g z ^ ((i:ℝ)))⁻¹
        ≤ (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n := by
      rw [Real.rpow_natCast]
      have hmh : (0:ℝ) < (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) ^ i :=
        pow_pos (by linarith) i
      have h1 : (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) ^ i ≤ radC g z ^ i :=
        pow_le_pow_left₀ (by linarith) (by linarith) i
      have h2 := one_div_le_one_div_of_le hmh h1
      rw [one_div, one_div] at h2
      refine h2.trans ?_
      rw [← inv_pow, inv_div]
      exact (pow_le_pow_left₀ (by positivity) (le_max_right _ _) i).trans
        (pow_le_pow_right₀ (le_max_left _ _) hi)
    have hprod : (∏ j ∈ Finset.range i, (‖u‖ + (j:ℝ)))
        ≤ (‖u‖ + n + 1) ^ n := by
      have hstep1 : (∏ j ∈ Finset.range i, (‖u‖ + (j:ℝ)))
          ≤ ∏ _j ∈ Finset.range i, (‖u‖ + (n:ℝ) + 1) := by
        refine Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j hj => ?_)
        have hjn : (j:ℝ) ≤ (n:ℝ) := by
          exact_mod_cast le_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hj) hi)
        linarith [norm_nonneg u]
      refine hstep1.trans ?_
      rw [Finset.prod_const, Finset.card_range]
      exact pow_le_pow_right₀ (by linarith [norm_nonneg u]) hi
    rw [hsplit]
    have hr0 : (0:ℝ) ≤ radC g z ^ (-u.re) := Real.rpow_nonneg hrad.le _
    calc (∏ j ∈ Finset.range i, (‖u‖ + (j:ℝ)))
          * (radC g z ^ (-u.re) * (radC g z ^ ((i:ℝ)))⁻¹)
        ≤ ((‖u‖ + n + 1) ^ n)
          * (radC g z ^ (-u.re)
            * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n) :=
          mul_le_mul hprod (mul_le_mul_of_nonneg_left hpowinv hr0)
            (mul_nonneg hr0 (inv_nonneg.2 (Real.rpow_nonneg hrad.le _))) hP.le
      _ = ((‖u‖ + n + 1) ^ n)
          * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n
          * radC g z ^ (-u.re) := by ring
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (radC g) z‖ ≤ (1 + ∑ k ∈ Finset.range n, CR k) ^ i := by
    intro i hi1 hin
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < n := by omega
    refine ((hCR k).2 z).trans (le_trans ?_ (le_self_pow₀ hD1 (by omega)))
    linarith [Finset.single_le_sum (f := CR) (fun j _ => (hCR j).1.le) (Finset.mem_range.2 hk)]
  have hcomp := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) hrange isOpen_Ioi.uniqueDiffOn hgOn
    (contDiff_radC' hg) (mod_cast le_top) z hC hD
  have hfun : (fun w => ((radC g w : ℂ)) ^ (-u))
      = (fun y : ℝ => ((y : ℂ)) ^ (-u)) ∘ radC g := rfl
  rw [hfun]
  refine hcomp.trans (le_of_eq ?_)
  ring

-- pin: integrable_rpow_neg_radC (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1752)
theorem integrable_rpow_neg_radC (hg : g.det ≠ 0) {κ : ℝ} (hκ : 2 < κ) :
    Integrable (fun z => radC g z ^ (-κ)) (volume : Measure ℂ) := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hB : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  set M : ℝ := min (botNormSqC g) (Complex.normSq g.det / botNormSqC g)
  have hM : (0:ℝ) < M := lt_min hA hB
  have hfinr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < κ := by
    rw [Complex.finrank_real_complex]; exact_mod_cast hκ
  have hcmp : ∀ z : ℂ, radC g z ^ (-κ)
      ≤ M ^ (-κ/2) * ((1 : ℝ) + ‖z - centerC g‖ ^ 2) ^ (-κ/2) := by
    intro z
    have hrad0 : 0 < radC g z := radC_pos' hg z
    have hlb : M * (1 + ‖z - centerC g‖ ^ 2) ≤ radC g z ^ 2 := by
      rw [radC_sq_eq' hg z, Complex.normSq_eq_norm_sq]
      nlinarith [mul_le_mul_of_nonneg_right (min_le_left (botNormSqC g)
          (Complex.normSq g.det / botNormSqC g)) (sq_nonneg ‖z - centerC g‖),
        min_le_right (botNormSqC g) (Complex.normSq g.det / botNormSqC g)]
    have hMn : 0 < M * (1 + ‖z - centerC g‖ ^ 2) := mul_pos hM (by positivity)
    calc radC g z ^ (-κ) = (radC g z ^ 2) ^ (-κ/2) := by
          rw [← Real.rpow_natCast (radC g z) 2, ← Real.rpow_mul hrad0.le]; ring_nf
      _ ≤ (M * (1 + ‖z - centerC g‖ ^ 2)) ^ (-κ/2) :=
          Real.rpow_le_rpow_of_nonpos hMn hlb (by linarith)
      _ = M ^ (-κ/2) * ((1 : ℝ) + ‖z - centerC g‖ ^ 2) ^ (-κ/2) := by
          rw [Real.mul_rpow hM.le (by positivity)]
  have hint : Integrable
      (fun z : ℂ => M ^ (-κ/2) * ((1 : ℝ) + ‖z - centerC g‖ ^ 2) ^ (-κ/2)) := by
    refine Integrable.const_mul ?_ _
    exact (integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) hfinr).comp_sub_right
      (centerC g)
  exact hint.mono'
    ((contDiff_radC' hg).continuous.rpow_const
      (fun z => Or.inl (radC_pos' hg z).ne')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (radC_pos' hg z).le _)]; exact hcmp z)

-- pin: contDiff_cpow_neg_radC (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1788)
theorem contDiff_cpow_neg_radC (hg : g.det ≠ 0) (u : ℂ) :
    ContDiff ℝ ∞ (fun w => ((radC g w : ℂ)) ^ (-u)) := by
  have hm : (0:ℝ) < ‖g.det‖ / Real.sqrt (botNormSqC g) :=
    div_pos (norm_pos_iff.2 hg) (Real.sqrt_pos.2 (botNormSqC_pos hg))
  have hrange : ∀ w : ℂ, radC g w ∈ Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) := by
    intro w
    exact Set.mem_Ioi.2 (by nlinarith [norm_det_div_sqrt_le_radC' hg w, radC_pos' hg w])
  have hfun : (fun w => ((radC g w : ℂ)) ^ (-u))
      = (fun y : ℝ => ((y : ℂ)) ^ (-u)) ∘ radC g := rfl
  rw [hfun]
  exact (contDiffOn_ofReal_cpow_neg (by linarith) u).comp_contDiff (contDiff_radC' hg) hrange

-- pin: exists_bound_iteratedFDeriv_cpow_neg_radC_mul (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1800)
theorem exists_bound_iteratedFDeriv_cpow_neg_radC_mul (hg : g.det ≠ 0) (u : ℂ)
    {P : ℂ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖iteratedFDeriv ℝ n P z‖ ≤ C) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun w => ((radC g w : ℂ) ^ (-u)) * P w) z‖
        ≤ C * radC g z ^ (-u.re) := by
  intro n
  choose Cf hCf using fun i => exists_bound_iteratedFDeriv_cpow_neg_radC hg u i
  choose Ch hCh using hPB
  have hpos : (0:ℝ) < ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * Ch (n - i) := by
    refine Finset.sum_pos (fun i hi => ?_) ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
    have h1 : (0:ℝ) < (n.choose i : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    exact mul_pos (mul_pos h1 (hCf i).1) (hCh (n - i)).1
  refine ⟨_, hpos, fun z => ?_⟩
  have hrad := radC_pos' hg z
  refine (norm_iteratedFDeriv_mul_le (contDiff_cpow_neg_radC hg u) hPC z
    (mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  calc (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i (fun w => ((radC g w : ℂ)) ^ (-u)) z‖
        * ‖iteratedFDeriv ℝ (n - i) P z‖
      ≤ (n.choose i : ℝ) * (Cf i * radC g z ^ (-u.re)) * Ch (n - i) := by
        gcongr
        · exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (hCf i).1.le (Real.rpow_nonneg hrad.le _))
        · exact (hCf i).2 z
        · exact (hCh (n - i)).2 z
    _ = (n.choose i : ℝ) * Cf i * Ch (n - i) * radC g z ^ (-u.re) := by ring

-- pin: norm_fourierIntegral_cpow_radC_mul_le_polyDecay (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1831)
theorem norm_fourierIntegral_cpow_radC_mul_le_polyDecay
    (hg : g.det ≠ 0) {u : ℂ} (hu : 2 < u.re)
    {P : ℂ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖iteratedFDeriv ℝ n P z‖ ≤ C)
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℂ, ∃ v : ℂ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℂ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun z => ((radC g z : ℂ) ^ (-u)) * P z) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  set f : ℂ → ℂ := fun z => ((radC g z : ℂ) ^ (-u)) * P z with hfdef

  obtain ⟨CB, hCB⟩ := Classical.axiom_of_choice
    (fun n => exists_bound_iteratedFDeriv_cpow_neg_radC_mul hg u hPC hPB n)
  have hintr : Integrable (fun z => radC g z ^ (-u.re)) volume :=
    integrable_rpow_neg_radC hg hu
  have hfC : ContDiff ℝ ∞ f := (contDiff_cpow_neg_radC hg u).mul hPC
  have hfCn : ContDiff ℝ (N : ℕ∞) f := hfC.of_le (mod_cast le_top)
  have h'f : ∀ j : ℕ, j ≤ N → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) volume := by
    intro j _
    refine (hintr.const_mul (CB j)).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (hfC.continuous_iteratedFDeriv (mod_cast le_top)).norm.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (hCB j).2 z

  have key := MeasureTheory.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive L
    (f := f) hfCn h'f hc.le hL
  set MN : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume
  have hMN0 : (0:ℝ) ≤ MN :=
    mul_nonneg (pow_nonneg (by norm_num) N)
      (Finset.sum_nonneg fun j _ => integral_nonneg fun v => norm_nonneg _)

  have hfint : Integrable f volume := by
    refine (hintr.const_mul (CB 0)).mono' hfC.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h0 := (hCB 0).2 z
    rwa [norm_iteratedFDeriv_zero] at h0
  set M0 : ℝ := ∫ v, ‖f v‖ ∂volume
  have hM00 : (0:ℝ) ≤ M0 := integral_nonneg fun v => norm_nonneg _
  refine ⟨(M0 * 2 ^ N + MN * (2 / c) ^ N) + 1, by positivity, fun ξ => ?_⟩
  have hξ0 : (0:ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have h1ξ : (0:ℝ) < 1 + ‖ξ‖ := by linarith
  have hrpow0 : (0:ℝ) < (1 + ‖ξ‖) ^ (-(N:ℝ)) := Real.rpow_pos_of_pos h1ξ _
  rcases lt_or_ge ‖ξ‖ 1 with hlt | hge
  ·
    have hbd : (2:ℝ) ^ (-(N:ℝ)) ≤ (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos h1ξ (by linarith)
        (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep1 : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ M0 :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hstep2 : (M0 : ℝ) = M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := by
      rw [mul_assoc, show ((2:ℝ)^N : ℝ) = (2:ℝ)^(N:ℝ) from (Real.rpow_natCast 2 N).symm,
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2), add_neg_cancel, Real.rpow_zero, mul_one]
    have hstep3 : M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ))
        ≤ M0 * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hbd
        (mul_nonneg hM00 (pow_nonneg (by norm_num) N))
    have hstep4 : (M0 * 2 ^ N : ℝ) ≤ M0 * 2 ^ N + MN * (2 / c) ^ N + 1 := by
      nlinarith [mul_nonneg hMN0
        (pow_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le) N)]
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ M0 := hstep1
      _ = M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := hstep2
      _ ≤ M0 * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := hstep3
      _ ≤ (M0 * 2 ^ N + MN * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le
  ·
    have hkey := key ξ
    have hcξ : (0:ℝ) < c * ‖ξ‖ := mul_pos hc (by linarith)
    have hdiv : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := by
      rw [Real.rpow_neg hcξ.le, Real.rpow_natCast, ← div_eq_mul_inv,
        le_div_iff₀ (pow_pos hcξ N), mul_comm]
      exact hkey
    have h2 : (1:ℝ) + ‖ξ‖ ≤ 2 * ‖ξ‖ := by linarith
    have hcmp : (c * ‖ξ‖) ^ (-(N:ℝ)) ≤ (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by
      have hsplit : (c * ‖ξ‖ : ℝ) = (c / 2) * (2 * ‖ξ‖) := by ring
      rw [hsplit, Real.mul_rpow (div_nonneg hc.le (by norm_num)) (by linarith)]
      have hp1 : ((c / 2 : ℝ)) ^ (-(N:ℝ)) = (2 / c) ^ N := by
        rw [Real.rpow_neg (div_nonneg hc.le (by norm_num)), Real.rpow_natCast,
          ← inv_pow, inv_div]
      rw [hp1]
      refine mul_le_mul_of_nonneg_left ?_
        (pow_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le) N)
      exact Real.rpow_le_rpow_of_nonpos h1ξ h2 (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep4 : (MN * (2 / c) ^ N : ℝ) ≤ M0 * 2 ^ N + MN * (2 / c) ^ N + 1 := by
      nlinarith [mul_nonneg hM00 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) N)]
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := hdiv
      _ ≤ MN * ((2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ))) :=
          mul_le_mul_of_nonneg_left hcmp hMN0
      _ = MN * (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by ring
      _ ≤ (M0 * 2 ^ N + MN * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le

end CplxDecay

namespace Engine

open MeasureTheory CplxSmooth Real VectorFourier Complex
open scoped FourierTransform

-- pin: exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact (S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean:229)
theorem exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (κ₀ κ₁ : ℝ) (_hκ₀ : 2 < κ₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ g ∈ 𝒢, ∀ κ : ℝ, κ₀ ≤ κ → κ ≤ κ₁ →
      Integrable (fun z : ℂ => radC g z ^ (-κ)) ∧ ∫ z : ℂ, radC g z ^ (-κ) ≤ M :=
  B2bCL2.main 𝒢 _h𝒢 _hdet κ₀ κ₁ _hκ₀

-- pin: norm_fourierIntegral_cpow_radC_mul_le_polyDecay (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1939)
theorem norm_fourierIntegral_cpow_radC_mul_le_polyDecay
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) {u : ℂ} (hu : 2 < u.re)
    {P : ℂ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖iteratedFDeriv ℝ n P z‖ ≤ C)
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℂ, ∃ v : ℂ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℂ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun z => ((radC g z : ℂ) ^ (-u)) * P z) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  @CplxDecay.norm_fourierIntegral_cpow_radC_mul_le_polyDecay g hg u hu P hPC hPB L c hc hL N

end Engine


end AutomorphicForm.ComplexIwasawa

end
