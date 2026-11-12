/-
  Near-zero growth bounds for three linear ODEs of the local Whittaker analysis.

  Each of the three statements is the same phenomenon at a different equation: on `(0, 1]` a solution
  whose inhomogeneity is bounded by a power of `y` is bounded by a power of `y`, with the exponent the
  one forced by the indicial data, up to an `ε`:
  a first-order equation `y f' = b f + h` (indicial exponent `Re b` against the forcing's `σ`), a
  first-order system `y F' = A F + B F` with diagonal leading part bounded below by `r₀` and an
  off-diagonal part of order `y ^ τ`, and the Bessel-type second-order equation
  `y ^ 2 f'' + (1 / 4 - ν ^ 2 - 4 π ^ 2 y ^ 2) f = h`, where an a-priori bound feeds the bootstrap.

  These are the elementary bounds the torus-system growth estimates for Whittaker coefficients rest on.

  The pin writes the first-order argument `y f' = b f + h` twice — `OdeCAux.main` (euler file `:19`) and
  `Gap41.odeC` (bessel file `:16`) — with identical statements; the port proves it once, at
  `OdeCAux.main`, and keeps the pin's second name as one application.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing.lean` (128 lines),
  `P2M/Sol/S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag.lean` (240) and
  `P2M/Sol/S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori.lean` (420),
  with the statements from their wrappers `Theorems/Thm_LanglandsTunnell_*.lean`.

  spec-pin: Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing.lean
  spec-pin: Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag.lean
  spec-pin: Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori.lean
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false

open scoped Real

noncomputable section

namespace LanglandsTunnell

namespace OdeCAux

open Real Set

theorem main (b : ℂ) (σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + h y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min b.re σ - ε) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = b.re - min b.re σ + ε := ⟨_, rfl⟩
  have hδpos : 0 < δ := by have := min_le_left b.re σ; linarith
  have hρσδ : b.re - σ ≤ δ := by have := min_le_right b.re σ; linarith
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = max A 0 := ⟨_, rfl⟩
  have hA'0 : 0 ≤ A' := hA' ▸ le_max_right _ _
  have hAA' : A ≤ A' := hA' ▸ le_max_left _ _
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = ‖f 1‖ + A' / δ := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity

  set G : ℝ → ℂ := fun t => Complex.exp (b * (t : ℂ)) * f (Real.exp (-t)) with hG
  set G' : ℝ → ℂ := fun t => -(Complex.exp (b * (t : ℂ)) * h (Real.exp (-t))) with hG'
  have hGder : ∀ t : ℝ, HasDerivAt G (G' t) t := by
    intro t
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp (b * (s : ℂ))) (Complex.exp (b * (t : ℂ)) * b) t := by
      have h0 : HasDerivAt (fun s : ℝ => b * (s : ℂ)) b t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul b
      exact h0.cexp
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have h3 : HasDerivAt f (deriv f (Real.exp (-t))) (Real.exp (-t)) :=
      (hf.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
    have h4 : HasDerivAt (fun s : ℝ => f (Real.exp (-s))) ((-Real.exp (-t)) • deriv f (Real.exp (-t))) t :=
      h3.scomp t h2
    have key := hfeq (Real.exp (-t)) hy
    refine (h1.mul h4).congr_deriv ?_
    simp only [hG', Complex.real_smul, Complex.ofReal_neg]
    linear_combination (-Complex.exp (b * (t : ℂ))) * key

  set B : ℝ → ℝ := fun t => C₀ * Real.exp (δ * t) with hB
  set B' : ℝ → ℝ := fun t => C₀ * (Real.exp (δ * t) * δ) with hB'
  have hBder : ∀ t : ℝ, HasDerivAt B (B' t) t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => δ * s) δ t := by simpa using (hasDerivAt_id t).const_mul δ
    exact h0.exp.const_mul C₀
  have hG0 : G 0 = f 1 := by simp [hG]

  have hbound : ∀ t : ℝ, 0 ≤ t → ‖G' t‖ ≤ B' t := by
    intro t ht
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have hy1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have hre : (b * (t : ℂ)).re = b.re * t := by simp [Complex.mul_re]
    have hnorm : ‖G' t‖ = Real.exp (b.re * t) * ‖h (Real.exp (-t))‖ := by
      simp only [hG', norm_neg, norm_mul, Complex.norm_exp, hre]
    have hh' : ‖h (Real.exp (-t))‖ ≤ A' * Real.exp (-t * σ) := by
      have h1 := hh (Real.exp (-t)) hy hy1
      rw [← Real.exp_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right hAA' (Real.exp_pos _).le)
    have hC₀B' : B' t = (‖f 1‖ * δ + A') * Real.exp (δ * t) := by
      simp only [hB']
      rw [hC₀]
      field_simp
    calc ‖G' t‖ = Real.exp (b.re * t) * ‖h (Real.exp (-t))‖ := hnorm
      _ ≤ Real.exp (b.re * t) * (A' * Real.exp (-t * σ)) :=
          mul_le_mul_of_nonneg_left hh' (Real.exp_pos _).le
      _ = A' * Real.exp ((b.re - σ) * t) := by
          rw [show (b.re - σ) * t = b.re * t + -t * σ by ring, Real.exp_add]; ring
      _ ≤ A' * Real.exp (δ * t) := by
          apply mul_le_mul_of_nonneg_left _ hA'0
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hρσδ ht)
      _ ≤ (‖f 1‖ * δ + A') * Real.exp (δ * t) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have : 0 ≤ ‖f 1‖ * δ := mul_nonneg (norm_nonneg _) hδpos.le
          linarith
      _ = B' t := hC₀B'.symm
  refine ⟨C₀, fun y hy hy1 => ?_⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = -Real.log y := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; have := Real.log_nonpos hy.le hy1; linarith
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := T)
    (fun t _ => (hGder t).continuousAt.continuousWithinAt)
    (fun t _ => (hGder t).hasDerivWithinAt)
    (B := B) (B' := B') (by rw [hG0]; simp only [hB, mul_zero, Real.exp_zero, mul_one, hC₀]; linarith [div_nonneg hA'0 hδpos.le])
    hBder (fun t ht => hbound t ht.1) (x := T) ⟨hT0, le_rfl⟩

  have e1 : Real.exp (-T) = y := by rw [hT, neg_neg, Real.exp_log hy]
  have e2 : ∀ c : ℝ, Real.exp (c * T) = y ^ (-c) := fun c => by
    rw [Real.rpow_def_of_pos hy, hT]; congr 1; ring
  have hre : (b * (T : ℂ)).re = b.re * T := by simp [Complex.mul_re]
  have hGT : ‖G T‖ = y ^ (-b.re) * ‖f y‖ := by
    simp only [hG, norm_mul, Complex.norm_exp, hre, e1, e2]
  have hBT : B T = C₀ * y ^ (-δ) := by simp only [hB, e2]
  rw [hGT, hBT] at hfence
  have hyρ : 0 < y ^ b.re := Real.rpow_pos_of_pos hy _
  have hsplit : ‖f y‖ = y ^ b.re * (y ^ (-b.re) * ‖f y‖) := by
    rw [Real.rpow_neg hy.le, ← mul_assoc, mul_inv_cancel₀ hyρ.ne', one_mul]
  rw [hsplit]
  calc y ^ b.re * (y ^ (-b.re) * ‖f y‖) ≤ y ^ b.re * (C₀ * y ^ (-δ)) :=
        mul_le_mul_of_nonneg_left hfence hyρ.le
    _ = C₀ * (y ^ b.re * y ^ (-δ)) := by ring
    _ = C₀ * y ^ (min b.re σ - ε) := by
        rw [← Real.rpow_add hy]
        congr 2
        rw [hδ]; ring

end OdeCAux

namespace OdeEAux

open Real Set

theorem re_inner_le (z s a : ℂ) (r₀ : ℝ) (ha : r₀ ≤ a.re) :
    2 * (z.re * (((r₀ : ℂ) - a) * z - s).re + z.im * (((r₀ : ℂ) - a) * z - s).im) ≤ 2 * (‖z‖ * ‖s‖) := by
  have h1 : z.re * (((r₀ : ℂ) - a) * z - s).re + z.im * (((r₀ : ℂ) - a) * z - s).im =
      (r₀ - a.re) * (z.re ^ 2 + z.im ^ 2) - (z * (starRingEnd ℂ) s).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have h2 : (r₀ - a.re) * (z.re ^ 2 + z.im ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h3 : -(z * (starRingEnd ℂ) s).re ≤ ‖z‖ * ‖s‖ := by
    have h := Complex.abs_re_le_norm (z * (starRingEnd ℂ) s)
    rw [norm_mul, Complex.norm_conj] at h
    have := neg_abs_le (z * (starRingEnd ℂ) s).re
    linarith
  rw [h1]
  linarith

theorem main (m : ℕ) (a : Fin m → ℂ) (r₀ c τ : ℝ) (hτ : 0 < τ) (ha : ∀ i, r₀ ≤ (a i).re)
    (B : ℝ → Matrix (Fin m) (Fin m) ℂ) (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j, ‖B y i j‖ ≤ c * y ^ τ)
    (F : Fin m → ℝ → ℂ) (hF : ∀ i, DifferentiableOn ℝ (F i) (Set.Ioi 0))
    (hFeq : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i,
      (y : ℂ) * deriv (F i) y = a i * F i y + ∑ j, B y i j * F j y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, ‖F i y‖ ≤ C * y ^ (r₀ - ε) := by

  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = max c 0 := ⟨_, rfl⟩
  have hc'0 : 0 ≤ c' := hc' ▸ le_max_right _ _
  have hcc' : c ≤ c' := hc' ▸ le_max_left _ _
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * c' * m / τ := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity

  set G : Fin m → ℝ → ℂ := fun i t => Complex.exp ((r₀ : ℂ) * (t : ℂ)) * F i (Real.exp (-t)) with hG
  set G' : Fin m → ℝ → ℂ := fun i t =>
    ((r₀ : ℂ) - a i) * G i t - ∑ j, B (Real.exp (-t)) i j * G j t with hG'

  have hGraw : ∀ (i : Fin m) (t : ℝ), HasDerivAt (G i)
      (Complex.exp ((r₀ : ℂ) * (t : ℂ)) * (r₀ : ℂ) * F i (Real.exp (-t)) +
        Complex.exp ((r₀ : ℂ) * (t : ℂ)) * ((-Real.exp (-t)) • deriv (F i) (Real.exp (-t)))) t := by
    intro i t
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp ((r₀ : ℂ) * (s : ℂ))) (Complex.exp ((r₀ : ℂ) * (t : ℂ)) * (r₀ : ℂ)) t := by
      have h0 : HasDerivAt (fun s : ℝ => (r₀ : ℂ) * (s : ℂ)) (r₀ : ℂ) t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (r₀ : ℂ)
      exact h0.cexp
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have h3 : HasDerivAt (F i) (deriv (F i) (Real.exp (-t))) (Real.exp (-t)) :=
      ((hF i).differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
    have h4 : HasDerivAt (fun s : ℝ => F i (Real.exp (-s))) ((-Real.exp (-t)) • deriv (F i) (Real.exp (-t))) t :=
      h3.scomp t h2
    exact h1.mul h4
  have hGder : ∀ (i : Fin m) (t : ℝ), 0 ≤ t → HasDerivAt (G i) (G' i t) t := by
    intro i t ht
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have hy1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have key := hFeq (Real.exp (-t)) hy hy1 i
    refine (hGraw i t).congr_deriv ?_
    have hs : ∑ j, B (Real.exp (-t)) i j * G j t =
        Complex.exp ((r₀ : ℂ) * (t : ℂ)) * ∑ j, B (Real.exp (-t)) i j * F j (Real.exp (-t)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [hG]; ring
    simp only [hG', hs, Complex.real_smul, Complex.ofReal_neg]
    linear_combination (-Complex.exp ((r₀ : ℂ) * (t : ℂ))) * key
  have hGcont : ∀ i : Fin m, Continuous (G i) := fun i =>
    continuous_iff_continuousAt.2 fun t => (hGraw i t).continuousAt

  set E : ℝ → ℝ := fun t => ∑ i, ((G i t).re ^ 2 + (G i t).im ^ 2) with hE
  set E' : ℝ → ℝ := fun t => ∑ i, 2 * ((G i t).re * (G' i t).re + (G i t).im * (G' i t).im) with hE'
  have hEnorm : ∀ t, E t = ∑ i, ‖G i t‖ ^ 2 := fun t =>
    Finset.sum_congr rfl fun i _ => by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hEder : ∀ t : ℝ, 0 ≤ t → HasDerivAt E (E' t) t := by
    intro t ht
    have hterm : ∀ i ∈ Finset.univ, HasDerivAt (fun s => (G i s).re ^ 2 + (G i s).im ^ 2)
        (2 * ((G i t).re * (G' i t).re + (G i t).im * (G' i t).im)) t := by
      intro i _
      have hre : HasDerivAt (fun s => (G i s).re) (G' i t).re t := by
        have h__af := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hGder i t ht))
        simp at h__af
        exact h__af
      have him : HasDerivAt (fun s => (G i s).im) (G' i t).im t := by
        have h__af := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hGder i t ht))
        simp at h__af
        exact h__af
      have h := (hre.pow 2).add (him.pow 2)
      refine h.congr_deriv ?_
      push_cast
      ring
    have h := HasDerivAt.fun_sum hterm
    exact h
  have hEcont : Continuous E := by
    simp only [hE]
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((Complex.continuous_re.comp (hGcont i)).pow 2).add ((Complex.continuous_im.comp (hGcont i)).pow 2)

  have hE'le : ∀ t : ℝ, 0 ≤ t → E' t ≤ (2 * c' * m * Real.exp (-(τ * t))) * E t := by
    intro t ht
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have hy1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have hyτ : Real.exp (-t) ^ τ = Real.exp (-(τ * t)) := by rw [← Real.exp_mul]; ring_nf
    set S := ∑ j, ‖G j t‖ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => norm_nonneg _

    have hsi : ∀ i, ‖∑ j, B (Real.exp (-t)) i j * G j t‖ ≤ c' * Real.exp (-(τ * t)) * S := by
      intro i
      calc ‖∑ j, B (Real.exp (-t)) i j * G j t‖ ≤ ∑ j, ‖B (Real.exp (-t)) i j * G j t‖ := norm_sum_le _ _
        _ ≤ ∑ j, (c' * Real.exp (-(τ * t))) * ‖G j t‖ := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            have h := hB (Real.exp (-t)) hy hy1 i j
            rw [hyτ] at h
            exact h.trans (mul_le_mul_of_nonneg_right hcc' (Real.exp_pos _).le)
        _ = c' * Real.exp (-(τ * t)) * S := by rw [hS, Finset.mul_sum]
    have hcomp : ∀ i, 2 * ((G i t).re * (G' i t).re + (G i t).im * (G' i t).im) ≤
        2 * (‖G i t‖ * (c' * Real.exp (-(τ * t)) * S)) := by
      intro i
      have h := re_inner_le (G i t) (∑ j, B (Real.exp (-t)) i j * G j t) (a i) r₀ (ha i)
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hsi i) (norm_nonneg _)) (by norm_num)
    calc E' t = ∑ i, 2 * ((G i t).re * (G' i t).re + (G i t).im * (G' i t).im) := rfl
      _ ≤ ∑ i, 2 * (‖G i t‖ * (c' * Real.exp (-(τ * t)) * S)) := Finset.sum_le_sum fun i _ => hcomp i
      _ = 2 * c' * Real.exp (-(τ * t)) * S ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, ← hS]; ring
      _ ≤ 2 * c' * Real.exp (-(τ * t)) * (m * E t) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hEnorm t, hS]
          simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖G j t‖))
      _ = (2 * c' * m * Real.exp (-(τ * t))) * E t := by ring

  set Φ : ℝ → ℝ := fun t => L * (1 - Real.exp (-(τ * t))) with hΦ
  set W : ℝ → ℝ := fun t => Real.exp (-Φ t) * E t with hW
  set W' : ℝ → ℝ := fun t => Real.exp (-Φ t) * (E' t - (2 * c' * m * Real.exp (-(τ * t))) * E t) with hW'
  have hΦder : ∀ t, HasDerivAt Φ (2 * c' * m * Real.exp (-(τ * t))) t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => -(τ * s)) (-τ) t := by
      have h__af := ((hasDerivAt_id t).const_mul τ).neg
      simp at h__af
      exact h__af
    have h1 := ((h0.exp).const_sub 1).const_mul L
    refine h1.congr_deriv ?_
    rw [hL]; field_simp
  have hWder : ∀ t, 0 ≤ t → HasDerivAt W (W' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => Real.exp (-Φ s)) (Real.exp (-Φ t) * -(2 * c' * m * Real.exp (-(τ * t)))) t :=
      (hΦder t).neg.exp
    have h := h1.mul (hEder t ht)
    refine h.congr_deriv ?_
    simp only [hW']
    ring
  have hWcont : Continuous W := by
    have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun t => (hΦder t).continuousAt
    exact (Real.continuous_exp.comp hΦc.neg).mul hEcont
  have hW'le : ∀ t, 0 ≤ t → W' t ≤ 0 := by
    intro t ht
    have h := hE'le t ht
    have : E' t - (2 * c' * m * Real.exp (-(τ * t))) * E t ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this
  have hW0 : W 0 = E 0 := by simp [hW, hΦ]

  refine ⟨Real.sqrt (E 0 * Real.exp L), fun y hy hy1 i => ?_⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = -Real.log y := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; have := Real.log_nonpos hy.le hy1; linarith
  have hfence := image_le_of_deriv_right_le_deriv_boundary (f := W) (f' := W') (a := 0) (b := T)
    hWcont.continuousOn (fun t ht => (hWder t ht.1).hasDerivWithinAt)
    (B := fun _ => E 0) (B' := fun _ => 0) (by rw [hW0]) continuousOn_const
    (fun t _ => (hasDerivAt_const t (E 0)).hasDerivWithinAt) (fun t ht => hW'le t ht.1) (x := T) ⟨hT0, le_rfl⟩

  have hE0 : 0 ≤ E 0 := by rw [hEnorm]; exact Finset.sum_nonneg fun i _ => by positivity
  have hΦT : Φ T ≤ L := by
    simp only [hΦ]
    have : 0 ≤ Real.exp (-(τ * T)) := (Real.exp_pos _).le
    nlinarith
  have hET : E T ≤ E 0 * Real.exp L := by
    have h1 : Real.exp (-Φ T) * E T ≤ E 0 := hfence
    have h2 : E T = Real.exp (Φ T) * (Real.exp (-Φ T) * E T) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    rw [h2]
    calc Real.exp (Φ T) * (Real.exp (-Φ T) * E T) ≤ Real.exp (Φ T) * E 0 :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ ≤ Real.exp L * E 0 := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hΦT) hE0
      _ = E 0 * Real.exp L := mul_comm _ _

  have hGi : ‖G i T‖ ^ 2 ≤ E 0 * Real.exp L := by
    have h1 : ‖G i T‖ ^ 2 ≤ E T := by
      rw [hEnorm]
      exact Finset.single_le_sum (f := fun j => ‖G j T‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
    exact h1.trans hET
  have hGi' : ‖G i T‖ ≤ Real.sqrt (E 0 * Real.exp L) := by
    rw [← Real.sqrt_sq (norm_nonneg (G i T))]
    exact Real.sqrt_le_sqrt hGi

  have e1 : Real.exp (-T) = y := by rw [hT, neg_neg, Real.exp_log hy]
  have e2 : Real.exp (r₀ * T) = y ^ (-r₀) := by
    rw [Real.rpow_def_of_pos hy, hT]; congr 1; ring
  have hre : ((r₀ : ℂ) * (T : ℂ)).re = r₀ * T := by simp [Complex.mul_re]
  have hGT : ‖G i T‖ = y ^ (-r₀) * ‖F i y‖ := by
    simp only [hG, norm_mul, Complex.norm_exp, hre, e1, e2]
  rw [hGT] at hGi'
  have hyρ : 0 < y ^ r₀ := Real.rpow_pos_of_pos hy _
  have hsplit : ‖F i y‖ = y ^ r₀ * (y ^ (-r₀) * ‖F i y‖) := by
    rw [Real.rpow_neg hy.le, ← mul_assoc, mul_inv_cancel₀ hyρ.ne', one_mul]
  rw [hsplit]
  calc y ^ r₀ * (y ^ (-r₀) * ‖F i y‖) ≤ y ^ r₀ * Real.sqrt (E 0 * Real.exp L) :=
        mul_le_mul_of_nonneg_left hGi' hyρ.le
    _ = Real.sqrt (E 0 * Real.exp L) * y ^ r₀ := mul_comm _ _
    _ ≤ Real.sqrt (E 0 * Real.exp L) * y ^ (r₀ - ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)) (Real.sqrt_nonneg _)

end OdeEAux

namespace Gap41

open Real Set Filter

open scoped Topology

theorem odeC (b : ℂ) (σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + h y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min b.re σ - ε) :=
  OdeCAux.main b σ A f h hf hh hfeq ε hε

theorem gapC (b : ℂ) (m K r B : ℝ) (hr : b.re < r) (f u : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hu : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖u y‖ ≤ K * y ^ m)
    (hap : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ r)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + u y) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ m := by
  set β : ℝ := b.re with hβ
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  rcases le_or_gt m β with hm | hm
  ·
    refine ⟨max B 0, fun y hy hy1 => ?_⟩
    calc ‖f y‖ ≤ B * y ^ r := hap y hy hy1
      _ ≤ max B 0 * y ^ r := by gcongr; exact le_max_left _ _
      _ ≤ max B 0 * y ^ m := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)) hB0
  ·
    set F : ℝ → ℂ := fun s => f (Real.exp (-s)) with hF
    set G : ℝ → ℂ := fun s => Complex.exp (b * (s : ℂ)) * F s with hG
    have hGd : ∀ s : ℝ, HasDerivAt G (-(Complex.exp (b * (s : ℂ)) * u (Real.exp (-s)))) s := by
      intro s
      have hy : 0 < Real.exp (-s) := Real.exp_pos _
      have hfd : HasDerivAt f (deriv f (Real.exp (-s))) (Real.exp (-s)) :=
        (hf.differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt
      have hu' : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s := by
        have h__af := (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
        simp at h__af
        exact h__af
      have hFd : HasDerivAt F ((-Real.exp (-s)) • deriv f (Real.exp (-s))) s := hfd.scomp s hu'
      have he : HasDerivAt (fun s : ℝ => Complex.exp (b * (s : ℂ))) (Complex.exp (b * (s : ℂ)) * b) s := by
        have h1 : HasDerivAt (fun s : ℝ => b * (s : ℂ)) b s := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul b
        exact (Complex.hasDerivAt_exp (b * (s : ℂ))).comp s h1
      have h := he.mul hFd
      refine h.congr_deriv ?_
      have key := hfeq (Real.exp (-s)) hy
      simp only [hF, Complex.real_smul, Complex.ofReal_neg]
      linear_combination (-Complex.exp (b * (s : ℂ))) * key

    have hG'b : ∀ τ : ℝ, 0 ≤ τ → ‖-(Complex.exp (b * (τ : ℂ)) * u (Real.exp (-τ)))‖ ≤ max K 0 * Real.exp ((β - m) * τ) := by
      intro τ hτ
      have hy : 0 < Real.exp (-τ) := Real.exp_pos _
      have hy1 : Real.exp (-τ) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      rw [norm_neg, norm_mul, Complex.norm_exp, show (b * (τ : ℂ)).re = β * τ by simp [hβ, Complex.mul_re]]
      calc Real.exp (β * τ) * ‖u (Real.exp (-τ))‖ ≤ Real.exp (β * τ) * (max K 0 * Real.exp (-τ) ^ m) := by
            gcongr
            calc ‖u (Real.exp (-τ))‖ ≤ K * Real.exp (-τ) ^ m := hu _ hy hy1
              _ ≤ max K 0 * Real.exp (-τ) ^ m := by gcongr; exact le_max_left _ _
        _ = max K 0 * Real.exp ((β - m) * τ) := by
            rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]; ring_nf

    have hmβ : 0 < m - β := by linarith
    set K' : ℝ := max K 0 with hK'
    have hseg : ∀ s T : ℝ, 0 ≤ s → s ≤ T →
        ‖G T - G s‖ ≤ K' / (m - β) * (Real.exp ((β - m) * s) - Real.exp ((β - m) * T)) := by
      intro s T hs hsT
      set φ : ℝ → ℂ := fun τ => G τ - G s with hφ
      set Bf : ℝ → ℝ := fun τ => K' / (m - β) * (Real.exp ((β - m) * s) - Real.exp ((β - m) * τ)) with hBf
      have hφc : ContinuousOn φ (Icc s T) := fun τ _ =>
        (((hGd τ).continuousAt).sub continuousAt_const).continuousWithinAt
      have hφd : ∀ τ ∈ Ico s T, HasDerivWithinAt φ (-(Complex.exp (b * (τ : ℂ)) * u (Real.exp (-τ)))) (Ici τ) τ :=
        fun τ _ => ((hGd τ).sub_const (G s)).hasDerivWithinAt
      have hφs : ‖φ s‖ ≤ Bf s := by simp [hφ, hBf]
      have hBd : ∀ τ : ℝ, HasDerivAt Bf (K' * Real.exp ((β - m) * τ)) τ := by
        intro τ
        have h1 : HasDerivAt (fun τ : ℝ => Real.exp ((β - m) * τ)) (Real.exp ((β - m) * τ) * (β - m)) τ := by
          have hl : HasDerivAt (fun τ : ℝ => (β - m) * τ) (β - m) τ := by
            simpa using (hasDerivAt_id τ).const_mul (β - m)
          exact (Real.hasDerivAt_exp _).comp τ hl
        have h2 := (h1.const_sub (Real.exp ((β - m) * s))).const_mul (K' / (m - β))
        have hmβ' : m - β ≠ 0 := hmβ.ne'
        refine h2.congr_deriv ?_
        field_simp
        ring
      have hbound : ∀ τ ∈ Ico s T, ‖-(Complex.exp (b * (τ : ℂ)) * u (Real.exp (-τ)))‖ ≤ K' * Real.exp ((β - m) * τ) :=
        fun τ hτ => hG'b τ (hs.trans hτ.1)
      have := image_norm_le_of_norm_deriv_right_le_deriv_boundary hφc hφd hφs hBd hbound
        (right_mem_Icc.mpr hsT)
      simpa [hφ, hBf] using this

    have hGT : ∀ T : ℝ, 0 ≤ T → ‖G T‖ ≤ max B 0 * Real.exp ((β - r) * T) := by
      intro T hT
      have hy : 0 < Real.exp (-T) := Real.exp_pos _
      have hy1 : Real.exp (-T) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      simp only [hG, hF]
      rw [norm_mul, Complex.norm_exp, show (b * (T : ℂ)).re = β * T by simp [hβ, Complex.mul_re]]
      calc Real.exp (β * T) * ‖f (Real.exp (-T))‖ ≤ Real.exp (β * T) * (max B 0 * Real.exp (-T) ^ r) := by
            gcongr
            calc ‖f (Real.exp (-T))‖ ≤ B * Real.exp (-T) ^ r := hap _ hy hy1
              _ ≤ max B 0 * Real.exp (-T) ^ r := by gcongr; exact le_max_left _ _
        _ = max B 0 * Real.exp ((β - r) * T) := by
            rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]; ring_nf
    have htend : ∀ s : ℝ, Tendsto (fun T : ℝ => K' / (m - β) * (Real.exp ((β - m) * s) - Real.exp ((β - m) * T)) +
        max B 0 * Real.exp ((β - r) * T)) atTop (𝓝 (K' / (m - β) * (Real.exp ((β - m) * s) - 0) + max B 0 * 0)) := by
      intro s
      have h1 : Tendsto (fun T : ℝ => Real.exp ((β - m) * T)) atTop (𝓝 0) := by
        have hlin : Tendsto (fun T : ℝ => (β - m) * T) atTop atBot :=
          (tendsto_id.const_mul_atTop_of_neg (show β - m < 0 by linarith))
        exact Real.tendsto_exp_atBot.comp hlin
      have h2 : Tendsto (fun T : ℝ => Real.exp ((β - r) * T)) atTop (𝓝 0) := by
        have hlin : Tendsto (fun T : ℝ => (β - r) * T) atTop atBot :=
          (tendsto_id.const_mul_atTop_of_neg (show β - r < 0 by linarith))
        exact Real.tendsto_exp_atBot.comp hlin
      exact ((tendsto_const_nhds.sub h1).const_mul _).add (h2.const_mul _)
    have hGs : ∀ s : ℝ, 0 ≤ s → ‖G s‖ ≤ K' / (m - β) * Real.exp ((β - m) * s) := by
      intro s hs
      have hlim := htend s
      simp only [sub_zero, mul_zero, add_zero] at hlim
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop s] with T hT
      have h1 : ‖G s‖ ≤ ‖G T - G s‖ + ‖G T‖ := by
        have := norm_sub_le (G T - G s) (G T); simp only [sub_sub_cancel_left, norm_neg] at this; exact this
      linarith [hseg s T hs hT, hGT T (hs.trans hT)]

    refine ⟨K' / (m - β), fun y hy hy1 => ?_⟩
    set s : ℝ := -Real.log y with hsdef
    have hs0 : 0 ≤ s := by rw [hsdef, neg_nonneg]; exact Real.log_nonpos hy.le hy1
    have hys : Real.exp (-s) = y := by rw [hsdef, neg_neg, Real.exp_log hy]
    have hfy : ‖f y‖ = Real.exp (-(β * s)) * ‖G s‖ := by
      rw [show f y = F s by simp [hF, hys], hG]
      simp only
      rw [norm_mul, Complex.norm_exp, show (b * (s : ℂ)).re = β * s by simp [hβ, Complex.mul_re], ← mul_assoc,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    have hpow : Real.exp (-(β * s)) * Real.exp ((β - m) * s) = y ^ m := by
      rw [← Real.exp_add, Real.rpow_def_of_pos hy, hsdef]; ring_nf
    calc ‖f y‖ = Real.exp (-(β * s)) * ‖G s‖ := hfy
      _ ≤ Real.exp (-(β * s)) * (K' / (m - β) * Real.exp ((β - m) * s)) := by gcongr; exact hGs s hs0
      _ = K' / (m - β) * y ^ m := by rw [← hpow]; ring

theorem twoTermAp (ν : ℂ) (σ A ρ B : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hap : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ ρ)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (ρ + 2) - ε) := by
  have hO : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  set u : ℝ → ℂ := fun y => (y : ℂ) * deriv f y - (1 / 2 - ν) * f y with hu
  set h₂ : ℝ → ℂ := fun y => h y + 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * f y with hh₂
  have hud : ∀ y : ℝ, 0 < y →
      HasDerivAt u (deriv f y + (y : ℂ) * deriv (deriv f) y - (1 / 2 - ν) * deriv f y) y := by
    intro y hy
    have h1 : HasDerivAt f (deriv f y) y := (hf.differentiableAt (hO.mem_nhds hy)).hasDerivAt
    have h2 : HasDerivAt (deriv f) (deriv (deriv f) y) y := (hf'.differentiableAt (hO.mem_nhds hy)).hasDerivAt
    have hc : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
    have h3 := (hc.mul h2).sub (h1.const_mul (1 / 2 - ν))
    refine h3.congr_deriv ?_
    ring
  have hudiff : DifferentiableOn ℝ u (Ioi 0) := fun y hy => (hud y hy).differentiableAt.differentiableWithinAt
  have hueq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv u y = (1 / 2 + ν) * u y + h₂ y := by
    intro y hy
    rw [(hud y hy).deriv]
    simp only [hu, hh₂]
    linear_combination hfeq y hy
  set σ₂ : ℝ := min σ (ρ + 2) with hσ₂
  set A₂ : ℝ := max A 0 + 4 * π ^ 2 * max B 0 with hA₂
  have hh₂b : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h₂ y‖ ≤ A₂ * y ^ σ₂ := by
    intro y hy hy1
    have e1 : y ^ σ ≤ y ^ σ₂ := Real.rpow_le_rpow_of_exponent_ge hy hy1 (min_le_left _ _)
    have e2 : y ^ 2 * y ^ ρ ≤ y ^ σ₂ := by
      rw [show (y ^ 2 : ℝ) = y ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hy]
      exact Real.rpow_le_rpow_of_exponent_ge hy hy1 (by rw [hσ₂, add_comm]; exact min_le_right _ _)
    have hn : ‖(4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * f y‖ = 4 * π ^ 2 * y ^ 2 * ‖f y‖ := by
      rw [show (4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * f y = ((4 * π ^ 2 * y ^ 2 : ℝ) : ℂ) * f y by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ‖h₂ y‖ ≤ ‖h y‖ + ‖(4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * f y‖ := norm_add_le _ _
      _ ≤ A * y ^ σ + 4 * π ^ 2 * y ^ 2 * (B * y ^ ρ) := by
          rw [hn]
          gcongr
          · exact hh y hy hy1
          · exact hap y hy hy1
      _ ≤ max A 0 * y ^ σ₂ + 4 * π ^ 2 * (max B 0 * y ^ σ₂) := by
          refine add_le_add ?_ ?_
          · calc A * y ^ σ ≤ max A 0 * y ^ σ := by gcongr; exact le_max_left _ _
              _ ≤ max A 0 * y ^ σ₂ := by gcongr
          · calc 4 * π ^ 2 * y ^ 2 * (B * y ^ ρ)
                = 4 * π ^ 2 * (B * (y ^ 2 * y ^ ρ)) := by ring
              _ ≤ 4 * π ^ 2 * (max B 0 * (y ^ 2 * y ^ ρ)) := by
                  gcongr; exact le_max_left _ _
              _ ≤ 4 * π ^ 2 * (max B 0 * y ^ σ₂) := by gcongr
      _ = A₂ * y ^ σ₂ := by rw [hA₂]; ring
  obtain ⟨C, hC⟩ := odeC (1 / 2 + ν) σ₂ A₂ u h₂ hudiff hh₂b hueq ε hε
  have hre : (1 / 2 + ν).re = 1 / 2 + ν.re := by simp
  refine ⟨C, fun y hy hy1 => ?_⟩
  have := hC y hy hy1
  rw [hre, hσ₂, ← min_assoc] at this
  exact this

theorem round (ν : ℂ) (σ A r B ρ Bρ : ℝ) (hr : 1 / 2 - ν.re < r) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hapriori : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ r)
    (hapρ : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ Bρ * y ^ ρ)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (ρ + 2) - ε) := by
  obtain ⟨C, hC⟩ := twoTermAp ν σ A ρ Bρ f h hf hf' hh hapρ hfeq ε hε
  have hfeq1 : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = (1 / 2 - ν) * f y +
      ((y : ℂ) * deriv f y - (1 / 2 - ν) * f y) := fun y _ => by ring
  have hr' : (1 / 2 - ν).re < r := by simpa using hr
  exact gapC (1 / 2 - ν) _ C r B hr' f _ hf hC hapriori hfeq1

end Gap41

theorem norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing
    (b : ℂ) (σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + h y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min b.re σ - ε) := by
  intro ε hε
  exact OdeCAux.main b σ A f h hf hh hfeq ε hε

theorem norm_le_mul_rpow_near_zero_of_first_order_system_of_diag
    (m : ℕ) (a : Fin m → ℂ) (r₀ c τ : ℝ) (hτ : 0 < τ) (ha : ∀ i, r₀ ≤ (a i).re)
    (B : ℝ → Matrix (Fin m) (Fin m) ℂ) (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j, ‖B y i j‖ ≤ c * y ^ τ)
    (F : Fin m → ℝ → ℂ) (hF : ∀ i, DifferentiableOn ℝ (F i) (Set.Ioi 0))
    (hFeq : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i,
      (y : ℂ) * deriv (F i) y = a i * F i y + ∑ j, B y i j * F j y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, ‖F i y‖ ≤ C * y ^ (r₀ - ε) := by
  intro ε hε
  exact OdeEAux.main m a r₀ c τ hτ ha B hB F hF hFeq ε hε

theorem norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori
    (ν : ℂ) (hν : 0 ≤ ν.re) (σ A r B : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hapriori : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ r)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (r + 2) - ε)) ∧
    (1 / 2 - ν.re < r → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ (min (1 / 2 + ν.re) σ - ε) ∧
      ‖(y : ℂ) * deriv f y‖ ≤ C * y ^ (min (1 / 2 + ν.re) σ - ε)) := by
  set M : ℝ := min (1 / 2 + ν.re) σ with hM
  -- `hν` is not needed by either bound; the pin's statement carries it, so it is referenced here.
  have hν₀ : 0 ≤ ν.re := hν
  refine ⟨fun ε hε => Gap41.twoTermAp ν σ A r B f h hf hf' hh hapriori hfeq ε hε, fun hr => ?_⟩

  have hind : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ (min M (r + 2 * k) - ε) := by
    intro k
    induction k with
    | zero =>
      intro ε hε
      refine ⟨max B 0, fun y hy hy1 => ?_⟩
      calc ‖f y‖ ≤ B * y ^ r := hapriori y hy hy1
        _ ≤ max B 0 * y ^ r := by gcongr; exact le_max_left _ _
        _ ≤ max B 0 * y ^ (min M (r + 2 * (0 : ℕ)) - ε) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1
              (by simp only [Nat.cast_zero, mul_zero, add_zero]; linarith [min_le_right M r])) (le_max_right _ _)
    | succ k ih =>
      intro ε hε
      obtain ⟨Bρ, hBρ⟩ := ih (ε / 2) (by linarith)
      obtain ⟨C, hC⟩ := Gap41.round ν σ A r B (min M (r + 2 * k) - ε / 2) Bρ hr f h hf hf' hh hapriori hBρ hfeq (ε / 2) (by linarith)
      refine ⟨max C 0, fun y hy hy1 => ?_⟩
      have hexp : min M (r + 2 * ((k + 1 : ℕ) : ℝ)) - ε ≤ min (min (1 / 2 + ν.re) σ) (min M (r + 2 * k) - ε / 2 + 2) - ε / 2 := by
        rw [← hM]
        push_cast
        have hkey : min M (r + 2 * ((k : ℝ) + 1)) - ε / 2 ≤ min M (min M (r + 2 * k) - ε / 2 + 2) := by
          refine le_min (by linarith [min_le_left M (r + 2 * ((k : ℝ) + 1))]) ?_
          have : min M (r + 2 * ((k : ℝ) + 1)) ≤ min M (r + 2 * k) + 2 := by
            rw [← min_add_add_right]
            exact min_le_min (by linarith) (by linarith)
          linarith
        linarith
      calc ‖f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (min M (r + 2 * k) - ε / 2 + 2) - ε / 2) := hC y hy hy1
        _ ≤ max C 0 * y ^ (min (min (1 / 2 + ν.re) σ) (min M (r + 2 * k) - ε / 2 + 2) - ε / 2) := by
            gcongr; exact le_max_left _ _
        _ ≤ max C 0 * y ^ (min M (r + 2 * ((k + 1 : ℕ) : ℝ)) - ε) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 hexp) (le_max_right _ _)

  obtain ⟨k, hk⟩ : ∃ k : ℕ, M ≤ r + 2 * k := by
    obtain ⟨k, hk⟩ := exists_nat_ge ((M - r) / 2)
    exact ⟨k, by linarith [hk, (div_le_iff₀ (show (0:ℝ) < 2 by norm_num)).mp (le_refl ((M - r) / 2))]⟩
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := hind k (ε / 2) (by linarith)
  have hmin : min M (r + 2 * k) = M := min_eq_left hk
  rw [hmin] at hC₁

  obtain ⟨C₂, hC₂⟩ := Gap41.twoTermAp ν σ A (M - ε / 2) C₁ f h hf hf' hh hC₁ hfeq (ε / 2) (by linarith)
  have hexp2 : M - ε ≤ min (min (1 / 2 + ν.re) σ) (M - ε / 2 + 2) - ε / 2 := by
    rw [← hM]
    have : M - ε / 2 ≤ min M (M - ε / 2 + 2) := le_min (by linarith) (by linarith)
    linarith
  refine ⟨max C₁ 0 + (max C₂ 0 + ‖(1 / 2 : ℂ) - ν‖ * max C₁ 0), fun y hy hy1 => ?_⟩
  have hyM : 0 ≤ y ^ (M - ε) := (Real.rpow_pos_of_pos hy _).le
  have hf1 : ‖f y‖ ≤ max C₁ 0 * y ^ (M - ε) :=
    calc ‖f y‖ ≤ C₁ * y ^ (M - ε / 2) := hC₁ y hy hy1
      _ ≤ max C₁ 0 * y ^ (M - ε / 2) := by gcongr; exact le_max_left _ _
      _ ≤ max C₁ 0 * y ^ (M - ε) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)) (le_max_right _ _)
  have hu1 : ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ max C₂ 0 * y ^ (M - ε) :=
    calc ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ C₂ * y ^ (min (min (1 / 2 + ν.re) σ) (M - ε / 2 + 2) - ε / 2) := hC₂ y hy hy1
      _ ≤ max C₂ 0 * y ^ (min (min (1 / 2 + ν.re) σ) (M - ε / 2 + 2) - ε / 2) := by gcongr; exact le_max_left _ _
      _ ≤ max C₂ 0 * y ^ (M - ε) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 hexp2) (le_max_right _ _)
  constructor
  · calc ‖f y‖ ≤ max C₁ 0 * y ^ (M - ε) := hf1
      _ ≤ (max C₁ 0 + (max C₂ 0 + ‖(1 / 2 : ℂ) - ν‖ * max C₁ 0)) * y ^ (M - ε) := by
          gcongr; nlinarith [le_max_right C₂ 0, le_max_right C₁ 0, norm_nonneg ((1 / 2 : ℂ) - ν)]
  · have : (y : ℂ) * deriv f y = ((y : ℂ) * deriv f y - (1 / 2 - ν) * f y) + (1 / 2 - ν) * f y := by ring
    rw [this]
    calc ‖((y : ℂ) * deriv f y - (1 / 2 - ν) * f y) + (1 / 2 - ν) * f y‖
        ≤ ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ + ‖(1 / 2 - ν) * f y‖ := norm_add_le _ _
      _ ≤ max C₂ 0 * y ^ (M - ε) + ‖(1 / 2 : ℂ) - ν‖ * (max C₁ 0 * y ^ (M - ε)) := by
          rw [norm_mul]; gcongr
      _ ≤ (max C₁ 0 + (max C₂ 0 + ‖(1 / 2 : ℂ) - ν‖ * max C₁ 0)) * y ^ (M - ε) := by
          nlinarith [le_max_right C₁ 0, hyM]

end LanglandsTunnell
