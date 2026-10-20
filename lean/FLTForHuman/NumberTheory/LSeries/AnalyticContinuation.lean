/-
  Two structural lemmas for `LSeries`: the abscissa of absolute convergence of a
  non-negative Dirichlet series that is locally `exp` of an analytic function, and
  the realisation of a weighted prime-power series as an `LSeries` with an Euler
  product over the primes.

  **`LSeries.abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq`.**
  Let `d : ℕ → ℝ` be non-negative, `Λ` analytic on the real half-line `x < σ`, and
  suppose that on some half-plane `σ₀ < re s` the series `L d` converges absolutely
  and `exp (L d s) = Λ s`. Then `abscissaOfAbsConv d ≤ x`, and on the *whole*
  half-line `x < σ` the series converges absolutely with `exp (L d σ) = Λ σ`. The
  proof is the argument principle-free route of the pin: the set of real points where
  `Λ = exp ∘ L` is clopen in `(x, ∞)` (`ray`, by analytic continuation of the two
  analytic functions), hence everything, and a hypothetical abscissa `r > x` is
  contradicted by applying Landau's theorem to `log ∘ Λ` on a ball around `r` — the
  values of `Λ` on `(r, ∞)` have real part `≥ 1`, so `Λ (r)` is in the slit plane and
  `log ∘ Λ` is analytic there.

  **`LSeries.exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow`.**
  For an injective family `N` of primes and coefficients `c i m` with
  `0 ≤ c i m ≤ B * (N i)^m`, there is a non-negative `d : ℕ → ℝ`, supported on the
  prime powers `N i ^ m` (`m > 0`) and equal to `c i m` there, whose `LSeries`
  converges absolutely for `2 < re s` and equals the absolutely convergent
  fibre-wise sum `∑ i, ∑' m, c i m * (N i)^{-s m}`; the map `(i, m) ↦ N i ^ m` is
  injective (`key_inj`), and on the real line the `i = 1` terms bound the value from
  below. The abscissa bound is `LSeriesSummable_of_le_const_mul_rpow` applied to
  `d n ≤ max B 0 * n`.

  Transcribed verbatim from the pin (pinned `aa2d8b3`):

  * `Theorems/Thm_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq.lean`
    / `P2M/Sol/S_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq.lean`
    (218 pin lines, `namespace RS40E`), and
  * `Theorems/Thm_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow.lean`
    / `P2M/Sol/S_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow.lean`
    (196 pin lines, `namespace PPSeries43`).

  The two nodes are unrelated (one is analytic continuation of an exponential, the
  other an Euler-product assembly) and the order prices the family as one module;
  they are kept in one file, in the pin's two inner namespaces, because they share
  no vocabulary: each block opens the namespaces its pin proof needs.

  The one premise that is a *pin node of its own* is
  `LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball` (the ball form of Landau's
  theorem, pin `Theorems/Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball`,
  `namespace P2M_Landau`). It is already homed in the port as
  `FLTForHuman/NumberTheory/LSeries/Landau.lean` and is **imported, not re-proved**;
  the pin's `import Theorems.Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball`
  becomes `import FLTForHuman.NumberTheory.LSeries.Landau`. Gate consumption: no
  `Definitions/` gate, only that theorem.

  Drift against `v4.34.0` — statements untouched:

  * port:186: the pin's `haveI : PreconnectedSpace (Ioi y) := Subtype.preconnectedSpace
    isPreconnected_Ioi` followed by `hT.eq_univ` becomes an explicit instance argument,
    `@IsClopen.eq_univ (Ioi y) _ (Subtype.preconnectedSpace isPreconnected_Ioi) _ hT …`
    (`linter.style.haveILetI`'s `haveI`→`have` repair, applied as an application rather
    than a local instance; the `IsPreconnected` form of the same statement,
    `isPreconnected_univ.subset_isClopen`, is not available because `isPreconnected_univ`
    itself requires the `PreconnectedSpace` instance);
  * port:179: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (deprecated alias);
  * port:342, 352, 353: `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right` (deprecated
    aliases);
  * port:76: `import Mathlib.Analysis.Complex.Convex` is added for
    `convex_halfSpace_re_gt`, which the pin got from `import Mathlib`;
  * port:77: the pin's `import Theorems.Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball`
    becomes the port's `import FLTForHuman.NumberTheory.LSeries.Landau` (the same node,
    homed — imported, not re-proved).

  Assumes: mathlib `v4.34.0` plus the port module
  `FLTForHuman.NumberTheory.LSeries.Landau`.

  Mathlib-first check (2026-10-20): neither statement is in mathlib. `rg` over
  `Mathlib/` for `abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq`,
  `exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow` and for the concept
  ("abscissa of absolute convergence from analytic continuation of the exponential",
  "Euler product of a prime-power Dirichlet series") returns only the general
  `LSeries` API the proofs already use (`LSeriesSummable_of_le_const_mul_rpow`,
  `LSeriesSummable_of_abscissaOfAbsConv_lt_re`, `LSeries_analyticOnNhd`,
  `LSeries.term_def₀`, `Complex.hasSum_re`, `tsum_comp_le_tsum_of_inj`); no mathlib
  lemma implies either statement. There is no broader lemma being re-proved: the
  analytic-continuation step `ray` is the pinned proof's own clopen argument.

  spec-pin: Theorems/Thm_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq.lean
  spec-pin: P2M/Sol/S_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq.lean
  spec-pin: Theorems/Thm_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow.lean
  spec-pin: P2M/Sol/S_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow.lean
-/

import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Convex
import FLTForHuman.NumberTheory.LSeries.Landau
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open scoped ComplexOrder

noncomputable section

namespace RS40E

open Complex Filter Topology Metric Set

theorem dist_ofReal (a b : ℝ) : dist (a : ℂ) (b : ℂ) = dist a b := by
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]

def rterm (d : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else d n / (n : ℝ) ^ σ

theorem term_eq_rterm (d : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
    LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) n = ((rterm d σ n : ℝ) : ℂ) := by
  rw [LSeries.term_def, rterm]
  split_ifs with h
  · simp
  · push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_cast

theorem lseries_eq_ofReal_tsum (d : ℕ → ℝ) (σ : ℝ) :
    LSeries (fun n => (d n : ℂ)) (σ : ℂ) = ((∑' n, rterm d σ n : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (term_eq_rterm d σ)

theorem rterm_nonneg {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (σ : ℝ) (n : ℕ) : 0 ≤ rterm d σ n := by
  unfold rterm; split_ifs
  · exact le_rfl
  · exact div_nonneg (hd n) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

theorem lseries_im_eq_zero (d : ℕ → ℝ) (σ : ℝ) : (LSeries (fun n => (d n : ℂ)) (σ : ℂ)).im = 0 := by
  rw [lseries_eq_ofReal_tsum, ofReal_im]

theorem lseries_re_nonneg {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (σ : ℝ) :
    0 ≤ (LSeries (fun n => (d n : ℂ)) (σ : ℂ)).re := by
  rw [lseries_eq_ofReal_tsum, ofReal_re]
  exact tsum_nonneg (rterm_nonneg hd σ)

theorem ray (Λ L : ℂ → ℂ) (y σ₁ : ℝ)
    (hΛ : ∀ σ : ℝ, y < σ → AnalyticAt ℂ Λ (σ : ℂ)) (hL : ∀ s : ℂ, y < s.re → AnalyticAt ℂ L s)
    (heq : ∀ s : ℂ, σ₁ < s.re → Complex.exp (L s) = Λ s) :
    ∀ σ : ℝ, y < σ → Λ =ᶠ[𝓝 (σ : ℂ)] fun s => Complex.exp (L s) := by
  let P : ℝ → Prop := fun σ => Λ =ᶠ[𝓝 (σ : ℂ)] fun s => Complex.exp (L s)

  have hopen : IsOpen {σ : ℝ | P σ} := by
    rw [Metric.isOpen_iff]
    intro σ hσ
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hσ
    refine ⟨ε / 2, half_pos hε, fun σ' hσ' => ?_⟩
    show Λ =ᶠ[𝓝 (σ' : ℂ)] fun s => Complex.exp (L s)
    refine Metric.eventually_nhds_iff.2 ⟨ε / 2, half_pos hε, fun z hz => hball ?_⟩
    have h1 : dist (σ' : ℂ) (σ : ℂ) < ε / 2 := by rw [dist_ofReal]; exact mem_ball.1 hσ'
    calc dist z (σ : ℂ) ≤ dist z (σ' : ℂ) + dist (σ' : ℂ) (σ : ℂ) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hz h1
      _ = ε := by ring

  have hclosed : IsOpen {σ : ℝ | y < σ ∧ ¬ P σ} := by
    rw [Metric.isOpen_iff]
    rintro σ ⟨hyσ, hnot⟩
    have h1 : AnalyticAt ℂ Λ (σ : ℂ) := hΛ σ hyσ
    have h2 : AnalyticAt ℂ (fun s => Complex.exp (L s)) (σ : ℂ) :=
      (hL σ (by simpa using hyσ)).cexp
    rcases h1.eventually_eq_or_eventually_ne h2 with h | h
    · exact absurd h hnot
    obtain ⟨ε, hε, hne⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
    refine ⟨min ε (σ - y), lt_min hε (by linarith), fun σ' hσ' => ⟨?_, fun hP' => ?_⟩⟩
    · have := lt_of_lt_of_le (mem_ball.1 hσ') (min_le_right _ _)
      rw [Real.dist_eq, abs_lt] at this
      linarith
    · by_cases hσσ : σ' = σ
      · exact hnot (hσσ ▸ hP')
      · have heqpt : Λ (σ' : ℂ) = Complex.exp (L (σ' : ℂ)) := hP'.eq_of_nhds
        have hd : dist (σ' : ℂ) (σ : ℂ) < ε := by
          rw [dist_ofReal]; exact lt_of_lt_of_le (mem_ball.1 hσ') (min_le_left _ _)
        have hmem : (σ' : ℂ) ∈ ({(σ : ℂ)}ᶜ : Set ℂ) := by
          simpa using (fun h => hσσ (by exact_mod_cast h) : (σ' : ℂ) ≠ (σ : ℂ))
        exact hne hd hmem heqpt

  set σ₂ : ℝ := max σ₁ y + 1 with hσ₂
  have hσ₂y : y < σ₂ := by rw [hσ₂]; linarith [le_max_right σ₁ y]
  have hne0 : P σ₂ := by
    show Λ =ᶠ[𝓝 (σ₂ : ℂ)] fun s => Complex.exp (L s)
    have : ∀ᶠ s in 𝓝 (σ₂ : ℂ), σ₁ < s.re := by
      apply (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      show σ₁ < (σ₂ : ℂ).re
      rw [ofReal_re, hσ₂]; linarith [le_max_left σ₁ y]
    filter_upwards [this] with s hs
    exact (heq s hs).symm

  have hcl : IsClosed {p : Ioi y | P p.1} := by
    rw [← isOpen_compl_iff]
    have : {p : Ioi y | P p.1}ᶜ = ((↑) : Ioi y → ℝ) ⁻¹' {σ | y < σ ∧ ¬ P σ} := by
      ext p
      simp only [mem_compl_iff, Set.mem_ofPred_eq, mem_preimage]
      exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩
    rw [this]
    exact hclosed.preimage continuous_subtype_val
  have hop : IsOpen {p : Ioi y | P p.1} := hopen.preimage continuous_subtype_val
  have hT : IsClopen {p : Ioi y | P p.1} := ⟨hcl, hop⟩
  have huniv : {p : Ioi y | P p.1} = Set.univ :=
    @IsClopen.eq_univ (Ioi y) _ (Subtype.preconnectedSpace isPreconnected_Ioi) _
      hT ⟨⟨σ₂, hσ₂y⟩, hne0⟩
  intro σ hσ
  have : (⟨σ, hσ⟩ : Ioi y) ∈ {p : Ioi y | P p.1} := by rw [huniv]; trivial
  exact this

end RS40E

open RS40E Complex Filter Topology Metric Set in
theorem LSeries.abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
    (d : ℕ → ℝ) (hd : ∀ n : ℕ, 0 ≤ d n) (Λ : ℂ → ℂ) (x σ₀ : ℝ)
    (han : ∀ σ : ℝ, x < σ → AnalyticAt ℂ Λ (σ : ℂ))
    (heq : ∀ s : ℂ, σ₀ < s.re →
      LSeriesSummable (fun n => (d n : ℂ)) s ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) s) = Λ s) :
    LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ (x : EReal) ∧
      ∀ σ : ℝ, x < σ →
        LSeriesSummable (fun n => (d n : ℂ)) σ ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) σ) = Λ σ := by
  set f : ℕ → ℂ := fun n => (d n : ℂ) with hf
  have hf0 : 0 ≤ f := by
    intro n
    show (0 : ℂ) ≤ (d n : ℂ)
    exact_mod_cast hd n
  set L : ℂ → ℂ := LSeries f with hL
  have hLan : ∀ s : ℂ, LSeries.abscissaOfAbsConv f < s.re → AnalyticAt ℂ L s :=
    fun s hs => LSeries_analyticOnNhd f s hs

  have hxtop : LSeries.abscissaOfAbsConv f ≤ ((σ₀ + 1 : ℝ) : EReal) := by
    have h := (heq ((σ₀ + 1 : ℝ) : ℂ) (by simp)).1.abscissaOfAbsConv_le
    simpa using h

  have hmain : LSeries.abscissaOfAbsConv f ≤ (x : EReal) := by
    by_contra hcon
    push Not at hcon
    have hnetop : LSeries.abscissaOfAbsConv f ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hxtop
    have hnebot : LSeries.abscissaOfAbsConv f ≠ ⊥ := ne_bot_of_gt hcon
    set r : ℝ := (LSeries.abscissaOfAbsConv f).toReal with hr
    have hrx0 : (r : EReal) = LSeries.abscissaOfAbsConv f := EReal.coe_toReal hnetop hnebot
    have hxr : x < r := by rw [← EReal.coe_lt_coe_iff, hrx0]; exact hcon
    have hLan' : ∀ s : ℂ, r < s.re → AnalyticAt ℂ L s := fun s hs =>
      hLan s (by rw [← hrx0]; exact_mod_cast hs)

    have hray := ray Λ L r σ₀ (fun σ hσ => han σ (hxr.trans hσ)) hLan' (fun s hs => (heq s hs).2)
    have hval : ∀ σ : ℝ, r < σ → Λ σ = Complex.exp (L σ) := fun σ hσ => (hray σ hσ).eq_of_nhds
    have hre1 : ∀ σ : ℝ, r < σ → 1 ≤ (Λ σ).re := by
      intro σ hσ
      rw [hval σ hσ, hL, lseries_eq_ofReal_tsum, ← Complex.ofReal_exp, ofReal_re]
      exact Real.one_le_exp (tsum_nonneg (rterm_nonneg hd σ))

    have hΛr : AnalyticAt ℂ Λ (r : ℂ) := han r hxr
    have hcont : ContinuousAt (fun σ : ℝ => Λ (σ : ℂ)) r :=
      hΛr.continuousAt.comp_of_eq continuous_ofReal.continuousAt rfl
    have hre_r : 1 ≤ (Λ (r : ℂ)).re := by
      have h1 : Tendsto (fun σ : ℝ => (Λ (σ : ℂ)).re) (𝓝[>] r) (𝓝 (Λ (r : ℂ)).re) :=
        ((continuous_re.tendsto _).comp hcont.tendsto).mono_left nhdsWithin_le_nhds
      exact ge_of_tendsto h1 (eventually_nhdsWithin_of_forall fun σ hσ => hre1 σ hσ)
    have hslit : Λ (r : ℂ) ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by linarith))

    obtain ⟨ρ₁, hρ₁, hanB⟩ := hΛr.exists_ball_analyticOnNhd
    obtain ⟨ρ₂, hρ₂, hslitB⟩ := Metric.eventually_nhds_iff.1
      (hΛr.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hslit))
    set ρ : ℝ := min ρ₁ ρ₂ with hρdef
    have hρ : 0 < ρ := lt_min hρ₁ hρ₂
    have hFdiff : DifferentiableOn ℂ (fun z => Complex.log (Λ z)) (ball (r : ℂ) ρ) := by
      intro z hz
      have hz1 : z ∈ ball (r : ℂ) ρ₁ := ball_subset_ball (min_le_left _ _) hz
      have hz2 : dist z (r : ℂ) < ρ₂ := lt_of_lt_of_le (mem_ball.1 hz) (min_le_right _ _)
      exact ((hanB z hz1).differentiableAt.clog (hslitB hz2)).differentiableWithinAt

    set V : Set ℂ := ball (r : ℂ) ρ ∩ {s : ℂ | r < s.re} with hV
    have hVpre : IsPreconnected V := ((convex_ball _ _).inter (convex_halfSpace_re_gt r)).isPreconnected
    set σs : ℝ := r + ρ / 2 with hσs
    have hσsr : r < σs := by rw [hσs]; linarith
    have hσsV : (σs : ℂ) ∈ V := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_ofReal, Real.dist_eq, hσs, show r + ρ / 2 - r = ρ / 2 by ring, abs_of_pos (half_pos hρ)]
        linarith
      · show r < (σs : ℂ).re
        rw [ofReal_re]; exact hσsr
    have hFan : AnalyticOnNhd ℂ (fun z => Complex.log (Λ z)) V :=
      (hFdiff.analyticOnNhd isOpen_ball).mono inter_subset_left
    have hLanV : AnalyticOnNhd ℂ L V := fun s hs => hLan' s hs.2

    have hnear : (fun z => Complex.log (Λ z)) =ᶠ[𝓝 (σs : ℂ)] L := by
      have h1 := hray σs hσsr
      have hLc : ContinuousAt L (σs : ℂ) := (hLan' (σs : ℂ) (by rw [ofReal_re]; exact hσsr)).continuousAt
      have him0 : (L (σs : ℂ)).im = 0 := by rw [hL]; exact lseries_im_eq_zero d σs
      have him : ∀ᶠ z in 𝓝 (σs : ℂ), (L z).im ∈ Ioo (-Real.pi) Real.pi := by
        have hc : ContinuousAt (fun z => (L z).im) (σs : ℂ) := continuous_im.continuousAt.comp hLc
        apply hc.preimage_mem_nhds
        apply isOpen_Ioo.mem_nhds
        rw [him0]; exact ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
      filter_upwards [h1, him] with z hz1 hz2
      show Complex.log (Λ z) = L z
      rw [hz1, Complex.log_exp hz2.1 hz2.2.le]
    have hEq : EqOn (fun z => Complex.log (Λ z)) L V :=
      hFan.eqOn_of_preconnected_of_eventuallyEq hLanV hVpre hσsV hnear

    have hlt := LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball hf0 (x := r) (le_of_eq hrx0.symm) hρ hFdiff
      (fun s hs hsr => hEq ⟨hs, hsr⟩)
    rw [← hrx0] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hmain, fun σ hσ => ?_⟩
  have hσ' : LSeries.abscissaOfAbsConv f < ((σ : ℂ)).re := lt_of_le_of_lt hmain (by simp; exact_mod_cast hσ)
  have hsum : LSeriesSummable f σ := LSeriesSummable_of_abscissaOfAbsConv_lt_re hσ'
  refine ⟨hsum, ?_⟩
  have hray := ray Λ L x σ₀ han
    (fun s hs => hLan s (lt_of_le_of_lt hmain (by exact_mod_cast hs))) (fun s hs => (heq s hs).2)
  exact ((hray σ hσ).eq_of_nhds).symm

namespace PPSeries43

open Complex

variable {ι : Type*} (N : ι → ℕ) (hN : ∀ i : ι, (N i).Prime) (hinj : Function.Injective N)

include hN hinj in

theorem key_inj {q q' : ι × ℕ} (hq : 0 < q.2) (_hq' : 0 < q'.2) (h : N q.1 ^ q.2 = N q'.1 ^ q'.2) :
    q = q' := by
  have hp := hN q.1
  have hp' := hN q'.1
  have h1 : N q.1 = N q'.1 := by
    have hd : N q.1 ∣ N q'.1 ^ q'.2 := by
      rw [← h]; exact dvd_pow_self _ hq.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp hp').mp (hp.dvd_of_dvd_pow hd)
  have hm : q.2 = q'.2 := by
    rw [h1] at h
    exact Nat.pow_right_injective hp'.two_le h
  exact Prod.ext (hinj h1) hm

include hN hinj in
theorem main
    (c : ι → ℕ → ℝ) (hc0 : ∀ i : ι, c i 0 = 0) (hc : ∀ (i : ι) (m : ℕ), 0 ≤ c i m)
    (B : ℝ) (hcB : ∀ (i : ι) (m : ℕ), c i m ≤ B * (N i : ℝ) ^ m) :
    ∃ d : ℕ → ℝ, (∀ n : ℕ, 0 ≤ d n) ∧
      (∀ (i : ι) (m : ℕ), 0 < m → d (N i ^ m) = c i m) ∧
      (∀ n : ℕ, d n ≠ 0 → ∃ (i : ι) (m : ℕ), 0 < m ∧ N i ^ m = n) ∧
      LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ ((2 : ℝ) : EReal) ∧
      (∀ s : ℂ, 2 < s.re →
        (∀ i : ι, Summable (fun m : ℕ => (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)) ∧
        HasSum (fun i : ι => ∑' m : ℕ, (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)
          (LSeries (fun n => (d n : ℂ)) s)) ∧
      ∀ σ : ℝ, LSeriesSummable (fun n => (d n : ℂ)) σ →
        Summable (fun i : ι => c i 1 * (N i : ℝ) ^ (-σ)) ∧
        ∑' i : ι, c i 1 * (N i : ℝ) ^ (-σ) ≤ (LSeries (fun n => (d n : ℂ)) σ).re := by
  classical

  let P : ℕ → Prop := fun n => ∃ q : ι × ℕ, 0 < q.2 ∧ N q.1 ^ q.2 = n
  let d : ℕ → ℝ := fun n => if h : P n then c h.choose.1 h.choose.2 else 0
  have hNpos : ∀ i, 0 < N i := fun i => (hN i).pos
  have hNR : ∀ i, (1 : ℝ) < (N i : ℝ) := fun i => by exact_mod_cast (hN i).one_lt
  have hd_pow : ∀ (i : ι) (m : ℕ), 0 < m → d (N i ^ m) = c i m := by
    intro i m hm
    have h : P (N i ^ m) := ⟨(i, m), hm, rfl⟩
    have hq : h.choose = (i, m) := key_inj N hN hinj h.choose_spec.1 hm h.choose_spec.2
    show (if h : P (N i ^ m) then c h.choose.1 h.choose.2 else 0) = c i m
    rw [dite_eq_left h, hq]
  have hd_nonneg : ∀ n, 0 ≤ d n := by
    intro n
    show 0 ≤ (if h : P n then c h.choose.1 h.choose.2 else 0)
    split_ifs with h
    · exact hc _ _
    · exact le_rfl
  have hd_P : ∀ n, d n ≠ 0 → P n := by
    intro n hn
    by_contra hP
    exact hn (dite_eq_right hP)
  have hd_notP : ∀ n, ¬ P n → d n = 0 := fun n hP => dite_eq_right hP
  have hd0 : d 0 = 0 := hd_notP 0 (by
    rintro ⟨q, -, hq⟩
    exact pow_ne_zero _ (hN q.1).ne_zero hq)
  have hd0C : (fun n => (d n : ℂ)) 0 = 0 := by simp [hd0]
  have hB : ∀ n, d n ≤ max B 0 * n := by
    intro n
    by_cases h : P n
    · obtain ⟨q, hq, hqn⟩ := h
      rw [← hqn, hd_pow q.1 q.2 hq]
      calc c q.1 q.2 ≤ B * (N q.1 : ℝ) ^ q.2 := hcB _ _
        _ ≤ max B 0 * (N q.1 : ℝ) ^ q.2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ = max B 0 * ((N q.1 ^ q.2 : ℕ) : ℝ) := by push_cast; ring
    · rw [hd_notP n h]; positivity
  have hbound : ∃ C : ℝ, ∀ n : ℕ, n ≠ 0 → ‖((d n : ℝ) : ℂ)‖ ≤ C * (n : ℝ) ^ ((2 : ℝ) - 1) := by
    refine ⟨max B 0, fun n _ => ?_⟩
    rw [Complex.norm_real, Real.norm_of_nonneg (hd_nonneg n), show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    exact hB n
  have hsummable : ∀ s : ℂ, 2 < s.re → LSeriesSummable (fun n => (d n : ℂ)) s :=
    fun s hs => LSeriesSummable_of_le_const_mul_rpow hs hbound
  refine ⟨d, hd_nonneg, hd_pow, fun n hn => ?_, ?_, fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨q, hq, hqn⟩ := hd_P n hn
    exact ⟨q.1, q.2, hq, hqn⟩
  · exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsummable y (by simpa using hy)
  ·
    set σ : ℝ := s.re with hσdef
    let F : ι × ℕ → ℂ := fun q => (c q.1 q.2 : ℂ) * (((N q.1 : ℕ) : ℂ) ^ (-s)) ^ q.2

    have hinner : ∀ i : ι, Summable (fun m : ℕ => F (i, m)) := by
      intro i
      have hp : (0 : ℝ) < N i := by exact_mod_cast hNpos i
      set r : ℝ := (N i : ℝ) ^ (1 - σ) with hr
      have hr0 : 0 ≤ r := Real.rpow_nonneg hp.le _
      have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (hNR i) (by linarith)
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left (max B 0)) fun m => ?_
      have hnorm : ‖F (i, m)‖ = c i m * ((N i : ℝ) ^ (-σ)) ^ m := by
        show ‖(c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m‖ = _
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hc i m),
          Complex.norm_natCast_cpow_of_pos (hNpos i), Complex.neg_re]
      rw [hnorm]
      have hre : (N i : ℝ) ^ m * ((N i : ℝ) ^ (-σ)) ^ m = r ^ m := by
        rw [← mul_pow, hr, show (1 : ℝ) - σ = 1 + -σ by ring, Real.rpow_add hp, Real.rpow_one]
      calc c i m * ((N i : ℝ) ^ (-σ)) ^ m ≤ (B * (N i : ℝ) ^ m) * ((N i : ℝ) ^ (-σ)) ^ m :=
            mul_le_mul_of_nonneg_right (hcB i m) (by positivity)
        _ ≤ (max B 0 * (N i : ℝ) ^ m) * ((N i : ℝ) ^ (-σ)) ^ m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
              (by positivity)
        _ = max B 0 * r ^ m := by rw [mul_assoc, hre]
    refine ⟨hinner, ?_⟩

    let T : Set (ι × ℕ) := {q | 0 < q.2}
    let eT : T → ℕ := fun q => N q.1.1 ^ q.1.2
    have heT : Function.Injective eT := by
      intro q q' h
      exact Subtype.ext (key_inj N hN hinj q.2 q'.2 h)
    have hrange : ∀ n : ℕ, n ∉ Set.range eT → LSeries.term (fun n => (d n : ℂ)) s n = 0 := by
      intro n hn
      have hP : ¬ P n := by
        rintro ⟨q, hq, hqn⟩
        exact hn ⟨⟨q, hq⟩, hqn⟩
      rw [LSeries.term_def₀ hd0C, hd_notP n hP]
      simp
    have h1 : HasSum (LSeries.term (fun n => (d n : ℂ)) s) (LSeries (fun n => (d n : ℂ)) s) :=
      (hsummable s hs).LSeriesHasSum
    have h2 : HasSum (LSeries.term (fun n => (d n : ℂ)) s ∘ eT) (LSeries (fun n => (d n : ℂ)) s) :=
      (heT.hasSum_iff hrange).mpr h1
    have hterm : ∀ q : T, LSeries.term (fun n => (d n : ℂ)) s (eT q) = F q.1 := by
      intro q
      rw [LSeries.term_def₀ hd0C]
      show ((d (N q.1.1 ^ q.1.2) : ℝ) : ℂ) * (((N q.1.1 ^ q.1.2 : ℕ) : ℂ)) ^ (-s) =
        (c q.1.1 q.1.2 : ℂ) * (((N q.1.1 : ℕ) : ℂ) ^ (-s)) ^ q.1.2
      rw [hd_pow _ _ q.2, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
    have h3 : HasSum (F ∘ (↑) : T → ℂ) (LSeries (fun n => (d n : ℂ)) s) := by
      have hfun : (LSeries.term (fun n => (d n : ℂ)) s ∘ eT) = (F ∘ (↑) : T → ℂ) := funext hterm
      rw [← hfun]; exact h2
    have hsupp : Function.support F ⊆ T := by
      intro q hq
      by_contra hq0
      apply hq
      have h0 : q.2 = 0 := Nat.eq_zero_of_not_pos hq0
      show (c q.1 q.2 : ℂ) * (((N q.1 : ℕ) : ℂ) ^ (-s)) ^ q.2 = 0
      rw [h0, hc0]; simp
    have h4 : HasSum F (LSeries (fun n => (d n : ℂ)) s) :=
      (hasSum_subtype_iff_of_support_subset hsupp).mp h3
    exact h4.prod_fiberwise fun i => (hinner i).hasSum
  ·
    let g : ℕ → ℝ := fun n => d n * (n : ℝ) ^ (-σ)
    have hg0 : ∀ n, 0 ≤ g n := fun n => mul_nonneg (hd_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hterm : ∀ n, LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) n = ((g n : ℝ) : ℂ) := by
      intro n
      rw [LSeries.term_def₀ hd0C]
      show ((d n : ℝ) : ℂ) * ((n : ℕ) : ℂ) ^ (-(σ : ℂ)) = (((d n * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg]
    have hre : ∀ n, (LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) n).re = g n := fun n => by
      rw [hterm n, Complex.ofReal_re]
    have hg : Summable g := by
      have := Complex.hasSum_re hσ.LSeriesHasSum
      simp_rw [hre] at this
      exact this.summable
    have hgN : (fun i : ι => c i 1 * (N i : ℝ) ^ (-σ)) = g ∘ N := by
      funext i
      show c i 1 * (N i : ℝ) ^ (-σ) = d (N i) * ((N i : ℕ) : ℝ) ^ (-σ)
      rw [← pow_one (N i), hd_pow i 1 one_pos, pow_one]
    rw [hgN]
    refine ⟨hg.comp_injective hinj, ?_⟩
    calc ∑' i : ι, (g ∘ N) i ≤ ∑' n, g n := tsum_comp_le_tsum_of_inj hg hg0 hinj
      _ = ∑' n, (LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) n).re := by simp_rw [hre]
      _ = (LSeries (fun n => (d n : ℂ)) σ).re := (Complex.re_tsum hσ).symm

end PPSeries43

theorem LSeries.exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow
    {ι : Type*} (N : ι → ℕ) (hN : ∀ i : ι, (N i).Prime) (hinj : Function.Injective N)
    (c : ι → ℕ → ℝ) (hc0 : ∀ i : ι, c i 0 = 0) (hc : ∀ (i : ι) (m : ℕ), 0 ≤ c i m)
    (B : ℝ) (hcB : ∀ (i : ι) (m : ℕ), c i m ≤ B * (N i : ℝ) ^ m) :
    ∃ d : ℕ → ℝ, (∀ n : ℕ, 0 ≤ d n) ∧
      (∀ (i : ι) (m : ℕ), 0 < m → d (N i ^ m) = c i m) ∧
      (∀ n : ℕ, d n ≠ 0 → ∃ (i : ι) (m : ℕ), 0 < m ∧ N i ^ m = n) ∧
      LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ ((2 : ℝ) : EReal) ∧
      (∀ s : ℂ, 2 < s.re →
        (∀ i : ι, Summable (fun m : ℕ => (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)) ∧
        HasSum (fun i : ι => ∑' m : ℕ, (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)
          (LSeries (fun n => (d n : ℂ)) s)) ∧
      ∀ σ : ℝ, LSeriesSummable (fun n => (d n : ℂ)) σ →
        Summable (fun i : ι => c i 1 * (N i : ℝ) ^ (-σ)) ∧
        ∑' i : ι, c i 1 * (N i : ℝ) ^ (-σ) ≤ (LSeries (fun n => (d n : ℂ)) σ).re :=
  PPSeries43.main N hN hinj c hc0 hc B hcB
