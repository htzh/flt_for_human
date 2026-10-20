/-
  Coefficient facts for the `q`-expansion of a function on the upper half plane.

  Mathlib has the object: `UpperHalfPlane.qExpansion` together with
  `hasSum_qExpansion`, `qExpansion_coeff_unique`,
  `qExpansion_coeff_eq_intervalIntegral`, `analyticAt_cuspFunction_zero`
  (`Mathlib/NumberTheory/ModularForms/QExpansion.lean`).  It has none of the
  three lemmas below, which the Sturm-bound side of the port consumes:

  * `UpperHalfPlane.qExpansion_coeff_eq_zero_of_isBigO_exp_neg` — if `f` is
    `O (exp (-(2 π L) · im))` at the cusp then every coefficient of index
    `n < L` vanishes (the integral formula plus a decaying bound).
  * `UpperHalfPlane.qExpansion_coeff_mul_width` — multiplying the strict period
    by a positive `m'` reindexes the coefficients: `i` is `m'` times an index of
    the old expansion, all other coefficients vanish.
  * `UpperHalfPlane.qExpansion_coeff_sum_vAdd_eq_mul_coeff` — the `q`-expansion
    of `∑_{j < h₀} f (j +ᵥ τ)` is `h₀` times the period-`h₀` expansion in degree
    `h₀ * m` (a `q ↦ q^{h₀}` reindexing plus the finite geometric sum).

  FLT provenance, pinned `aa2d8b3` (Lean `v4.33.1`; the port is at mathlib
  `v4.34.0`), 88 + 91 + 202 lines:

  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_mul_width.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff.lean

  Each node's statement authority is its `Theorems/Thm_` wrapper, cited by the
  `spec-pin:` lines below.

  What this module assumes from earlier port modules: nothing.  The pin `S_`
  files import `Mathlib` and `P2M.Util` only.  `Mathlib` is scaffolding: the
  named imports are exactly what the proofs use.  `P2M.Util` is metaprogramming
  with no mathematics in it (`p2m_open` opens namespaces, `p2m_reactivate`
  re-activates scoped instances); the port spells `p2m_open` as `open` and drops
  `p2m_reactivate`.

  Two of the pin files need a `FunLike` wrapper for a bare `ℍ → ℂ`, because
  mathlib's `qExpansion_coeff_unique` infers that type from a `FunLike` class
  and the bare function type does not provide one.  Both files define the same
  10-line `FnWrap` structure; the port carries one copy (`QExpansionCoeff.FnWrap`).

  Mathlib-first negative (checked against
  `Mathlib/NumberTheory/ModularForms/QExpansion.lean` at `v4.34.0`): no lemma
  there mentions a translate sum or a `vAdd` of a `ℍ`-point; there is no
  coefficient formula for `qExpansion (m' * h)`; and `exp_decay_atImInfty` /
  `exp_decay_sub_atImInfty` are the wrong direction (`q`-expansion coefficients
  decay, they do not imply a bound on a coefficient below the decay rate).
  spec-pin: P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg.lean
  spec-pin: Theorems/Thm_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg.lean
  spec-pin: P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_mul_width.lean
  spec-pin: Theorems/Thm_UpperHalfPlane_qExpansion_coeff_mul_width.lean
  spec-pin: P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff.lean
  spec-pin: Theorems/Thm_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff.lean
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

noncomputable section

namespace QExpansionCoeff

open UpperHalfPlane

/-- A `FunLike` wrapper for a bare `ℍ → ℂ`: mathlib's `qExpansion_coeff_unique`
is polymorphic in a `FunLike` type, and the wrapper restores the coercion the
lemma expects.  (The pin defines this structure once per `S_` file; the port
carries one copy.) -/
structure FnWrap where

  toFun : ℍ → ℂ

scoped instance : FunLike FnWrap ℍ ℂ where
  coe := FnWrap.toFun
  coe_injective := by rintro ⟨f⟩ ⟨g⟩ h; congr

end QExpansionCoeff

namespace DecayVanish

open UpperHalfPlane Filter Asymptotics Function
open scoped Real Topology Manifold

/-- The integrand of `qExpansion_coeff_eq_intervalIntegral` is bounded on the
horizontal line `im = t` by the decay rate of `f` times the `n`-th power of the
inverse `q`-parameter. -/
theorem norm_integrand_le (f : ℍ → ℂ) (n : ℕ) {C L t A : ℝ} (ht : 0 < t) (hAt : A ≤ t)
    (hC : ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C * ‖Real.exp (-(2 * Real.pi * L) * z.im)‖) (u : ℝ) :
    ‖1 / Periodic.qParam 1 (u + t * (UpperHalfPlane.I : ℂ)) ^ n *
        f ⟨u + t * (UpperHalfPlane.I : ℂ), by simpa using ht⟩‖ ≤
      max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t) := by
  set τ : ℍ := ⟨u + t * (UpperHalfPlane.I : ℂ), by simpa using ht⟩ with hτ
  have hI : (u + t * (UpperHalfPlane.I : ℂ)).im = t := by simp [UpperHalfPlane.I]
  have him : τ.im = t := by rw [hτ]; exact hI
  rw [norm_mul, norm_div, norm_one, norm_pow, Periodic.norm_qParam]
  have h1 : (1 : ℝ) / Real.exp (-2 * Real.pi * (u + t * (UpperHalfPlane.I : ℂ)).im / 1) ^ n =
      Real.exp (2 * Real.pi * n * t) := by
    rw [hI, div_one, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1; ring
  rw [h1]
  have h2 : ‖f τ‖ ≤ max C 0 * Real.exp (-(2 * Real.pi * L) * t) := by
    have := hC τ (him ▸ hAt)
    rw [him, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  calc Real.exp (2 * Real.pi * n * t) * ‖f τ‖
      ≤ Real.exp (2 * Real.pi * n * t) * (max C 0 * Real.exp (-(2 * Real.pi * L) * t)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- A coefficient of index `n` below the exponential decay rate `L` vanishes. -/
theorem main (f : ℍ → ℂ)
    (hper : Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : IsBoundedAtImInfty f)
    (L : ℝ) (hO : f =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi * L) * τ.im))
    (n : ℕ) (hn : (n : ℝ) < L) :
    PowerSeries.coeff n (qExpansion 1 f) = 0 := by
  obtain ⟨C, hC⟩ := hO.bound
  rw [Filter.Eventually, atImInfty_mem] at hC
  obtain ⟨A, hA⟩ := hC
  set a : ℂ := PowerSeries.coeff n (qExpansion 1 f) with ha

  have hbound : ∀ t : ℝ, max A 1 ≤ t →
      ‖a‖ ≤ max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t) := by
    intro t hAt
    have ht : 0 < t := lt_of_lt_of_le one_pos ((le_max_right A 1).trans hAt)
    have hint := qExpansion_coeff_eq_intervalIntegral one_pos hper hhol hbdd n ht
    simp only [Complex.ofReal_one, div_one, one_mul] at hint
    rw [ha, hint]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun u : ℝ => 1 / Periodic.qParam 1 (u + t * (UpperHalfPlane.I : ℂ)) ^ n *
        f ⟨u + t * (UpperHalfPlane.I : ℂ), by simpa using ht⟩)
      (C := max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t))
      (fun u _ => norm_integrand_le f n ht ((le_max_left A 1).trans hAt) hA u)
    simpa using this

  have hlim : Tendsto (fun t : ℝ => max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t))
      atTop (𝓝 0) := by
    have hneg : 2 * Real.pi * ((n : ℝ) - L) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hn)
    have h1 : Tendsto (fun t : ℝ => Real.exp (2 * Real.pi * ((n : ℝ) - L) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hneg)
    simpa using h1.const_mul (max C 0)
  have hle : ‖a‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨max A 1, hbound⟩)
  exact norm_le_zero_iff.mp hle

end DecayVanish

namespace WidthChange

open QExpansionCoeff UpperHalfPlane Filter Function
open scoped Real Topology Manifold

/-- `q`-parameter of a period multiplied by `m'`, raised to `m'`, is the
`q`-parameter of the original period. -/
theorem qParam_mul_width_pow {h₀ : ℝ} (hh₀ : 0 < h₀) {m' : ℕ} (hm' : 0 < m') (z : ℂ) :
    Periodic.qParam ((m' : ℝ) * h₀) z ^ m' = Periodic.qParam h₀ z := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have h1 : (h₀ : ℂ) ≠ 0 := by exact_mod_cast hh₀.ne'
  have h2 : (m' : ℂ) ≠ 0 := by exact_mod_cast hm'.ne'
  push_cast
  field_simp

/-- Multiplying the period by `m'` reindexes the coefficients. -/
theorem main (f : ℍ → ℂ) (h₀ : ℝ) (hh₀ : 0 < h₀)
    (hper : Periodic (f ∘ UpperHalfPlane.ofComplex) h₀)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : IsBoundedAtImInfty f)
    (m' : ℕ) (hm' : 0 < m') (i : ℕ) :
    PowerSeries.coeff i (qExpansion ((m' : ℝ) * h₀) f) =
      if m' ∣ i then PowerSeries.coeff (i / m') (qExpansion h₀ f) else 0 := by
  have hper' : Periodic (f ∘ UpperHalfPlane.ofComplex) (Complex.ofReal ((m' : ℝ) * h₀)) := by
    have e : Complex.ofReal ((m' : ℝ) * h₀) = (m' : ℕ) * (h₀ : ℂ) := by push_cast; ring
    rw [e]
    exact hper.nat_mul m'
  have hh : 0 < (m' : ℝ) * h₀ := by positivity
  let F : FnWrap := ⟨f⟩
  let a : ℕ → ℂ := fun n => PowerSeries.coeff n (qExpansion h₀ f)
  have hinj : Injective (fun n : ℕ => m' * n) := mul_right_injective₀ hm'.ne'
  let c : ℕ → ℂ := extend (fun n : ℕ => m' * n) a 0
  have hnot : ∀ i : ℕ, ¬ m' ∣ i → ¬ ∃ n, (fun n : ℕ => m' * n) n = i :=
    fun i hdiv ⟨n, hn⟩ => hdiv ⟨n, hn.symm⟩
  have hc : ∀ i, c i = if m' ∣ i then a (i / m') else 0 := by
    intro i
    split_ifs with hdiv
    · obtain ⟨n, rfl⟩ := hdiv
      show extend (fun n : ℕ => m' * n) a 0 (m' * n) = _
      rw [hinj.extend_apply, Nat.mul_div_cancel_left _ hm']
    · show extend (fun n : ℕ => m' * n) a 0 i = 0
      rw [extend_apply' _ _ _ (hnot i hdiv), Pi.zero_apply]
  have hsum : ∀ τ : ℍ, HasSum (fun i => c i • Periodic.qParam ((m' : ℝ) * h₀) τ ^ i) (F τ) := by
    intro τ
    have h1 := hasSum_qExpansion hh₀ hper hhol hbdd τ
    have heq : (fun i => c i • Periodic.qParam ((m' : ℝ) * h₀) τ ^ i) =
        extend (fun n : ℕ => m' * n) (fun n => a n • Periodic.qParam h₀ τ ^ n) 0 := by
      funext i
      rw [hc]
      split_ifs with hdiv
      · obtain ⟨n, rfl⟩ := hdiv
        rw [hinj.extend_apply, Nat.mul_div_cancel_left _ hm', pow_mul, qParam_mul_width_pow hh₀ hm']
      · rw [extend_apply' _ _ _ (hnot i hdiv), Pi.zero_apply, zero_smul]
    rw [heq, hasSum_extend_zero hinj]
    exact h1
  have huniq := qExpansion_coeff_unique F hh (analyticAt_cuspFunction_zero hh hper' hhol hbdd) hsum i

  change c i = PowerSeries.coeff i (qExpansion ((m' : ℝ) * h₀) f) at huniq
  rw [← huniq, hc]

end WidthChange

namespace ProjTranslates

open UpperHalfPlane Filter Function Complex
open QExpansionCoeff
open scoped Real Topology Manifold

variable (f : ℍ → ℂ) (h₀ : ℕ)

def trSum : ℍ → ℂ := fun τ => ∑ j ∈ Finset.range h₀, f (((j : ℕ) : ℝ) +ᵥ τ)

variable {f h₀}

theorem vadd_eq_ofComplex (x : ℝ) (τ : ℍ) : x +ᵥ τ = ofComplex ((τ : ℂ) + x) := by
  have him : 0 < ((τ : ℂ) + x).im := by simpa using τ.im_pos
  rw [ofComplex_apply_of_im_pos him]
  ext
  simp [coe_vadd, add_comm]

theorem translate_comp_ofComplex (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    f (x +ᵥ ofComplex z) = (f ∘ ofComplex) (z + x) := by
  rw [comp_apply, vadd_eq_ofComplex, ofComplex_apply_of_im_pos hz]

theorem trSum_comp_ofComplex_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    trSum f h₀ (ofComplex z) = ∑ j ∈ Finset.range h₀, (f ∘ ofComplex) (z + ((j : ℕ) : ℝ)) := by
  simp only [trSum]
  exact Finset.sum_congr rfl fun j _ => translate_comp_ofComplex (f := f) _ hz

theorem periodic_trSum (hper : Periodic (f ∘ ofComplex) (h₀ : ℝ)) :
    Periodic (trSum f h₀ ∘ ofComplex) (1 : ℝ) := by
  intro w
  by_cases hw : 0 < im w
  · have hw1 : 0 < im (w + (1 : ℝ)) := by simpa using hw
    simp only [comp_apply]
    rw [trSum_comp_ofComplex_of_im_pos hw1, trSum_comp_ofComplex_of_im_pos hw]
    have key : ∀ g : ℕ → ℂ, g h₀ = g 0 →
        ∑ j ∈ Finset.range h₀, g (j + 1) = ∑ j ∈ Finset.range h₀, g j := by
      intro g hg
      have := (Finset.sum_range_succ' g h₀).symm.trans (Finset.sum_range_succ g h₀)
      rw [← hg] at this
      exact add_right_cancel this
    have e1 : ∀ j : ℕ, w + ((1 : ℝ) : ℂ) + (((j : ℕ) : ℝ) : ℂ) = w + ((((j + 1 : ℕ)) : ℝ) : ℂ) := by
      intro j; push_cast; ring
    simp only [e1]
    refine key (fun j => (f ∘ ofComplex) (w + (((j : ℕ) : ℝ) : ℂ))) ?_
    have := hper w
    simpa [add_comm, add_left_comm] using this
  · push Not at hw
    have hw1 : im (w + (1 : ℝ)) ≤ 0 := by simpa using hw
    simp only [comp_apply, ofComplex_apply_eq_of_im_nonpos hw1 hw]

theorem mdifferentiable_trSum (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (trSum f h₀) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hhol ⊢
  have heq : Set.EqOn (trSum f h₀ ∘ ofComplex)
      (fun z => ∑ j ∈ Finset.range h₀, (f ∘ ofComplex) (z + ((j : ℕ) : ℝ))) {z | 0 < z.im} :=
    fun z hz => trSum_comp_ofComplex_of_im_pos hz
  refine DifferentiableOn.congr ?_ heq
  refine DifferentiableOn.fun_sum fun j _ => ?_
  refine hhol.comp ((differentiable_id.add_const _).differentiableOn) fun z hz => ?_
  simpa using hz

theorem isBoundedAtImInfty_trSum (hbdd : IsBoundedAtImInfty f) : IsBoundedAtImInfty (trSum f h₀) := by
  have htend : ∀ x : ℝ, Tendsto (fun τ : ℍ => x +ᵥ τ) atImInfty atImInfty := by
    intro x
    simp only [atImInfty, tendsto_comap_iff]
    have : (UpperHalfPlane.im ∘ fun τ : ℍ => x +ᵥ τ) = UpperHalfPlane.im := by
      funext τ; simp [vadd_im]
    rw [this]
    exact tendsto_comap
  have h1 : ∀ j ∈ Finset.range h₀,
      (fun τ : ℍ => f (((j : ℕ) : ℝ) +ᵥ τ)) =O[atImInfty] (1 : ℍ → ℝ) := fun j _ =>
    (hbdd.comp_tendsto (htend _))
  refine (Asymptotics.IsBigO.sum h1).congr' (Eventually.of_forall fun τ => ?_) EventuallyEq.rfl
  rw [Finset.sum_apply]; rfl

theorem qParam_vadd (x : ℝ) (τ : ℍ) :
    Periodic.qParam (h₀ : ℝ) (((x +ᵥ τ : ℍ)) : ℂ) =
      cexp (2 * π * Complex.I * x / h₀) * Periodic.qParam (h₀ : ℝ) τ := by
  simp only [Periodic.qParam, coe_vadd, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sum_exp_eq (hh₀ : 0 < h₀) (n : ℕ) :
    ∑ j ∈ Finset.range h₀, cexp (2 * π * Complex.I * ((j : ℕ) : ℝ) / h₀) ^ n =
      if h₀ ∣ n then (h₀ : ℂ) else 0 := by
  have hh₀' : (h₀ : ℂ) ≠ 0 := by exact_mod_cast hh₀.ne'

  set ζ : ℂ := cexp (2 * π * Complex.I * n / h₀) with hζ
  have hterm : ∀ j : ℕ, cexp (2 * π * Complex.I * ((j : ℕ) : ℝ) / h₀) ^ n = ζ ^ j := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    exact congrArg cexp (by push_cast; ring)
  simp only [hterm]
  have hζpow : ζ ^ h₀ = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨n, ?_⟩
    push_cast
    field_simp
  split_ifs with hdiv
  · obtain ⟨k, rfl⟩ := hdiv
    have hζ1 : ζ = 1 := by
      rw [hζ, Complex.exp_eq_one_iff]
      refine ⟨k, ?_⟩
      push_cast; field_simp
    simp [hζ1]
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      rw [hζ, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      apply hdiv
      have h2 : (n : ℂ) = k * h₀ := by
        field_simp at hk
        linear_combination hk
      have h3 : (n : ℤ) = k * h₀ := by exact_mod_cast h2
      exact Int.natCast_dvd_natCast.mp ⟨k, by rw [h3]; ring⟩
    rw [geom_sum_eq hζ1, hζpow, sub_self, zero_div]

theorem qParam_pow_h₀ (hh₀ : 0 < h₀) (z : ℂ) :
    Periodic.qParam (h₀ : ℝ) z ^ h₀ = Periodic.qParam 1 z := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (h₀ : ℂ) ≠ 0 := by exact_mod_cast hh₀.ne'
  push_cast
  field_simp

theorem main (hh₀ : 0 < h₀) (hper : Periodic (f ∘ ofComplex) (h₀ : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : IsBoundedAtImInfty f) (m : ℕ) :
    PowerSeries.coeff m (qExpansion 1 (trSum f h₀)) =
      (h₀ : ℂ) * PowerSeries.coeff (h₀ * m) (qExpansion (h₀ : ℝ) f) := by
  have hh₀r : 0 < (h₀ : ℝ) := by exact_mod_cast hh₀
  let a : ℕ → ℂ := fun n => PowerSeries.coeff n (qExpansion (h₀ : ℝ) f)
  let b : ℕ → ℂ := fun m => (h₀ : ℂ) * a (h₀ * m)
  have hinj : Injective (fun m : ℕ => h₀ * m) := mul_right_injective₀ hh₀.ne'
  have hnot : ∀ i : ℕ, ¬ h₀ ∣ i → ¬ ∃ m, (fun m : ℕ => h₀ * m) m = i :=
    fun i hdiv ⟨m, hm⟩ => hdiv ⟨m, hm.symm⟩

  have hsum1 : ∀ τ : ℍ, HasSum (fun n => ((if h₀ ∣ n then (h₀ : ℂ) else 0) * a n) •
      Periodic.qParam (h₀ : ℝ) τ ^ n) (trSum f h₀ τ) := by
    intro τ
    have hj : ∀ j ∈ Finset.range h₀, HasSum (fun n => a n • Periodic.qParam (h₀ : ℝ)
        ((((((j : ℕ) : ℝ)) +ᵥ τ : ℍ)) : ℂ) ^ n) (f (((j : ℕ) : ℝ) +ᵥ τ)) :=
      fun j _ => hasSum_qExpansion hh₀r hper hhol hbdd _
    have := hasSum_sum hj
    refine this.congr_fun fun n => ?_
    simp only [qParam_vadd, mul_pow, smul_eq_mul]
    rw [← sum_exp_eq hh₀ n, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hsum2 : ∀ τ : ℍ, HasSum (fun m => b m • Periodic.qParam 1 τ ^ m) (trSum f h₀ τ) := by
    intro τ
    have heq : (fun n => ((if h₀ ∣ n then (h₀ : ℂ) else 0) * a n) • Periodic.qParam (h₀ : ℝ) τ ^ n) =
        extend (fun m : ℕ => h₀ * m) (fun m => b m • Periodic.qParam 1 τ ^ m) 0 := by
      funext n
      split_ifs with hdiv
      · obtain ⟨m, rfl⟩ := hdiv
        rw [hinj.extend_apply, pow_mul, qParam_pow_h₀ hh₀]
      · rw [extend_apply' _ _ _ (hnot n hdiv), Pi.zero_apply, zero_mul, zero_smul]
    have := hsum1 τ
    rwa [heq, hasSum_extend_zero hinj] at this

  let F : FnWrap := ⟨trSum f h₀⟩
  have hFsum : ∀ τ : ℍ, HasSum (fun m => b m • Periodic.qParam 1 τ ^ m) (F τ) := hsum2
  have huniq := qExpansion_coeff_unique F one_pos
    (analyticAt_cuspFunction_zero one_pos (periodic_trSum hper) (mdifferentiable_trSum hhol)
      (isBoundedAtImInfty_trSum hbdd)) hFsum m
  change b m = PowerSeries.coeff m (qExpansion 1 (trSum f h₀)) at huniq
  rw [← huniq]

end ProjTranslates

namespace UpperHalfPlane

open UpperHalfPlane
open scoped Manifold

/-- If `f` decays at the cusp at least as fast as `exp (-(2 π L) · im)`, every
`q`-expansion coefficient of index `n < L` vanishes. -/
theorem qExpansion_coeff_eq_zero_of_isBigO_exp_neg (f : UpperHalfPlane → ℂ)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (L : ℝ) (hO : f =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * L) * τ.im))
    (n : ℕ) (hn : (n : ℝ) < L) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) = 0 :=
  DecayVanish.main f hper hhol hbdd L hO n hn

/-- Multiplying the strict period of `f` by a positive `m'` reindexes the
`q`-expansion coefficients: the coefficient of `i` is the coefficient of
`i / m'` of the old expansion, and it vanishes when `m' ∤ i`. -/
theorem qExpansion_coeff_mul_width (f : UpperHalfPlane → ℂ) (h₀ : ℝ) (hh₀ : 0 < h₀)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) h₀)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (m' : ℕ) (hm' : 0 < m') (i : ℕ) :
    PowerSeries.coeff i (UpperHalfPlane.qExpansion ((m' : ℝ) * h₀) f) =
      if m' ∣ i then PowerSeries.coeff (i / m') (UpperHalfPlane.qExpansion h₀ f) else 0 :=
  WidthChange.main f h₀ hh₀ hper hhol hbdd m' hm' i

/-- The `q`-expansion of the sum of the `h₀` translates of `f` is `h₀` times the
period-`h₀` expansion in degree `h₀ * m`. -/
theorem qExpansion_coeff_sum_vAdd_eq_mul_coeff (f : UpperHalfPlane → ℂ) (h₀ : ℕ) (hh₀ : 0 < h₀)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (h₀ : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1
        (fun τ : UpperHalfPlane => ∑ j ∈ Finset.range h₀, f (((j : ℕ) : ℝ) +ᵥ τ))) =
      (h₀ : ℂ) * PowerSeries.coeff (h₀ * m) (UpperHalfPlane.qExpansion (h₀ : ℝ) f) :=
  ProjTranslates.main hh₀ hper hhol hbdd m

end UpperHalfPlane
