/-
  Stone–Weierstrass vanishing criterion for continuous functions:

      `(∀ f ∈ A, ∫ x, f x * β x ∂μ = 0) → (β : X → ℂ) =ᵐ[μ] 0`

  for a point-separating `⋆`-subalgebra `A ≤ C(X, ℂ)` on a compact Hausdorff `X`
  and a finite measure `μ`.

  The port of the pin leaf `ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero`
  (68 pin lines), together with the statement of its `Theorems/` wrapper.

  The mathematics: `Φ f = ∫ x, f x * β x ∂μ` is continuous in `f` on `C(X, ℂ)` (a
  Lipschitz estimate against `‖f‖ ‖β‖ μ(univ)`), so its zero set is closed; it
  contains the dense `A`, hence also `star β`; then `Φ (star β) = ∫ ‖β‖²` is
  `0`, and a nonnegative integrable function with zero integral vanishes a.e.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has no such criterion — `rg -n
  "ae_eq_zero_of_forall_mem_starSubalgebra"` and `rg -n
  "integral_mul_eq_zero"` over `Mathlib/` find nothing. The ingredients
  (`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`,
  `StarSubalgebra.topologicalClosure_coe`, `integral_eq_zero_iff_of_nonneg`,
  `integral_complex_ofReal`) are imported, not restated.

  spec-pin: Theorems/Thm_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero.lean
  spec-pin: P2M/Sol/S_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero.lean
-/
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.RCLike.Lemmas

set_option autoImplicit false

open MeasureTheory

theorem ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (A : StarSubalgebra ℂ C(X, ℂ)) (hA : A.SeparatesPoints)
    (β : C(X, ℂ))
    (h : ∀ f ∈ A, ∫ x, f x * β x ∂μ = 0) :
    (β : X → ℂ) =ᵐ[μ] 0 := by
  classical

  have hInt : ∀ f : C(X, ℂ), Integrable (fun x => f x) μ := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

  set Φ : C(X, ℂ) → ℂ := fun f => ∫ x, f x * β x ∂μ with hΦ
  have hL : ∀ f g : C(X, ℂ), ‖Φ f - Φ g‖ ≤ ‖f - g‖ * ‖β‖ * (μ Set.univ).toReal := by
    intro f g
    have hfg : Φ f - Φ g = ∫ x, (f - g) x * β x ∂μ := by
      simp only [hΦ, ContinuousMap.sub_apply, sub_mul]
      rw [integral_sub]
      · exact (hInt (f * β))
      · exact (hInt (g * β))
    rw [hfg]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (ContinuousMap.norm_coe_le_norm (f - g) x) (ContinuousMap.norm_coe_le_norm β x)
      (norm_nonneg _) (norm_nonneg _)
  have hcont : Continuous Φ := by
    refine continuous_iff_continuousAt.2 fun f₀ => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun f => norm_nonneg _) (fun f => hL f f₀) ?_
    have hc : Continuous fun f : C(X, ℂ) => ‖f - f₀‖ * ‖β‖ * (μ Set.univ).toReal := by fun_prop
    simpa using hc.tendsto f₀

  have hcl : IsClosed {f : C(X, ℂ) | Φ f = 0} := isClosed_eq hcont continuous_const
  have hsub : (A : Set C(X, ℂ)) ⊆ {f : C(X, ℂ) | Φ f = 0} := fun f hf => h f hf
  have hclos : closure (A : Set C(X, ℂ)) ⊆ {f : C(X, ℂ) | Φ f = 0} := closure_minimal hsub hcl
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  have hmem : star β ∈ closure (A : Set C(X, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]
    exact StarSubalgebra.mem_top
  have hzero : Φ (star β) = 0 := hclos hmem

  have hsq : ∫ x, (‖β x‖ ^ 2 : ℝ) ∂μ = 0 := by
    have h1 : Φ (star β) = ((∫ x, (‖β x‖ ^ 2 : ℝ) ∂μ : ℝ) : ℂ) := by
      have hfun : (fun x => (star β) x * β x) = fun x => (((‖β x‖ ^ 2 : ℝ)) : ℂ) := by
        funext x
        simp only [ContinuousMap.star_apply, RCLike.star_def, Complex.conj_mul', Complex.ofReal_pow]
      simp only [hΦ]
      rw [hfun]
      exact integral_complex_ofReal
    rw [hzero] at h1
    exact_mod_cast h1.symm
  have hint2 : Integrable (fun x => (‖β x‖ ^ 2 : ℝ)) μ :=
    (β.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint2).1 hsq
  filter_upwards [hae] with x hx
  simpa [sq_eq_zero_iff, norm_eq_zero] using hx
