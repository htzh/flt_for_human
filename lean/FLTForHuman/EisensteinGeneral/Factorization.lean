/-
  The factorization of the finite-adelic integral into an Euler product — the headline of
  the set.

  For a number field `F`, a Haar measure `ν` on the finite adèles, local Haar measures
  `μ v` and local factors `h v` that are integrable, are `1` on the integer ring outside a
  finite set `S` of places, and whose normalized norms satisfy
  `∑' v ∉ S, (μ v (integers))⁻¹ * ∫ ‖h v‖ - 1 < ∞`, the function
  `x ↦ ∏ᶠ v, h v (x v)` is integrable and its integral, normalized by the Haar measure of
  the box `integralFiniteAdeles`, is the Euler product `∏' v, (μ v (integers))⁻¹ * ∫ h v`.

  The proof is the pin's, taken whole: an exhaustive increasing sequence of strata
  `stratumSet F (T n)` (`exists_exhaustion`) reduces integrability to a uniform bound on
  `∫_{stratumSet F (T n)} ‖∏ᶠ v, h v (x v)‖` (`integrable_of_forall_setIntegral_norm_le`),
  which `setIntegral_norm_finprod_stratumSet_eq` evaluates as
  `ν(box) * ∏ v ∈ T n, β v` and bounds by `ν(box) * (∏ v ∈ S, β v) * exp (∑' v ∉ S, β v - 1)`
  (using `β v ≥ 1` outside `S` and `log β ≤ β - 1`).  Then
  `inv_measure_mul_setIntegral_integralOffSet_finprod_eq` identifies the normalized
  stratum integrals with the finite products `∏ v ∈ T n, a v`, and the two limits —
  monotone convergence on strata and `Multipliable.hasProd` for `a`
  (`multipliable_normalized_integral`) — agree, so the normalized integral is `∏' v, a v`
  (`tendsto_nhds_unique`).

  This is the **listed façade** of the set: one declaration, its statement copied verbatim
  from the pin's wrapper
  `Theorems/Thm_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:10-27`
  (= `P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:750-768`),
  at the wrapper's dotted name; its proof is the pin's `solution` body
  (`S_…:769-832`), the pin's `private theorem
  FiniteAdelicFactorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod` being
  the same statement and therefore not ported twice.  The five engines it stands on are
  `Factorization/{ProductMeasure,Stratum,Measure,Integrability,Tprod}.lean`.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`, mathlib `v4.34.0`.  The pin's `p2m_*`
  scaffolding, its `section Assembly` wrapper and its final `#print axioms` are dropped; no
  `maxHeartbeats` is set.
-/
import FLTForHuman.EisensteinGeneral.Factorization.ProductMeasure
import FLTForHuman.EisensteinGeneral.Factorization.Stratum
import FLTForHuman.EisensteinGeneral.Factorization.Measure
import FLTForHuman.EisensteinGeneral.Factorization.Integrability
import FLTForHuman.EisensteinGeneral.Factorization.Tprod
import Mathlib.Topology.Algebra.InfiniteSum.Order

set_option autoImplicit false

-- The pin's `haveI` declarations are load-bearing: they feed instance search.
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField

open IsDedekindDomain.HeightOneSpectrum Filter Topology
open NumberField.AdelicLevel
open EisensteinGeneral.FiniteAdelicFactorization
open scoped RestrictedProduct ENNReal NNReal

attribute [local instance] countable_heightOneSpectrum

-- pin: integrable_finprod_and_inv_measure_mul_integral_eq_tprod (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:750)
theorem EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1)
    (hint : ∀ v : HeightOneSpectrum (𝓞 F), Integrable (h v) (μ v))
    (hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ((μ v.1).real (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)))⁻¹
          * (∫ y, ‖h v.1 y‖ ∂(μ v.1)) - 1) :
    Integrable (fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)) ν ∧
      (ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
          * ∫ x, ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν
        = ∏' v : HeightOneSpectrum (𝓞 F),
            (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
              * ∫ y, h v y ∂(μ v)) := by
  classical
  obtain ⟨T, hTmono, hST, hTcov⟩ := exists_exhaustion F S
  have hAmeas : ∀ n, MeasurableSet (stratumSet F (T n)) := fun n => (isOpen_stratumSet F (T n)).measurableSet
  have hAmono : Monotone fun n => stratumSet F (T n) := fun m n hmn => stratumSet_mono F (hTmono hmn)
  have hU : (⋃ n, stratumSet F (T n)) = Set.univ := iUnion_stratumSet_eq_univ F hTmono hTcov
  set β : HeightOneSpectrum (𝓞 F) → ℝ :=
    fun v => ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹ * ∫ y, ‖h v y‖ ∂(μ v) with hβ_def
  have hsum' : Summable fun w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => β w.1 - 1 := hsum
  have hβ₁ : ∀ v ∉ S, 1 ≤ β v := by
    intro v hv
    have hmpos : 0 < (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      lt_of_le_of_ne measureReal_nonneg (measureReal_integers_ne_zero F μ v).symm
    rw [hβ_def]
    dsimp only
    rw [inv_mul_eq_div, one_le_div hmpos]
    exact measureReal_integers_le_integral_norm F μ v (hint v) (h₁ v hv)
  have hβ₀ : ∀ v, 0 ≤ β v := fun v =>
    mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg fun y => norm_nonneg _)
  set c : ℝ := ν.real (integralFiniteAdeles (𝓞 F) F) with hc_def
  set B : ℝ := ∏ v ∈ S, β v with hB_def
  set E : ℝ := Real.exp (∑' w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (β w.1 - 1)) with hE_def
  have hI : Integrable (fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)) ν := by
    refine integrable_of_forall_setIntegral_norm_le (fun n => stratumSet F (T n)) hAmeas hAmono
      (exists_mem_stratumSet F hTmono hTcov)
      (fun n => integrableOn_finprod_stratumSet F ν μ (hST n) h h₁ hint) (c * B * E) fun n => ?_
    have hn : ∫ x in stratumSet F (T n), ‖∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)‖ ∂ν
        = c * ∏ v ∈ T n, β v := setIntegral_norm_finprod_stratumSet_eq F ν μ (hST n) h h₁
    have htail : ∏ v ∈ T n \ S, β v ≤ E := by
      calc ∏ v ∈ T n \ S, β v ≤ ∏ v ∈ T n \ S, Real.exp (β v - 1) :=
            Finset.prod_le_prod₀ (fun v _ => hβ₀ v) fun v _ => by
              linarith [Real.add_one_le_exp (β v - 1)]
        _ = Real.exp (∑ v ∈ T n \ S, (β v - 1)) := (Real.exp_sum _ _).symm
        _ ≤ E := by
            refine Real.exp_le_exp.mpr ?_
            rw [← Finset.sum_subtype_of_mem (f := fun v => β v - 1) (p := fun v => v ∉ S)
              fun v hv => (Finset.mem_sdiff.mp hv).2]
            exact hsum'.sum_le_tsum _ fun w _ => sub_nonneg.mpr (hβ₁ w.1 w.2)
    have hcB : 0 ≤ c * B := mul_nonneg measureReal_nonneg (Finset.prod_nonneg fun v _ => hβ₀ v)
    calc ∫ x in stratumSet F (T n), ‖∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)‖ ∂ν
        = c * ((∏ v ∈ T n \ S, β v) * B) := by rw [hn, hB_def, Finset.prod_sdiff (hST n)]
      _ = c * B * ∏ v ∈ T n \ S, β v := by ring
      _ ≤ c * B * E := mul_le_mul_of_nonneg_left htail hcB
  refine ⟨hI, ?_⟩
  set a : HeightOneSpectrum (𝓞 F) → ℂ :=
    fun v => (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹ * ∫ y, h v y ∂(μ v))
    with ha_def
  have hmult : Multipliable a := multipliable_normalized_integral F μ S h h₁ hint hsum
  have hstar : ∀ n, (ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
      * ∫ x in stratumSet F (T n), ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν = ∏ v ∈ T n, a v :=
    fun n => inv_measure_mul_setIntegral_integralOffSet_finprod_eq F ν (T n) μ h
      fun v hv => h₁ v fun hvS => hv (hST n hvS)
  have hlimI : Tendsto (fun n => ∫ x in stratumSet F (T n), ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν)
      atTop (𝓝 (∫ x, ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν)) := by
    have hlim := tendsto_setIntegral_of_monotone (μ := ν)
      (f := fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v))
      hAmeas hAmono hI.integrableOn
    rwa [hU, setIntegral_univ] at hlim
  have hlimP : Tendsto (fun n => ∏ v ∈ T n, a v) atTop (𝓝 (∏' v, a v)) :=
    hmult.hasProd.comp (tendsto_atTop_finset_of_monotone hTmono hTcov)
  have hL : Tendsto (fun n => ∏ v ∈ T n, a v) atTop
      (𝓝 ((ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * ∫ x, ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν)) :=
    (hlimI.const_mul ((ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹)).congr hstar
  exact tendsto_nhds_unique hL hlimP
