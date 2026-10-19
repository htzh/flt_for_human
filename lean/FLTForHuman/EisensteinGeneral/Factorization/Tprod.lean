/-
  The Euler product: integrability on a stratum, the `L¹` norm identity that bounds it,
  and the convergence of the normalized local integrals.

  The mathematics: `integrableOn_finprod_stratumSet` pushes the integrand to the product
  `GT F T × YT F T`, where it is the finite product over `T` (`finprod_incl_split_symm`)
  times the constant `1` in the outside-integral coordinates, hence integrable by
  `Integrable.fintype_prod_dep`.  `setIntegral_norm_finprod_stratumSet_eq` evaluates the
  norm integral over the stratum as `ν(integralFiniteAdeles) * ∏ v ∈ T, β v` — the box
  measure times the normalized local norms `β v` — using `exists_rhoT_eq_prod` and
  Fubini over a finite product (`integral_fintype_prod_eq_prod`).  The last three
  declarations are the product-convergence input: `measureReal_integers_le_integral_norm`
  bounds the local norm below by the measure of the integers,
  `norm_normalized_integral_sub_one_le` bounds the distance of `a v` from `1` by
  `β v - 1` (splitting the integral at the integers and applying the norm triangle
  inequality), and `multipliable_normalized_integral` concludes that the family
  `a v = μ(integers)⁻¹ * ∫ h v` is `Multipliable` from the summability of `β v - 1`
  (`multipliable_one_add_of_summable` plus `Multipliable.mul_compl` for the finite
  exceptional set `S`).

  Pin `anthropics/fermats-last-theorem@aa2d8b3`,
  `P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:601-749`
  (the rest of `section LocalIntegrals` / `section Assembly`), mathlib `v4.34.0`.  The
  pin's `private` becomes public (the module is listed); the proofs are transcribed
  unchanged.
-/
import FLTForHuman.EisensteinGeneral.Factorization.Integrability
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false

-- The pin's `haveI` declarations are load-bearing: they feed instance search.
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField

open IsDedekindDomain.HeightOneSpectrum Filter Topology
open NumberField.AdelicLevel
open scoped RestrictedProduct ENNReal NNReal

namespace EisensteinGeneral

namespace FiniteAdelicFactorization

attribute [local instance] countable_heightOneSpectrum

variable (F : Type) [Field F] [NumberField F]

section Assembly

-- pin: integrableOn_finprod_stratumSet (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:601)
theorem integrableOn_finprod_stratumSet
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1)
    (hint : ∀ v : HeightOneSpectrum (𝓞 F), Integrable (h v) (μ v)) :
    IntegrableOn (fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v))
      (stratumSet F T) ν := by
  rw [integrableOn_stratumSet_iff]
  obtain ⟨σ, hσfin, hρ, -⟩ := exists_rhoT_eq_prod F ν T μ
  haveI := hσfin
  have hfun : (fun p : GT F T × YT F T =>
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (incl F T ((split F T).symm p) v))
      = fun p => (∏ i : ↥T, h i.1 (p.1 i)) * (fun _ : YT F T => (1 : ℂ)) p.2 := by
    funext p
    rw [mul_one]
    exact finprod_incl_split_symm F hST h h₁ p
  rw [hfun, hρ]
  exact (Integrable.fintype_prod_dep fun i : ↥T => hint i.1).mul_prod (integrable_const (1 : ℂ))

-- pin: setIntegral_norm_finprod_stratumSet_eq (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:625)
theorem setIntegral_norm_finprod_stratumSet_eq
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1) :
    ∫ x in stratumSet F T, ‖∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)‖ ∂ν
      = ν.real (integralFiniteAdeles (𝓞 F) F)
        * ∏ v ∈ T, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹ * ∫ y, ‖h v y‖ ∂(μ v)) := by
  obtain ⟨σ, hσfin, hρ, hboxm⟩ := exists_rhoT_eq_prod F ν T μ
  haveI := hσfin
  have hI : ∫ x in stratumSet F T, ‖∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)‖ ∂ν
      = σ.real Set.univ * ∏ v ∈ T, ∫ y, ‖h v y‖ ∂(μ v) := by
    rw [setIntegral_stratumSet_eq]
    have hfun : (fun p : GT F T × YT F T =>
          ‖∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (incl F T ((split F T).symm p) v)‖)
        = fun p => (fun g : GT F T => ∏ i : ↥T, ‖h i.1 (g i)‖) p.1 := by
      funext p
      rw [finprod_incl_split_symm F hST h h₁ p, norm_prod]
    have hfst := integral_fun_fst (μ := Measure.pi fun i : ↥T => μ i.1) (ν := σ)
      (fun g : GT F T => ∏ i : ↥T, ‖h i.1 (g i)‖)
    have hprod : ∫ g : GT F T, ∏ i : ↥T, ‖h i.1 (g i)‖ ∂(Measure.pi fun i : ↥T => μ i.1)
        = ∏ i : ↥T, ∫ y, ‖h i.1 y‖ ∂(μ i.1) :=
      integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun i : ↥T => μ i.1)
        (fun (i : ↥T) (y : i.1.adicCompletion F) => ‖h i.1 y‖)
    rw [hfun, hρ, hfst, hprod, smul_eq_mul]
    congr 1
    exact Finset.prod_coe_sort T fun v => ∫ y, ‖h v y‖ ∂(μ v)
  have hbox : ν.real (integralFiniteAdeles (𝓞 F) F)
      = (∏ v ∈ T, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))) * σ.real Set.univ := by
    simp only [measureReal_def]
    rw [hboxm, ENNReal.toReal_mul, ENNReal.toReal_prod]
  have hT : (∏ v ∈ T, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => measureReal_integers_ne_zero F μ v
  rw [hI, hbox, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  field_simp

-- pin: measureReal_integers_le_integral_norm (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:665)
theorem measureReal_integers_le_integral_norm
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (v : HeightOneSpectrum (𝓞 F)) {k : v.adicCompletion F → ℂ} (hk : Integrable k (μ v))
    (hk₁ : ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → k y = 1) :
    (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≤ ∫ y, ‖k y‖ ∂(μ v) := by
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (isOpen_adicCompletionIntegers F v).measurableSet
  have h1 : ∫ y in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖k y‖ ∂(μ v)
      = ∫ _ in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), (1 : ℝ) ∂(μ v) :=
    setIntegral_congr_fun hO fun y hy => by simp only [hk₁ y hy, norm_one]
  calc (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ∫ y in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖k y‖ ∂(μ v) := by
        rw [h1, setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ ∫ y, ‖k y‖ ∂(μ v) := setIntegral_le_integral hk.norm (ae_of_all _ fun y => norm_nonneg (k y))

-- pin: norm_normalized_integral_sub_one_le (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:682)
theorem norm_normalized_integral_sub_one_le
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (v : HeightOneSpectrum (𝓞 F)) {k : v.adicCompletion F → ℂ} (hk : Integrable k (μ v))
    (hk₁ : ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → k y = 1) :
    ‖(((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹ * ∫ y, k y ∂(μ v)) - 1‖
      ≤ ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹ * (∫ y, ‖k y‖ ∂(μ v)) - 1 := by
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (isOpen_adicCompletionIntegers F v).measurableSet
  have hm0 : (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ 0 :=
    measureReal_integers_ne_zero F μ v
  have hkO : ∫ y in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), k y ∂(μ v)
      = ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ) := by
    rw [setIntegral_congr_fun hO (g := fun _ => (1 : ℂ)) fun y hy => hk₁ y hy, setIntegral_const,
      Complex.real_smul, mul_one]
  have hnO : ∫ y in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖k y‖ ∂(μ v)
      = (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rw [setIntegral_congr_fun hO (g := fun _ => (1 : ℝ)) fun y hy => by simp only [hk₁ y hy, norm_one],
      setIntegral_const, smul_eq_mul, mul_one]
  have hsplit := (integral_add_compl hO hk).symm
  have hsplitn := (integral_add_compl hO hk.norm).symm
  have hkey : (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹ * ∫ y, k y ∂(μ v)) - 1
      = ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
          * ∫ y in (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ, k y ∂(μ v) := by
    have hc : ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ) ≠ 0 := by exact_mod_cast hm0
    rw [hsplit, hkO]
    field_simp
    ring
  have hbound : ‖∫ y in (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ, k y ∂(μ v)‖
      ≤ ∫ y in (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ, ‖k y‖ ∂(μ v) :=
    norm_integral_le_integral_norm _
  have hrhs : ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹ * (∫ y, ‖k y‖ ∂(μ v)) - 1
      = ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
          * ∫ y in (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ, ‖k y‖ ∂(μ v) := by
    rw [hsplitn, hnO]
    field_simp
    ring
  rw [hkey, hrhs, ← Complex.ofReal_inv, ← Complex.real_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr measureReal_nonneg)]
  exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr measureReal_nonneg)

-- pin: multipliable_normalized_integral (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:724)
theorem multipliable_normalized_integral
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1)
    (hint : ∀ v : HeightOneSpectrum (𝓞 F), Integrable (h v) (μ v))
    (hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ((μ v.1).real (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)))⁻¹
          * (∫ y, ‖h v.1 y‖ ∂(μ v.1)) - 1) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) =>
      (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹ * ∫ y, h v y ∂(μ v)) := by
  have hnorm : Summable fun v : ↥((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) =>
      ‖(((μ v.1).real (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) : ℂ)⁻¹
          * ∫ y, h v.1 y ∂(μ v.1)) - 1‖ :=
    Summable.of_nonneg_of_le (fun v => norm_nonneg _)
      (fun v => norm_normalized_integral_sub_one_le F μ v.1 (hint v.1) (h₁ v.1 v.2)) hsum
  have hc : Multipliable fun v : ↥((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) =>
      (((μ v.1).real (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) : ℂ)⁻¹
        * ∫ y, h v.1 y ∂(μ v.1)) :=
    (multipliable_one_add_of_summable hnorm).congr fun v => by ring
  exact Multipliable.mul_compl (s := (S : Set (HeightOneSpectrum (𝓞 F)))) Multipliable.of_finite hc

end Assembly

end FiniteAdelicFactorization

end EisensteinGeneral
