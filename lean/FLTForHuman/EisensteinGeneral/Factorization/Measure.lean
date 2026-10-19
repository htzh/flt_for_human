/-
  The stratum measure `rhoT F ν T` on `GT F T × YT F T` and the two facts that make it a
  product measure: translation invariance in the `GT` coordinate
  (`rhoT_map_add_left`) and finiteness on `K ×ˢ univ` for compact `K`
  (`rhoT_prod_univ_lt_top`).  Together with the recognition theorem of
  `Factorization/ProductMeasure.lean` they give `exists_rhoT_eq_prod`: the stratum measure
  is `Measure.pi (μ ·) .prod σ` for a finite measure `σ` on the outside-integral part,
  and the Haar measure of the box `integralFiniteAdeles` factors as
  `∏ v ∈ T, μ v (integers) * σ univ`.

  The mathematics: `setIntegral_stratumSet_eq` and `integrableOn_stratumSet_iff` move an
  integral over the open set `stratumSet F T` to the homeomorphic product
  `GT F T × YT F T` (`MeasurableEmbedding.map_comap` + `integral_map_equiv`), and
  `comap_incl_map_add_left` proves that `ν.comap (incl F T)` is invariant under adding a
  point of the stratum — which is `split_add_symm` read through the homeomorphism
  `split`.  The two `measureReal_*_ne_zero` lemmas in `section StratumIdentity` are the
  non-vanishing of the normalizing constants (openness + compactness of the closed box).

  Pin `anthropics/fermats-last-theorem@aa2d8b3`,
  `P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:287-438`
  (`section Measures` + `section StratumIdentity`), mathlib `v4.34.0`.  The pin's
  `private` becomes public (§1 of the work order lists this module) and the `omit [...] in`
  clauses are kept as written.  Statement spelling: the pin writes
  `AdelicBox.integralFiniteAdeles` in `exists_rhoT_eq_prod` and `measureReal_box_ne_zero`, and
  the port keeps that spelling — it is the port-only reducible alias of
  `NumberField.AdelicLevel.integralFiniteAdeles` declared in
  `NumberTheory/AdelicHaar/PlaceMeasure.lean` for exactly this pin name, which is why this
  module imports it.  Elsewhere the pin writes the term bare and so does the port.
-/
import FLTForHuman.EisensteinGeneral.Factorization.ProductMeasure
import FLTForHuman.EisensteinGeneral.Factorization.Stratum
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

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

section Measures

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
-- pin: measurableEmbedding_incl (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:297)
theorem measurableEmbedding_incl (T : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableEmbedding (incl F T) :=
  (isOpenEmbedding_incl F T).measurableEmbedding

-- pin: rhoT (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:300)
def rhoT (T : Finset (HeightOneSpectrum (𝓞 F))) : Measure (GT F T × YT F T) :=
  (ν.comap (incl F T)).map (split F T).toMeasurableEquiv

omit [ν.IsAddHaarMeasure] in

-- pin: setIntegral_stratumSet_eq (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:305)
theorem setIntegral_stratumSet_eq (T : Finset (HeightOneSpectrum (𝓞 F))) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : FiniteAdeleRing (𝓞 F) F → E) :
    ∫ x in stratumSet F T, f x ∂ν = ∫ p, f (incl F T ((split F T).symm p)) ∂(rhoT F ν T) := by
  rw [← range_incl F T, ← (measurableEmbedding_incl F T).map_comap ν,
    (measurableEmbedding_incl F T).integral_map]
  unfold rhoT
  rw [integral_map_equiv]
  simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply]

omit [ν.IsAddHaarMeasure] in

-- pin: integrableOn_stratumSet_iff (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:316)
theorem integrableOn_stratumSet_iff (T : Finset (HeightOneSpectrum (𝓞 F))) {E : Type*} [NormedAddCommGroup E]
    (f : FiniteAdeleRing (𝓞 F) F → E) :
    IntegrableOn f (stratumSet F T) ν ↔ Integrable (fun p => f (incl F T ((split F T).symm p))) (rhoT F ν T) := by
  rw [IntegrableOn, ← range_incl F T, ← (measurableEmbedding_incl F T).map_comap ν,
    (measurableEmbedding_incl F T).integrable_map_iff]
  unfold rhoT
  rw [integrable_map_equiv]
  have hfg : (fun p : GT F T × YT F T => f (incl F T ((split F T).symm p))) ∘ (split F T).toMeasurableEquiv
      = f ∘ incl F T := by
    funext x
    simp only [Function.comp_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply]
  rw [hfg]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in

-- pin: comap_incl_map_add_left (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:332)
theorem comap_incl_map_add_left (T : Finset (HeightOneSpectrum (𝓞 F))) (b : Stratum F T) :
    (ν.comap (incl F T)).map (fun x => b + x) = ν.comap (incl F T) := by
  have hme := measurableEmbedding_incl F T
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_add b) hs, hme.comap_apply, hme.comap_apply]
  have hset : incl F T '' ((fun x => b + x) ⁻¹' s) = (fun y => incl F T b + y) ⁻¹' (incl F T '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨b + x, hx, incl_add T b x⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨z - b, ?_, ?_⟩
      · show b + (z - b) ∈ s
        rwa [add_sub_cancel]
      · rw [incl_sub, hzy, add_sub_cancel_left]
  rw [hset, measure_preimage_add]

-- pin: rhoT_map_add_left (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:349)
theorem rhoT_map_add_left (T : Finset (HeightOneSpectrum (𝓞 F))) (a : GT F T) :
    (rhoT F ν T).map (fun p : GT F T × YT F T => (a + p.1, p.2)) = rhoT F ν T := by
  have hTa : Measurable fun p : GT F T × YT F T => (a + p.1, p.2) :=
    (measurable_fst.const_add a).prodMk measurable_snd
  have hem : Measurable (split F T).toMeasurableEquiv := (split F T).toMeasurableEquiv.measurable
  have hconj : (fun p : GT F T × YT F T => (a + p.1, p.2)) ∘ (split F T).toMeasurableEquiv
      = (split F T).toMeasurableEquiv ∘ fun x => (split F T).symm (a, 0) + x := by
    funext x
    simp only [Function.comp_apply, Homeomorph.toMeasurableEquiv_coe]
    have h := split_add_symm F T a (split F T x)
    rw [Homeomorph.symm_apply_apply] at h
    exact h.symm
  unfold rhoT
  rw [Measure.map_map hTa hem, hconj, ← Measure.map_map hem (measurable_const_add _), comap_incl_map_add_left]

-- pin: rhoT_prod_univ_lt_top (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:364)
theorem rhoT_prod_univ_lt_top (T : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (GT F T)) (hK : IsCompact K) :
    rhoT F ν T (K ×ˢ Set.univ) < ∞ := by
  unfold rhoT
  rw [MeasurableEquiv.map_apply, (measurableEmbedding_incl F T).comap_apply, Homeomorph.toMeasurableEquiv_coe,
    ← Homeomorph.image_symm]
  exact (((hK.prod isCompact_univ).image (split F T).symm.continuous).image
    (isOpenEmbedding_incl F T).continuous).measure_lt_top

-- pin: exists_rhoT_eq_prod (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:372)
theorem exists_rhoT_eq_prod (T : Finset (HeightOneSpectrum (𝓞 F)))
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure] :
    ∃ σ : Measure (YT F T), IsFiniteMeasure σ ∧
      rhoT F ν T = (Measure.pi fun i : ↥T => μ i.1).prod σ ∧
      ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)
        = (∏ v ∈ T, μ v (v.adicCompletionIntegers F : Set (v.adicCompletion F))) * σ Set.univ := by
  obtain ⟨σ, hσfin, hρ⟩ := exists_eq_prod_of_forall_map_add_left (Measure.pi fun i : ↥T => μ i.1) (rhoT F ν T)
    (rhoT_map_add_left F ν T) (rhoT_prod_univ_lt_top F ν T)
  haveI := hσfin
  refine ⟨σ, hσfin, hρ, ?_⟩

  have hbox : AdelicBox.integralFiniteAdeles (𝓞 F) F = incl F T '' ((split F T).toMeasurableEquiv ⁻¹'
      ((Set.univ.pi fun i : ↥T => ((i.1).adicCompletionIntegers F : Set ((i.1).adicCompletion F))) ×ˢ
        (Set.univ : Set (YT F T)))) := by
    rw [Homeomorph.toMeasurableEquiv_coe]
    ext y
    constructor
    · intro hy
      have hy' : y ∈ Set.range (incl F T) := by
        rw [range_incl]
        exact fun v _ => hy v
      obtain ⟨x, rfl⟩ := hy'
      refine ⟨x, ?_, rfl⟩
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Set.mem_univ_pi, split_apply,
        splitFun_fst]
      exact fun i => hy i.1
    · rintro ⟨x, hx, rfl⟩ v
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Set.mem_univ_pi, split_apply,
        splitFun_fst] at hx
      by_cases hv : v ∈ T
      · exact hx ⟨v, hv⟩
      · exact mem_of_not_mem x hv
  rw [hbox, ← (measurableEmbedding_incl F T).comap_apply, ← MeasurableEquiv.map_apply]
  show rhoT F ν T _ = _
  rw [hρ, Measure.prod_prod, Measure.pi_pi]
  congr 1
  exact Finset.prod_coe_sort T fun v => μ v (v.adicCompletionIntegers F : Set (v.adicCompletion F))

end Measures

section StratumIdentity

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
-- pin: measureReal_integers_ne_zero (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:423)
theorem measureReal_integers_ne_zero (v : HeightOneSpectrum (𝓞 F)) :
    (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ 0 := by
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  have hc : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers F) from inferInstance)
  exact ⟨((isOpen_adicCompletionIntegers F v).measure_pos (μ v) ⟨0, zero_mem _⟩).ne', hc.measure_lt_top.ne⟩

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
-- pin: measureReal_box_ne_zero (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:432)
theorem measureReal_box_ne_zero :
    ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) ≠ 0 := by
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨((AdelicBox.isOpen_integralFiniteAdeles F).measure_pos ν ⟨0, fun v => zero_mem _⟩).ne',
    (AdelicBox.isCompact_integralFiniteAdeles F).measure_ne_top⟩

end StratumIdentity

end FiniteAdelicFactorization

end EisensteinGeneral
