/-
  The two generic integrability devices and the stratum exhaustion, plus the first half of
  the assembly: the finiteness of the finite product over `T` and the identity
  `inv_measure_mul_setIntegral_integralOffSet_finprod_eq`.

  The mathematics: `integrable_of_forall_setIntegral_norm_le` is a monotone-convergence
  criterion — an a.e.-strongly-measurable function whose integrals over an increasing
  covering sequence of measurable sets are uniformly bounded is integrable
  (`lintegral_iSup'` on `‖·‖ₑ`).  `exists_exhaustion` produces such a covering by
  strata `stratumSet F (T n)` (an increasing exhaustive sequence of finite sets of places
  from countability of the spectrum), so `iUnion_stratumSet_eq_univ` says every finite
  adèle is integral outside some `T n`.  `finprod_incl_split_symm` evaluates the infinite
  product of the local factors along the stratum: because `h v = 1` on the integers
  outside `S`, the `finprod` collapses to the finite product over `T`
  (`finprod_eq_prod_of_mulSupport_subset`).  Finally
  `inv_measure_mul_setIntegral_integralOffSet_finprod_eq` normalizes: the integral over
  the box of `∏ᶠ v, h v (x v)` is `σ univ` times the product of the local integrals over
  `T`, and dividing by the Haar measure of the box leaves exactly the product over `S` of
  the normalized local integrals.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`,
  `P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:440-600`
  (`section Generic` + `section LocalIntegrals` + the first half of `section FinitePlaces`),
  mathlib `v4.34.0`.  The pin's `private` becomes public (the module is listed).

  One declaration is a **substitution**, not a transcription: the pin's `integralOffSet`
  (`:531`) is by definition the port's `NumberField.TateGlobal.ShellSupport.integralOff`
  (`NumberTheory/NumberField/TateGlobal/ShellSupport.lean:44`, the same body
  `{x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}`), so the port declares it as a
  one-line alias to that landed definition instead of a second copy of the set; all the
  proofs below are the pin's, unchanged, and every downstream statement keeps the pin's
  text.
-/
import FLTForHuman.EisensteinGeneral.Factorization.Measure
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ShellSupport
import Mathlib.MeasureTheory.Integral.Pi

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

section Generic

-- pin: integrable_of_forall_setIntegral_norm_le (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:442)
theorem integrable_of_forall_setIntegral_norm_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E : Type*} [NormedAddCommGroup E] {f : X → E} (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) (hcov : ∀ x, ∃ n, x ∈ A n) (hint : ∀ n, IntegrableOn f (A n) μ) (M : ℝ)
    (hbd : ∀ n, ∫ x in A n, ‖f x‖ ∂μ ≤ M) : Integrable f μ := by
  have hU : (⋃ n, A n) = Set.univ := Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (hcov x)
  refine ⟨?_, ?_⟩
  · have h := (aestronglyMeasurable_iUnion_iff (μ := μ) (f := f) (s := A)).mpr
      fun n => (hint n).aestronglyMeasurable
    rwa [hU, Measure.restrict_univ] at h
  · rw [hasFiniteIntegral_iff_enorm]
    have hg_meas : ∀ n, AEMeasurable ((A n).indicator fun x => ‖f x‖ₑ) μ := fun n =>
      (aemeasurable_indicator_iff (hA n)).mpr (hint n).aestronglyMeasurable.enorm
    have hg_mono : ∀ x, Monotone fun n => (A n).indicator (fun x => ‖f x‖ₑ) x := fun x m n hmn =>
      Set.indicator_le_indicator_of_subset (hmono hmn) (fun _ => zero_le) x
    have hg_sup : ∀ x, (⨆ n, (A n).indicator (fun x => ‖f x‖ₑ) x) = ‖f x‖ₑ := fun x => by
      obtain ⟨n, hn⟩ := hcov x
      apply le_antisymm
      · exact iSup_le fun m => Set.indicator_le_self _ _ x
      · calc ‖f x‖ₑ = (A n).indicator (fun x => ‖f x‖ₑ) x := (Set.indicator_of_mem hn fun x => ‖f x‖ₑ).symm
          _ ≤ ⨆ m, (A m).indicator (fun x => ‖f x‖ₑ) x := le_iSup (fun m => (A m).indicator (fun x => ‖f x‖ₑ) x) n
    have hbound : ∀ n, ∫⁻ x, (A n).indicator (fun x => ‖f x‖ₑ) x ∂μ ≤ ENNReal.ofReal M := fun n => by
      rw [lintegral_indicator (hA n), ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
      exact ENNReal.ofReal_le_ofReal (hbd n)
    calc ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, ⨆ n, (A n).indicator (fun x => ‖f x‖ₑ) x ∂μ :=
          lintegral_congr fun x => (hg_sup x).symm
      _ = ⨆ n, ∫⁻ x, (A n).indicator (fun x => ‖f x‖ₑ) x ∂μ := lintegral_iSup' hg_meas (ae_of_all _ hg_mono)
      _ ≤ ENNReal.ofReal M := iSup_le hbound
      _ < ∞ := ENNReal.ofReal_lt_top

end Generic

section LocalIntegrals

variable (F : Type) [Field F] [NumberField F]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in

-- pin: exists_exhaustion (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:483)
theorem exists_exhaustion (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ T : ℕ → Finset (HeightOneSpectrum (𝓞 F)), Monotone T ∧ (∀ n, S ⊆ T n) ∧ ∀ v, ∃ n, v ∈ T n := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat (HeightOneSpectrum (𝓞 F))
  refine ⟨fun n => S ∪ (Finset.range n).preimage f hf.injOn, fun m n hmn v hv => ?_,
    fun n => Finset.subset_union_left,
    fun v => ⟨f v + 1, Finset.mem_union_right _ (Finset.mem_preimage.mpr (Finset.self_mem_range_succ (f v)))⟩⟩
  simp only [Finset.mem_union, Finset.mem_preimage, Finset.mem_range] at hv ⊢
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr (lt_of_lt_of_le hv hmn)

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
-- pin: stratumSet_mono (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:497)
theorem stratumSet_mono {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hTT' : T ⊆ T') :
    stratumSet F T ⊆ stratumSet F T' :=
  fun _ hx v hv => hx v fun h => hv (hTT' h)

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in

-- pin: exists_mem_stratumSet (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:504)
theorem exists_mem_stratumSet {T : ℕ → Finset (HeightOneSpectrum (𝓞 F))} (hTmono : Monotone T)
    (hTcov : ∀ v, ∃ n, v ∈ T n) (x : FiniteAdeleRing (𝓞 F) F) : ∃ n, x ∈ stratumSet F (T n) := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | x v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp x.2
  choose nv hnv using hTcov
  refine ⟨hfin.toFinset.sup nv, fun v hv => ?_⟩
  by_contra hbad
  have hvB : v ∈ hfin.toFinset := hfin.mem_toFinset.mpr hbad
  exact hv (hTmono (Finset.le_sup hvB) (hnv v))

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
-- pin: iUnion_stratumSet_eq_univ (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:517)
theorem iUnion_stratumSet_eq_univ {T : ℕ → Finset (HeightOneSpectrum (𝓞 F))} (hTmono : Monotone T)
    (hTcov : ∀ v, ∃ n, v ∈ T n) : (⋃ n, stratumSet F (T n)) = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (exists_mem_stratumSet F hTmono hTcov x)

end LocalIntegrals

variable (F : Type) [Field F] [NumberField F]

section FinitePlaces

-- pin: integralOffSet (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:531)
def integralOffSet (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (FiniteAdeleRing (𝓞 F) F) :=
  NumberField.TateGlobal.ShellSupport.integralOff S

-- pin: finprod_incl_split_symm (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:534)
theorem finprod_incl_split_symm {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1)
    (p : GT F T × YT F T) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (incl F T ((split F T).symm p) v) = ∏ i : ↥T, h i.1 (p.1 i) := by
  have hcoord : ∀ v, incl F T ((split F T).symm p) v = glue F T p v := fun v => rfl
  simp only [hcoord]
  have hone : ∀ v, v ∉ T → h v (glue F T p v) = 1 := fun v hv => by
    rw [glue_of_not_mem T p hv]
    exact h₁ v (fun hvS => hv (hST hvS)) _ (Subtype.coe_prop _)
  rw [finprod_eq_prod_of_mulSupport_subset (fun v => h v (glue F T p v)) (s := T) ?_]
  · rw [← Finset.prod_coe_sort T]
    exact Fintype.prod_congr _ _ fun i => by rw [glue_of_mem T p i.2]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    by_contra hvT
    exact hv (hone v fun h' => hvT (Finset.mem_coe.mpr h'))

-- pin: inv_measure_mul_setIntegral_integralOffSet_finprod_eq (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:552)
theorem inv_measure_mul_setIntegral_integralOffSet_finprod_eq
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1) :
    (ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * ∫ x in integralOffSet F S, ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν
      = ∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
          * ∫ y, h v y ∂(μ v)) := by
  obtain ⟨σ, hσfin, hρ, hboxm⟩ := exists_rhoT_eq_prod F ν S μ
  haveI := hσfin

  have hI : ∫ x in integralOffSet F S, ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν
      = (σ.real Set.univ : ℂ) * ∏ v ∈ S, ∫ y, h v y ∂(μ v) := by
    rw [show integralOffSet F S = stratumSet F S from rfl, setIntegral_stratumSet_eq]
    have hfun : (fun p : GT F S × YT F S =>
          ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (incl F S ((split F S).symm p) v))
        = fun p => (fun g : GT F S => ∏ i : ↥S, h i.1 (g i)) p.1 := by
      funext p
      exact finprod_incl_split_symm F (Finset.Subset.refl S) h h₁ p
    have hfst := integral_fun_fst (μ := Measure.pi fun i : ↥S => μ i.1) (ν := σ)
      (fun g : GT F S => ∏ i : ↥S, h i.1 (g i))
    have hprod : ∫ g : GT F S, ∏ i : ↥S, h i.1 (g i) ∂(Measure.pi fun i : ↥S => μ i.1)
        = ∏ i : ↥S, ∫ y, h i.1 y ∂(μ i.1) :=
      integral_fintype_prod_eq_prod (𝕜 := ℂ) (μ := fun i : ↥S => μ i.1) (fun i : ↥S => h i.1)
    rw [hfun, hρ, hfst, hprod]
    rw [Complex.real_smul]
    congr 1
    exact Finset.prod_coe_sort S fun v => ∫ y, h v y ∂(μ v)

  have hbox : ν.real (integralFiniteAdeles (𝓞 F) F)
      = (∏ v ∈ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))) * σ.real Set.univ := by
    simp only [measureReal_def]
    rw [hboxm, ENNReal.toReal_mul, ENNReal.toReal_prod]

  have hσ0 : (σ.real Set.univ : ℂ) ≠ 0 := by
    have h0 := measureReal_box_ne_zero F ν
    rw [hbox] at h0
    exact Complex.ofReal_ne_zero.mpr (right_ne_zero_of_mul h0)
  rw [hI, hbox]
  push_cast
  rw [mul_inv, mul_assoc, inv_mul_cancel_left₀ hσ0, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end FinitePlaces

end FiniteAdelicFactorization

end EisensteinGeneral
