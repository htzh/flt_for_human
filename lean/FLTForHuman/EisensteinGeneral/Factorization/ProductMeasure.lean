/-
  Recognition of a product measure: a measure on `G × Y` that is invariant under the
  left translations `(a + ·, ·)` of a locally compact second countable abelian group `G`
  is the product of a Haar measure on `G` with a finite measure on `Y`.

  This is the sole declaration of the pin's `section Recognition`, and it is the input
  that turns the stratum measure `rhoT` of the next module into a product
  `Measure.pi … .prod σ`: the invariance is `rhoT_map_add_left` and the finiteness on
  compacts is `rhoT_prod_univ_lt_top`.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`,
  `P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:20-93`
  (`section Recognition`), mathlib `v4.34.0`.  The pin's `private` becomes public: every
  declaration of this set is registered (work order §1).  The proof is the pin's,
  transcribed unchanged; `T2Space G` is a local hypothesis of the theorem, not a
  section variable.
-/
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

-- The pin's `haveI` declarations are load-bearing: they feed instance search.
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory

open scoped ENNReal NNReal

namespace EisensteinGeneral

namespace FiniteAdelicFactorization

section Recognition

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Y : Type*} [MeasurableSpace Y]

-- pin: exists_eq_prod_of_forall_map_add_left (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:26)
theorem exists_eq_prod_of_forall_map_add_left [T2Space G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (ρ : Measure (G × Y)) (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (hfin : ∀ K : Set G, IsCompact K → ρ (K ×ˢ Set.univ) < ∞) :
    ∃ σ : Measure Y, IsFiniteMeasure σ ∧ ρ = μ.prod σ := by
  haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨K₀, hK₀c, hK₀n⟩ := exists_compact_mem_nhds (0 : G)
  have hK₀m : MeasurableSet K₀ := hK₀c.measurableSet
  have hK₀pos : μ K₀ ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK₀n).ne'
  have hK₀top : μ K₀ ≠ ∞ := hK₀c.measure_lt_top.ne
  have hT : ∀ a : G, Measurable fun p : G × Y => (a + p.1, p.2) := fun a =>
    (measurable_fst.const_add a).prodMk measurable_snd

  have hrect : ∀ (a : G) (A : Set G) (B : Set Y), MeasurableSet A → MeasurableSet B →
      ρ (((fun g => a + g) ⁻¹' A) ×ˢ B) = ρ (A ×ˢ B) := by
    intro a A B hA hB
    have h := congrArg (fun m : Measure (G × Y) => m (A ×ˢ B)) (hinv a)
    rw [Measure.map_apply (hT a) (hA.prod hB)] at h
    have hpre : (fun p : G × Y => (a + p.1, p.2)) ⁻¹' (A ×ˢ B) = ((fun g => a + g) ⁻¹' A) ×ˢ B := by
      ext ⟨g, y⟩
      simp only [Set.mem_preimage, Set.mem_prod]
    rw [hpre] at h
    exact h

  let ρB : Set Y → Measure G := fun B => (ρ.restrict (Set.univ ×ˢ B)).map Prod.fst
  have hρB : ∀ (B : Set Y) (A : Set G), MeasurableSet A → ρB B A = ρ (A ×ˢ B) := by
    intro B A hA
    simp only [ρB]
    rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
    congr 1
    ext ⟨g, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]

  let σ : Measure Y := (μ K₀)⁻¹ • (ρ.restrict (K₀ ×ˢ Set.univ)).map Prod.snd
  have hσ : ∀ B : Set Y, MeasurableSet B → σ B = (μ K₀)⁻¹ * ρ (K₀ ×ˢ B) := by
    intro B hB
    simp only [σ, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]
    congr 2
    ext ⟨g, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact and_comm
  have hσfin : IsFiniteMeasure σ := by
    refine ⟨?_⟩
    rw [hσ _ MeasurableSet.univ]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hK₀pos)) (hfin K₀ hK₀c)
  haveI := hσfin
  refine ⟨σ, hσfin, (Measure.prod_eq fun A B hA hB => ?_).symm⟩

  haveI hBinv : (ρB B).IsAddLeftInvariant := by
    refine ⟨fun a => Measure.ext fun A' hA' => ?_⟩
    rw [Measure.map_apply (measurable_const_add a) hA', hρB B _ (measurable_const_add a hA'), hρB B A' hA']
    exact hrect a A' B hA' hB
  haveI hBfin : IsFiniteMeasureOnCompacts (ρB B) := by
    refine ⟨fun K hK => ?_⟩
    rw [hρB B K hK.measurableSet]
    exact lt_of_le_of_lt (measure_mono (Set.prod_mono le_rfl (Set.subset_univ _))) (hfin K hK)
  have huniq : ρB B = (ρB B).addHaarScalarFactor μ • μ := Measure.isAddLeftInvariant_eq_smul (ρB B) μ
  set c : ℝ≥0 := (ρB B).addHaarScalarFactor μ with hc_def
  have hcA : ∀ A' : Set G, MeasurableSet A' → ρ (A' ×ˢ B) = (c : ℝ≥0∞) * μ A' := by
    intro A' hA'
    rw [← hρB B A' hA', huniq]
    exact Measure.coe_nnreal_smul_apply c μ A'
  have hc : (c : ℝ≥0∞) = (μ K₀)⁻¹ * ρ (K₀ ×ˢ B) := by
    rw [hcA K₀ hK₀m, mul_comm (c : ℝ≥0∞) (μ K₀), ← mul_assoc, ENNReal.inv_mul_cancel hK₀pos hK₀top, one_mul]
  rw [hcA A hA, hc, hσ B hB]
  ring

end Recognition

end FiniteAdelicFactorization

end EisensteinGeneral
