/-
  A mathlib supplement for `Mathlib/MeasureTheory/Integral/Prod.lean`.

  In `v4.34.0` the product-measure API is gated on s-finiteness: the
  integrability lemmas `Integrable.mul_prod` / `Integrable.smul_prod` /
  `Integrable.op_fst_snd` carry `[SFinite ν]` (through
  `AEStronglyMeasurable.comp_fst`), and so do the structural lemmas one would use
  to move between the product measure and its restrictions — `Measure.prod_restrict`,
  `Measure.prod_add`, `Measure.add_prod`, `Measure.prod_mono`, `prod_prod_le`,
  `lintegral_prod_le`, `lintegral_prod_mul` and `Measurable.map_prodMk_left`.  The
  pin's mathlib `v4.33.0` instead had `omit [SFinite ν]` on
  `Integrable.op_fst_snd`, so statements that assume only `Integrable f μ` and
  `Integrable g ν` (for example the pin's `integrable_refMeasure_mul`) were
  provable there but are not reachable through `v4.34.0`'s API as stated.

  The one lemma here is the natural s-finiteness input for such a repair: the
  measure restricted to the support of an integrable function is s-finite.  The
  support is covered by the countable family `{x | 1 / (n + 1) ≤ ‖f x‖}`, and on
  each member Markov's inequality (`mul_meas_ge_le_lintegral₀`) bounds the measure
  by `(n + 1) * ∫⁻ ‖f‖ₑ < ∞`; disjointifying the cover writes the restricted
  measure as a countable sum of those finite pieces.

  (The full s-finite-free `Integrable.mul_prod` is *not* proved here: transferring
  integrability from `(μ.restrict s).prod (ν.restrict t)` back to `μ.prod ν` needs
  `Measure.prod_restrict` in the same direction, and that lemma requires `[SFinite]`
  on the unrestricted factors, which this lemma does not supply.)

  No file-wide option beyond `set_option autoImplicit false`.
-/
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Set Filter Function
open scoped ENNReal NNReal

namespace MeasureTheory

-- port-only: not in mathlib.  In v4.34.0 this is the natural input for repairing
-- the `[SFinite]` requirements of `Integrable.mul_prod` and the surrounding
-- product-measure API for statements that only assume integrability.
theorem sFinite_restrict_support_of_integrable {α L : Type*} [MeasurableSpace α] [NormedRing L]
    {μ : Measure α} {f : α → L} (hf : Integrable f μ) :
    SFinite (μ.restrict (Function.support f)) := by
  classical
  have hae : AEMeasurable (fun x => ‖f x‖ₑ) μ := hf.1.enorm
  have hint : ∫⁻ x, ‖f x‖ₑ ∂μ < ∞ := hasFiniteIntegral_iff_enorm.mp hf.2
  -- the measurable enlargements of the cover `{x | 1 / (n + 1) ≤ ‖f x‖}`
  let t : ℕ → Set α := fun n => toMeasurable μ {x | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ ‖f x‖ₑ}
  have ht_meas : ∀ n, MeasurableSet (t n) := fun n => measurableSet_toMeasurable μ _
  have hcover : Function.support f ⊆ ⋃ n, t n := by
    intro x hx
    rw [Function.mem_support] at hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hx)
    refine Set.mem_iUnion.mpr ⟨n, subset_toMeasurable μ _ ?_⟩
    show ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ ‖f x‖ₑ
    rw [← ofReal_norm (f x)]
    exact ENNReal.ofReal_le_ofReal hn.le
  -- disjointification of the cover
  let u : ℕ → Set α := fun n => t n \ ⋃ i : {i : ℕ // i < n}, t i.1
  have hu_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    exact (ht_meas n).diff (MeasurableSet.iUnion fun i => ht_meas i.1)
  have hu_disj : Pairwise (Function.onFun Disjoint u) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    intro x hxm hxn
    obtain ⟨hxm_t, hxm_not⟩ := hxm
    obtain ⟨hxn_t, hxn_not⟩ := hxn
    rcases lt_or_gt_of_ne hmn with hmn' | hmn'
    · exact hxn_not (Set.mem_iUnion.mpr ⟨⟨m, hmn'⟩, hxm_t⟩)
    · exact hxm_not (Set.mem_iUnion.mpr ⟨⟨n, hmn'⟩, hxn_t⟩)
  have hu_iUnion : (⋃ n, u n) = ⋃ n, t n := by
    refine le_antisymm (Set.iUnion_subset fun n => Set.sdiff_subset.trans (Set.subset_iUnion _ n)) ?_
    intro x hx
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
    have hP : ∃ n, x ∈ t n := ⟨N, hN⟩
    refine Set.mem_iUnion.mpr ⟨Nat.find hP, Nat.find_spec hP, ?_⟩
    intro hmem
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hmem
    exact Nat.find_min hP i.2 hxi
  -- each piece is a finite measure
  have ht_lt_top : ∀ n, μ (t n) < ∞ := by
    intro n
    have hmarkov : ENNReal.ofReal (1 / (n + 1 : ℝ)) * μ (t n) ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
      rw [measure_toMeasurable]
      exact mul_meas_ge_le_lintegral₀ hae _
    have hlt : ENNReal.ofReal (1 / (n + 1 : ℝ)) * μ (t n) < ∞ := hmarkov.trans_lt hint
    rw [ENNReal.mul_lt_top_iff] at hlt
    rcases hlt with ⟨_, h2⟩ | h0 | h0
    · exact h2
    · exact absurd h0 (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    · rw [h0]; exact ENNReal.zero_lt_top
  have hfin : ∀ n, IsFiniteMeasure (μ.restrict (u n)) := by
    intro n
    rw [isFiniteMeasure_iff, restrict_apply_univ]
    exact (measure_mono Set.sdiff_subset).trans_lt (ht_lt_top n)
  have hsum : Measure.sum (fun n => μ.restrict (u n)) = μ.restrict (⋃ n, t n) := by
    rw [← restrict_iUnion hu_disj hu_meas, hu_iUnion]
  -- conclude: restricting the s-finite `μ.restrict (⋃ t n)` to the support is s-finite
  have hS : SFinite (μ.restrict (⋃ n, t n)) := ⟨⟨fun n => μ.restrict (u n), hfin, hsum.symm⟩⟩
  have hS' : SFinite ((μ.restrict (⋃ n, t n)).restrict (Function.support f)) := inferInstance
  rwa [restrict_restrict_of_subset hcover] at hS'

end MeasureTheory
