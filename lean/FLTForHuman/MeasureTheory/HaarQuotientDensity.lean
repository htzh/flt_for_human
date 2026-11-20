/-
  The density on the Haar quotient: the integral of the density is one.

  For a closed subgroup `H` of a locally compact second countable group `G` and a right-invariant
  Haar measure `μH` on `H`, the Radon–Nikodym density `HaarQuotient.density H μH` of
  `HaarQuotient.lean` is an `H`-invariant function on `G` (its `H`-orbit integral does not depend on
  the point), and the total mass of one `H`-orbit of it is exactly `1`:

  `∫⁻ x : H, density H μH ((x : G) * g) ∂μH = 1`.

  That is the normalisation which makes the quotient measure
  `HaarQuotient.measure μ H μH = (Quotient.mk'')_* (μ.withDensity (density H μH))` a probability
  measure when `μ` is, and makes the counting/measure dictionary of the automorphic quotient
  exact: the `Γ`-integral over a fundamental domain becomes the quotient integral of the fibre
  integrals with no leftover scalar.

  The mathematics is the exhaustion argument of the pin: a weight `weight H μH` built from a
  compact exhaustion `E n` and the `μH`-masses of the `H`-preimages of `E n * (E n)⁻¹` is positive,
  locally bounded by a geometric series, and its orbit integral `orbit H μH g` therefore takes a
  value in `(0, ∞)`; the density is `weight / orbit`, and `orbit` is invariant under left
  `H`-translation, so the orbit integral of the density is `orbit / orbit = 1`.

  Transcribed whole from the pin's `P2M/Sol/S_HaarQuotient_lintegral_density_mul_eq_one.lean`
  (170 lines, 12 declarations) at `aa2d8b34`: the pin's eleven engines and its `solution` row are
  all here, the row renamed `lintegral_density_mul_eq_one`. The pin's `weight` and `density` are
  the ones already ported in `FLTForHuman/MeasureTheory/HaarQuotient.lean`, so this module proves
  the pin's own *properties* of them rather than redefining them.

  ## Heartbeat probe (recorded, never installed — FR-0225)

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` on this file: **silent at `N = 5000`,
  fails at `N = 4000`** (a deterministic timeout at `whnf`/`isDefEq`, inside `orbit_ne_top` — its
  `unfold coef` and the `mul_le_mul'` geometric bound), so the whole twelve-declaration
  development costs ≈4–5 k heartbeats against the project cap of 4 M. No
  `set_option maxHeartbeats` is carried.

  ## Port deltas

  * The pin's `SEC` section label is flattened into `HaarQuotient` (the port's treatment of the
    pin's search-stage namespaces). No pin statement mentions `SEC`, so all twelve statements are
    the pin's byte-for-byte and `check_port` reads twelve `ok`.
  * **Visibility: all twelve declarations are public**, because the pin marks none of them
    `private`. `check_port` therefore diffs every one of them rather than skipping a `private`
    engine (FR-0242).
  * Body-only Mathlib drift (FR-0255), no statement touched: `dif_pos` -> `dite_eq_left` in
    `weight_eq`; `Measurable.ennreal_tsum` (deprecated 2026-04-30) replaced by its own inlined
    `ENNReal.tsum_eq_iSup_sum` + `Measurable.iSup` proof in `measurable_weight`; and
    `(Topology.IsClosedEmbedding.subtypeVal hH).isCompact_preimage hC` re-spelled through
    `hH.isClosedEmbedding_subtypeVal` in `isCompact_preimage_coe`, because the pin's form leaves
    the subtype's `TopologicalSpace` instance postponed at the `isCompact_preimage` step.
  * `set_option linter.unusedSectionVars false in` guards `weight_eq`, `isCompact_preimage_coe`
    and `orbit_mul`, whose auto-included section variables are unused (the pin carries the same
    unused ones and prints the same warnings). The option changes no statement.
  * The import list is the scaffold's single `FLTForHuman.MeasureTheory.HaarQuotient`; nothing was
    added (FR-0254).

  spec-pin: P2M/Sol/S_HaarQuotient_lintegral_density_mul_eq_one.lean
-/

import FLTForHuman.MeasureTheory.HaarQuotient

set_option autoImplicit false

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace HaarQuotient

/-! ### The weight, its positivity and its `H`-orbit integral

The pin's development, with its `SEC` section label flattened into `HaarQuotient` (the port's
naming policy for the pin's search-stage namespaces). -/

section Engine

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant]

/-- The pin's coefficient of the `n`-th piece of the exhaustion: a geometric factor times the
reciprocal of `1 + μH` of the `H`-preimage of `E (n+1) * (E (n+1))⁻¹`. -/
noncomputable def coef (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ n *
    (1 + μH (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹

set_option linter.unusedSectionVars false in
/-- The defining series of `weight`, with `coef` factored out. -/
theorem weight_eq :
    weight H μH = fun g => ∑' n : ℕ, coef H μH n *
      (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  have h : SigmaCompactSpace G ∧ WeaklyLocallyCompactSpace G := ⟨inferInstance, inferInstance⟩
  unfold weight
  rw [dite_eq_left h]
  rfl

theorem measurable_weight : Measurable (weight H μH) := by
  rw [weight_eq H μH]
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine Measurable.iSup fun s => ?_
  exact s.measurable_fun_sum fun n _ =>
    (measurable_const.indicator isOpen_interior.measurableSet).const_mul _

set_option linter.unusedSectionVars false in
include hH in
theorem isCompact_preimage_coe {C : Set G} (hC : IsCompact C) : IsCompact (((↑) : H → G) ⁻¹' C) := by
  have hce : Topology.IsClosedEmbedding ((↑) : H → G) := hH.isClosedEmbedding_subtypeVal
  exact hce.isCompact_preimage hC

include hH in
theorem weight_pos (g : G) : 0 < weight H μH g := by
  rw [weight_eq H μH]
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem g
  have hint : g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) :=
    (CompactExhaustion.choice G).subset_interior_succ n hn
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum n)
  simp only [Set.indicator_of_mem hint, mul_one]
  unfold coef
  refine ENNReal.mul_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)) ?_
  refine ENNReal.inv_ne_zero.mpr (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ?_⟩)
  have hc : IsCompact ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹) :=
    ((CompactExhaustion.choice G).isCompact _).mul ((CompactExhaustion.choice G).isCompact _).inv
  exact (isCompact_preimage_coe H hH hc).measure_lt_top.ne

/-- The `H`-orbit integral of the weight at `g`: this is the denominator of `density`. -/
noncomputable def orbit (g : G) : ℝ≥0∞ := ∫⁻ y : H, weight H μH ((y : G) * g) ∂μH

set_option linter.unusedSectionVars false in
/-- `orbit` is invariant under left translation by `H`, by right-invariance of `μH`. -/
theorem orbit_mul (x : H) (g : G) : orbit H μH ((x : G) * g) = orbit H μH g := by
  unfold orbit
  have := lintegral_mul_right_eq_self (μ := μH) (fun y : H => weight H μH ((y : G) * g)) x
  simp only [Subgroup.coe_mul, mul_assoc] at this ⊢
  exact this

theorem measurable_weight_mul (g : G) : Measurable fun y : H => weight H μH ((y : G) * g) :=
  (measurable_weight H μH).comp (continuous_subtype_val.mul continuous_const).measurable

include hH in
theorem orbit_ne_zero (g : G) : orbit H μH g ≠ 0 := by
  unfold orbit
  intro h0
  rw [lintegral_eq_zero_iff (measurable_weight_mul H μH g)] at h0
  have : μH Set.univ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact h0.mono fun y hy _ => (weight_pos H hH μH ((y : G) * g)).ne' hy
  exact isOpen_univ.measure_ne_zero μH Set.univ_nonempty this

include hH in
theorem orbit_ne_top (g : G) : orbit H μH g ≠ ∞ := by
  unfold orbit
  set E := CompactExhaustion.choice G with hE
  obtain ⟨N, hN⟩ := E.exists_mem g
  set C := μH (((↑) : H → G) ⁻¹' ((E N : Set G) * ({g} : Set G)⁻¹)) with hCdef
  have hC : C < ∞ :=
    (isCompact_preimage_coe H hH ((E.isCompact N).mul isCompact_singleton.inv)).measure_lt_top

  set A : ℕ → Set H := fun n => {y : H | (y : G) * g ∈ interior (E (n + 1) : Set G)} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    isOpen_interior.measurableSet.preimage (continuous_subtype_val.mul continuous_const).measurable

  have hterm : ∀ n, ∫⁻ y : H, coef H μH n * (interior (E (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((y : G) * g) ∂μH =
      coef H μH n * μH (A n) := by
    intro n
    have hind : ∀ y : H, (interior (E (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((y : G) * g) =
        (A n).indicator (fun _ => (1 : ℝ≥0∞)) y := by
      intro y; rfl
    simp_rw [hind]
    rw [lintegral_const_mul _ (measurable_const.indicator (hAm n)), lintegral_indicator_const (hAm n), one_mul]

  have hbound : ∀ n, coef H μH n * μH (A n) ≤ (2⁻¹ : ℝ≥0∞) ^ n + (↑(Finset.range N) : Set ℕ).indicator (fun _ => C) n := by
    intro n
    by_cases hn : n + 1 < N
    ·
      have hsub : A n ⊆ ((↑) : H → G) ⁻¹' ((E N : Set G) * ({g} : Set G)⁻¹) := by
        intro y hy
        have hyg : (y : G) * g ∈ (E N : Set G) := E.subset hn.le (interior_subset hy)
        refine ⟨(y : G) * g, hyg, g⁻¹, by simp, by group⟩
      have hcoef : coef H μH n ≤ 1 := by
        unfold coef
        calc (2⁻¹ : ℝ≥0∞) ^ n * _ ≤ 1 * 1 := mul_le_mul' (pow_le_one₀ bot_le (ENNReal.inv_le_one.mpr one_le_two))
              (ENNReal.inv_le_one.mpr le_self_add)
          _ = 1 := one_mul _
      rw [Set.indicator_of_mem (by simpa using Nat.lt_of_succ_lt hn)]
      exact le_add_left ((mul_le_mul' hcoef (measure_mono hsub)).trans_eq (one_mul _))
    ·
      rw [not_lt] at hn
      have hg : g ∈ (E (n + 1) : Set G) := E.subset hn hN
      set m := μH (((↑) : H → G) ⁻¹' ((E (n + 1) : Set G) * (E (n + 1) : Set G)⁻¹)) with hm
      have hsub : A n ⊆ ((↑) : H → G) ⁻¹' ((E (n + 1) : Set G) * (E (n + 1) : Set G)⁻¹) := by
        intro y hy
        refine ⟨(y : G) * g, interior_subset hy, g⁻¹, Set.inv_mem_inv.mpr hg, by group⟩
      refine le_add_right ?_
      unfold coef
      rw [mul_assoc]
      calc (2⁻¹ : ℝ≥0∞) ^ n * ((1 + m)⁻¹ * μH (A n)) ≤ (2⁻¹ : ℝ≥0∞) ^ n * 1 := by
            gcongr
            calc (1 + m)⁻¹ * μH (A n) ≤ (1 + m)⁻¹ * m := mul_le_mul_right (measure_mono hsub) _
              _ ≤ 1 := by
                rw [← ENNReal.div_eq_inv_mul]
                exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)
        _ = _ := mul_one _

  have hmeas : ∀ n, Measurable fun y : H => coef H μH n *
      (interior (E (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((y : G) * g) := fun n =>
    measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet).comp
      (continuous_subtype_val.mul continuous_const).measurable)
  rw [weight_eq H μH]
  simp only []
  rw [lintegral_tsum fun n => (hmeas n).aemeasurable]
  simp_rw [hterm]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_add, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofNat_ne_top, ?_⟩
  rw [tsum_eq_sum (s := Finset.range N) (fun n hn => Set.indicator_of_notMem (by simpa using hn) _)]
  refine (ENNReal.sum_lt_top.mpr fun n _ => ?_).ne
  exact lt_of_le_of_lt (Set.indicator_le_self _ _ n) hC

include hH in
/-- **The orbit integral of the density is one**: the normalisation of the Haar quotient. -/
theorem lintegral_density (g : G) : ∫⁻ x : H, density H μH ((x : G) * g) ∂μH = 1 := by
  have h0 := orbit_ne_zero H hH μH g
  have htop := orbit_ne_top H hH μH g
  have hrew : ∀ x : H, density H μH ((x : G) * g) = weight H μH ((x : G) * g) * (orbit H μH g)⁻¹ := by
    intro x
    rw [density, div_eq_mul_inv]
    congr 2
    exact orbit_mul H μH x g
  simp_rw [hrew]
  rw [lintegral_mul_const _ (measurable_weight_mul H μH g)]
  exact ENNReal.mul_inv_cancel h0 htop

end Engine

/-- **The quotient measure is a probability measure.** For a closed subgroup `H` of a locally
compact second countable group `G`, a right-invariant Haar measure `μH` on `H` and any `g : G`, the
`H`-orbit integral of the quotient density is `1`. -/
theorem lintegral_density_mul_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : MeasureTheory.Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, HaarQuotient.density H μH ((x : G) * g) ∂μH = 1 :=
  HaarQuotient.lintegral_density H hH μH g

end HaarQuotient

end
