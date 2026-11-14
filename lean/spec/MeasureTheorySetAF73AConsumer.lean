/-
  SET-AF73A consumer: the Haar-quotient Fubini identity, spent on the additive real line.

  **The row.** `FLTForHuman/MeasureTheory/HaarQuotientFubini.lean`:
  `HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out` — for a closed subgroup `H ≤ G`, a
  right-invariant Haar measure `μH` on `H` and a measurable `f : G → ℝ≥0∞`, the integral of `f`
  over `G` against a left-invariant `μ` equals the integral over the quotient `H \ G` (against the
  exhaustion-and-density quotient measure) of the orbital sum `∫⁻ x, f (x * q.out) ∂μH`.

  **The instantiation.** `G = ℝ` read additively — `AddReal := Multiplicative ℝ`, whose group law
  is addition of reals and whose unit `1` is `0` — so that `H = ⊥ ≤ G` is the trivial subgroup
  `{0}`, a singleton.  `μH` is the Dirac mass at that unit (the Haar measure of a one-point group),
  and `f` is the constant `c`.  On the right the orbital sum has a single term `c`, so the row's
  content here is entirely in the quotient side: the quotient measure of the exhaustion-and-density
  construction, read at a trivial `H`.

  The zone is one executed composition: the row is *applied*, not re-stated, so deleting the module
  (or leaving a hole in it) breaks this file.  `ℝ`'s Borel structure is transported to the
  type synonym by the two `inferInstanceAs` instances below, because mathlib transfers
  `TopologicalSpace`/`IsTopologicalGroup` to `Multiplicative` but not `MeasurableSpace`/`BorelSpace`.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.MeasureTheory.HaarQuotientFubini

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace MeasureTheorySetAF73AConsumer

/-- `ℝ` with its additive group law written multiplicatively: the unit is `0` and `⊥` is `{0}`. -/
abbrev AddReal : Type := Multiplicative ℝ

instance : MeasurableSpace AddReal := inferInstanceAs (MeasurableSpace ℝ)

instance : BorelSpace AddReal := inferInstanceAs (BorelSpace ℝ)

/-- `⊥ ≤ AddReal` is the one-point subgroup `{1} = {0}`. -/
instance subsingleton_bot : Subsingleton ↥(⊥ : Subgroup AddReal) :=
  ⟨fun a b => Subtype.ext (by
    rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩

/-- The Dirac mass at the unit of a one-point group is right-invariant: right translation is the
identity there. -/
instance dirac_isMulRightInvariant :
    Measure.IsMulRightInvariant (Measure.dirac (1 : ↥(⊥ : Subgroup AddReal))) where
  map_mul_right_eq_self g := by
    rw [Measure.map_dirac' (measurable_mul_const g), Subsingleton.elim (1 * g) 1]

/-- The Dirac mass at the unit of a one-point group is a Haar measure: it is finite on compacts,
left-invariant, and positive on every nonempty open set, the unit lying in all of them. -/
instance dirac_isHaarMeasure :
    Measure.IsHaarMeasure (Measure.dirac (1 : ↥(⊥ : Subgroup AddReal))) where
  lt_top_of_isCompact K hK := by
    have hle : (Measure.dirac (1 : ↥(⊥ : Subgroup AddReal))) K ≤ 1 := by
      rw [Measure.dirac_apply' _ hK.measurableSet]
      by_cases h : (1 : ↥(⊥ : Subgroup AddReal)) ∈ K
      · rw [Set.indicator_of_mem h]; simp
      · rw [Set.indicator_of_notMem h]; simp
    exact lt_of_le_of_lt hle ENNReal.one_lt_top
  map_mul_left_eq_self g := by
    rw [Measure.map_dirac' (measurable_const_mul g), Subsingleton.elim (g * 1) 1]
  open_pos U _ hne := by
    obtain ⟨x, hx⟩ := hne
    have h1 : (1 : ↥(⊥ : Subgroup AddReal)) ∈ U := by
      simpa [Subsingleton.elim x 1] using hx
    rw [Measure.dirac_apply_of_mem h1]
    simp

/-- **The zone.** The row at `G = AddReal`, `H = ⊥`, `μH = δ_0` and `f` the constant `c`: the
`μ`-integral of `c` is the quotient integral of the (one-term) orbital sum `∫⁻ x, c ∂δ_0`. -/
theorem lintegral_eq_lintegral_lintegral_mul_out_at_additive_real
    (μ : Measure AddReal) [μ.IsMulLeftInvariant] [SFinite μ] (c : ℝ≥0∞) :
    ∫⁻ _g, c ∂μ =
      ∫⁻ _q, (∫⁻ _x : ↥(⊥ : Subgroup AddReal), c
        ∂(Measure.dirac (1 : ↥(⊥ : Subgroup AddReal))))
        ∂(HaarQuotient.measure μ (⊥ : Subgroup AddReal)
          (Measure.dirac (1 : ↥(⊥ : Subgroup AddReal)))) := by
  have hH : IsClosed ((⊥ : Subgroup AddReal) : Set AddReal) := by
    simp
  exact HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ (⊥ : Subgroup AddReal) hH
    (Measure.dirac (1 : ↥(⊥ : Subgroup AddReal))) (fun _ => c) measurable_const

end MeasureTheorySetAF73AConsumer
