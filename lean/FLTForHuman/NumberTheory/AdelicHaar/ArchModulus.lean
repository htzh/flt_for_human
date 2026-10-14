/-
  The modulus character of the archimedean adèle ring.

  `refBox` is the unit box `∏_w {‖x_w‖ ≤ 1}` in `K_∞ = ∏_w K_w`; it is compact, has
  non-empty interior, and has finite positive measure for `infMeasure`, which makes
  `distribHaarChar (InfiniteAdeleRing F)` computable by the measure-scaling criterion:
  `distribHaarChar_infiniteAdeleRing` evaluates the character of an archimedean idele as
  the product `∏_w ‖a_w‖ ^ w.mult` of the local normalised absolute values.

  Transcribed from
  `S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean` (pinned
  `aa2d8b3`), lines 326–411, keeping the pin namespace `ArchModS44`. The pin's lines 20–316
  re-declare the `M4aS4` place-measure block (`placeBorel`, `placeMeasure`,
  `archMeasure`, `infMeasure`, `image_mul_pi`, `archMeasure_image_mul_pi`, …) and are not
  re-transcribed: `AdelicHaar/PlaceMeasure.lean` is imported and its `M4aS4` names are used
  here (this module opens `M4aS4` so that its scoped instances are active). The pin's
  `regular_infMeasure` (lines 361–364, carrying a `synthInstance.maxHeartbeats` override
  this order forbids) is not transcribed either: in the port `Regular (infMeasure F)` is
  found by instance search on the product measure `archMeasure`, so the declaration is
  redundant. The pin's final `theorem solution` (413–418) is left to the façade.

  The pin's `S_` file is a `P2MW` wrapper: its outer namespace and every `p2m_*` line are
  dropped here, and its bare `import Mathlib` is replaced by specific mathlib modules.
-/
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact

set_option autoImplicit false

open MeasureTheory Complex NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum TopologicalSpace Filter
open scoped Pointwise ENNReal NNReal

noncomputable section

open M4aS4

namespace ArchModS44

variable (F : Type) [Field F] [NumberField F]

variable {F}

-- port-only: `PlaceMeasure.lean`'s `placeBorel`/`infMS` are local instances there; the pin
-- re-declares them (and sets the same attributes) in `ArchModS44`. This module imports
-- `PlaceMeasure.lean` and re-establishes the two local instances it needs.
attribute [local instance] placeBorel infMS

variable (F) in

-- pin: refBox (S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean:326)
def refBox : Set (InfiniteAdeleRing F) :=
  (show Set ((w : InfinitePlace F) → w.Completion) from
    Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)

variable (F) in
-- v4.34 drift: `omit [NumberField F]` — the linter `linter.unusedSectionVars` (new in
-- v4.34) rejects the pin's automatically-included-but-unused section variable; the
-- statement itself is the pin's verbatim.
omit [NumberField F] in
-- pin: isCompact_refBox (S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean:331)
theorem isCompact_refBox : IsCompact (refBox F) :=
  isCompact_univ_pi fun w => isCompact_closedBall (0 : w.Completion) 1

variable (F) in
-- pin: interior_refBox_nonempty (S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean:335)
theorem interior_refBox_nonempty : (interior (refBox F)).Nonempty := by
  have hopen : IsOpen (show Set (InfiniteAdeleRing F) from
      (Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)) :=
    isOpen_set_pi Set.finite_univ fun w _ => Metric.isOpen_ball
  have hsub : (show Set (InfiniteAdeleRing F) from
      (Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)) ⊆ refBox F :=
    Set.pi_mono fun w _ => Metric.ball_subset_closedBall
  have hmem : (0 : InfiniteAdeleRing F) ∈ (show Set (InfiniteAdeleRing F) from
      (Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)) :=
    fun w _ => Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)
  exact ⟨_, interior_maximal hsub hopen hmem⟩

variable (F) in
-- pin: infMeasure_refBox_ne_top (S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean:348)
theorem infMeasure_refBox_ne_top : infMeasure F (refBox F) ≠ ⊤ := by
  show archMeasure F _ ≠ ⊤
  unfold archMeasure refBox
  rw [Measure.pi_pi]
  exact (ENNReal.prod_lt_top fun w _ => placeMeasure_closedBall_lt_top w).ne

variable (F) in
-- pin: infMeasure_refBox_ne_zero (S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean:355)
theorem infMeasure_refBox_ne_zero : infMeasure F (refBox F) ≠ 0 := by
  show archMeasure F _ ≠ 0
  unfold archMeasure refBox
  rw [Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.mpr fun w _ => (placeMeasure_pos_closedBall w).ne'

omit [NumberField F] in
-- pin: arch_unit_ne_zero (S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean:367)
theorem arch_unit_ne_zero (a : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    (a : InfiniteAdeleRing F) w ≠ 0 := by
  intro h0
  have h := congrArg (fun x : InfiniteAdeleRing F => x w) a.mul_inv
  rw [show ((a : InfiniteAdeleRing F) * (↑a⁻¹ : InfiniteAdeleRing F)) w
      = (a : InfiniteAdeleRing F) w * (↑a⁻¹ : InfiniteAdeleRing F) w from rfl, h0, zero_mul] at h
  exact zero_ne_one h

-- pin: distribHaarChar_infiniteAdeleRing (S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean:375)
theorem distribHaarChar_infiniteAdeleRing (a : (InfiniteAdeleRing F)ˣ) :
    (distribHaarChar (InfiniteAdeleRing F) a : ℝ) = ∏ w : InfinitePlace F, ‖(a : InfiniteAdeleRing F) w‖ ^ w.mult := by
  classical
  set aArch : (w : InfinitePlace F) → w.Completion :=
    (show (w : InfinitePlace F) → w.Completion from (a : InfiniteAdeleRing F)) with haArch
  have haw : ∀ w, aArch w ≠ 0 := fun w => arch_unit_ne_zero a w
  have hsplit : (show Set ((w : InfinitePlace F) → w.Completion) from (a • refBox F)) =
      (fun x : (w : InfinitePlace F) → w.Completion => aArch * x) ''
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) := by
    rw [← Set.image_smul]
    rfl
  have harch : archMeasure F ((fun x => aArch * x) ''
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1))
      = (∏ w, ‖aArch w‖ₑ ^ w.mult) * archMeasure F
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) :=
    archMeasure_image_mul_pi aArch haw
      (fun w => Metric.closedBall (0 : w.Completion) 1) (fun w => measurableSet_closedBall)
  have hμgs : infMeasure F (a • refBox F)
      = ((∏ w : InfinitePlace F, ‖aArch w‖₊ ^ w.mult : ℝ≥0) : ℝ≥0∞) * infMeasure F (refBox F) := by
    show archMeasure F (show Set ((w : InfinitePlace F) → w.Completion) from (a • refBox F)) =
      _ * archMeasure F (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)
    rw [hsplit, harch]
    congr 1
    rw [ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ENNReal.coe_pow, enorm_eq_nnnorm]
  have key := distribHaarChar_eq_of_measure_smul_eq_mul (μ := infMeasure F)
    (s := refBox F) (g := a) (infMeasure_refBox_ne_zero F) (infMeasure_refBox_ne_top F) hμgs
  rw [key]
  push_cast [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  rfl

end ArchModS44

end
