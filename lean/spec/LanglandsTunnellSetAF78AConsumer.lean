/-
  SET-AF78A consumer: inversion invariance of a local Haar measure, spent at `K = ℚ_[2]`.

  **The row.** `FLTForHuman/LanglandsTunnell/TateLocal/HaarInvariance.lean` (row A) carries the row's
  own statement as well — `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion`,
  the pin's `solution` (`S_…:269–304`), which discharges both of the local hypotheses at a completed
  place.  The zones below read the general
  `LanglandsTunnell.TateLocal.integral_comp_inv`, the invariance of a local field's additive Haar
  measure under inversion, `∫ f x⁻¹ ∂μ = ∫ |modulus u|⁻² • f u ∂μ`, together with the unit-scaling
  engine it rests on (`modulus_units`, `measure_smul_units`).

  **The readings.** The module is general in the local field `K`; the consumer spends it at
  `K = ℚ_[2]` with `μ = Measure.addHaar`, the chosen additive Haar measure of the locally compact
  additive group:

  * Zone 1 — `modulus_units` at the unit `c = 2`: the modulus of `2` is the distributive Haar
    character of `2`, so multiplying a set by `2` scales its measure by `distribHaarChar ℚ_[2] 2`.
  * Zone 2 — `measure_smul_units` at `s = univ`: `μ (2 • univ) = modulus 2 * μ univ`, the scaling
    law the inversion argument is built on.
  * Zone 3 — the headline at `f = 1`, i.e. at the constant function `1`: the identity becomes
    `∫ x, 1 ∂μ = ∫ u, ((modulus u)⁻¹)² • 1 ∂μ`.  Its left side is the mass of the whole space,
    `μ.real univ`; the right side is the same mass weighted by the squared inverse modulus, which is
    the content of the identity at the constant function (it is not `μ.real univ` again unless
    `modulus ≡ 1`).

  **Hypothesis form.** Three data enter as hypotheses rather than being executed, and only these: the
  Borel structure `[MeasurableSpace ℚ_[2]] [BorelSpace ℚ_[2]]` (mathlib registers neither for
  `ℚ_[2]`); `Continuous (modulus : ℚ_[2] → ℝ≥0)` — the identification of the port's `modulus` with
  the `p`-adic norm, a separate row that this module does not contain; and `μ {0} = 0` for
  `μ = addHaar`, the atomlessness of the Haar measure, supplied by the caller.  The field, the
  measure, the unit `2` and the test function `1` are all concrete.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.LanglandsTunnell.TateLocal.HaarInvariance
import Mathlib.NumberTheory.Padics.ProperSpace

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell.SetAF78AConsumer

/-- The unit `2` of `ℚ_[2]`, the concrete unit all three zones are read at. -/
private def two : ℚ_[2]ˣ := Units.mk0 (2 : ℚ_[2]) (by norm_num)

/-- **Zone 1.** `modulus_units` at `c = 2`: `modulus 2 = distribHaarChar ℚ_[2] 2`.  This zone needs
no measurable structure: `modulus` and `distribHaarChar` are topological. -/
theorem consumer_modulus_units :
    LanglandsTunnell.TateLocal.modulus (two : ℚ_[2]) = MeasureTheory.distribHaarChar ℚ_[2] two :=
  LanglandsTunnell.TateLocal.modulus_units two

/- `ℚ_[2]` is a metric space, but mathlib registers no `MeasurableSpace` instance for it, so the
remaining zones carry the Borel structure of the metric space as a binder — the same device the
port's `adicCompletion` consumers use. -/
variable [MeasurableSpace ℚ_[2]] [BorelSpace ℚ_[2]]

/-- **Zone 2.** `measure_smul_units` at `s = univ`: `μ (2 • univ) = modulus 2 * μ univ`. -/
theorem consumer_measure_smul_units :
    Measure.addHaar (G := ℚ_[2]) ((two : ℚ_[2]) • Set.univ)
      = LanglandsTunnell.TateLocal.modulus (two : ℚ_[2]) * Measure.addHaar (G := ℚ_[2]) Set.univ :=
  LanglandsTunnell.TateLocal.measure_smul_units Measure.addHaar two Set.univ

/-- **Zone 3.** The headline at `f = 1`: inversion invariance read at the constant function `1`. -/
theorem consumer_integral_comp_inv_at_one
    (hmod : Continuous (LanglandsTunnell.TateLocal.modulus : ℚ_[2] → ℝ≥0))
    (h0 : Measure.addHaar (G := ℚ_[2]) {0} = 0) :
    ∫ _ : ℚ_[2], (1 : ℂ) ∂(Measure.addHaar (G := ℚ_[2]))
      = ∫ u : ℚ_[2], ((((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) ^ 2)⁻¹ : ℝ) • (1 : ℂ)
          ∂(Measure.addHaar (G := ℚ_[2])) :=
  LanglandsTunnell.TateLocal.integral_comp_inv Measure.addHaar hmod h0 (fun _ => 1)

/-- **Zone 3, the left side.** At `f = 1` the identity's left side is `μ.real univ`. -/
theorem consumer_at_one_left_side :
    ∫ _ : ℚ_[2], (1 : ℂ) ∂(Measure.addHaar (G := ℚ_[2]))
      = ((Measure.addHaar (G := ℚ_[2])).real Set.univ : ℂ) := by
  rw [integral_const]
  simp

end LanglandsTunnell.SetAF78AConsumer
