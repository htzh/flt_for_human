/-
  Cross-module wire test for the Schwartz–Bruhat space of the adèles (`AF75A`).

  A `spec/` probe, not a library module. Two executed zones, both at `F = ℚ`:

  * the pure tensor `fTensor` built from an *explicit* Schwartz function (`gBump`, a smooth
    compactly supported bump on the mixed space, packaged by `HasCompactSupport.toSchwartzMap`)
    and an *explicit* compactly supported locally constant function (`hInt`, the indicator of the
    integral finite adèles, which is clopen and compact) — read by `tensor_mem_pureTensorSet` and
    evaluated at `0`, where it takes the value `1`;
  * one *evaluated* use of each headline: `Integrable fTensor (adelicAddHaar)` (through both
    `integrable_pureTensor` and `integrable_of_mem_schwartzBruhat`) and summability of the
    diagonal translates at `x = 0` (`summable_translate_of_mem_schwartzBruhat`), plus the three
    cell lemmas `isCompact_cell`, `mem_cell_floor` and `measure_cell` read at that tensor.

  Deleting the module (or leaving a hole in it) breaks this file: every zone is a real
  composition, no `#check`.
-/
import FLTForHuman.NumberTheory.AdelicFourier.Space
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open NumberField NumberField.AdelicFourier NumberField.InfiniteAdeleRing IsDedekindDomain
open MeasureTheory
open Classical
open scoped ContDiff Topology SchwartzMap

noncomputable section

namespace NumberFieldAdelicFourierConsumer

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

/-! ### The explicit Schwartz function on the mixed space of `ℚ` -/

/-- A bump function at `0` on the mixed space `ℝ^{r₁} × ℂ^{r₂}` of `ℚ`. -/
private def bumpSpace : ContDiffBump (0 : mixedEmbedding.mixedSpace ℚ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The bump, as a plain function: keeps the `ContDiffBump` coercions out of later defeq
checks. -/
private def bumpFun : mixedEmbedding.mixedSpace ℚ → ℝ := bumpSpace

/-- The bump is smooth. -/
private theorem bumpFun_contDiff : ContDiff ℝ ∞ bumpFun :=
  bumpSpace.contDiff

/-- The bump is compactly supported. -/
private theorem bumpFun_hasCompactSupport : HasCompactSupport bumpFun :=
  bumpSpace.hasCompactSupport

/-- The complex-valued bump, still compactly supported. -/
private theorem bumpFun_hasCompactSupport_complex :
    HasCompactSupport fun z : mixedEmbedding.mixedSpace ℚ => (bumpFun z : ℂ) :=
  bumpFun_hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl

/-- The explicit Schwartz function: the complex-valued bump on the mixed space of `ℚ`. -/
private def gBump : 𝓢(mixedEmbedding.mixedSpace ℚ, ℂ) :=
  bumpFun_hasCompactSupport_complex.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp bumpFun_contDiff)

/-- The Schwartz function is `1` at the origin. -/
private theorem gBump_zero : gBump 0 = 1 := by
  have h0 : (0 : mixedEmbedding.mixedSpace ℚ) ∈ Metric.closedBall 0 bumpSpace.rIn := by
    simp [bumpSpace.rIn_pos.le]
  show (bumpFun 0 : ℂ) = 1
  rw [show bumpFun 0 = 1 from bumpSpace.one_of_mem_closedBall h0]
  norm_num

/-! ### The explicit compactly supported locally constant function -/

/-- The indicator of the integral finite adèles: the standard compactly supported locally
constant test function on the finite adèles. -/
private def hInt : FiniteAdeleRing (𝓞 ℚ) ℚ → ℂ :=
  (AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ).indicator fun _ => 1

/-- The indicator of a clopen set is locally constant. -/
private theorem hInt_locallyConstant : IsLocallyConstant hInt := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ
  · filter_upwards [(AdelicBox.isOpen_integralFiniteAdeles ℚ).mem_nhds hx] with y hy
    simp only [hInt, Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards
      [(AdelicBox.isClosed_integralFiniteAdeles (K := ℚ)).isOpen_compl.mem_nhds hx] with y hy
    simp only [hInt, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

/-- Its support sits in the compact integral finite adèles. -/
private theorem hInt_hasCompactSupport : HasCompactSupport hInt := by
  have hsupp : Function.support hInt ⊆ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro x hx
    by_contra h
    exact hx (by simp [hInt, h])
  exact (AdelicBox.isCompact_integralFiniteAdeles (K := ℚ)).of_isClosed_subset
    isClosed_closure
    (closure_minimal hsupp (AdelicBox.isClosed_integralFiniteAdeles (K := ℚ)))

/-- The indicator is `1` at the origin of the finite adèles. -/
private theorem hInt_zero : hInt 0 = 1 := by
  have h0 : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :=
    zero_mem_integralFiniteAdeles' ℚ
  simp [hInt, h0]

/-! ### Zone 1 — the pure tensor, and its value at `0` -/

/-- The pure tensor of the bump and the indicator of the integral finite adèles. -/
private def fTensor : AdeleRing (𝓞 ℚ) ℚ → ℂ :=
  fun x => gBump (ringEquiv_mixedSpace ℚ x.1) * hInt x.2

/-- `fTensor` is a pure tensor: the module's `tensor_mem_pureTensorSet` read at it. -/
theorem fTensor_mem_pureTensorSet : fTensor ∈ pureTensorSet ℚ :=
  tensor_mem_pureTensorSet gBump hInt hInt_locallyConstant hInt_hasCompactSupport

/-- Hence it lies in the Schwartz–Bruhat space. -/
theorem fTensor_mem_schwartzBruhat : fTensor ∈ schwartzBruhat ℚ :=
  mem_schwartzBruhat_of_mem_pureTensorSet fTensor_mem_pureTensorSet

/-- The tensor evaluated at the origin: both factors take the value `1` there. -/
theorem fTensor_zero : fTensor 0 = 1 := by
  have h1 : ((0 : AdeleRing (𝓞 ℚ) ℚ)).1 = 0 := rfl
  have h2 : ((0 : AdeleRing (𝓞 ℚ) ℚ)).2 = 0 := rfl
  show gBump (ringEquiv_mixedSpace ℚ ((0 : AdeleRing (𝓞 ℚ) ℚ)).1)
      * hInt ((0 : AdeleRing (𝓞 ℚ) ℚ)).2 = 1
  rw [h1, h2, map_zero, gBump_zero, hInt_zero, mul_one]

/-! ### Zone 2 — the two headlines and the cell lemmas, at `fTensor` -/

/-- `fTensor` is integrable for the additive Haar measure, through the pin's pure-tensor
engine. -/
theorem fTensor_integrable_pureTensor :
    Integrable fTensor (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
  integrable_pureTensor (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    gBump hInt hInt_locallyConstant hInt_hasCompactSupport

/-- The same, through the module's headline `integrable_of_mem_schwartzBruhat`. -/
theorem fTensor_integrable :
    Integrable fTensor (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
  integrable_of_mem_schwartzBruhat ℚ (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    fTensor_mem_schwartzBruhat

/-- The diagonal translates of `fTensor` are summable at `x = 0` — the module's headline
`summable_translate_of_mem_schwartzBruhat`, evaluated. -/
theorem fTensor_summable_at_zero :
    Summable fun ξ : ℚ => fTensor (0 + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) :=
  summable_translate_of_mem_schwartzBruhat ℚ fTensor_mem_schwartzBruhat 0

/-- The compactness of the cell carrying the tensor: `isCompact_cell` at `K = tsupport hInt`
and `l = 0`. -/
theorem cell_compact :
    IsCompact (cell (tsupport hInt) (0 : mixedEmbedding.mixedSpace ℚ)) :=
  isCompact_cell hInt_hasCompactSupport 0

/-- The origin lies in the cell of its own floor: `mem_cell_floor` at the tensor's finite
coordinate `0`, which lies in `tsupport hInt`. -/
theorem origin_mem_cell :
    (0 : AdeleRing (𝓞 ℚ) ℚ) ∈
      cell (tsupport hInt)
        (ZSpan.floor (mixedEmbedding.latticeBasis ℚ)
          (ringEquiv_mixedSpace ℚ ((0 : AdeleRing (𝓞 ℚ) ℚ)).1) : mixedEmbedding.mixedSpace ℚ) := by
  refine mem_cell_floor (x := (0 : AdeleRing (𝓞 ℚ) ℚ)) ?_
  refine subset_tsupport hInt ?_
  have h2 : ((0 : AdeleRing (𝓞 ℚ) ℚ)).2 = 0 := rfl
  rw [h2, Function.mem_support, hInt_zero]
  exact one_ne_zero

/-- The translated cell has the measure of the untranslated one (`measure_cell`), so the
covering used by the integrability proof is measure-stationary at the tensor's cell. -/
theorem cell_measure :
    NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
        (cell (tsupport hInt) (0 : mixedEmbedding.mixedSpace ℚ)) =
      NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
        (cell0 (tsupport hInt)) :=
  measure_cell (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    (tsupport hInt) (0 : mixedEmbedding.mixedSpace ℚ)

end NumberFieldAdelicFourierConsumer
