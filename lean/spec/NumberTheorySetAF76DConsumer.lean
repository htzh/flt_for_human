/-
  Consumer zone for `WORKORDER-AF76D` — the integrable pure tensor, at `F = ℚ`.

  A `spec/` probe, not a library module. The row under test is
  `NumberField.AdelicFourier.integrable_mul_of_integrable_of_integrable`: for an additive Haar
  measure `μ` on `𝔸_F`, a Haar measure `ν` on the finite adèles and integrable `f`, `g`, the pure
  tensor `x ↦ f x.1 * g x.2` is `μ`-integrable.  Here it is read twice at the same concrete pair:

  * `f = gBump`, an explicit Schwartz function on the mixed space of `ℚ` (a smooth compactly
    supported bump), `volume`-integrable by `SchwartzMap.integrable`;
  * `g = hInt`, the indicator of an explicit compact set — the integral finite adèles, the finite
    half of the box — which is locally constant and compactly supported, hence `ν`-integrable by
    `Continuous.integrable_of_hasCompactSupport`;
  * `μ = adelicAddHaar`, `ν = M4aS4.finMeasure` (the `zhatCompacts` Haar measure).

  Zone 1 feeds that pair to the row.  Zone 2 feeds the *same* tensor to SET-AF75's
  `integrable_of_mem_schwartzBruhat` (it is a pure tensor, so Schwartz–Bruhat), and the last
  theorem states that the two roads reach one and the same `Integrable` statement — the row is the
  Schwartz–Bruhat engine with the two smoothness hypotheses dropped.  `fTensor_zero` shows the pair
  is not degenerate: the tensor is `1` at the origin.

  It was written while the row's dependency `FLTForHuman/NumberTheory/AdelicBox/Normalization`
  (order AF76B) was still red, so every API use was first elaborated against the row's *statement*
  in `lean/tmp/af76/consumer_probe.lean` (the row's proof replaced by `sorry`, §3.5 probe step 2);
  this file was then checked as it stands by
  `lake env lean spec/NumberTheorySetAF76DConsumer.lean` — 0 errors, 0 warnings, no `#check`.
-/
import FLTForHuman.NumberTheory.AdelicFourier.IntegrableTensor
import FLTForHuman.NumberTheory.AdelicFourier.Space
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox IsDedekindDomain
open Classical
open scoped ENNReal NNReal ContDiff Topology SchwartzMap M4aS4

set_option autoImplicit false

noncomputable section

namespace NumberFieldAdelicFourierAF76DConsumer

open NumberField.AdelicFourier NumberField.InfiniteAdeleRing

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] M4aS4.finBorel

/-! ### The explicit integrable pair at `F = ℚ` -/

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

/-- The archimedean factor: the explicit Schwartz function (a bump) on the mixed space of `ℚ`. -/
private def gBump : 𝓢(mixedEmbedding.mixedSpace ℚ, ℂ) :=
  bumpFun_hasCompactSupport_complex.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp bumpFun_contDiff)

/-- The finite factor: the indicator of the integral finite adèles (the finite half of the box),
which is clopen and compact. -/
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

/-- The archimedean half of the row's hypothesis: the Schwartz function is `volume`-integrable. -/
private theorem gBump_integrable : Integrable (gBump : mixedEmbedding.mixedSpace ℚ → ℂ) volume :=
  gBump.integrable

/-- The finite half of the row's hypothesis: the indicator is integrable for the finite Haar
measure. -/
private theorem hInt_integrable : Integrable hInt (M4aS4.finMeasure ℚ) :=
  hInt_locallyConstant.continuous.integrable_of_hasCompactSupport hInt_hasCompactSupport

/-- The pure tensor of the bump and the indicator of the integral finite adèles. -/
private def fTensor : AdeleRing (𝓞 ℚ) ℚ → ℂ :=
  fun x => gBump (ringEquiv_mixedSpace ℚ x.1) * hInt x.2

/-- `fTensor` is a pure tensor (AF75A's `tensor_mem_pureTensorSet`). -/
theorem fTensor_mem_pureTensorSet : fTensor ∈ pureTensorSet ℚ :=
  tensor_mem_pureTensorSet gBump hInt hInt_locallyConstant hInt_hasCompactSupport

/-- Hence it lies in the Schwartz–Bruhat space (AF75A's `mem_schwartzBruhat_of_mem_pureTensorSet`). -/
theorem fTensor_mem_schwartzBruhat : fTensor ∈ schwartzBruhat ℚ :=
  mem_schwartzBruhat_of_mem_pureTensorSet fTensor_mem_pureTensorSet

/-- The tensor evaluated at the origin: both factors take the value `1` there, so the pair is not
degenerate. -/
theorem fTensor_zero : fTensor 0 = 1 := by
  have h1 : ((0 : AdeleRing (𝓞 ℚ) ℚ)).1 = 0 := rfl
  have h2 : ((0 : AdeleRing (𝓞 ℚ) ℚ)).2 = 0 := rfl
  have hg0 : gBump 0 = 1 := by
    have h0 : (0 : mixedEmbedding.mixedSpace ℚ) ∈ Metric.closedBall 0 bumpSpace.rIn := by
      simp [bumpSpace.rIn_pos.le]
    show (bumpFun 0 : ℂ) = 1
    rw [show bumpFun 0 = 1 from bumpSpace.one_of_mem_closedBall h0]
    norm_num
  have hi0 : hInt 0 = 1 := by
    have h0 : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :=
      zero_mem_integralFiniteAdeles' ℚ
    simp [hInt, h0]
  show gBump (ringEquiv_mixedSpace ℚ ((0 : AdeleRing (𝓞 ℚ) ℚ)).1)
      * hInt ((0 : AdeleRing (𝓞 ℚ) ℚ)).2 = 1
  rw [h1, h2, map_zero, hg0, hi0, mul_one]

/-! ### Zone 1 — the row, read at the pair -/

/-- **The row**, read out at the concrete pair: the tensor of the bump and the indicator is
integrable for the additive Haar measure on `𝔸_ℚ`. -/
theorem tensor_integrable_of_row :
    Integrable fTensor (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
  integrable_mul_of_integrable_of_integrable (F := ℚ)
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (M4aS4.finMeasure ℚ)
    gBump hInt gBump_integrable hInt_integrable

/-! ### Zone 2 — SET-AF75's engine at the same tensor, and the agreement -/

/-- **AF75's engine** at the same tensor: the pure tensor is Schwartz–Bruhat, hence integrable. -/
theorem tensor_integrable_of_schwartzBruhat :
    Integrable fTensor (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
  integrable_of_mem_schwartzBruhat ℚ (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    fTensor_mem_schwartzBruhat

/-- **They agree**: at the pure tensor `fTensor` the row's conclusion (from the two factors'
integrability) and AF75's conclusion (from Schwartz–Bruhat membership) are one and the same
`Integrable` statement, and both hold. -/
theorem tensor_integrable_two_ways :
    Integrable fTensor (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) ∧
      Integrable fTensor (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
  ⟨tensor_integrable_of_row, tensor_integrable_of_schwartzBruhat⟩

end NumberFieldAdelicFourierAF76DConsumer
