/-
  Cross-module wire test for the automorphic / adèlic definition foundation.

  A `spec/` probe, not a library module. One executed zone per definition level
  (`topics/PORTING-AutomorphicForm.md` §5): D0 the mathlib-only leaves, then the
  adele topology / level projections and the factorisable-test-function premise.
  Every zone is a real composition — no `#check` — so deleting any one module it
  imports makes the probe fail.
-/
import FLTForHuman.RepTheory.ContinuousSMulDiscrete
import FLTForHuman.RepTheory.SmoothVectors
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.TestFnNearIdentity
import FLTForHuman.AutomorphicForm.Adelic.RightConvNeZero
import FLTForHuman.AutomorphicForm.Adelic.RightConvNeZeroPrincipal
import FLTForHuman.AutomorphicForm.Adelic.RightConvNeZeroArch
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicCentre
import FLTForHuman.MeasureTheory.ContractionDecay
import FLTForHuman.MeasureTheory.ScalingDichotomy
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm Matrix MeasureTheory
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace AutomorphicFormConsumer

-- Zone D0a: the discrete-`SMul` class, its stabilizer form and the `ContinuousSMul`
-- direction of the equivalence.
example {G M : Type*} [TopologicalSpace G] [Group G] [MulAction G M]
    [ContinuousSMulDiscrete G M] (x : M) : IsOpen (MulAction.stabilizer G x : Set G) :=
  ContinuousSMulDiscrete.isOpen_stabilizer G x

example {G M : Type*} [TopologicalSpace G] [SMul G M] [TopologicalSpace M]
    [DiscreteTopology M] (h : ContinuousSMulDiscrete G M) : ContinuousSMul G M :=
  continuousSMulDiscrete_iff.mp h

-- Zone D0b: the adèlic group `GL₂(𝔸_F)` and the determinant character `chiDet`.
example (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F χ g = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := rfl

-- Zone D0c: unipotents, constant terms and cuspidality.
example {R : Type*} [CommRing R] (x y : R) :
    unipotentGL2 (x + y) = unipotentGL2 x * unipotentGL2 y :=
  unipotentGL2_add x y

example {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G] (μ : Measure Q) (u : Q → G)
    (g : G) : constantTerm μ u (fun _ => (0 : ℂ)) g = 0 :=
  constantTerm_zero μ u g

-- Zone D0d: the `LsXi` space is non-empty.
example (F : Type) [Field F] [NumberField F] [MeasureSpace (AdelicGL2 (𝓞 F) F)]
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) (D : Set (AdelicGL2 (𝓞 F) F)) :
    LsXiMember (𝓞 F) F Z ξ D (fun _ => (0 : ℂ)) :=
  lsXiMember_zero (𝓞 F) F Z ξ D

-- Zone D1: the adele ring is Hausdorff and the level projections are continuous.
example (F : Type) [Field F] [NumberField F] : T2Space (AdeleRing (𝓞 F) F) := inferInstance

example (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) :
    NumberField.AdelicLevel.adeleArch (𝓞 F) F a = a.1 := rfl

example (F : Type) [Field F] [NumberField F] (g : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (i j : Fin 2) :
    (NumberField.AdelicLevel.glArch (𝓞 F) F g :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 := rfl

-- Zone D1: the adele / GL₂(𝔸_F) Borel and Haar layer.
example (F : Type) [Field F] [NumberField F] :
    @BorelSpace (AdeleRing (𝓞 F) F) _ (NumberField.AdelicHaar.adeleBorel (𝓞 F) F) :=
  NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F

example (F : Type) [Field F] [NumberField F] :
    @Measure.IsAddHaarMeasure (AdeleRing (𝓞 F) F) _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 F) F)
      (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) :=
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F

example (F : Type) [Field F] [NumberField F] :
    @Measure.IsHaarMeasure (GL (Fin 2) (AdeleRing (𝓞 F) F)) _ _
      (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

example (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := inferInstance

example (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) := inferInstance

-- Zone D2: smooth vectors and the smooth-vector submodule.
example {G M : Type*} [Group G] [TopologicalSpace G] [AddMonoid M] [DistribMulAction G M] :
    FLT.SmoothVectors.IsSmoothVector G (0 : M) :=
  FLT.SmoothVectors.isSmoothVector_zero

example {G M : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MulAction G M]
    {v : M} (h : FLT.SmoothVectors.IsSmoothVector G v) (g : G) :
    FLT.SmoothVectors.IsSmoothVector G (g • v) :=
  h.smul g

example (G : Type*) [Group G] [TopologicalSpace G] [ContinuousMul G]
    (R : Type*) [Semiring R] (M : Type*) [AddCommMonoid M] [Module R M]
    [DistribMulAction G M] [SMulCommClass G R M] {v : M} :
    v ∈ FLT.SmoothVectors.smoothVectors G R M ↔ FLT.SmoothVectors.IsSmoothVector G v :=
  FLT.SmoothVectors.mem_smoothVectors_iff

-- Zone D3: the level-`N` lattice and the adèlic level subgroups.
example (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    NumberField.AdelicLevel.levelOne (𝓞 F) F N ≤ NumberField.AdelicLevel.levelZero (𝓞 F) F N :=
  NumberField.AdelicLevel.levelOne_le_levelZero (𝓞 F) F N

example (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    IsCompact (NumberField.AdelicLevel.finiteLevelOne (𝓞 F) F N :
      Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
  NumberField.AdelicLevel.isCompact_finiteLevelOne (𝓞 F) F N

example (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    (0 : FiniteAdeleRing (𝓞 F) F) ∈ NumberField.AdelicLevel.idealBall (𝓞 F) F N :=
  NumberField.AdelicLevel.zero_mem_idealBall N

example (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    NumberField.AdelicLevel.idealBound (𝓞 F) ⊥ v = 0 :=
  NumberField.AdelicLevel.idealBound_bot v

-- Zone D4: the carrier pins and right convolution.
example (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F)) :
    (productionPinsOf F D U gen B).μ = NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F :=
  productionPinsOf_μ F D U gen B

example (K : Type) [Field K] [NumberField K] (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    rightConv K φ (fun _ => 0) = fun _ => 0 :=
  rightConv_zero_right K φ

-- Zone D5: automorphic / smooth automorphic functions.
example (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsAutomorphicFnAt F pins ξ (fun _ => (0 : ℂ)) :=
  isAutomorphicFnAt_zero F pins ξ

example (F : Type) [Field F] [NumberField F] (k : AdelicGL2 (𝓞 F) F) :
    k ∈ finiteAdelicGL2Subgroup F ↔ NumberField.AdelicLevel.glArch (𝓞 F) F k = 1 :=
  mem_finiteAdelicGL2Subgroup_iff F k

example (F : Type) [Field F] [NumberField F] :
    IsKfSmooth F (fun _ => (0 : ℂ)) :=
  isKfSmooth_zero F

-- Zone D6: the windowed Siegel norms and row isometries.
example {K : Type*} [NormedField K] :
    AutomorphicForm.WindowedSiegel.rowNormSq (1 : Matrix (Fin 2) (Fin 2) K) = 1 :=
  AutomorphicForm.WindowedSiegel.rowNormSq_one

example {K : Type*} [NormedField K] :
    AutomorphicForm.WindowedSiegel.IsRowIsometry (1 : GL (Fin 2) K) :=
  AutomorphicForm.WindowedSiegel.isRowIsometry_one

example (F : Type) [Field F] [NumberField F] {c u : ℝ} (hc : c ≤ 1) :
    (1 : AdelicGL2 (𝓞 F) F) ∈ AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u :=
  AutomorphicForm.WindowedSiegel.one_mem_integralWindowedSiegelSet F hc

-- Zone D7: the archimedean inclusion and archimedean types.
example (F : Type) [Field F] [NumberField F] (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    NumberField.AdelicLevel.glArch (𝓞 F) F (adelicArchGLIncl F k) = k :=
  glArch_adelicArchGLIncl F k

example (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F,
      AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion →* ℂˣ) :
    HasArchType F χ (fun _ => (0 : ℂ)) :=
  hasArchType_zero F χ

-- Zone H1: the shared near-identity factorisable-test-function prelude.
example (F : Type) [Field F] [NumberField F] (ρ : ℝ) (hρ : 0 < ρ)
    (hρε : ρ ≤ AutomorphicForm.TestFnNearIdentity.ε F / 2) {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsFactorizableTestFn F (AutomorphicForm.TestFnNearIdentity.testFn F ρ hρ N) :=
  AutomorphicForm.TestFnNearIdentity.isFactorizableTestFn_testFn F ρ hρ hρε hN

example (F : Type) [Field F] [NumberField F] (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) :
    AutomorphicForm.TestFnNearIdentity.testFnR F ρ hρ N 1 = 1 :=
  AutomorphicForm.TestFnNearIdentity.testFnR_one F ρ hρ N

example (F : Type) [Field F] [NumberField F] (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F))
    (g : AdelicGL2 (𝓞 F) F) :
    0 ≤ AutomorphicForm.TestFnNearIdentity.testFnR F ρ hρ N g :=
  AutomorphicForm.TestFnNearIdentity.testFnR_nonneg F ρ hρ N g

-- Zone T1: the two H1-served `rightConv_ne_zero_of_*` headlines.
example (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K,
      ∀ k ∈ NumberField.AdelicLevel.levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        φ (g * k) = φ g) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K f ∧ ∃ g, rightConv K φ f g ≠ 0 := by
  obtain ⟨f, hf, -, -, hg⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
      K N hN φ hcont hne hlev
  exact ⟨f, hf, hg⟩

example (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K,
      ∀ k ∈ NumberField.AdelicLevel.principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        φ (g * k) = φ g) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K f ∧ ∃ g, rightConv K φ f g ≠ 0 := by
  obtain ⟨f, hf, -, -, hg⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_principalLevel_invariant
      K N hN φ hcont hne hlev
  exact ⟨f, hf, hg⟩

-- Zone T1c: the arch-character headline.
example (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K,
      ∀ u ∈ NumberField.AdelicLevel.levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        φ (g * u) = φ g)
    (hk : HasArchCharacterAt₀ K w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K f ∧ ∃ g, rightConv K φ f g ≠ 0 := by
  obtain ⟨f, hf, -, -, -, hg⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt
      K N hN w hw k φ hcont hne hlev hk
  exact ⟨f, hf, hg⟩

-- Zone 2: the definitions and their non-vacuity witness.
example (F : Type) [Field F] [NumberField F] :
    AutomorphicForm.IsFactorizableTestFn F
      (fun _ : GL (Fin 2) (AdeleRing (𝓞 F) F) => (0 : ℂ)) :=
  AutomorphicForm.isFactorizableTestFn_zero F

-- Zone 3: the headline, applied to that witness.
example (F : Type) [Field F] [NumberField F] :
    Continuous (fun _ : GL (Fin 2) (AdeleRing (𝓞 F) F) => (0 : ℂ)) ∧
      HasCompactSupport (fun _ : GL (Fin 2) (AdeleRing (𝓞 F) F) => (0 : ℂ)) :=
  AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F _
    (AutomorphicForm.isFactorizableTestFn_zero F)

-- Zone W1 (TOPIC-rightConv-comm): the adèlic box. `adelicBox` is the pinned argument
-- of `productionPinsOf`; here it is a fundamental domain with finite positive Haar
-- measure, and conditioning on it is a probability measure.
example (K : Type) [Field K] [NumberField K] (x : AdeleRing (𝓞 K) K) :
    ∃! k : K, algebraMap K (AdeleRing (𝓞 K) K) k + x ∈ NumberField.AdelicBox.adelicBox K :=
  NumberField.AdelicBox.existsUnique_algebraMap_add_mem_adelicBox K x

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel in
example (K : Type) [Field K] [NumberField K] :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K)
      (NumberField.AdelicBox.adelicBox K) (NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K) :=
  NumberField.AdelicBox.isAddFundamentalDomain_adelicBox_adelicAddHaar K

example (K : Type) [Field K] [NumberField K] :
    0 < NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K (NumberField.AdelicBox.adelicBox K) :=
  NumberField.AdelicBox.adelicAddHaar_adelicBox_pos K

open scoped ProbabilityTheory in
example (K : Type) [Field K] [NumberField K] :
    IsProbabilityMeasure
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K)[|NumberField.AdelicBox.adelicBox K]) :=
  NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox K

-- Zone W2 (TOPIC-rightConv-comm): the adèlic centre and the projective quotient.
-- `AdelicPGL2` is `GL₂(𝔸_K)` modulo its centre (`scalar_injective` names the centre
-- as the injective scalar image) and `adelicPGLHaar` is a Haar measure on it:
-- positive on the image of any open nonempty set and finite on the image of a
-- compact set times the centre — the two estimates the cusp and Siegel carriers
-- integrate against.
example (K : Type) [Field K] [NumberField K] :
    Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing (𝓞 K) K)ˣ →* _) :=
  NumberField.AdelicCentre.scalar_injective (𝓞 K) K

example (K : Type) [Field K] [NumberField K] :
    @Measure.IsHaarMeasure (NumberField.AdelicCentre.AdelicPGL2 (𝓞 K) K) _ _
      (NumberField.AdelicCentre.pglBorel (𝓞 K) K)
      (NumberField.AdelicCentre.adelicPGLHaar (𝓞 K) K) :=
  NumberField.AdelicCentre.isHaarMeasure_adelicPGLHaar (𝓞 K) K

example (K : Type) [Field K] [NumberField K] :
    0 < NumberField.AdelicCentre.adelicPGLHaar (𝓞 K) K
      ((QuotientGroup.mk : GL (Fin 2) (AdeleRing (𝓞 K) K) →
          NumberField.AdelicCentre.AdelicPGL2 (𝓞 K) K) '' Set.univ) :=
  NumberField.AdelicCentre.adelicPGLHaar_image_pos (𝓞 K) K
    ⟨Set.univ, isOpen_univ, ⟨1, Set.mem_univ _⟩, Set.subset_univ _⟩

open scoped Pointwise in
example (K : Type) [Field K] [NumberField K] :
    NumberField.AdelicCentre.adelicPGLHaar (𝓞 K) K
      ((QuotientGroup.mk : GL (Fin 2) (AdeleRing (𝓞 K) K) →
          NumberField.AdelicCentre.AdelicPGL2 (𝓞 K) K) ''
        ({(1 : GL (Fin 2) (AdeleRing (𝓞 K) K))} *
          ((Subgroup.center (GL (Fin 2) (AdeleRing (𝓞 K) K)) :
            Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))) < ⊤ :=
  NumberField.AdelicCentre.adelicPGLHaar_image_lt_top_of_subset (𝓞 K) K
    isCompact_singleton le_rfl

-- Zone W3 (TOPIC-rightConv-comm): the generic measure-theoretic decay engines, both over
-- an arbitrary group and so homed in `MeasureTheory/` rather than `AutomorphicForm/`.
-- `ContractionDecay` cuts a set into `r`-scaled shells (`iUnion_shell`) and sums them to
-- bound the whole mass by the low shell; `ScalingDichotomy` cuts a positive function into
-- `ℤ`-slices and shows that a measure invariant under the scaling is `0` or `⊤`. The zone
-- instantiates both in `ℝˣ` with the zero measure.
example :
    ⋃ k, MeasureTheory.ContractionDecay.shell (Set.univ : Set ℝˣ) (fun _ => (1 : ℝ)) 1 2 k
      = Set.univ :=
  MeasureTheory.ContractionDecay.iUnion_shell (G := ℝˣ) (S := Set.univ)
    (φ := fun _ => (1 : ℝ)) (c := 1) (r := 2) one_pos one_lt_two (fun _ _ => le_rfl)

example : MeasurableSet (MeasureTheory.ContractionDecay.shell (Set.univ : Set ℝˣ)
    (fun _ => (1 : ℝ)) 1 2 3) :=
  MeasureTheory.ContractionDecay.measurableSet_shell MeasurableSet.univ measurable_const 1 2 3

example :
    ⋃ k : ℤ, MeasureTheory.ScalingDichotomy.zpowSlice (Set.univ : Set ℝˣ)
      (fun _ => (1 : ℝ)) 2 k = Set.univ :=
  MeasureTheory.ScalingDichotomy.iUnion_zpowSlice (D := Set.univ) (f := fun _ => (1 : ℝ))
    (r := 2) one_lt_two (fun _ _ => one_pos)

section
-- The default `MeasurableSpace ℝˣ` is not Borel, so pin it locally to let the
-- `ContinuousMul → MeasurableMul` instance fire for the two measure headlines.
local instance : MeasurableSpace ℝˣ := borel ℝˣ
local instance : BorelSpace ℝˣ := ⟨rfl⟩

example :
    (0 : Measure ℝˣ) Set.univ ≤
      2 * (0 : Measure ℝˣ) (Set.univ ∩ (fun _ : ℝˣ => (1 : ℝ)) ⁻¹' Set.Iio 2) := by
  have : (0 : Measure ℝˣ).IsMulLeftInvariant := ⟨fun g => by simp⟩
  exact MeasureTheory.ContractionDecay.measure_le_two_mul_measure_inter (0 : Measure ℝˣ)
    MeasurableSet.univ measurable_const one_pos one_lt_two (S := Set.univ)
    (φ := fun _ => (1 : ℝ)) (c := 1) (r := 2) (p := 1) (q := 1)
    (fun _ _ => le_rfl) (fun _ _ h => absurd h (by norm_num))
    (fun _ _ h => absurd h (by norm_num))
    (fun _ _ _ _ h _ => absurd h (by norm_num))

example : (0 : Measure ℝˣ) Set.univ < ⊤ := by
  have : (0 : Measure ℝˣ).IsMulLeftInvariant := ⟨fun g => by simp⟩
  exact MeasureTheory.ContractionDecay.measure_lt_top_of_measure_inter_lt_top (0 : Measure ℝˣ)
    MeasurableSet.univ measurable_const one_pos one_lt_two (S := Set.univ)
    (φ := fun _ => (1 : ℝ)) (c := 1) (r := 2) (p := 1) (q := 1)
    (fun _ _ => le_rfl) (fun _ _ h => absurd h (by norm_num))
    (fun _ _ h => absurd h (by norm_num))
    (fun _ _ _ _ h _ => absurd h (by norm_num)) (by simp)

example :
    (0 : Measure ℝˣ) Set.univ = 0 ∨ (0 : Measure ℝˣ) Set.univ = ⊤ := by
  have : (0 : Measure ℝˣ).IsMulLeftInvariant := ⟨fun g => by simp⟩
  exact MeasureTheory.ScalingDichotomy.measure_eq_zero_or_top_of_mul_preimage_eq
    (μ := (0 : Measure ℝˣ)) (z := Units.mk0 (2 : ℝ) (by norm_num))
    (f := fun x : ℝˣ => ((x : ℝ)) ^ 2) (r := 4)
    (by fun_prop) (by norm_num)
    (fun g => by rw [Units.val_mul, Units.val_mk0]; ring)
    (fun g _ => sq_pos_of_ne_zero g.ne_zero) MeasurableSet.univ (by ext g; simp)

end

end AutomorphicFormConsumer

end
