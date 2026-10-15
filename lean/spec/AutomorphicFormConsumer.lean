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
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Topology
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Coordinates
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
import FLTForHuman.RepTheory.AbstractHeckeOperator
import FLTForHuman.AutomorphicForm.Adelic.HeckeEigensystem
import FLTForHuman.RepTheory.LocalNewvector.CongruenceSubgroupK1
import FLTForHuman.NumberTheory.NumberField.IdeleClass.Vocab
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArithRealization
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.ArchSpherical
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Frame
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.PlaceClassData
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.SliceCentrality
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.MeasureAssembly
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Compact
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Level
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Principal
-- The archimedean approximate-identity chain (WORKORDER-Q): the definition gate, the
-- adèlic half, the two generic engines, the instantiation, and the façade headline.
import FLTForHuman.AutomorphicForm.Adelic.ArchHaar
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.EntryBall
import FLTForHuman.RepTheory.TypeReproducer
import FLTForHuman.RepTheory.ConvolutionLimit
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.Instantiate
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity
-- The Bruhat-transversal / Weyl-integrand trio (WORKORDER-R): the generic base, the
-- coset/transfer/box layers, the estimates/assembly/uniform bound, the per-file caps
-- and the façade headlines.
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Coset
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Transfer
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.BoxBounds
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.LatticeEstimates
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Assembly
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.UniformBound
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Caps
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable
import FLTForHuman.NumberTheory.SiegelVolume
import FLTForHuman.Order.Filter.Cofinite
import FLTForHuman.Topology.Bases
import FLTForHuman.Topology.Algebra.Module.Quotient
import FLTForHuman.Topology.Algebra.ContinuousMonoidHom
import FLTForHuman.Topology.Algebra.RestrictedProduct.Basic
import FLTForHuman.Topology.Algebra.RestrictedProduct.Equiv
import FLTForHuman.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm Matrix MeasureTheory
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open NumberField.AdelicHaar
open scoped NNReal

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

-- Zone W4 (TOPIC-rightConv-comm): the windowed-Siegel topology and coordinates.
-- `Topology.lean` gives the continuity of the window data and the open structure of
-- `integralWindowedSiegelSet`; `Coordinates.lean` gives the matrix coordinates
-- (`upperUnit`, `xCoord`) and their height-scaling laws.
example {K : Type*} [NormedField K] :
    Continuous (AutomorphicForm.WindowedSiegel.xWindowSq (K := K)) :=
  AutomorphicForm.WindowedSiegel.continuous_xWindowSq

example (F : Type) [Field F] [NumberField F] {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    (1 : AdelicGL2 (𝓞 F) F) ∈
      interior (AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u) :=
  AutomorphicForm.WindowedSiegel.one_mem_interior_integralWindowedSiegelSet F hc hu

example (F : Type) [Field F] [NumberField F] {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    ∃ U : Set (AdelicGL2 (𝓞 F) F), IsOpen U ∧ U.Nonempty ∧
      U ⊆ AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u :=
  AutomorphicForm.WindowedSiegel.exists_isOpen_subset_integralWindowedSiegelSet F hc hu

example {K : Type*} [NormedField K] (g : GL (Fin 2) K) :
    0 ≤ AutomorphicForm.WindowedSiegel.xWindowSq g :=
  AutomorphicForm.SiegelCoordinates.xWindowSq_nonneg g

example (g : GL (Fin 2) ℂ) :
    AutomorphicForm.WindowedSiegel.xWindowSq g =
      ‖AutomorphicForm.SiegelCoordinates.xCoord (g : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 :=
  AutomorphicForm.SiegelCoordinates.xWindowSq_eq_norm_xCoord_sq g

example {K : Type*} [NormedField K] (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    AutomorphicForm.WindowedSiegel.localHeight
        (AutomorphicForm.SiegelCoordinates.upperUnit a b t ha ht) =
      ‖a‖ / ‖t‖ * AutomorphicForm.WindowedSiegel.localHeight (1 : GL (Fin 2) K) := by
  simpa using AutomorphicForm.SiegelCoordinates.localHeight_upper_entries_mul (s :=
    AutomorphicForm.SiegelCoordinates.upperUnit a b t ha ht) ht rfl rfl rfl 1

-- Zone W5 (TOPIC-rightConv-comm): the Hecke/local vocabulary, cut by mathematical role.
-- `AbstractHeckeOperator` is the generic Hecke operator on `fixedPoints`; the automorphic
-- `HeckeEigensystem` and its Satake recursion are the eigenvalue datum; `LocalNewvector`
-- supplies the congruence subgroups `K₀`/`K₁`; `M4aHerbrand` the idèle-class group with its
-- Galois descent.
example {G : Type*} [Group G] {A : Type*} [AddCommMonoid A] [DistribMulAction G A]
    (a b : MulAction.fixedPoints G A) :
    ((a + b : MulAction.fixedPoints G A) : A) = a + b :=
  FixedPoints.coe_add a b

open scoped Pointwise in
example {G : Type*} [Group G] (U : Subgroup G) (X : Set G) {u : G} (hu : u ∈ U) :
    Set.BijOn (fun x ↦ u • x) ((U : Set G) * X) (U * X) :=
  Set.bijOn_smul G U X hu

example : AutomorphicForm.satakePow 2 (3 : ℤ) 5 = 9 - 10 := by
  rw [AutomorphicForm.satakePow_add_two 0, AutomorphicForm.satakePow_one,
    AutomorphicForm.satakePow_zero]
  norm_num

example (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (({ level := ⊤, level_ne_bot := by simp, a := fun _ => (1 : ℂ),
        b := fun _ => (1 : ℂ) } : AutomorphicForm.HeckeEigensystem ℚ ℂ).twist χ).a v
      = χ v * 1 :=
  AutomorphicForm.HeckeEigensystem.twist_a _ χ v

example (p : ℕ) [Fact p.Prime] :
    LocalNewvector.padicK1 p 1 ≤ LocalNewvector.padicK0 p 1 :=
  LocalNewvector.congruenceK1_le_congruenceK0 (p : ℤ_[p]) 1

example : M4aHerbrand.IdeleGaloisDescent ℤ ℚ ℚ :=
  M4aHerbrand.identityDescent ℤ ℚ ℚ

-- Zone W6 (TOPIC-rightConv-comm): the mathlib-gap stubs of the twin's definition closure,
-- ported whole to a mathlib-mirroring tree (`Order/`, `Topology/`). Two are mathlib
-- substitutions rather than ports: `Submonoid.units_isOpen` is mathlib's
-- `Submonoid.isOpen_units`, and `RestrictedProduct.singleAddMonoidHom` is mathlib's
-- `to_additive` companion of `mulSingleMonoidHom`.
example : Countable (Filter.cofinite : Filter ℕ).sets := inferInstance

example (ι : Type*) [Countable ι] : (Filter.cofinite : Filter ι).sets.Countable :=
  Filter.cofinite.sets.countable ι

example :
    (((i : Fin 2) → ℝ) ⧸ Submodule.pi Set.univ (fun _ => (⊥ : Submodule ℝ ℝ)))
      ≃L[ℝ] ((i : Fin 2) → ℝ ⧸ (⊥ : Submodule ℝ ℝ)) :=
  Submodule.quotientPiContinuousLinearEquiv (fun _ : Fin 2 => (⊥ : Submodule ℝ ℝ))

example : ((i : Fin 1) → ℝ) ≃ₜ* ℝ := ContinuousMulEquiv.piUnique (fun _ : Fin 1 => ℝ)

example {M : Type*} [TopologicalSpace M] [Monoid M] {U : Submonoid M} (hU : IsOpen (U : Set M)) :
    IsOpen (U.units : Set Mˣ) := Submonoid.isOpen_units hU

open scoped RestrictedProduct in
example : SecondCountableTopology (Πʳ _i : ℕ, [ℝ, Set.univ]) :=
  RestrictedProduct.secondCountableTopology (fun _ : ℕ => isOpen_univ)

-- Zone W7-W10 (TOPIC-rightConv-comm): the definition gate proper, cross-module. The
-- production-pins bundles, the arithmetic cusp realization and the Siegel-volume
-- archimedean embedding.
example (F : Type) [Field F] [NumberField F] :
    (AutomorphicForm.productionPins F).μ =
      NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F :=
  AutomorphicForm.productionPins_μ F

example (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    (AutomorphicForm.productionPinsCompact F).U N ≤ (AutomorphicForm.productionPins F).U N :=
  AutomorphicForm.productionPinsCompact_U_le_productionPins_U F N

example (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    AutomorphicForm.HeckeEigensystem.cNorm v ≠ 0 :=
  AutomorphicForm.HeckeEigensystem.cNorm_ne_zero v

example (F : Type) [Field F] [NumberField F] (v₀ : InfinitePlace F)
    (g : Matrix (Fin 2) (Fin 2) v₀.Completion) :
    (NumberField.AdelicLevel.archEval F v₀).mapMatrix
        (NumberField.SiegelVolume.archPiMat F v₀ g) = g :=
  NumberField.SiegelVolume.archEval_mapMatrix_archPiMat_self F v₀ g

-- Zone W11 (TOPIC-rightConv-comm): the isotypic cusp space. Probes across the module's
-- sections: the isotypic predicate and its span (`Isotypic`), the trace/contraction
-- pairing (`Trace`), the isotypic-component algebra (`TypePiece`, where the port needs
-- mathlib's `RepresentationTheory.Basic` for `Representation`), the archimedean cut
-- (`ArchCut`) and the cut trace (`CutTrace`, which composes the `Operators` layer).
example {K : Type} [Field K] [NumberField K] {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : IsIsotypicCuspFormAt K pins ξ N S Φ φ) :
    φ ∈ isotypicCuspSubmodule K pins ξ N S Φ :=
  h.mem_isotypicCuspSubmodule

example (K : Type) [Field K] [NumberField K] (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K pins ξ N S Φ = ⊥ ↔
      ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, IsIsotypicCuspFormAt K pins ξ N S Φ φ → φ = 0 :=
  isotypicCuspSubmodule_eq_bot_iff K pins ξ N S Φ

example {M : Type*} [AddCommGroup M] [Module ℂ M] (V : Submodule ℂ M) (T : M → M)
    (h : IsStableLinearOn V T) : traceOn V T h = LinearMap.trace ℂ V h.toEnd :=
  traceOn_eq V T h

example {H G : Type*} [Group H] [Group G] (ι : H →* G) (χ : H →* ℂˣ) (f : G → ℂ) :
    f ∈ typeSubmodule ι (charRep χ) ↔
      ∀ (k : H) (x : G), f (x * ι k) = ((χ k : ℂˣ) : ℂ) * f x :=
  mem_typeSubmodule_charRep_iff ι χ f

example (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    f ∈ archCutSubmodule F tys ↔
      ∀ w : InfinitePlace F,
        f ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) :=
  mem_archCutSubmodule_iff F tys f

example (K : Type) [Field K] [NumberField K] (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (tys : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    cutTrace K pins ξ N S Ψ tys f hf hfc =
      convTraceOn K (isotypicCuspSubmodule K pins ξ N S Ψ ⊓ archCutSubmodule K tys)
        (continuous_of_mem_isotypicCuspSubmodule_inf K) f hf hfc :=
  cutTrace_eq K pins ξ N S Ψ tys f hf hfc

-- Zone W12 (TOPIC-rightConv-comm): the cuspidal constituent and the archimedean
-- spherical predicate. `CuspidalConstituent` gives the cuspidal subrepresentation
-- datum, its irreducibility predicate and the isotypic-cut meeting condition;
-- `ArchSpherical` gives the archimedean factor together with the level-spherical
-- predicate the twin headlines are stated over.
example (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    CuspidalConstituent.IsCuspSubrep F pins ξ ⊥ :=
  CuspidalConstituent.isCuspSubrep_bot F pins ξ

example (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    ¬ CuspidalConstituent.IsCuspConstituent F pins ξ ⊥ :=
  CuspidalConstituent.not_isCuspConstituent_bot F pins ξ

example {F : Type} [Field F] [NumberField F] {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ}
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (h : CuspidalConstituent.CuspConstituentMeets F pins ξ N S Ψ V) :
    V ⊓ isotypicCuspSubmodule F pins ξ N S Ψ ≠ ⊥ :=
  CuspidalConstituent.inf_isotypicCuspSubmodule_ne_bot_of_cuspConstituentMeets F h

example (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F) :
    IsArchSphericalOfType F tys (fun _ => 0) :=
  isArchSphericalOfType_zero F tys

example (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) :
    IsLevelSphericalOfType F tys U (fun _ => 0) :=
  isLevelSphericalOfType_zero F tys U

example (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLevelSphericalOfType F tys U f ↔
      ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchSphericalOfType F tys fa ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (NumberField.AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((NumberField.AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (NumberField.AdelicLevel.glFin (𝓞 F) F g) :=
  isLevelSphericalOfType_iff' F tys U f

/-! ### Zone P (WORKORDER-P-rightConv-comm, round 2)

The adèlic instantiation of the projected-Haar engine and the three right-convolution
commutation headlines. P1 exercises the generic cut engine on the finite-product frame
`ℂˣ × ℂˣ → ℂˣ`; P2 the adèlic frame's separation, the archimedean measure assembly and
`levelSpherical_eq_cut`; P3 the three headlines executed at `N = ⊤` (`levelOne`), at an
abstract compact carrier `U = O ⊓ finiteAdelicGL2Subgroup F`, and at `principalLevel`.
Every one of the seven round-2 modules is named, so deleting any of them breaks this
zone. -/

-- Zone P1: `ProjectedHaar.convKer_cut_comm` on the finite-product frame
-- `Multiplicative ℝ × Multiplicative ℝ → Multiplicative ℝ` (the additive group of `ℝ`
-- written multiplicatively — `Multiplicative ℝ` carries no `MeasurableSpace` instance of
-- its own, so the two local instances below equip it), with counting measure and the
-- zero cut function. Non-vacuous: the engine is applied with all hypotheses discharged,
-- and the central identity is a real Bochner-integral computation.
private instance : MeasurableSpace (Multiplicative ℝ) := borel _

private instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩

private def prodUnitsFrame :
    ProjectedHaar.Frame (Multiplicative ℝ × Multiplicative ℝ) (Multiplicative ℝ) (Multiplicative ℝ) where
  π := MonoidHom.fst _ _
  πf := MonoidHom.snd _ _
  ι := MonoidHom.inl _ _
  ιf := MonoidHom.inr _ _
  π_ι := fun _ => rfl
  πf_ι := fun _ => rfl
  π_ιf := fun _ => rfl
  πf_ιf := fun _ => rfl
  sep := fun _ _ h₁ h₂ => Prod.ext h₁ h₂

example :
    ProjectedHaar.convKer MeasureTheory.Measure.count
        (ProjectedHaar.cut prodUnitsFrame ⊤ (0 : Multiplicative ℝ → ℂ))
        (1 : Multiplicative ℝ × Multiplicative ℝ → ℂ) =
      ProjectedHaar.convKer MeasureTheory.Measure.count
        (1 : Multiplicative ℝ × Multiplicative ℝ → ℂ)
        (ProjectedHaar.cut prodUnitsFrame ⊤ (0 : Multiplicative ℝ → ℂ)) :=
  ProjectedHaar.convKer_cut_comm prodUnitsFrame MeasureTheory.Measure.count ⊤
    (0 : Multiplicative ℝ → ℂ) (1 : Multiplicative ℝ × Multiplicative ℝ → ℂ)
    continuous_fst (by rw [ProjectedHaar.slab]; exact MeasurableSet.univ) measurable_const
    continuous_const (continuous_id.prodMk continuous_const)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => by
      unfold ProjectedHaar.convKer
      simp)

-- Zone P2: the adèlic frame (`Frame.lean`), its measure assembly
-- (`MeasureAssembly.lean`), the place-class anti-involution (`PlaceClassData.lean`) and
-- the slice centrality surface (`SliceCentrality.lean`).
attribute [local instance] NumberField.AdelicHaar.glBorel MeasureAssembly.archBorel

example (F : Type) [Field F] [NumberField F] {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : AdelicLevel.glArch (𝓞 F) F x = AdelicLevel.glArch (𝓞 F) F y)
    (h₂ : AdelicLevel.glFin (𝓞 F) F x = AdelicLevel.glFin (𝓞 F) F y) : x = y :=
  ProjectedHaar.eq_of_glArch_eq_of_glFin_eq F h₁ h₂

example (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) :
    (productionPinsOf F D (fun N => AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => NumberField.AdelicLevel.heckeGen (𝓞 F) F v) (NumberField.AdelicBox.adelicBox F)).U N
      = AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
  MeasureGlue.pins_U F D (fun v => NumberField.AdelicLevel.heckeGen (𝓞 F) F v)
    (NumberField.AdelicBox.adelicBox F) N

example (F : Type) [Field F] [NumberField F] (U : Subgroup (AdelicGL2 (𝓞 F) F))
    {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsLevelSphericalOfType F tys U f) :
    ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchSphericalOfType F tys fa ∧
      f = ProjectedHaar.cut (ProjectedHaar.adelicFrame F)
        (U.map (ProjectedHaar.adelicFrame F).πf) fa :=
  MeasureAssembly.levelSpherical_eq_cut F U hf

example (F : Type) [Field F] [NumberField F] (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)))) :
    (MeasureAssembly.archNu F U).IsMulRightInvariant :=
  MeasureAssembly.archNu_isMulRightInvariant F U hUo

example (F : Type) [Field F] [NumberField F] (x : GL (Fin 2) (InfiniteAdeleRing F)) :
    (PlaceClassData.archAntiInvolution F).θ x = PlaceClassData.thetaArch F x :=
  PlaceClassData.archAntiInvolution_θ F x

example (F : Type) [Field F] [NumberField F] (ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    ψ ∈ SliceCentrality.contSubmodule F ↔ Continuous ψ :=
  SliceCentrality.mem_contSubmodule_iff F ψ

-- Zone P3: the three headlines, executed at `N = ⊤`, at an abstract compact `U`, and at
-- `principalLevel`. The archimedean data `τ`/`hirr` stay parameters; the substance is
-- the landed `isLevelSphericalOfType_zero`, `isFactorizableTestFn_zero`,
-- `isArchBiFinite_zero` with `φ := 0`, `h := 0`, `f := 0`.
example (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (hN : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible) :
    rightConv F (rightConv F (0 : AdelicGL2 (𝓞 F) F → ℂ) 0) 0 =
      rightConv F (rightConv F 0 0) 0 :=
  AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType F D ⊤ hN τ hirr
    (0 : AdelicGL2 (𝓞 F) F → ℂ)
    (isLevelSphericalOfType_zero F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) _)
    (0 : AdelicGL2 (𝓞 F) F → ℂ) (isFactorizableTestFn_zero F)
    (isArchBiFinite_zero F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F))
    (fun _ _ _ => ⟨rfl, rfl⟩) (0 : AdelicGL2 (𝓞 F) F → ℂ) continuous_zero

example (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible) :
    rightConv F (rightConv F (0 : AdelicGL2 (𝓞 F) F → ℂ) 0) 0 =
      rightConv F (rightConv F 0 0) 0 :=
  AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact F U hU O hO hUO
    τ hirr (0 : AdelicGL2 (𝓞 F) F → ℂ)
    (isLevelSphericalOfType_zero F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) U)
    (0 : AdelicGL2 (𝓞 F) F → ℂ) (isFactorizableTestFn_zero F)
    (isArchBiFinite_zero F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F))
    (fun _ _ _ => ⟨rfl, rfl⟩) (0 : AdelicGL2 (𝓞 F) F → ℂ) continuous_zero

example (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (hN : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible) :
    rightConv F (rightConv F (0 : AdelicGL2 (𝓞 F) F → ℂ) 0) 0 =
      rightConv F (rightConv F 0 0) 0 :=
  AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_principal F D ⊤ hN τ hirr
    (0 : AdelicGL2 (𝓞 F) F → ℂ)
    (isLevelSphericalOfType_zero F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) _)
    (0 : AdelicGL2 (𝓞 F) F → ℂ) (isFactorizableTestFn_zero F)
    (isArchBiFinite_zero F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F))
    (fun _ _ _ => ⟨rfl, rfl⟩) (0 : AdelicGL2 (𝓞 F) F → ℂ) continuous_zero

-- Zone Q-D0: the archimedean Borel σ-algebra `glBorelOf` at an abstract topological ring,
-- and Haar measure `archHaarK` on `GL₂(𝔸_{F,∞})` (the definition gate).
example (R : Type) [CommRing R] [TopologicalSpace R] :
    @BorelSpace (GL (Fin 2) R) _ (glBorelOf R) :=
  borelSpace_glBorelOf R

example (F : Type) [Field F] [NumberField F] : (archHaarK F).IsHaarMeasure :=
  Q09.isHaarMeasure_archHaarK F

-- Zone Q-Q1: the adèlic infrastructure — the product Haar `muK` on the row-isometry
-- product is a probability measure.
example (F : Type) [Field F] [NumberField F] : Q09AIarch.muK F Set.univ = 1 :=
  Q09AIarch.muK_univ F

-- Zone Q-Q2: the entry map and the ball/bump layer — `archEntries` is the matrix-entry
-- embedding, and the approximate identity exists in the archimedean factor.
example (F : Type) [Field F] [NumberField F] (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F g =
      Q09AIarchG.matrixEntries F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  Q09AIarchG.archEntries_eq F g

example (F : Type) [Field F] [NumberField F] [(archHaarK F).IsHaarMeasure] :
    ∃ ψ : ℕ → GL (Fin 2) (InfiniteAdeleRing F) → ℝ,
      (∀ n, IsArchTestFactor F (fun g => (ψ n g : ℂ)) ∧ Continuous (ψ n) ∧
        HasCompactSupport (ψ n) ∧ (∀ g, 0 ≤ ψ n g) ∧ (∫ g, ψ n g ∂archHaarK F) = 1) ∧
      ∀ U ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∀ᶠ n in Filter.atTop, tsupport (ψ n) ⊆ U :=
  Q09AIarchG.exists_approxIdentity F

-- Zone Q-Q3: the generic type reproducer — the product representation acts componentwise.
example {H A : Type} [Group H] {W : A → Type} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]
    (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    Q09.piRep ρ k v a = ρ a k (v a) :=
  Q09.piRep_apply ρ k v a

-- Zone Q-Q4: the generic double-convolution engine — the continuous functions form a
-- submodule of all functions.
example {X : Type} [TopologicalSpace X] {u : X → ℂ} :
    u ∈ Q09.contSubmodule X ↔ Continuous u :=
  Q09.mem_contSubmodule

-- Zone Q-Q6: the headline, executed at the zero function and a concrete `tys` built from
-- abstract archimedean representations. The zone forces the façade and the whole
-- `ArchApproxIdentity/Instantiate.lean` engine beneath it.
example (F : Type) [Field F] [NumberField F] (τ : ∀ w : InfinitePlace F, ArchRepAt F w) :
    ∃ fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      (∀ n, IsArchTestFactor F (fa n) ∧
        IsArchFactorBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) (fa n)) ∧
      ∀ g, Filter.Tendsto
        (fun n => letI := glBorelOf (InfiniteAdeleRing F)
          ∫ y, (0 : AdelicGL2 (𝓞 F) F → ℂ) (g * adelicArchGLIncl F y) * fa n y ∂(archHaarK F))
        Filter.atTop (nhds ((0 : AdelicGL2 (𝓞 F) F → ℂ) g)) :=
  exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule F
    (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) (0 : AdelicGL2 (𝓞 F) F → ℂ)
    continuous_zero (Submodule.zero_mem (archCutSubmodule F ⟨fun _ => 1, fun w _ => τ w⟩))

-- The pin's adèlic Borel structure is a local instance: the R zones' measure types
-- (`Measure (AdeleRing …)`, `adelicAddHaar`) are elaborated against it.
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

-- Zone R1 (WORKORDER-R turn 1): the generic `S4Base` base — the place measures and
-- the distributive-character product formula (`M4aS4`, `NumberField.AdeleRing`).
example {c : ℝ} (hc : c ≠ 0) :
    (volume : Measure ℝ).map (fun x => c * x) = ‖c‖ₑ⁻¹ • volume :=
  M4aS4.map_mul_left_volume_real hc

example (F : Type) [Field F] [NumberField F]
    (a : (AdeleRing (𝓞 F) F)ˣ) (ha : (a : AdeleRing (𝓞 F) F).2 = 1) :
    (distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) =
      ∏ w : InfinitePlace F, ‖(a : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult :=
  NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one_impl F a ha

-- Zone R2 (WORKORDER-R turn 1): the coset transversal (`Coset`), the transfer algebra
-- (`Transfer`) and the entry-box bound (`BoxBounds`).
example (F : Type) [Field F] [NumberField F] {S : Set (InfiniteAdeleRing F)}
    {T : Set (FiniteAdeleRing (𝓞 F) F)} {x : AdeleRing (𝓞 F) F} :
    x ∈ WeylIntegrable.slab F S T ↔ x.1 ∈ S ∧ x.2 ∈ T :=
  WeylIntegrable.mem_slab F

example (F : Type) [Field F] [NumberField F] (μ : Measure (AdeleRing (𝓞 F) F))
    [μ.IsAddLeftInvariant] {S : Set (InfiniteAdeleRing F)} (hS : IsClosed S)
    (A B : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) (hAB : A ≤ B)
    (hA : IsClosed (A : Set (FiniteAdeleRing (𝓞 F) F))) (hfin : A.relIndex B ≠ 0) :
    μ (WeylIntegrable.slab F S B) = A.relIndex B * μ (WeylIntegrable.slab F S A) :=
  WeylIntegrable.measure_slab_eq_relIndex_mul F μ hS A B hAB hA hfin

example (F : Type) [Field F] [NumberField F] (a : InfiniteAdeleRing F)
    (b : FiniteAdeleRing (𝓞 F) F) :
    WeylIntegrable.mFactor F a b ∈ WeylIntegrable.unitBox (WeylIntegrable.entrySet F) :=
  WeylIntegrable.mFactor_mem_unitBox F a b

-- Zone R3 (WORKORDER-R turn 2): the estimates (`LatticeEstimates`), the assembly
-- (`Assembly`) and the uniform bound (`UniformBound`), plus the continuous cap
-- `RhSContinuity.rhs_hole` (`Caps`).
example {G : Type*} [Group G] (α : G →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) {e : G} (he : e * e = 1) :
    ((α e : ℝˣ) : ℝ) = 1 :=
  WeylIntegrable.val_eq_one_of_mul_self_eq_one α hα he

example (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, Filter.Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, WeylIntegrable.idealCount F k) / n)
      Filter.atTop (nhds C) :=
  WeylIntegrable.tendsto_sum_idealCount_div F

example (F : Type) [Field F] [NumberField F] (x : AdeleRing (𝓞 F) F) :
    0 < WeylIntegrable.Dy F x :=
  WeylIntegrable.Dy_pos F x

example (F : Type) [Field F] [NumberField F] (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hαΔ : ∀ x, ((α x : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (s : ℂ)
    (hs : 1 / 2 < s.re)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) :
    Continuous (fun g : AdelicGL2 (𝓞 F) F => ∑' ξ : F, (0 : AdelicGL2 (𝓞 F) F → ℂ)
      (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) :=
  AutomorphicForm.RhSContinuity.rhs_hole F α hαΔ hα μ ν hμ hν s hs
    (0 : AdelicGL2 (𝓞 F) F → ℂ) (isInducedSection_zero _ _) continuous_zero

-- The pin's `α` for the Bruhat-transversal trio (the headline's `let`) — spelled once
-- so the distributive Haar character's implicit group is pinned.
abbrev bruhatAlpha (F : Type) [Field F] [NumberField F] : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
    (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

-- Zone R4 (WORKORDER-R turn 2): the three façade headlines, executed at the zero
-- section `φ := 0` (`isInducedSection_zero`), the identity group element `g := 1`,
-- and abstract unitary characters; the `let`-bound `α`/`hα` are the headline's own.
-- Deleting any of `LatticeEstimates`/`Assembly`/`UniformBound`/`Caps` or the façade
-- breaks this zone.
example (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (s : ℂ)
    (hs : 1 / 2 < s.re)
    (hα : ∀ x, 0 < ((bruhatAlpha F x : ℝˣ) : ℝ)) :
    Summable (fun ξ : F => ‖(0 : AdelicGL2 (𝓞 F) F → ℂ)
      (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * 1)‖) :=
  bruhatTransversal_summand_norm_summable_of_re_gt_half F hα μ ν hμ hν s hs
    (0 : AdelicGL2 (𝓞 F) F → ℂ) (isInducedSection_zero _ _) continuous_zero 1

example (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (s : ℂ)
    (hs : 1 / 2 < s.re)
    (hα : ∀ x, 0 < ((bruhatAlpha F x : ℝˣ) : ℝ)) :
    Continuous (fun g : AdelicGL2 (𝓞 F) F => ∑' ξ : F, (0 : AdelicGL2 (𝓞 F) F → ℂ)
      (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) :=
  continuous_bruhatTransversal_tsum_of_re_gt_half F hα μ ν hμ hν s hs
    (0 : AdelicGL2 (𝓞 F) F → ℂ) (isInducedSection_zero _ _) continuous_zero

example (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (s : ℂ)
    (hs : 1 / 2 < s.re) (g : AdelicGL2 (𝓞 F) F)
    (hα : ∀ x, 0 < ((bruhatAlpha F x : ℝˣ) : ℝ)) :
    letI := adeleBorel (𝓞 F) F
    Integrable (fun x : AdeleRing (𝓞 F) F =>
      (0 : AdelicGL2 (𝓞 F) F → ℂ) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g))
      (adelicAddHaar (𝓞 F) F) :=
  weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν s hs
    (0 : AdelicGL2 (𝓞 F) F → ℂ) (isInducedSection_zero _ _) continuous_zero g

end AutomorphicFormConsumer

end
