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
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm Matrix MeasureTheory

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

end AutomorphicFormConsumer

end
