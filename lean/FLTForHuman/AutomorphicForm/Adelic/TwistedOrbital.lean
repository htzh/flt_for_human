/-
  Twisted orbital integrals and the semi-local unit-factorizable tiers.

  This is the whole pin node `Definitions/Def_AutomorphicForm_TwistedOrbital.lean`
  (pinned `aa2d8b3`, 574 lines / 83 declarations), transcribed at the pin's names in
  namespace `AutomorphicForm`: the base-change carrier instances on
  `L ⊗[K] A`, the semi-local integers `semiLocalIntegers` and integral set
  `semiLocalIntegralSet` with their Haar measure, the `σ`-twisted conjugation
  `sigmaGL`/`normString`/`IsSigmaConjugate`/`twistedCentralizer`, the untwisted and
  twisted orbital integrals, the matching conditions `AreMatchingOn`/
  `AreMatchingLocal`/`AreMatchingArch`/`AreMatchingAt`, and the semi-local
  unit-factorizable tiers `IsSemiLocalFactorization`, `IsUnitFactorizableAbove` and
  `IsUnitFactorizableAboveOfType` (the trio's definition gate).

  Three declarations of this pin node are already landed in
  `AutomorphicForm/Adelic/ArchHaar.lean` and are imported, not re-declared:
  `glBorelOf` (pin `:57`), `borelSpace_glBorelOf` (pin `:59`) and `archHaarK`
  (pin `:401`).

  ## Substitutions against mathlib `v4.34.0`

  | pin declaration | mathlib `v4.34.0` | action |
  |---|---|---|
  | `IsModuleTopology.Module.topologicalRing` | `IsModuleTopology.isTopologicalRing` | substituted in `isTopologicalRing_tensor` |
  | `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` | substituted where used in proofs |
  | `glBorelOf`, `borelSpace_glBorelOf`, `archHaarK` | landed in `Adelic/ArchHaar.lean` | imported |
  | `IsArchTestFactor`, `IsFinTestFactor`, `IsFactorizableTestFn` | landed in `Adelic/FactorizableTestFn.lean` | imported |
  | `IsArchBiFinite`, `ArchTypeFamily`, `IsArchFactorBiFinite` | landed in `Adelic/IsotypicCuspSpace.lean` | imported |
  | `HeightOneSpectrum.tensorAdicCompletionIntegersTo` | landed in `RingTheory/DedekindDomain/CompletionBaseChange.lean` | imported, used by `semiLocalIntegers` |
  | `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv` | landed in `RingTheory/DedekindDomain/CompletionBaseChange.lean` | imported, used by `semiLocalEval` |
  | `HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv`, `baseChange`, `baseChange_bijective`, `range_baseChange_comp_tensorAdicCompletionTo_eq_pi` | landed in `RingTheory/DedekindDomain/CompletionBaseChange.lean` | imported, used by `semiLocalHomeomorph`/`semiLocalIntegers_eq_preimage` |
  | `HeightOneSpectrum.Extension.finite` | landed in `RingTheory/DedekindDomain/IntegralClosure.lean` | imported |
  | `sigmaCentralizer` | landed in `Adelic/SigmaCentralizer.lean` | imported, used by `twistedCentralizer` |
  | `M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData` | landed in `NumberTheory/NumberField/IdeleClass/ArchSemilocal.lean` | imported, used by `archIdent` |

  The pin's bare `import Mathlib` is replaced by the explicit imports below.  Where the
  pin uses the `letI`/`haveI` tactics in a proof whose goal is a proposition, this port
  uses `let`/`have` (which also register local instances), to satisfy the `v4.34.0`
  `haveILetI` linter.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchHaar
import FLTForHuman.AutomorphicForm.Adelic.SigmaCentralizer
import FLTForHuman.AutomorphicForm.Adelic.UnitFactorizableOfType
import FLTForHuman.NumberTheory.NumberField.IdeleClass.ArchSemilocal
import FLTForHuman.RingTheory.DedekindDomain.CompletionBaseChange

set_option autoImplicit false


open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm

section Carrier

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

-- pin: isTopologicalRing_tensor (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:20)
theorem isTopologicalRing_tensor : IsTopologicalRing (L ⊗[K] A) :=
  IsModuleTopology.isTopologicalRing A (L ⊗[K] A)

-- pin: t2Space_tensor (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:23)
theorem t2Space_tensor [T2Space A] : T2Space (L ⊗[K] A) :=
  IsModuleTopology.t2Space A

-- pin: locallyCompactSpace_tensor (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:26)
theorem locallyCompactSpace_tensor [LocallyCompactSpace A] : LocallyCompactSpace (L ⊗[K] A) :=
  IsModuleTopology.locallyCompactSpaceOfFinite A (M := L ⊗[K] A)

-- pin: isTopologicalGroup_tensorGL (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:29)
theorem isTopologicalGroup_tensorGL : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := by
  have h := isTopologicalRing_tensor K L A
  infer_instance

-- pin: t2Space_tensorGL (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:33)
theorem t2Space_tensorGL [T2Space A] : T2Space (GL (Fin 2) (L ⊗[K] A)) := by
  have h1 := isTopologicalRing_tensor K L A
  have h2 := t2Space_tensor K L A
  have h3 : T2Space (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] A))
  exact Units.isEmbedding_embedProduct.t2Space

-- pin: locallyCompactSpace_tensorGL (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:40)
theorem locallyCompactSpace_tensorGL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) (L ⊗[K] A)) := by
  have h1 := isTopologicalRing_tensor K L A
  have h2 := t2Space_tensor K L A
  have h3 := locallyCompactSpace_tensor K L A
  have h4 : T2Space (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] A))
  have h5 : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → L ⊗[K] A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Carrier

section Borel

variable (R : Type) [CommRing R] [TopologicalSpace R]

-- pin: centralizerBorel (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:62)
@[reducible] def centralizerBorel (γ : GL (Fin 2) R) :
    MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) R))) := borel _

end Borel

section Embed

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

-- pin: toTensorGL (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:71)
def toTensorGL : GL (Fin 2) A →* GL (Fin 2) (L ⊗[K] A) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom

end Embed

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

-- pin: semiLocalHomeomorph (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:81)
def semiLocalHomeomorph :
    L ⊗[K] v.adicCompletion K ≃ₜ Π w : v.Extension (𝓞 L), w.1.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L)
    v).toContinuousLinearEquiv.toHomeomorph

-- pin: piIntegers (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:86)
def piIntegers : Set (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  Set.univ.pi fun w => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))

-- pin: isCompact_piIntegers (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:89)
theorem isCompact_piIntegers : IsCompact (piIntegers K L v) :=
  isCompact_univ_pi fun w =>
    isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 L) L w.1)

-- pin: isOpen_piIntegers (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:93)
theorem isOpen_piIntegers : IsOpen (piIntegers K L v) := by
  have h := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  exact isOpen_set_pi Set.finite_univ fun w _ =>
    (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 L) L).out w.1

-- pin: semiLocalIntegers (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:98)
def semiLocalIntegers : Set (L ⊗[K] v.adicCompletion K) :=
  Set.range (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v)

-- pin: semiLocalIntegers_eq_preimage (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:101)
theorem semiLocalIntegers_eq_preimage :
    semiLocalIntegers K L v = semiLocalHomeomorph K L v ⁻¹' piIntegers K L v := by
  have h := HeightOneSpectrum.range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L (𝓞 L) v
  rw [Set.range_comp] at h
  have hinj : Function.Injective (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v) :=
    (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v).1
  calc semiLocalIntegers K L v
      = HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ⁻¹'
          (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v '' semiLocalIntegers K L v) :=
        (Set.preimage_image_eq _ hinj).symm
    _ = semiLocalHomeomorph K L v ⁻¹' piIntegers K L v := by
        rw [semiLocalIntegers, h]; rfl

-- pin: isCompact_semiLocalIntegers (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:114)
theorem isCompact_semiLocalIntegers : IsCompact (semiLocalIntegers K L v) := by
  rw [semiLocalIntegers_eq_preimage]
  exact (semiLocalHomeomorph K L v).isCompact_preimage.2 (isCompact_piIntegers K L v)

-- pin: isOpen_semiLocalIntegers (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:118)
theorem isOpen_semiLocalIntegers : IsOpen (semiLocalIntegers K L v) := by
  rw [semiLocalIntegers_eq_preimage]
  exact (isOpen_piIntegers K L v).preimage (semiLocalHomeomorph K L v).continuous

-- pin: zero_mem_semiLocalIntegers (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:123)
omit [NumberField L] in
theorem zero_mem_semiLocalIntegers : (0 : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v :=
  ⟨0, map_zero _⟩

-- pin: one_mem_semiLocalIntegers (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:127)
omit [NumberField L] in
theorem one_mem_semiLocalIntegers : (1 : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v :=
  ⟨1, map_one _⟩

-- pin: IsSemiLocalTestFn (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:130)
def IsSemiLocalTestFn (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) : Prop :=
  IsLocallyConstant φv ∧ HasCompactSupport φv

-- pin: isSemiLocalTestFn_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:133)
theorem isSemiLocalTestFn_zero : IsSemiLocalTestFn K L v (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

-- pin: semiLocalIntegralSet (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:136)
def semiLocalIntegralSet : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  integralUnitsSet (semiLocalIntegers K L v)

-- pin: one_mem_semiLocalIntegralSet (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:140)
omit [NumberField L] in
theorem one_mem_semiLocalIntegralSet :
    (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ semiLocalIntegralSet K L v :=
  one_mem_integralUnitsSet (zero_mem_semiLocalIntegers K L v) (one_mem_semiLocalIntegers K L v)

-- pin: isCompact_semiLocalIntegralSet (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:144)
theorem isCompact_semiLocalIntegralSet : IsCompact (semiLocalIntegralSet K L v) := by
  have h1 := isTopologicalRing_tensor K L (v.adicCompletion K)
  have h2 := t2Space_tensor K L (v.adicCompletion K)
  exact isCompact_integralUnitsSet (isCompact_semiLocalIntegers K L v)

-- pin: isOpen_semiLocalIntegralSet (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:149)
theorem isOpen_semiLocalIntegralSet : IsOpen (semiLocalIntegralSet K L v) := by
  have h1 := isTopologicalRing_tensor K L (v.adicCompletion K)
  have h2 := t2Space_tensor K L (v.adicCompletion K)
  exact isOpen_integralUnitsSet (isOpen_semiLocalIntegers K L v)

-- pin: semiLocalIntegralCompacts (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:154)
def semiLocalIntegralCompacts : PositiveCompacts (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) where
  carrier := semiLocalIntegralSet K L v
  isCompact' := isCompact_semiLocalIntegralSet K L v
  interior_nonempty' := by
    rw [(isOpen_semiLocalIntegralSet K L v).interior_eq]
    exact ⟨1, one_mem_semiLocalIntegralSet K L v⟩

-- pin: isSemiLocalTestFn_indicator_semiLocalIntegralSet (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:161)
theorem isSemiLocalTestFn_indicator_semiLocalIntegralSet :
    IsSemiLocalTestFn K L v ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) := by
  have h1 := t2Space_tensorGL K L (v.adicCompletion K)
  have h2 : R1Space (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := T2Space.r1Space
  exact ⟨isLocallyConstant_indicator_one (isOpen_semiLocalIntegralSet K L v)
      (isCompact_semiLocalIntegralSet K L v).isClosed,
    HasCompactSupport.intro (isCompact_semiLocalIntegralSet K L v) fun _ hg => by simp [hg]⟩

-- pin: semiLocalHaar (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:169)
def semiLocalHaar :
    @Measure (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (glBorelOf (L ⊗[K] v.adicCompletion K)) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  exact Measure.haarMeasure (semiLocalIntegralCompacts K L v)

-- pin: isHaarMeasure_semiLocalHaar (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:176)
theorem isHaarMeasure_semiLocalHaar :
    @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) _ _
      (glBorelOf (L ⊗[K] v.adicCompletion K)) (semiLocalHaar K L v) := by
  let ms := glBorelOf (L ⊗[K] v.adicCompletion K)
  have hbs := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  have htg := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  have hlc := locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  exact Measure.isHaarMeasure_haarMeasure _

-- pin: semiLocalHaar_semiLocalIntegralSet (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:185)
theorem semiLocalHaar_semiLocalIntegralSet :
    semiLocalHaar K L v (semiLocalIntegralSet K L v) = 1 := by
  let ms := glBorelOf (L ⊗[K] v.adicCompletion K)
  have hbs := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  have htg := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  exact Measure.haarMeasure_self

end SemiLocal

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

-- pin: sigmaTensor (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:199)
def sigmaTensor : L ⊗[K] A →+* L ⊗[K] A :=
  (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)).toRingHom

-- pin: sigmaGL (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:202)
def sigmaGL : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] A) :=
  Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ)

-- pin: normString (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:205)
def normString (δ : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range (Module.finrank K L)).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod

-- pin: IsSigmaConjugate (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:208)
def IsSigmaConjugate (δ δ' : GL (Fin 2) (L ⊗[K] A)) : Prop :=
  ∃ x : GL (Fin 2) (L ⊗[K] A), δ' = x⁻¹ * δ * sigmaGL K L A σ x

-- pin: isSigmaConjugate_self (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:211)
theorem isSigmaConjugate_self (δ : GL (Fin 2) (L ⊗[K] A)) : IsSigmaConjugate K L A σ δ δ :=
  ⟨1, by simp⟩

-- pin: IsNormConjugator (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:214)
def IsNormConjugator (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A)) : Prop :=
  toTensorGL K L A γ = y⁻¹ * normString K L A σ δ * y

-- pin: IsNormOf (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:217)
def IsNormOf (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A)) : Prop :=
  ∃ y, IsNormConjugator K L A σ γ δ y

-- pin: twistedCentralizer (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:220)
abbrev twistedCentralizer (δ : GL (Fin 2) (L ⊗[K] A)) : Subgroup (GL (Fin 2) (L ⊗[K] A)) :=
  sigmaCentralizer (sigmaGL K L A σ) δ

end Twist

section TwistedBorel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

-- pin: twistedCentralizerBorel (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:230)
@[reducible] def twistedCentralizerBorel (δ : GL (Fin 2) (L ⊗[K] A)) :
    MeasurableSpace (twistedCentralizer K L A σ δ) := borel _

end TwistedBorel

section Untwisted

variable (A : Type) [CommRing A] [TopologicalSpace A]

-- pin: IsSectionFnOn (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:239)
def IsSectionFnOn (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (f : GL (Fin 2) A → ℂ) (w : GL (Fin 2) A → ℝ) : Prop :=
  letI := glBorelOf A
  letI := centralizerBorel A γ
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, f (x⁻¹ * γ * x) ≠ 0 →
      ∫ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), w (t * x) ∂τ = 1

-- pin: IsOrbitalIntegralOn (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:248)
def IsOrbitalIntegralOn (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (f : GL (Fin 2) A → ℂ) (I : ℂ) : Prop :=
  letI := glBorelOf A
  ∃ w : GL (Fin 2) A → ℝ, IsSectionFnOn A γ τ f w ∧ I = ∫ x, f (x⁻¹ * γ * x) * (w x : ℂ) ∂μ

-- pin: isSectionFnOn_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:254)
theorem isSectionFnOn_zero (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    IsSectionFnOn A γ τ (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩

-- pin: isOrbitalIntegralOn_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:259)
theorem isOrbitalIntegralOn_zero (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    IsOrbitalIntegralOn A μ γ τ (fun _ => 0) 0 :=
  ⟨fun _ => 0, isSectionFnOn_zero A γ τ, by simp⟩

-- pin: not_isOrbitalIntegralOn_zero_one (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:264)
theorem not_isOrbitalIntegralOn_zero_one (μ : @Measure (GL (Fin 2) A) (glBorelOf A))
    (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    ¬ IsOrbitalIntegralOn A μ γ τ (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h

end Untwisted

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

-- pin: IsTwistedSectionFnOn (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:278)
def IsTwistedSectionFnOn (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (w : GL (Fin 2) (L ⊗[K] A) → ℝ) : Prop :=
  letI := glBorelOf (L ⊗[K] A)
  letI := twistedCentralizerBorel K L A σ δ
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) ≠ 0 →
      ∫ t : twistedCentralizer K L A σ δ, w (t * x) ∂τ' = 1

-- pin: IsTwistedOrbitalIntegralOn (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:287)
def IsTwistedOrbitalIntegralOn (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I' : ℂ) : Prop :=
  letI := glBorelOf (L ⊗[K] A)
  ∃ w : GL (Fin 2) (L ⊗[K] A) → ℝ, IsTwistedSectionFnOn K L A σ δ τ' φ w ∧
    I' = ∫ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) * (w x : ℂ) ∂μ

-- pin: isTwistedSectionFnOn_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:295)
theorem isTwistedSectionFnOn_zero (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    IsTwistedSectionFnOn K L A σ δ τ' (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩

-- pin: isTwistedOrbitalIntegralOn_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:300)
theorem isTwistedOrbitalIntegralOn_zero (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    IsTwistedOrbitalIntegralOn K L A σ μ δ τ' (fun _ => 0) 0 :=
  ⟨fun _ => 0, isTwistedSectionFnOn_zero K L A σ δ τ', by simp⟩

-- pin: not_isTwistedOrbitalIntegralOn_zero_one (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:306)
theorem not_isTwistedOrbitalIntegralOn_zero_one
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    ¬ IsTwistedOrbitalIntegralOn K L A σ μ δ τ' (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h

-- pin: Coupled (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:313)
def Coupled (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) : Prop :=
  letI := glBorelOf (L ⊗[K] A)
  letI := centralizerBorel A γ
  letI := twistedCentralizerBorel K L A σ δ
  Measure.map (fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y) τ' =
    Measure.map
      (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => toTensorGL K L A (t : GL (Fin 2) A))
      τ

-- pin: AreMatchingOn (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:324)
def AreMatchingOn (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (μK : @Measure (GL (Fin 2) A) (glBorelOf A))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (f : GL (Fin 2) A → ℂ) : Prop :=
  (∀ δ : GL (Fin 2) (L ⊗[K] A), IsRegularSemisimple (normString K L A σ δ) →
    ∀ γ : GL (Fin 2) A, IsRegularSemisimple γ →
    ∀ y : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ y →
    ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
      (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ →
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ' →
      Coupled K L A σ γ δ y τ τ' →
      ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L A σ μL δ τ' φ I' →
        IsOrbitalIntegralOn A μK γ τ f I → I' = I) ∧
  (∀ γ : GL (Fin 2) A, IsRegularSemisimple γ → (¬ ∃ δ, IsNormOf K L A σ γ δ) →
    ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ →
      ∀ I : ℂ, IsOrbitalIntegralOn A μK γ τ f I → I = 0)

-- pin: areMatchingOn_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:342)
theorem areMatchingOn_zero (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (μK : @Measure (GL (Fin 2) A) (glBorelOf A)) :
    AreMatchingOn K L A σ μL μK (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun δ _ γ _ y _ τ τ' _ _ _ I I' hI' hI => ?_, fun γ _ _ τ _ I hI => ?_⟩
  · obtain ⟨w', -, rfl⟩ := hI'
    obtain ⟨w, -, rfl⟩ := hI
    simp
  · obtain ⟨w, -, rfl⟩ := hI
    simp

end Twisted

section FinitePlaces

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

-- pin: isOrbitalIntegralOn_localHaar_iff (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:359)
theorem isOrbitalIntegralOn_localHaar_iff (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ) :
    IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ fv I ↔
      IsOrbitalIntegral K v γ τ fv I :=
  Iff.rfl

-- pin: IsTwistedOrbitalIntegral (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:366)
def IsTwistedOrbitalIntegral (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (I' : ℂ) : Prop :=
  IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φv I'

-- pin: isTwistedOrbitalIntegral_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:372)
theorem isTwistedOrbitalIntegral_zero (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)) :
    IsTwistedOrbitalIntegral K L v σ δ τ' (fun _ => 0) 0 := by
  unfold IsTwistedOrbitalIntegral
  exact isTwistedOrbitalIntegralOn_zero K L _ σ _ δ τ'

-- pin: not_isTwistedOrbitalIntegral_zero_one (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:379)
theorem not_isTwistedOrbitalIntegral_zero_one (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)) :
    ¬ IsTwistedOrbitalIntegral K L v σ δ τ' (fun _ => 0) 1 := by
  unfold IsTwistedOrbitalIntegral
  exact not_isTwistedOrbitalIntegralOn_zero_one K L _ σ _ δ τ'

-- pin: AreMatchingLocal (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:386)
def AreMatchingLocal (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  AreMatchingOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) (localHaar K v) φv fv

-- pin: areMatchingLocal_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:390)
theorem areMatchingLocal_zero : AreMatchingLocal K L v σ (fun _ => 0) (fun _ => 0) := by
  unfold AreMatchingLocal
  exact areMatchingOn_zero K L _ σ _ _

end FinitePlaces

section Archimedean

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L)

-- pin: archHaarL (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:412)
def archHaarL :
    @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (glBorelOf (L ⊗[K] InfiniteAdeleRing K)) := by
  letI := glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
  exact Measure.haar

-- pin: archIdent (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:420)
def archIdent : L ⊗[K] InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)).toRingEquiv.toRingHom

-- pin: archIdentGL (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:424)
def archIdentGL : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) →* GL (Fin 2) (InfiniteAdeleRing L) :=
  Matrix.GeneralLinearGroup.map (archIdent K L)

-- pin: AreMatchingArch (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:427)
def AreMatchingArch (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) : Prop :=
  AreMatchingOn K L (InfiniteAdeleRing K) σ (archHaarL K L) (archHaarK K) (φa ∘ archIdentGL K L) fa

-- pin: areMatchingArch_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:431)
theorem areMatchingArch_zero : AreMatchingArch K L σ (fun _ => 0) (fun _ => 0) := by
  unfold AreMatchingArch
  exact areMatchingOn_zero K L _ σ _ _

end Archimedean

section AboveTier

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

-- pin: semiLocalEval (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:441)
def semiLocalEval (v : HeightOneSpectrum (𝓞 K)) :
    FiniteAdeleRing (𝓞 L) L →+* L ⊗[K] v.adicCompletion K :=
  (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm.toRingEquiv.toRingHom.comp
    (RingHom.pi fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1)

-- pin: semiLocalComponent (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:446)
def semiLocalComponent (v : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) →* GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (semiLocalEval K L v)

variable (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L))) (S : Finset (HeightOneSpectrum (𝓞 K)))

-- pin: IsSemiLocalFactorization (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:452)
def IsSemiLocalFactorization (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) : Prop :=
  IsArchTestFactor L φa ∧ IsFinTestFactor L φf ∧ (∀ v ∈ S, IsSemiLocalTestFn K L v (φS v)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
    (∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) →
      φf h = ∏ v ∈ S, φS v (semiLocalComponent K L v h)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
    (∃ v ∉ S, semiLocalComponent K L v h ∉ semiLocalIntegralSet K L v) → φf h = 0) ∧
  ∀ g, φ g = φa (AdelicLevel.glArch (𝓞 L) L g) * φf (AdelicLevel.glFin (𝓞 L) L g)

-- pin: IsUnitFactorizableAbove (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:463)
def IsUnitFactorizableAbove (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) : Prop :=
  IsBiInvariantUnder L U φ ∧ ∃ φa φf φS, IsSemiLocalFactorization K L S φ φa φf φS

-- pin: IsUnitFactorizableAbove.mono (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:466)
theorem IsUnitFactorizableAbove.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L))} (hUV : U ≤ V)
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAbove K L V S φ) :
    IsUnitFactorizableAbove K L U S φ :=
  ⟨hφ.1.mono L hUV, hφ.2⟩

-- pin: isSemiLocalFactorization_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:471)
theorem isSemiLocalFactorization_zero (hS : S.Nonempty) :
    IsSemiLocalFactorization K L S (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) := by
  obtain ⟨v₀, hv₀⟩ := hS
  refine ⟨isArchTestFactor_zero L, isFinTestFactor_zero L, fun v _ => isSemiLocalTestFn_zero K L v,
    fun h _ => ?_, fun _ _ => rfl, fun _ => by simp⟩
  exact (Finset.prod_eq_zero hv₀ rfl).symm

-- pin: isUnitFactorizableAbove_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:478)
theorem isUnitFactorizableAbove_zero (hS : S.Nonempty) : IsUnitFactorizableAbove K L U S (fun _ => 0) :=
  ⟨fun _ _ _ => ⟨rfl, rfl⟩, _, _, _, isSemiLocalFactorization_zero K L S hS⟩

end AboveTier

section AboveTierRefined

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (tys : ArchTypeFamily L) (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L)))
  (S : Finset (HeightOneSpectrum (𝓞 K)))

-- pin: IsUnitFactorizableAboveOfType (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:489)
def IsUnitFactorizableAboveOfType (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) : Prop :=
  IsUnitFactorizableAbove K L U S φ ∧ IsArchBiFinite L tys φ

variable {K L tys U S}

-- pin: IsUnitFactorizableAboveOfType.isUnitFactorizableAbove (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:494)
theorem IsUnitFactorizableAboveOfType.isUnitFactorizableAbove
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) :
    IsUnitFactorizableAbove K L U S φ :=
  hφ.1

-- pin: IsUnitFactorizableAboveOfType.isArchBiFinite (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:499)
theorem IsUnitFactorizableAboveOfType.isArchBiFinite
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) :
    IsArchBiFinite L tys φ :=
  hφ.2

-- pin: IsUnitFactorizableAboveOfType.mono (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:504)
theorem IsUnitFactorizableAboveOfType.mono {V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L))}
    (hUV : U ≤ V) {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys V S φ) : IsUnitFactorizableAboveOfType K L tys U S φ :=
  ⟨hφ.1.mono K L S hUV, hφ.2⟩

-- pin: IsUnitFactorizableAboveOfType.mono_type (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:509)
theorem IsUnitFactorizableAboveOfType.mono_type {tys' : ArchTypeFamily L} (h : tys.IsContainedIn L tys')
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) :
    IsUnitFactorizableAboveOfType K L tys' U S φ :=
  ⟨hφ.1, hφ.2.mono L h⟩

variable (K L tys U S)

-- pin: isUnitFactorizableAboveOfType_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:516)
theorem isUnitFactorizableAboveOfType_zero (hS : S.Nonempty) :
    IsUnitFactorizableAboveOfType K L tys U S (fun _ => 0) :=
  ⟨isUnitFactorizableAbove_zero K L U S hS, isArchBiFinite_zero L tys⟩

end AboveTierRefined

section BelowTier

variable (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

-- pin: IsUnitFactorization (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:526)
def IsUnitFactorization (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧ (∀ v ∈ S, IsLocalTestFn K v (fS v)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
    (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
      ff h = ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
    (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) → ff h = 0) ∧
  ∀ g, f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)

-- pin: isUnitFactorizableAt_iff (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:537)
theorem isUnitFactorizableAt_iff (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    IsUnitFactorizableAt K U S f ↔
      IsBiInvariantUnder K U f ∧ ∃ fa ff fS, IsUnitFactorization K S f fa ff fS :=
  Iff.rfl

-- pin: isUnitFactorization_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:543)
theorem isUnitFactorization_zero (hS : S.Nonempty) :
    IsUnitFactorization K S (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) := by
  obtain ⟨v₀, hv₀⟩ := hS
  refine ⟨isArchTestFactor_zero K, isFinTestFactor_zero K, fun v _ => isLocalTestFn_zero K v,
    fun h _ => ?_, fun _ _ => rfl, fun _ => by simp⟩
  exact (Finset.prod_eq_zero hv₀ rfl).symm

end BelowTier

section Global

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))

-- pin: AreMatchingAt (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:557)
def AreMatchingAt (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    Prop :=
  ∃ (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
    IsSemiLocalFactorization K L S φ φa φf φS ∧ IsUnitFactorization K S f fa ff fS ∧
    AreMatchingArch K L σ φa fa ∧ ∀ v ∈ S, AreMatchingLocal K L v σ (φS v) (fS v)

-- pin: areMatchingAt_zero (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:566)
theorem areMatchingAt_zero (hS : S.Nonempty) : AreMatchingAt K L σ S (fun _ => 0) (fun _ => 0) :=
  ⟨_, _, _, _, _, _, isSemiLocalFactorization_zero K L S hS, isUnitFactorization_zero K S hS,
    areMatchingArch_zero K L σ, fun v _ => areMatchingLocal_zero K L v σ⟩

end Global

end AutomorphicForm

end
