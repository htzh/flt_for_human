/-
  Local orbital integrals and the unit-factorizable base layer.

  This is the whole pin node `Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean`
  (pinned `aa2d8b3`, 433 lines / 62 declarations), transcribed at the pin's names
  in namespace `AutomorphicForm`: the integrality sets `integralMatrixSet`/
  `integralUnitsSet` and their compactness/openness, the local test functions and
  the local Haar measure `localHaar`, the local orbital integrals `IsSectionFn`/
  `IsOrbitalIntegral`, the finite unit set `unitFinSet`, the tier-level
  `IsUnitFactorizableAt`/`IsIntegralLevel`/`IsBiInvariantUnder`, and
  regular-semi-simplicity.

  ## Fold

  This module folds in the landed `FLTForHuman/AutomorphicForm/Adelic/IntegralUnits.lean`
  (UF1's M1, 13 public declarations: the `IntegralUnits` section,
  `isLocallyConstant_indicator_one` and the `IsBiInvariantUnder` block).  All of
  those declarations are re-landed here at the same pin names, so this module holds
  the pin node whole; `IntegralUnits.lean` is deleted.

  ## Substitutions against mathlib `v4.34.0`

  * `Set.mem_setOf_eq` is `Set.mem_ofPred_eq` in `v4.34.0` (used in
    `integralUnitsSet_eq_preimage`).
  * No declaration of this pin node is replaced by a mathlib declaration: mathlib
    has no counterpart of `integralMatrixSet`, `integralUnitsSet`, `IsLocalTestFn`,
    `localHaar`, `IsSectionFn`, `IsOrbitalIntegral`, `unitFinSet`,
    `IsUnitFactorizableAt`, `IsIntegralLevel` or `IsRegularSemisimple`.  The
    supporting mathlib objects (`PositiveCompacts`, `Units.embedProduct`,
    `Measure.haarMeasure`, `Measure.isHaarMeasure_haarMeasure`,
    `Measure.haarMeasure_self`, `isCompact_univ_pi`, `isOpen_set_pi`) are imported
    and used directly.
  * the pin's bare `import Mathlib` is replaced by the explicit imports below.

  ## Linter adaptation

  Where the pin uses the `letI`/`haveI` tactics in a proof whose goal is a
  proposition, this port uses `let`/`have` (which also register local instances), to
  satisfy the `v4.34.0` `haveILetI` linter.
-/
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.NumberTheory.AdelicHaar.Local
import FLTForHuman.NumberTheory.AdelicLevel.Level
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false


open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

noncomputable section

namespace AutomorphicForm

section IntegralUnits

variable {A : Type*}

-- pin: integralMatrixSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:15)
def integralMatrixSet (U : Set A) : Set (Matrix (Fin 2) (Fin 2) A) := {m | ∀ i j, m i j ∈ U}

-- pin: integralMatrixSet_eq_pi (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:17)
theorem integralMatrixSet_eq_pi (U : Set A) :
    integralMatrixSet U = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => U := by
  ext m
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩

-- pin: isCompact_integralMatrixSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:22)
theorem isCompact_integralMatrixSet [TopologicalSpace A] {U : Set A} (hU : IsCompact U) :
    IsCompact (integralMatrixSet U) := by
  rw [integralMatrixSet_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hU

-- pin: isOpen_integralMatrixSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:27)
theorem isOpen_integralMatrixSet [TopologicalSpace A] {U : Set A} (hU : IsOpen U) : IsOpen (integralMatrixSet U) := by
  rw [integralMatrixSet_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hU

variable [CommRing A]

-- pin: integralUnitsSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:33)
def integralUnitsSet (U : Set A) : Set (GL (Fin 2) A) :=
  {g | (g : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U ∧
    ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U}

-- pin: mem_integralUnitsSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:37)
theorem mem_integralUnitsSet {U : Set A} {g : GL (Fin 2) A} :
    g ∈ integralUnitsSet U ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) A) i j ∈ U) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j ∈ U :=
  Iff.rfl

-- pin: one_mem_integralUnitsSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:42)
theorem one_mem_integralUnitsSet {U : Set A} (h0 : (0 : A) ∈ U) (h1 : (1 : A) ∈ U) :
    (1 : GL (Fin 2) A) ∈ integralUnitsSet U := by
  have hmat : (1 : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U := fun i j => by
    by_cases h : i = j
    · subst h; rw [Matrix.one_apply_eq]; exact h1
    · rw [Matrix.one_apply_ne h]; exact h0
  refine ⟨?_, ?_⟩
  · rw [Units.val_one]; exact hmat
  · rw [inv_one, Units.val_one]; exact hmat

-- pin: integralUnitsSet_eq_preimage (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:52)
theorem integralUnitsSet_eq_preimage (U : Set A) :
    integralUnitsSet U = (Units.embedProduct (Matrix (Fin 2) (Fin 2) A)) ⁻¹'
      (integralMatrixSet U ×ˢ (MulOpposite.op '' integralMatrixSet U)) := by
  ext g
  simp only [integralUnitsSet, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := MulOpposite.op_injective hm'
    rw [← this]
    exact hm

-- pin: isCompact_integralUnitsSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:67)
theorem isCompact_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {U : Set A}
    (hU : IsCompact U) :
    IsCompact (integralUnitsSet U) := by
  rw [integralUnitsSet_eq_preimage]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_integralMatrixSet hU).prod
      ((isCompact_integralMatrixSet hU).image MulOpposite.continuous_op))

-- pin: isOpen_integralUnitsSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:75)
theorem isOpen_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {U : Set A}
    (hU : IsOpen U) : IsOpen (integralUnitsSet U) := by
  rw [integralUnitsSet_eq_preimage]
  exact ((isOpen_integralMatrixSet hU).prod
    (MulOpposite.opHomeomorph.isOpenMap _ (isOpen_integralMatrixSet hU))).preimage
    Units.continuous_embedProduct

end IntegralUnits

section Local

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

-- pin: IsLocalTestFn (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:88)
def IsLocalTestFn (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  IsLocallyConstant fv ∧ HasCompactSupport fv

-- pin: isLocalTestFn_zero (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:91)
theorem isLocalTestFn_zero : IsLocalTestFn K v (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

-- pin: localAt (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:94)
def localAt : GL (Fin 2) (AdeleRing (𝓞 K) K) →* GL (Fin 2) (v.adicCompletion K) :=
  (AdelicLevel.finComponent (𝓞 K) K v).comp (AdelicLevel.glFin (𝓞 K) K)

-- pin: continuous_localAt (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:97)
theorem continuous_localAt : Continuous (localAt K v) :=
  (AdelicLevel.continuous_finComponent (𝓞 K) K v).comp (AdelicLevel.continuous_glFin (𝓞 K) K)

-- pin: localIntegralSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:100)
def localIntegralSet : Set (GL (Fin 2) (v.adicCompletion K)) :=
  integralUnitsSet (v.adicCompletionIntegers K : Set (v.adicCompletion K))

-- pin: mem_localIntegralSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:103)
theorem mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)} :
    g ∈ localIntegralSet K v ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K :=
  Iff.rfl

-- pin: one_mem_localIntegralSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:110)
theorem one_mem_localIntegralSet : (1 : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v :=
  one_mem_integralUnitsSet (zero_mem _) (one_mem _)

-- pin: isCompact_localIntegralSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:113)
theorem isCompact_localIntegralSet : IsCompact (localIntegralSet K v) :=
  isCompact_integralUnitsSet
    (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v))

-- pin: isOpen_localIntegralSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:117)
theorem isOpen_localIntegralSet : IsOpen (localIntegralSet K v) :=
  isOpen_integralUnitsSet ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v)

-- pin: localIntegralCompacts (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:120)
def localIntegralCompacts : PositiveCompacts (GL (Fin 2) (v.adicCompletion K)) where
  carrier := localIntegralSet K v
  isCompact' := isCompact_localIntegralSet K v
  interior_nonempty' := by
    rw [(isOpen_localIntegralSet K v).interior_eq]
    exact ⟨1, one_mem_localIntegralSet K v⟩

-- pin: coe_localIntegralCompacts (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:127)
theorem coe_localIntegralCompacts :
    (localIntegralCompacts K v : Set (GL (Fin 2) (v.adicCompletion K))) = localIntegralSet K v :=
  rfl

-- pin: isLocallyConstant_indicator_one (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:131)
theorem isLocallyConstant_indicator_one {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsOpen U) (hU' : IsClosed U) : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) := by
  intro s
  by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = Set.univ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact isOpen_univ
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = U := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact hU
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = Uᶜ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact hU'.isOpen_compl
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = ∅ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact isOpen_empty

-- pin: isLocalTestFn_indicator_localIntegralSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:148)
theorem isLocalTestFn_indicator_localIntegralSet :
    IsLocalTestFn K v ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_localIntegralSet K v)
      (isCompact_localIntegralSet K v).isClosed,
    HasCompactSupport.intro (isCompact_localIntegralSet K v) fun _ hg => by simp [hg]⟩

-- pin: localGLBorel (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:154)
@[reducible] def localGLBorel : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := borel _

-- pin: borelSpace_localGLBorel (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:156)
theorem borelSpace_localGLBorel :
    @BorelSpace (GL (Fin 2) (v.adicCompletion K)) _ (localGLBorel K v) :=
  @BorelSpace.mk _ _ (localGLBorel K v) rfl

-- pin: locallyCompactSpace_matrix_adicCompletion (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:160)
theorem locallyCompactSpace_matrix_adicCompletion :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → v.adicCompletion K))

-- pin: locallyCompactSpace_localGL (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:164)
theorem locallyCompactSpace_localGL : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) := by
  have h := locallyCompactSpace_matrix_adicCompletion K v
  infer_instance

-- pin: localHaar (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:168)
def localHaar : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.haarMeasure (localIntegralCompacts K v)

-- pin: isHaarMeasure_localHaar (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:174)
theorem isHaarMeasure_localHaar :
    @Measure.IsHaarMeasure (GL (Fin 2) (v.adicCompletion K)) _ _ (localGLBorel K v) (localHaar K v) := by
  let ms := localGLBorel K v
  have hbs := borelSpace_localGLBorel K v
  have hlc := locallyCompactSpace_localGL K v
  exact Measure.isHaarMeasure_haarMeasure _

-- pin: localHaar_localIntegralSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:181)
theorem localHaar_localIntegralSet : localHaar K v (localIntegralSet K v) = 1 := by
  let ms := localGLBorel K v
  have hbs := borelSpace_localGLBorel K v
  have hlc := locallyCompactSpace_localGL K v
  exact Measure.haarMeasure_self

end Local

section OrbitalIntegral

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

-- pin: localCentralizer (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:193)
abbrev localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  Subgroup.centralizer {γ}

-- pin: localCentralizerBorel (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:197)
@[reducible] def localCentralizerBorel (γ : GL (Fin 2) (v.adicCompletion K)) :
    MeasurableSpace (localCentralizer K v γ) := borel _

-- pin: IsSectionFn (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:200)
def IsSectionFn (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (w : GL (Fin 2) (v.adicCompletion K) → ℝ) : Prop :=
  letI := localGLBorel K v
  letI := localCentralizerBorel K v γ
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, fv (x⁻¹ * γ * x) ≠ 0 → ∫ t : localCentralizer K v γ, w (t * x) ∂τ = 1

-- pin: IsOrbitalIntegral (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:208)
def IsOrbitalIntegral (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ) : Prop :=
  letI := localGLBorel K v
  ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ, IsSectionFn K v γ τ fv w ∧
    I = ∫ x, fv (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v)

-- pin: isSectionFn_zero (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:215)
theorem isSectionFn_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsSectionFn K v γ τ (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩

-- pin: isOrbitalIntegral_zero (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:220)
theorem isOrbitalIntegral_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsOrbitalIntegral K v γ τ (fun _ => 0) 0 :=
  ⟨fun _ => 0, isSectionFn_zero K v γ τ, by simp⟩

-- pin: not_isOrbitalIntegral_zero_one (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:225)
theorem not_isOrbitalIntegral_zero_one (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    ¬ IsOrbitalIntegral K v γ τ (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h

end OrbitalIntegral

section UnitFactor

variable (K : Type) [Field K] [NumberField K]

-- pin: unitFinSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:237)
def unitFinSet : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
  {h | ∀ v : HeightOneSpectrum (𝓞 K), AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v}

-- pin: unitFinSet_eq (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:240)
theorem unitFinSet_eq :
    unitFinSet K = integralUnitsSet (AdelicLevel.integralFiniteAdeles (𝓞 K) K) := by
  ext h
  simp only [unitFinSet, Set.mem_ofPred_eq, mem_localIntegralSet, mem_integralUnitsSet,
    AdelicLevel.integralFiniteAdeles, ← map_inv, AdelicLevel.finComponent_apply]
  exact ⟨fun H => ⟨fun i j v => (H v).1 i j, fun i j v => (H v).2 i j⟩,
    fun H v => ⟨fun i j => H.1 i j v, fun i j => H.2 i j v⟩⟩

-- pin: one_mem_unitFinSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:248)
theorem one_mem_unitFinSet : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∈ unitFinSet K :=
  fun v => by rw [map_one]; exact one_mem_localIntegralSet K v

-- pin: isCompact_unitFinSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:251)
theorem isCompact_unitFinSet : IsCompact (unitFinSet K) := by
  rw [unitFinSet_eq]
  exact isCompact_integralUnitsSet (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)

-- pin: isOpen_unitFinSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:255)
theorem isOpen_unitFinSet : IsOpen (unitFinSet K) := by
  rw [unitFinSet_eq]
  exact isOpen_integralUnitsSet (AdelicLevel.isOpen_integralFiniteAdeles (𝓞 K) K)

-- pin: isFinTestFactor_indicator_unitFinSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:259)
theorem isFinTestFactor_indicator_unitFinSet :
    IsFinTestFactor K ((unitFinSet K).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_unitFinSet K) (isCompact_unitFinSet K).isClosed,
    HasCompactSupport.intro (isCompact_unitFinSet K) fun _ hg => by simp [hg]⟩

end UnitFactor

section Tier

variable (K : Type) [Field K] [NumberField K]

-- pin: unitFinSet_eq_finiteIntegralGL2 (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:270)
theorem unitFinSet_eq_finiteIntegralGL2 :
    unitFinSet K = (AdelicLevel.finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  ext h
  rw [unitFinSet_eq, SetLike.mem_coe, AdelicLevel.mem_finiteIntegralGL2_iff]
  exact Iff.rfl

-- pin: indicator_unitFinSet_mul_left (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:276)
theorem indicator_unitFinSet_mul_left {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (unitFinSet K).indicator (fun _ => (1 : ℂ)) (u * x) =
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) x := by
  have key : u * x ∈ unitFinSet K ↔ x ∈ unitFinSet K := by
    rw [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_left _ hu
  by_cases hx : x ∈ unitFinSet K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]

-- pin: indicator_unitFinSet_mul_right (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:287)
theorem indicator_unitFinSet_mul_right {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (unitFinSet K).indicator (fun _ => (1 : ℂ)) (x * u) =
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) x := by
  have key : x * u ∈ unitFinSet K ↔ x ∈ unitFinSet K := by
    rw [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_right _ hu
  by_cases hx : x ∈ unitFinSet K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]

-- pin: IsBiInvariantUnder (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:298)
def IsBiInvariantUnder (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  ∀ u ∈ U, ∀ g, f (u * g) = f g ∧ f (g * u) = f g

-- pin: IsBiInvariantUnder.mono (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:302)
theorem IsBiInvariantUnder.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsBiInvariantUnder K V f) :
    IsBiInvariantUnder K U f :=
  fun u hu => hf u (hUV hu)

-- pin: isBiInvariantUnder_bot (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:307)
theorem isBiInvariantUnder_bot (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    IsBiInvariantUnder K ⊥ f := by
  intro u hu g
  rw [Subgroup.mem_bot.1 hu, one_mul, mul_one]
  exact ⟨rfl, rfl⟩

-- pin: IsUnitFactorizableAt (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:313)
def IsUnitFactorizableAt (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  IsBiInvariantUnder K U f ∧
  ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
    IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧ (∀ v ∈ S, IsLocalTestFn K v (fS v)) ∧
    (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
        ff h = ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
    (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) → ff h = 0) ∧
    ∀ g, f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)

-- pin: IsUnitFactorizableAt.mono (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:327)
theorem IsUnitFactorizableAt.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K V S f) : IsUnitFactorizableAt K U S f :=
  ⟨hf.1.mono K hUV, hf.2⟩

-- pin: IsUnitFactorizableAt.isBiInvariantUnder (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:332)
theorem IsUnitFactorizableAt.isBiInvariantUnder {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K U S f) : IsBiInvariantUnder K U f :=
  hf.1

-- pin: IsUnitFactorizableAt.isFactorizableTestFn (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:337)
theorem IsUnitFactorizableAt.isFactorizableTestFn {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K U S f) : IsFactorizableTestFn K f := by
  obtain ⟨-, fa, ff, _, hfa, hff, -, -, -, hf⟩ := hf
  exact ⟨fa, ff, hfa, hff, hf⟩

-- pin: IsIntegralLevel (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:343)
def IsIntegralLevel (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) : Prop :=
  ∀ u ∈ U, AdelicLevel.glArch (𝓞 K) K u = 1 ∧
    AdelicLevel.glFin (𝓞 K) K u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K

-- pin: isIntegralLevel_bot (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:347)
theorem isIntegralLevel_bot : IsIntegralLevel K ⊥ := by
  intro u hu
  rw [Subgroup.mem_bot.1 hu, map_one, map_one]
  exact ⟨rfl, one_mem _⟩

-- pin: isIntegralLevel_levelOne_inf_ker (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:352)
theorem isIntegralLevel_levelOne_inf_ker (N : Ideal (𝓞 K)) :
    IsIntegralLevel K (AdelicLevel.levelOne (𝓞 K) K N ⊓ (AdelicLevel.glArch (𝓞 K) K).ker) := by
  intro u hu
  obtain ⟨hlev, harch⟩ := Subgroup.mem_inf.1 hu
  refine ⟨MonoidHom.mem_ker.1 harch, ?_⟩
  have h0 := AdelicLevel.finiteLevelOne_le_finiteLevelZero (𝓞 K) K N (AdelicLevel.mem_levelOne_iff.1 hlev)
  exact AdelicLevel.mem_finiteIntegralGL2_iff.2 ⟨h0.1.integral, h0.2.integral⟩

-- pin: isUnitFactorizableAt_mul_indicator_unitFinSet (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:360)
theorem isUnitFactorizableAt_mul_indicator_unitFinSet {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (hfa : IsArchTestFactor K fa) {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    (hU : IsIntegralLevel K U) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableAt K U S fun g => fa (AdelicLevel.glArch (𝓞 K) K g) *
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 K) K g) := by
  refine ⟨fun u hu g => ?_, fa, (unitFinSet K).indicator fun _ => (1 : ℂ),
    fun v => (localIntegralSet K v).indicator fun _ => (1 : ℂ), hfa,
    isFinTestFactor_indicator_unitFinSet K, fun v _ => isLocalTestFn_indicator_localIntegralSet K v,
    fun h hS => ?_, fun h hS => ?_, fun _ => rfl⟩
  · obtain ⟨hu1, hu2⟩ := hU u hu
    constructor
    · dsimp only
      rw [map_mul, map_mul, hu1, one_mul, indicator_unitFinSet_mul_left K hu2]
    · dsimp only
      rw [map_mul, map_mul, hu1, mul_one, indicator_unitFinSet_mul_right K hu2]
  · by_cases hall : h ∈ unitFinSet K
    · rw [Set.indicator_of_mem hall]
      exact (Finset.prod_eq_one fun v _ => Set.indicator_of_mem (hall v) _).symm
    · rw [Set.indicator_of_notMem hall]
      obtain ⟨v, hv⟩ : ∃ v, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v := by
        by_contra hcon
        exact hall fun v => by_contra fun hv => hcon ⟨v, hv⟩
      have hvS : v ∈ S := by
        by_contra hvS
        exact hv (hS v hvS)
      exact (Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _)).symm
  · obtain ⟨v, -, hv⟩ := hS
    have hnot : h ∉ unitFinSet K := fun hall => hv (hall v)
    exact Set.indicator_of_notMem hnot _

-- pin: isUnitFactorizableAt_zero (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:390)
theorem isUnitFactorizableAt_zero (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) : IsUnitFactorizableAt K U S fun _ => 0 := by
  refine ⟨fun _ _ _ => ⟨rfl, rfl⟩, ?_⟩
  simpa using
    (isUnitFactorizableAt_mul_indicator_unitFinSet K (isArchTestFactor_zero K) (isIntegralLevel_bot K) S).2

end Tier

section RegularSemisimple

variable {A : Type*} [CommRing A]

-- pin: IsRegularSemisimple (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:402)
def IsRegularSemisimple (g : GL (Fin 2) A) : Prop :=
  IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A))

-- pin: isRegularSemisimple_iff (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:405)
theorem isRegularSemisimple_iff (g : GL (Fin 2) A) :
    IsRegularSemisimple g ↔
      IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A)) :=
  Iff.rfl

-- pin: isRegularSemisimple_iff_ne_zero (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:410)
theorem isRegularSemisimple_iff_ne_zero {F : Type*} [Field F] (g : GL (Fin 2) F) :
    IsRegularSemisimple g ↔
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) F) ≠ 0 :=
  isUnit_iff_ne_zero

-- pin: IsRegularSemisimple.conj (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:415)
theorem IsRegularSemisimple.conj {g : GL (Fin 2) A} (hg : IsRegularSemisimple g) (x : GL (Fin 2) A) :
    IsRegularSemisimple (x⁻¹ * g * x) := by
  unfold IsRegularSemisimple at hg ⊢
  have htr : Matrix.trace ((x⁻¹ * g * x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  have hdet : Matrix.det ((x⁻¹ * g * x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.det (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  rw [htr, hdet]
  exact hg

end RegularSemisimple

end AutomorphicForm

end
