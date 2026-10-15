/-
  Integrality sets in `M₂(A)`/`GL₂(A)` and bi-invariance under a subgroup.

  `integralMatrixSet U` is the set of `2 × 2` matrices all of whose entries lie in
  `U`; `integralUnitsSet U` is the set of invertible such matrices whose inverse
  also has all entries in `U`. They are the integrality blocks of the
  unit-factorizable definitions: the semi-local integral set
  (`AutomorphicForm.semiLocalIntegralSet`) is `integralUnitsSet` of the
  semi-local integers. `IsBiInvariantUnder U f` is the left-and-right invariance
  of `f` under a subgroup `U` of `GL₂(𝔸_K)`.

  Transcribed from `Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:13–82,
  131–140, 298–315` (pinned `aa2d8b3`), the `IntegralUnits` block together with
  `isLocallyConstant_indicator_one` and the `Tier`-section bi-invariance block.

  Not transcribed here (deferred with reason, `WORKORDER-UF1` §1.3): the
  local-orbital subject of the same pin module (`IsLocalTestFn`, `localIntegralSet`,
  `localHaar`, `IsOrbitalIntegral`, `IsUnitFactorizableAt`, `IsUnitFactorization`,
  …), whose dependency is the unported tensor/base-change chain
  (`Def_DedekindDomain_Completion_BaseChange`, `Def_AutomorphicForm_SigmaCentralizer`,
  …).

  `integralUnitsSet_eq_preimage` is the pin's support lemma for the compactness and
  openness of `integralUnitsSet`; it is not part of the gate's declaration list, so
  it stays `private` here (WORKORDER-UF1 §3, the helper rule).
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Constructions
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
private theorem integralUnitsSet_eq_preimage (U : Set A) :
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

section Tier

variable (K : Type) [Field K] [NumberField K]

-- pin: IsBiInvariantUnder (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:298)
def IsBiInvariantUnder (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  ∀ u ∈ U, ∀ g, f (u * g) = f g ∧ f (g * u) = f g

-- pin: IsBiInvariantUnder.mono (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:303)
theorem IsBiInvariantUnder.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsBiInvariantUnder K V f) :
    IsBiInvariantUnder K U f :=
  fun u hu => hf u (hUV hu)

-- pin: isBiInvariantUnder_bot (Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean:310)
theorem isBiInvariantUnder_bot (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    IsBiInvariantUnder K ⊥ f := by
  intro u hu g
  rw [Subgroup.mem_bot.1 hu, one_mul, mul_one]
  exact ⟨rfl, rfl⟩

end Tier

end AutomorphicForm

end
