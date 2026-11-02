/-
  The cuspidal subrepresentation datum.

  `IsCuspLift hΦ₀ σ ξ op S` says the bounded operator `S` on the cuspidal subcarrier is
  the carrier image of the function-level operator `op`: on every element of the carrier's
  cusp member submodule whose image under `op` is again a cusp member, `S` agrees with the
  composite of `op` and `toCuspSubcarrier`. `IsClosedCuspSubrep` is the closure condition
  read through such lifts: a closed submodule of the cuspidal subcarrier that is stable
  under every lifted right translation by the finite level group, under every lifted right
  translation by the archimedean row isometries, and under every lifted right convolution
  by a factorizable archimedean-bi-finite test function. `IsIrreducibleCuspSubrep` adds
  non-triviality and the absence of a proper closed sub-object, and the API records the
  top and bottom elements, the intersection of two closed sub-objects, and the projections
  from irreducibility.

  Transcribed from `Definitions/Def_AutomorphicForm_CuspidalSpectrumSubrep.lean` (pinned
  `aa2d8b3`, 104 lines / 11 declarations). The pin's single `import` is the carrier module,
  which this file imports; the pin's `open AutomorphicForm.CuspidalConstituent` is kept so
  the level-invariant vocabulary resolves at the pin's names. The pin namespace
  `AutomorphicForm.CuspidalSpectrum` is kept, and mathlib `v4.34.0` has no counterpart: all
  11 declarations are residue.

  spec-pin: Definitions/Def_AutomorphicForm_CuspidalSpectrumSubrep.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightCharTransport

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm.CuspidalConstituent

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

variable (F : Type) [Field F] [NumberField F]

def IsCuspLift {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop :=
  ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ),
    S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩

theorem isCuspLift_iff {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
    IsCuspLift F hΦ₀ σ ξ op S ↔
      ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩ := Iff.rfl

theorem isCuspLift_of_forall_exists {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hS : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), ∃ h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ,
      S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩) :
    IsCuspLift F hΦ₀ σ ξ op S := fun φ h => by
  obtain ⟨h', e⟩ := hS φ
  exact e

structure IsClosedCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop where
  isClosed : IsClosed (M : Set ↥(cuspSubcarrier F hΦ₀ σ ξ))
  map_le_of_rightTranslate_fin : ∀ g ∈ finiteAdelicGL2Subgroup F,
    ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S →
        M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M
  map_le_of_rightTranslate_arch : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
    ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S →
        M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M
  map_le_of_rightConv : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
    IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) S →
          M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M

def IsIrreducibleCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop :=
  IsClosedCuspSubrep F hΦ₀ σ ξ M ∧ M ≠ ⊥ ∧
    ∀ M' : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), IsClosedCuspSubrep F hΦ₀ σ ξ M' → M' ≤ M → M' = ⊥ ∨ M' = M

theorem isClosedCuspSubrep_top {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : IsClosedCuspSubrep F hΦ₀ σ ξ ⊤ :=
  ⟨isClosed_univ, fun _ _ _ _ => le_top, fun _ _ _ _ => le_top, fun _ _ _ _ _ _ => le_top⟩

theorem isClosedCuspSubrep_bot {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : IsClosedCuspSubrep F hΦ₀ σ ξ ⊥ :=
  ⟨by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩

theorem not_isIrreducibleCuspSubrep_bot {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ¬ IsIrreducibleCuspSubrep F hΦ₀ σ ξ ⊥ := fun h => h.2.1 rfl

theorem IsIrreducibleCuspSubrep.isClosedCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {hΦ₀ : IsSlabFundamentalDomain F α β Φ₀} {σ : ℝ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)} (h : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M) :
    IsClosedCuspSubrep F hΦ₀ σ ξ M := h.1

theorem IsIrreducibleCuspSubrep.ne_bot {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {hΦ₀ : IsSlabFundamentalDomain F α β Φ₀} {σ : ℝ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)} (h : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M) : M ≠ ⊥ := h.2.1

theorem IsClosedCuspSubrep.inf {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {hΦ₀ : IsSlabFundamentalDomain F α β Φ₀} {σ : ℝ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {M M' : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)}
    (h : IsClosedCuspSubrep F hΦ₀ σ ξ M) (h' : IsClosedCuspSubrep F hΦ₀ σ ξ M') :
    IsClosedCuspSubrep F hΦ₀ σ ξ (M ⊓ M') := by
  refine ⟨h.isClosed.inter h'.isClosed, fun g hg S hS => ?_, fun w k S hS => ?_, fun f tys hf hft S hS => ?_⟩
  · exact le_inf ((Submodule.map_mono inf_le_left).trans (h.map_le_of_rightTranslate_fin g hg S hS))
      ((Submodule.map_mono inf_le_right).trans (h'.map_le_of_rightTranslate_fin g hg S hS))
  · exact le_inf ((Submodule.map_mono inf_le_left).trans (h.map_le_of_rightTranslate_arch w k S hS))
      ((Submodule.map_mono inf_le_right).trans (h'.map_le_of_rightTranslate_arch w k S hS))
  · exact le_inf ((Submodule.map_mono inf_le_left).trans (h.map_le_of_rightConv f tys hf hft S hS))
      ((Submodule.map_mono inf_le_right).trans (h'.map_le_of_rightConv f tys hf hft S hS))

end CuspidalSpectrum

end AutomorphicForm
