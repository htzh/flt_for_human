/-
  Cross-module wire test for SET-AF25 (the cuspidal lift of a convolution operator).

  A `spec/` probe, not a library module. Two composition zones, each one *consuming* a headline of
  `AutomorphicForm/Adelic/Cusp/SpectrumLift.lean` rather than re-deriving it:

  * **175 row.** `isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep`
    produces an `IsCuspSubrep F (fdPins F Φ₀) ξ` for the `K`-finite vectors of a closed cusp
    subrepresentation. The zone feeds that datum into the structure's own `rightConv_mem` field to
    read `rightConv F φ f` back inside the submodule, and then into the `le` field to land in the
    `K`-finite span `cuspKFiniteSubmodule F (fdPins F Φ₀) ξ`. Both fields are consumed at the same
    element, so the composition is the headline's conclusion and nothing else.

  * **112 row.** `exists_commute_lift_rightTranslate_rowIsometry_of_isCompact` commutes the lift of a
    row-isometry translation with a `Tc` that satisfies the `hcomm` bundle; the bundle is the only
    hypothesis that mentions `f` and `Tc`, so the degenerate `Tc = 0`, `f = 0` case is what a
    consumer can discharge without any input: `rightConv_zero_right` makes the right-hand side
    `toCuspSubcarrier ⟨0, _⟩ = 0`, and the zero operator kills the left. The zone then reads the
    headline's second component at `φ = 0`, which is the sharp statement `S 0 = 0` for the operator
    the headline produced.

  It imports only the module it consumes.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumLift

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

namespace SetAF25Consumer

variable {F : Type} [Field F] [NumberField F]
  {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)

/-- **Zone 1 (175 row).** The `K`-finite vectors of a closed cusp subrepresentation form a
`IsCuspSubrep`, and that datum is consumed twice at one element: `rightConv_mem` puts `rightConv φ f`
back in the submodule `V`, and `le` then reads it in the `K`-finite span. -/
theorem rightConv_mem_cuspKFiniteSubmodule_of_isClosedCuspSubrep (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F) (hf : IsFactorizableTestFn F f)
    (hft : IsArchBiFinite F tys f)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule F (fdPins F Φ₀) ξ ⊓
      Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype
        (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) M)) :
    rightConv F φ f ∈ cuspKFiniteSubmodule F (fdPins F Φ₀) ξ := by
  have hV :=
    isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
      F hΦ₀ σ ξ hσ M hM
  exact hV.le (hV.rightConv_mem f tys hf hft φ hφ)

/-- **Zone 2 (112 row).** The row-isometry commutation at `f = 0` and `Tc = 0`, the one point where
`hcomm` is free: the headline's `S` then kills the zero cusp vector. -/
theorem exists_commute_zero_rightTranslate (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F) (tys : AutomorphicForm.ArchTypeFamily F)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      S.comp (0 : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) = 0 ∧
        S (toCuspSubcarrier F hΦ₀ σ ξ 0) = 0 := by
  classical
  obtain ⟨S, hS, hlift⟩ :=
    exists_commute_lift_rightTranslate_rowIsometry_of_isCompact F hΦ₀ σ ξ hσ U hU O hO hUO tys
      (fun _ => 0) (isFactorizableTestFn_zero F) (isLevelSphericalOfType_zero F tys U)
      (0 : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
      (fun φ hφ' => by
        show (0 : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
            (toCuspSubcarrier F hΦ₀ σ ξ φ) =
          toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ (fun _ => 0), hφ'⟩
        rw [zero_apply]
        have hz : (⟨rightConv F φ (fun _ => 0), hφ'⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = 0 := by
          apply Subtype.ext
          exact rightConv_zero_right F (φ : AdelicGL2 (𝓞 F) F → ℂ)
        rw [hz, map_zero])
      w k
  refine ⟨S, ?_, ?_⟩
  · simp
  · obtain ⟨h, hh⟩ := hlift (0 : ↥(cuspMemberSubmodule F Φ₀ ξ))
    rw [hh]
    have hz : (⟨rightTranslate F (rowIsometryInclAt₀ F w k)
          (0 : ↥(cuspMemberSubmodule F Φ₀ ξ)), h⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = 0 := by
      apply Subtype.ext
      exact rightTranslate_zero F (rowIsometryInclAt₀ F w k)
    rw [hz, map_zero]

end SetAF25Consumer

end
