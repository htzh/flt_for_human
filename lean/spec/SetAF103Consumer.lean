import FLTForHuman.FieldTheory.ValuationSubringValuedField
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumApproximation

set_option autoImplicit false

noncomputable section

open Polynomial MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
  NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

namespace SetAF103Consumer

/-! ## Zone C — the approximation row at the zero function produces a flat factorizable test function -/

theorem exists_factorizable_flat_levelSpherical
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys ((fdPins F Φ₀).U N) f ∧ flat F σ f = f := by
  obtain ⟨f, hf, hls, hfl, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_norm_toCarrier_sub_lt (F := F) hΦ₀ σ ξ hσ N hN tys
      (0 : AdelicGL2 (𝓞 F) F → ℂ) (by simp) (by simp) (by simp) 1 one_pos
  exact ⟨f, hf, hls, hfl⟩

/-! ## Zone E — the root-count row at the trivial valuation ring of `ℚ` -/

theorem natDegree_map_X_top :
    ((X : Polynomial ↥(⊤ : ValuationSubring ℚ)).map
        (RingHom.id ↥(⊤ : ValuationSubring ℚ))).natDegree
      = Multiset.card (X : Polynomial ↥(⊤ : ValuationSubring ℚ)).roots := by
  refine ValuationSubring.natDegree_map_eq_card_roots_of_splits (⊤ : ValuationSubring ℚ)
    (RingHom.id ↥(⊤ : ValuationSubring ℚ)) ?_ (X : Polynomial ↥(⊤ : ValuationSubring ℚ)) ?_ ?_
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    ext a
    simp
  · simp
  · simp [Polynomial.roots_X]

end SetAF103Consumer
