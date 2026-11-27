import FLTForHuman.AlgebraicCurve.RegularProlongationRetraction
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArchTypeProjector
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelSphericalEigenvector
import FLTForHuman.GaloisRep.SemisimpleCriterion
import FLTForHuman.ModularCurve.ComplexPlaceDictionaryPoint

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open UpperHalfPlane Filter Polynomial
open scoped ENNReal NNReal ComplexConjugate MatrixGroups Topology Manifold
  IntermediateField.algebraAdjoinAdjoin nonZeroDivisors

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace SetAF105Consumer

/-! ## Zone 1 — both projectors fix the level-invariant `archCut` vectors (orders A + B)

Order A's arch-type projector and order B's cut projector are applied to the *same* carrier: the
arch-type projector `E` (for `tys`) fixes every `archCut tys` vector, and the cut projector `P` (for
the compact open `U`) fixes every `U`-invariant vector, so their composite fixes the vectors that are
both. Deleting either module breaks this: `exists_idempotent_archTypeProjector` is
`Cusp/ArchTypeProjector.lean`'s and `exists_idempotent_cutProjector_of_isCompact` is
`Cusp/LevelSphericalEigenvector.lean`'s. -/

theorem both_projectors_fix_levelInvariant_archCut
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F) (tys : ArchTypeFamily F) :
    ∃ E P : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      E.comp E = E ∧ P.comp P = P ∧
        ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
          (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g) →
            φ ∈ archCutSubmodule F tys →
              (P.comp E) (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) =
                toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ := by
  obtain ⟨E, hE⟩ := exists_idempotent_archTypeProjector (F := F) hΦ₀ σ ξ hσ tys
  obtain ⟨P, hP⟩ := exists_idempotent_cutProjector_of_isCompact (F := F) hΦ₀ σ ξ hσ U hU O hO hUO tys
  refine ⟨E, P, hE.1, hP.1, fun φ hφ hinv harch => ?_⟩
  rw [ContinuousLinearMap.comp_apply, hE.2.2.1 φ hφ harch, hP.2.2.1 φ hφ hinv harch]

/-! ## Zone 2 — the dictionary's places are its points (order E)

The complex place dictionary is *surjective on points*: every place of the `X₁` function field is
`D.pt τ` for an archimedean point `τ`. -/

theorem exists_pt_eq_of_place
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀)
    (P : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀))
    (x : ModularCurve.laurentBaseChange ℂ F₀)
    (hx : (x : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hP : x ∈ P.toValuationSubring) :
    ∃ τ : UpperHalfPlane, D.pt τ = P :=
  ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem Γ hT F₀ hF D P x hx hP

/-! ## Zone 3 — the adjoin criterion produces a prolongation with the prescribed integers (order C)

Order C's `RegularProlongation` row, projected to the part a consumer uses: the prolongation
`R'` whose `integers` are the given valuation subring `W`, with its residue transcendental in the
same class. -/

theorem exists_regularProlongation_integers_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar)
    (f : F) (hfO : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfO⟩))
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (W : ValuationSubring F)
    (hW : ∀ e : F, e ∈ IntermediateField.adjoin L ({f} : Set F) → (e ∈ W ↔ e ∈ R.integers)) :
    ∃ (_ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField W))
      (R' : AlgebraicCurve.RegularProlongation A F (IsLocalRing.ResidueField W)),
      R'.integers = W := by
  obtain ⟨inst, R', hR', _⟩ :=
    AlgebraicCurve.RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic
      A R f hfO htr W hW
  exact ⟨inst, R', hR'⟩

/-! ## Zone 4 — the semisimple model has the same kernel (order D)

The criterion, projected to the two consequences a descent argument consumes: the `κ`-model is
semisimple, and it kills exactly what `ρ` kills. -/

theorem exists_semisimple_model_same_kernel
    (κ : Type) [Field κ] [Finite κ] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ι : κ →+* Ω)
    (ρ : Γℚ →* GL (Fin 2) Ω) (hρ : GaloisFactorsThroughFiniteLevel ρ) (S : Finset ℕ)
    (hfrob : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          Matrix.trace ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range ∧
            Matrix.det ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range) :
    ∃ ρ₀ : Γℚ →* GL (Fin 2) κ,
      (Deformation.matrixRepresentation ρ₀).IsSemisimpleRepresentation ∧
        ∀ σ : Γℚ, ρ σ = 1 → ρ₀ σ = 1 := by
  obtain ⟨ρ₀, _hfin, hss, hker, _hchar⟩ :=
    GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range
      κ Ω ι ρ hρ S hfrob
  exact ⟨ρ₀, hss, hker⟩

end SetAF105Consumer
