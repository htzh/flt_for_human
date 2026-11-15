/-
  SET-AF84B consumer: the irreducibility spine, used as an algebra of cusp subrepresentations.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/IrreducibleSpine.lean` carries four rows: two
  `CuspidalConstituent` rows (the invariants of a cusp subrepresentation lie in finitely many irreducible
  archimedean types, for the compact-open `U` and for the level-`N` submodule) and two `CuspidalSpectrum`
  rows (the orthogonal complement of a closed cusp subrepresentation is one, and so is the closure of the
  image of a cusp subrepresentation in the cusp subcarrier).

  **The readings.** The two `CuspidalSpectrum` rows are closure *operations* on the predicate
  `IsClosedCuspSubrep`, and an operation is worth having as a closure only if it composes:

  * Zone 1 — **idempotence**: taking the orthogonal complement twice lands back in the predicate. The row
    is the step; the consumer is the composition.
  * Zone 2 — **the two rows compose across files**: the closure row's output is a closed cusp
    subrepresentation, so the orthogonal row applies to *it*, giving
    `IsClosedCuspSubrep (closure-image)ᗮ`. Neither row states this, and it is the shape a decomposition
    argument needs (close, then take the complement).
  * Zone 3 — **the constituent row's family, read alone**: the row's first conjunct is "finitely many
    irreducible archimedean types", which a consumer of the isotypic decomposition wants without the
    `∀ S` half that the row also carries.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF84BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.IrreducibleSpine

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped Classical InnerProductSpace

namespace AutomorphicFormSetAF84BConsumer

/-! ### Zone 1 — the orthogonal complement is idempotent on closed cusp subrepresentations -/

/-- **Zone 1.** Two applications of the orthogonality row: the double orthogonal complement of a closed
cusp subrepresentation is again one. -/
theorem isClosedCuspSubrep_double_orthogonal (F : Type) [Field F] [NumberField F]
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M) :
    IsClosedCuspSubrep F hΦ₀ σ ξ Mᗮᗮ :=
  isClosedCuspSubrep_orthogonal F hΦ₀ σ ξ hσ Mᗮ
    (isClosedCuspSubrep_orthogonal F hΦ₀ σ ξ hσ M hM)

/-! ### Zone 2 — the closure row and the orthogonal row compose -/

/-- **Zone 2.** The closure of the image of a cusp subrepresentation is a closed cusp subrepresentation
(the closure row), so its orthogonal complement is one too (the orthogonality row). The two rows live in
different pin files and neither states the composition. -/
theorem isClosedCuspSubrep_orthogonal_topologicalClosure (F : Type) [Field F] [NumberField F]
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hW : IsCuspSubrep F (fdPins F Φ₀) ξ W) :
    IsClosedCuspSubrep F hΦ₀ σ ξ
      (Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ)
        (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W)).topologicalClosureᗮ :=
  isClosedCuspSubrep_orthogonal F hΦ₀ σ ξ hσ _
    (isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep F hΦ₀ σ ξ W hW)

/-! ### Zone 3 — the constituent row's finite family, read alone -/

/-- **Zone 3.** The "finitely many irreducible archimedean types" half of the constituent row, at a
caller-supplied cusp subrepresentation: the family `τs` the row produces is finite and every member is
irreducible at every place. -/
theorem exists_finite_irreducible_archTypeFamily (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : ArchTypeFamily F) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V) :
    ∃ (n : ℕ) (τs : Fin n → ∀ w : InfinitePlace F, ArchRepAt F w), ∀ j w, (τs j w).ρ.IsIrreducible := by
  obtain ⟨n, τs, hirr, -⟩ :=
    exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep F c u d₁ d₂ T ξ U hU O hO hUO tys V hV
  exact ⟨n, τs, hirr⟩

end AutomorphicFormSetAF84BConsumer
