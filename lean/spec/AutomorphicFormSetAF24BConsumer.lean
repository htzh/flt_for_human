/-
  Cross-module wire test for SET-AF24B — the coordinate matrix of a flow that preserves a finite
  span.

  A `spec/` probe, not a library module. **Two zones plus their composition**, over
  `Adelic/ArchRotCoordinate.lean`:

  * `engine_at_const_flow` takes the generic engine *off* the adelic setting — `G = ℂ` under
    multiplication, `ι = Fin 1`, the constant family `x ≡ 1`, the constant flow `k ≡ 1` and
    `M = 0`. It is a real application: the engine's `hspan`, `hk0` and `hder` hypotheses are
    discharged at that datum (the flow fixes the span, its value at `0` is `1`, and the
    derivative of the constant family is the zero combination), and the conclusion is read as
    `E 0 = 1` together with the derivative conjunct `E'(0) = M = 0`. Nothing about
    `archComplexLiftAt` survives into this zone.
  * `exists_E_one_of_headline` applies the headline at the degenerate datum `n = 0` with the
    constant nonzero family `x ≡ 1` on `AdelicGL2 (𝓞 F) F`: the rotation-stability hypotheses
    `hR`, `hS` hold because the flow cannot move a constant function out of its own span, and
    the derivative hypotheses `hR'`, `hS'` hold because the `𝔰𝔩₂` coefficient sums are empty —
    at `n = 0` every `if` condition is false, so the prescribed derivative is `0` and the
    family is constant. The `E₁ 0 = 1` conjunct is read off, and so is the last (expansion)
    conjunct: at a constant family it says `1 = ∑ p', E s p' 0 * 1`, i.e. `E s 0 0 = 1` for
    *every* `s`, not just `s = 0`.
  * `exists_coord_unit_and_E_one` is the composition: the engine's unit matrix over `ℂ` and the
    headline's unit coordinate matrix at a complex place in one statement. The wire dies if
    either headline's hypothesis bundle or conclusion shape changes.

  It imports only the module it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchRotCoordinate

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm

namespace SetAF24BRotCoordinateConsumer

/-! ### Zone 1 — the generic engine at a constant one-dimensional flow -/

/-- **The engine off the adelic setting.** `ArchRotCoordinate.engine` at `G = ℂ`, `ι = Fin 1`,
the constant family `x ≡ 1`, the constant flow `k ≡ 1` and `M = 0`. The conclusion read here is
the unit at `0` and the derivative at `0`. -/
theorem engine_at_const_flow :
    ∃ E : ℝ → Matrix (Fin 1) (Fin 1) ℂ,
      E 0 = 1 ∧ ∀ i j, HasDerivAt (fun s : ℝ => E s i j) (0 : ℂ) 0 := by
  obtain ⟨E, h0, hd, -⟩ := ArchRotCoordinate.engine (G := ℂ) (ι := Fin 1)
    (fun (_ : Fin 1) (_ : ℂ) => (1 : ℂ))
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h1 : g 0 = 0 := by
        have h2 := congrFun hg (1 : ℂ)
        simpa [Fin.sum_univ_one] using h2
      fin_cases i
      exact h1)
    (fun _ => (1 : ℂ)) rfl (fun (_ : Fin 1) (_ : Fin 1) => (0 : ℂ))
    (by
      intro p s
      exact Submodule.subset_span (Set.mem_range_self p))
    (by
      intro p g
      simpa [Fin.sum_univ_one] using hasDerivAt_const (c := (1 : ℂ)) (x := (0 : ℝ)))
  exact ⟨E, h0, fun i j => by simpa using hd i j⟩

/-! ### Zone 2 — the headline at `n = 0` and the constant family -/

/-- **The headline at the degenerate datum.** `n = 0`, `x ≡ 1`: both rotation flows have a
coordinate matrix whose value at `0` is the identity, and — through the expansion conjunct — whose
`(0, 0)` entry is `1` for *every* `s`. -/
theorem exists_E_one_of_headline (F : Type) [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsComplex) :
    ∃ E₁ E₂ : ℝ → Matrix (Fin 1) (Fin 1) ℂ,
      E₁ 0 = 1 ∧ E₂ 0 = 1 ∧ (∀ s : ℝ, E₁ s 0 0 = 1) ∧ (∀ s : ℝ, E₂ s 0 0 = 1) := by
  obtain ⟨E₁, E₂, h1, h2, -, -, hexp1, hexp2⟩ :=
    exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable F hw 0
      (fun (_ : Fin (0 + 1)) (_ : AdelicGL2 (𝓞 F) F) => (1 : ℂ))
      (by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have h1' : g 0 = 0 := by
          have h2' := congrFun hg (1 : AdelicGL2 (𝓞 F) F)
          simpa [Fin.sum_univ_one] using h2'
        fin_cases i
        exact h1')
      (by
        intro p s
        exact Submodule.subset_span (Set.mem_range_self p))
      (by
        intro p s
        exact Submodule.subset_span (Set.mem_range_self p))
      (by
        intro p g
        fin_cases p
        simpa [Fin.sum_univ_one] using hasDerivAt_const (c := (1 : ℂ)) (x := (0 : ℝ)))
      (by
        intro p g
        fin_cases p
        simpa [Fin.sum_univ_one] using hasDerivAt_const (c := (1 : ℂ)) (x := (0 : ℝ)))
  exact ⟨E₁, E₂, h1, h2,
    fun s => by simpa [Fin.sum_univ_one] using (hexp1 0 s (1 : AdelicGL2 (𝓞 F) F)).symm,
    fun s => by simpa [Fin.sum_univ_one] using (hexp2 0 s (1 : AdelicGL2 (𝓞 F) F)).symm⟩

/-! ### Zone 3 — the composition -/

/-- **The two zones in one statement.** The generic engine's unit coordinate matrix over `ℂ`
(left) and the complex-place rotation headline's unit coordinate matrix at `n = 0` (right), the
latter carrying the expansion read-off of `exists_E_one_of_headline`. -/
theorem exists_coord_unit_and_E_one (F : Type) [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsComplex) :
    (∃ E : ℝ → Matrix (Fin 1) (Fin 1) ℂ,
        E 0 = 1 ∧ ∀ i j, HasDerivAt (fun s : ℝ => E s i j) (0 : ℂ) 0) ∧
      (∃ E₁ : ℝ → Matrix (Fin 1) (Fin 1) ℂ, E₁ 0 = 1 ∧ ∀ s : ℝ, E₁ s 0 0 = 1) := by
  obtain ⟨E₁, _E₂, h1, _h2, h3, _h4⟩ := exists_E_one_of_headline F hw
  exact ⟨engine_at_const_flow, E₁, h1, h3⟩

end SetAF24BRotCoordinateConsumer

end
