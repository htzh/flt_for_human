/-
  Finite-dimensional `K`-span of vectors in finitely many archimedean types.

  At an infinite place `w` of `F`, let `φ` lie in the supremum of the archimedean type
  submodules `archTypeSubmoduleAt F w (ρs i)` over finitely many types
  `ρs : Fin m → ArchRepAt F w`. Then the `ℂ`-span `S` of the row-isometry right
  translates of `φ` is finite-dimensional, is stable under right translation by the
  row-isometry group `rowIsometrySubgroup₀ w.Completion`, and is still contained in that
  same supremum: `K`-finiteness and the cut survive the passage to the translate span.

  The proof is the generic representation-theoretic engine. A finite supremum of type
  pieces is one `LinearMap.pi` piece over finitely many indices (`typeSubmodule_piRep_le`,
  `exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule`): a vector of the
  supremum lies in the range of an equivariant map from a finite product of the types,
  and then the whole translate span lies in the range of that map's composition with the
  finite-dimensional product representation (`finiteDimensional_spanTranslates`). The
  instantiation `kspan_main` reads `ι := rowIsometryInclAt₀ F w` and `ρ i := (ρs i).ρ`,
  for which the supremum of type submodules is definitionally the `archTypeSubmoduleAt`
  supremum; the headline is the pin's `solution`.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt.lean`
  (pinned `aa2d8b3`, 813 lines, 39 declarations); the statement is the `Theorems/`
  wrapper verbatim. **31 of the 39 declarations — 696 of the 786 declaration lines — are
  byte-identical to the port's shared `ArchApproxIdentity` engine** in `RepTheory/TypeReproducer.lean`
  (tier 3, registered in `spec/UNWIRED-PUBLIC.md`; it was homed from the archTestFactor
  silo, whose `TypePiece`…`MultiPlace` sections are the same text), so this module
  imports them instead of re-proving them. New here: the 59-line instantiation
  `kspan_main` (the pin keeps it `private`, and so does the port) and the headline.

  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.RepTheory.TypeReproducer

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField
open ArchApproxIdentity

namespace AutomorphicForm

namespace CuspidalConstituent

section KSpanMain

variable (F : Type) [Field F] [NumberField F]

-- The two `haveI`s bind `FiniteDimensional` instances that the following tactic block
-- consumes by instance search; the linter reads them as proofs (they are propositions).
-- Narrowed to this declaration, as `RepTheory/TypeReproducer.lean` does at its two sites.
set_option linter.style.haveILetI false in
private theorem kspan_main (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    let S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
      Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        rightTranslate F (rowIsometryInclAt₀ F w k) φ)
    FiniteDimensional ℂ ↥S ∧
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) ∧
      S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) := by
  intro S

  let ι : rowIsometrySubgroup₀ w.Completion →* AdelicGL2 (𝓞 F) F := rowIsometryInclAt₀ F w
  let ρ : ∀ i : Fin m, Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin (ρs i).n → ℂ) := fun i => (ρs i).ρ
  have hcut : (⨆ i, archTypeSubmoduleAt F w (ρs i)) = ⨆ i, typeSubmodule ι (ρ i) := rfl

  let V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ {φ}
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton φ)
  have hV : V ≤ ⨆ i, typeSubmodule ι (ρ i) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hφ

  have hS : S ≤ spanTranslates ι V := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact rt_mem_spanTranslates ι V k (Submodule.subset_span rfl)
  refine ⟨?_, ?_, ?_⟩
  · haveI := finiteDimensional_spanTranslates ι ρ V hV
    exact Submodule.finiteDimensional_of_le hS
  · intro k g hg
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨k', rfl⟩
      rw [rightTranslate_rightTranslate, ← map_mul]
      exact Submodule.subset_span ⟨k * k', rfl⟩
    · rw [rightTranslate_zero]
      exact Submodule.zero_mem _
    · intro f g _ _ hf hg
      rw [rightTranslate_add]
      exact Submodule.add_mem _ hf hg
    · intro c f _ hf
      rw [rightTranslate_smul]
      exact Submodule.smul_mem _ c hf
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rw [hcut] at hφ ⊢
    have key : ∀ i : Fin m, (typeSubmodule ι (ρ i)).map (rightRegular F (ι k)) ≤ typeSubmodule ι (ρ i) := by
      intro i f hf
      obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
      exact rt_mem_typeSubmodule_self k hf₀
    have hmap : (⨆ i, typeSubmodule ι (ρ i)).map (rightRegular F (ι k)) ≤ ⨆ i, typeSubmodule ι (ρ i) := by
      rw [Submodule.map_iSup]
      exact iSup_mono key
    exact hmap (Submodule.mem_map_of_mem hφ)

end KSpanMain

theorem finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    let S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
      Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        rightTranslate F (rowIsometryInclAt₀ F w k) φ)
    FiniteDimensional ℂ ↥S ∧
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) ∧
      S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) :=
  kspan_main F w m ρs φ hφ

end CuspidalConstituent

end AutomorphicForm
