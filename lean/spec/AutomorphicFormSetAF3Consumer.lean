/-
  Cross-module wire test for the archimedean cut (SET-AF3).

  A `spec/` probe, not a library module.  It has the two zones of the set's brief (§4.4):

  * zone A composes the span module's two rows: the packaged four-conjunct form
    (`finiteDimensional_span_translates_of_mem_archCutSubmodule`) is applied to a vector of the cut,
    and the cut membership it produces at a translate is then the hypothesis of the unfolded row
    (`finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule`), read back at that translate;
  * zone B composes the reproducer with the projector API: the kernel's reproducing identity is
    instantiated at `x = 1` (so it reproduces `v 1`), and the projector's fixed-point property is
    read at a vector of the kernel's space.

  Every zone is a real composition — no `#check` — so deleting either module makes the probe fail.
  Both zones are in hypothesis form: a concrete archimedean type family with a concrete finite-
  dimensional stable `E` is not available in the probe.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchCutSpan
import FLTForHuman.AutomorphicForm.Adelic.ArchCutReproducer

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

namespace AutomorphicFormSetAF3Consumer

-- Zone A (`M1` then `M2`): the packaged span of the translates of a cut vector, and the unfolded
-- span read at one of those translates. The vector `fun g => x (g * adelicArchGLIncl F (ι κ))` is a
-- member of the packaged span by construction, so the third conjunct of the package is exactly the
-- cut membership the unfolded row consumes.
example (F : Type) [Field F] [NumberField F]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : ArchTypeFamily F) (x : AdelicGL2 (𝓞 F) F → ℂ) (hxc : Continuous x)
    (hxt : x ∈ archCutSubmodule F tys)
    (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun κ :
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
        fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ)))) ∧
      Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
        fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) ≤ archCutSubmodule F tys ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          ψ = rightTranslate F k (fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ)))}) := by
  obtain ⟨hfd, -, hle, -⟩ :=
    finiteDimensional_span_translates_of_mem_archCutSubmodule F ι hι tys x hxc hxt
  exact ⟨hfd, hle,
    finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule F tys
      (hle (Submodule.subset_span ⟨κ, rfl⟩))⟩

-- Zone B (`M4` then the projector): the kernel reproduces `v 1`, and the projector fixes every
-- vector of the kernel's space. The kernel's existence is the reproducer's headline; the fixed-point
-- property is the first conjunct of the projector's API, fed with the two hypotheses the reproducer
-- requires of `E`.
example (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : ArchTypeFamily F) (E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hE : FiniteDimensional ℂ ↥E) (hEc : ∀ v ∈ E, Continuous v)
    (hEt : E ≤ archCutSubmodule F tys)
    (hEK : ∀ v ∈ E, ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      (fun x => v (x * adelicArchGLIncl F (ι κ))) ∈ E)
    (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : v ∈ E) :
    (∃ e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ,
        Continuous e ∧
          (∀ κ κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
            e (κ' * κ * κ'⁻¹) = e κ) ∧
          (∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e κ⁻¹ = conj (e κ)) ∧
          ∫ κ, e κ * v (adelicArchGLIncl F (ι κ)) ∂μ = v 1) ∧
      (∃ Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
        (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ) ∧
        Q v = v) := by
  obtain ⟨e, heC, hconj, hinv, -, -, hrep⟩ :=
    exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
      F μ ι hι tys E hE hEc hEt hEK
  refine ⟨⟨e, heC, hconj, hinv, by simpa using hrep v hv 1⟩, ?_⟩
  obtain ⟨Q, hQ, -, -⟩ := AutomorphicForm.ArchCutProjector.exists_archCutProjector F tys
  exact ⟨Q, hQ, hQ v (hEc v hv) (hEt hv)⟩

end AutomorphicFormSetAF3Consumer
