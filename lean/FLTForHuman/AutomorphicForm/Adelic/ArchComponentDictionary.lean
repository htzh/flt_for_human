/-
  The archimedean component dictionary.

  `archComponent F v` is the projection of an archimedean adelic matrix onto its
  `v`-component. `ext_archComponent` says that the product of the one-place
  projections is injective, and `adelicArchGLIncl_iota_mulSingle` identifies the
  archimedean inclusion of the one-place factor `Pi.mulSingle w k` of any product
  homomorphism `ι` (one whose `archComponent` at `w` is `k`) with the one-place
  row-isometry inclusion `rowIsometryInclAt₀`.

  Both are pin-`private` helpers that the pin copies into every `S_` file of the
  finite-dimensionality cluster, so the port writes them once, public, at the pin's
  names: two modules of the cluster (the span module and the reproducing-kernel
  module) consume them, and neither is the other's premise.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule.lean:23–45`
  and
  `P2M/Sol/S_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule.lean:486–507`
  (pinned `aa2d8b3`), where the two statements are identical. The pin's local
  namespaces (`F4CutWords`, `TypeIdem`) are dropped: the declarations are
  `AutomorphicForm`'s, as their statements are.

  spec-pin: P2M/Sol/S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace

set_option autoImplicit false

open NumberField NumberField.AdelicLevel

noncomputable section

namespace AutomorphicForm

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem ext_archComponent {g g' : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ v : InfinitePlace F, archComponent F v g = archComponent F v g') : g = g' := by
  refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
  have := congrArg (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion) i j)
    (h v)
  simpa only [archComponent_apply] using this

theorem adelicArchGLIncl_iota_mulSingle [DecidableEq (InfinitePlace F)]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    adelicArchGLIncl F (ι (Pi.mulSingle w k)) = rowIsometryInclAt₀ F w k := by
  have : ι (Pi.mulSingle w k) = archGLIncl F w (k : GL (Fin 2) w.Completion) := by
    refine ext_archComponent fun v => ?_
    rw [hι]
    by_cases hv : v = w
    · subst hv
      rw [Pi.mulSingle_eq_same, archComponent_archGLIncl_self]
    · rw [Pi.mulSingle_eq_of_ne hv, archComponent_archGLIncl_of_ne F hv]
      rfl
  rw [this, rowIsometryInclAt₀_apply]
  rfl

end AutomorphicForm
