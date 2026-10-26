/-
  The archimedean approximate identity, the headline.

  This façade carries exactly one declaration — the consumed headline
  `AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`,
  stated from its pin wrapper and proved by `ArchApproxIdentity.exists_tendsto_integral_of_mem_archCutSubmodule`
  (`AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean`). The four supporting
  movements are modules of their own and each carries its own wire:
  `RepTheory/TypeReproducer.lean`, `RepTheory/ConvolutionLimit.lean`,
  `ArchApproxIdentity/Instantiate.lean`, on the adèlic half
  `ArchApproxIdentity/{ArchInfra,EntryBall}.lean` and the definition gate
  `AutomorphicForm/Adelic/ArchHaar.lean`. Nothing else is declared here: every public
  declaration of this module is diffed against the wrapper below and the `S_` copy.

  spec-pin: Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.Instantiate

set_option autoImplicit false

open NumberField AutomorphicForm

namespace AutomorphicForm

theorem exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
    (L : Type) [Field L] [NumberField L] (tys : ArchTypeFamily L)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (harch : f ∈ archCutSubmodule L tys) :
    ∃ fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ),
      (∀ n, IsArchTestFactor L (fa n) ∧ IsArchFactorBiFinite L tys (fa n)) ∧
      ∀ g, Filter.Tendsto
        (fun n => letI := glBorelOf (InfiniteAdeleRing L)
          ∫ y, f (g * adelicArchGLIncl L y) * fa n y ∂(archHaarK L))
        Filter.atTop (nhds (f g)) :=
  ArchApproxIdentity.exists_tendsto_integral_of_mem_archCutSubmodule L tys f hf harch

end AutomorphicForm
