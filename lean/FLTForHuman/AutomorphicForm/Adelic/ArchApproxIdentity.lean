/-
  The archimedean approximate identity, the headline.

  This façade carries exactly one declaration — the consumed headline
  `AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`,
  stated from its pin wrapper and proved by `Q09.main`
  (`AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean`). The development of
  the four supporting movements stays tier 3: `RepTheory/TypeReproducer.lean` (Q3),
  `RepTheory/ConvolutionLimit.lean` (Q4), `ArchApproxIdentity/Instantiate.lean` (Q5a),
  preceded by the landed adèlic half `ArchApproxIdentity/ArchInfra.lean` and
  `…/EntryBall.lean` and the definition gate `AutomorphicForm/Adelic/ArchHaar.lean`.
  Nothing else is declared here: the checker iterates every public declaration of a
  listed module, so anything extra would inflate the `identical` delta.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.Instantiate

set_option autoImplicit false

open NumberField AutomorphicForm

namespace AutomorphicForm

-- pin: solution (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:3142)
theorem exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
    (L : Type) [Field L] [NumberField L] (tys : ArchTypeFamily L)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (harch : f ∈ archCutSubmodule L tys) :
    ∃ fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ),
      (∀ n, IsArchTestFactor L (fa n) ∧ IsArchFactorBiFinite L tys (fa n)) ∧
      ∀ g, Filter.Tendsto
        (fun n => letI := glBorelOf (InfiniteAdeleRing L)
          ∫ y, f (g * adelicArchGLIncl L y) * fa n y ∂(archHaarK L))
        Filter.atTop (nhds (f g)) :=
  Q09.main L tys f hf harch

end AutomorphicForm
