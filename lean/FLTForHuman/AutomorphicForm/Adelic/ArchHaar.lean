/-
  The archimedean Haar measure on `GL₂(𝔸_{K,∞})`.

  `glBorelOf` is the Borel σ-algebra of `GL₂(R)` for a topological ring `R` — the
  pin's `@[reducible] def`, deliberately *not* a registered `MeasurableSpace`
  instance, so it cannot diamond with mathlib's Borel instance — and `archHaarK` is
  Haar measure on `GL₂(𝔸_{K,∞})` against it. These are the statement-critical
  definition half of the archimedean approximate identity
  (`AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`);
  the finite-place twisted-orbital subject of the same pin file is a separate wave
  (`topics/automorphicForm/TOPIC-archTestFactor-family.md` §5).

  Transcribed from `Definitions/Def_AutomorphicForm_TwistedOrbital.lean:57–59,401–410`
  (pinned `aa2d8b3`), the `Borel` and `Archimedean` sections. The pin's file-wide
  `variable` context is carried per declaration; `archHaarK` uses only `K`, so the
  pin's `L`/`σ` are auto-omitted exactly as at the pin.

  The `letI`/`haveI` wall in `archHaarK` is load-bearing: it feeds instance search
  the Borel structure and the archimedean local compactness. `InfiniteAdeleRing` is
  a `def`, so the matrix/`GL₂` instances are supplied through `inferInstanceAs` and
  `Units.isClosedEmbedding_embedProduct.locallyCompactSpace` rather than left to
  unfold the Pi type.
-/
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import Mathlib.Topology.Algebra.Group.Units

set_option autoImplicit false

open NumberField MeasureTheory
open scoped RestrictedProduct Topology

noncomputable section

namespace AutomorphicForm

section Borel

variable (R : Type) [CommRing R] [TopologicalSpace R]

-- pin: glBorelOf (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:57)
@[reducible] def glBorelOf : MeasurableSpace (GL (Fin 2) R) := borel _

-- pin: borelSpace_glBorelOf (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:59)
theorem borelSpace_glBorelOf : @BorelSpace (GL (Fin 2) R) _ (glBorelOf R) :=
  @BorelSpace.mk _ _ (glBorelOf R) rfl

end Borel

section Archimedean

variable (K : Type) [Field K] [NumberField K]

-- pin: archHaarK (Definitions/Def_AutomorphicForm_TwistedOrbital.lean:401)
def archHaarK : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (glBorelOf (InfiniteAdeleRing K)) := by
  letI := glBorelOf (InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing K)
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact Measure.haar

end Archimedean

end AutomorphicForm
