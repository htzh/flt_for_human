/-
  SET-AF89D1 consumer: bounded genuine ⇒ genuine ⇒ smooth cusp realizable.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/BoundedGenuineRealization.lean` carries the
  bounded genuine cusp realization and its API: `IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable`
  forgets the boundedness data, and `IsBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable`
  does the same after the arithmetic renormalisation. `ProductionPinsGeneral` carries
  `IsGenuineCuspRealizable.isSmoothCuspRealizable`.

  **The reading.** A bounded genuine cusp realization is, in particular, a smooth cusp realization:
  the chain crosses the new module (genuine, forgetting the bound) and the production-pins module
  (smooth, forgetting genuineness). That is the direction the weight-one comparison needs — the
  bounded hypotheses are what the pin's analytic estimates supply, and the conclusion is the
  smooth-cusp interface every consumer takes.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF89D1Consumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.BoundedGenuineRealization

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace AutomorphicFormSetAF89D1Consumer

/-- **The reading.** Bounded genuine cusp realizability implies smooth cusp realizability: forget
the bound (`IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable`), then forget genuineness
(`IsGenuineCuspRealizable.isSmoothCuspRealizable`). -/
theorem isSmoothCuspRealizable_of_isBoundedGenuineCuspRealizable
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : HeckeEigensystem F ℂ)
    (h : IsBoundedGenuineCuspRealizable F pins ψ Φ) :
    IsSmoothCuspRealizable F pins Φ :=
  (IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable h).isSmoothCuspRealizable

end AutomorphicFormSetAF89D1Consumer
