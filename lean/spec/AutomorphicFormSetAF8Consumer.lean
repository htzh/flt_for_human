/-
  Cross-module wire test for SET-AF8 (the cusp-subrepresentation bridge).

  A `spec/` probe, not a library module. One zone, and it is a real composition, not a `#check`:
  the AF8 headline `AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep` supplies the
  membership `rightConv F (rightTranslate F h φ) f ∈ V`, and SET-AF5's
  `continuous_rightConv_and_contDiff_of_isFactorizableTestFn` supplies the regularity of the *same*
  convolution — applied to the right translate `rightTranslate F h φ`, whose continuity comes from
  `continuous_rightTranslate` once `φ` is known continuous.

  Both outputs are therefore *derived* from the two headlines rather than assumed: the zone returns
  the pair `⟨membership, continuity⟩`. The continuity input `Continuous φ` is not a hypothesis of
  the example — it is read off `IsCuspSubrep.le : V ≤ cuspKFiniteSubmodule F pins ξ` together with
  `CuspidalConstituent.TSMain.continuous_of_mem_cuspKFiniteSubmodule`, exactly as the AF8 proof
  itself obtains it. Delete `RightConvSubrep.lean` (or `RightConvRegularity.lean`) and the example
  dies.

  The probe imports only the set's own module and the modules it consumes.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.RightConvSubrep
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent

namespace SetAF8CuspSubrepConsumer

variable {F : Type} [Field F] [NumberField F]

/-- Zone A: the AF8 headline (membership in the cuspidal subrepresentation) composed with
SET-AF5's regularity theorem (continuity of the right convolution by a factorisable test
function), both at the right translate `rightTranslate F h φ`; the continuity of `φ` needed by
SET-AF5 is derived from the `K`-finiteness half of `IsCuspSubrep`, not assumed. -/
example (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F pins ξ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ V)
    (h : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    rightConv F (rightTranslate F h φ) f ∈ V ∧ Continuous (rightConv F (rightTranslate F h φ) f) := by
  have hφc : Continuous φ := TSMain.continuous_of_mem_cuspKFiniteSubmodule F (hV.le hφ)
  exact ⟨rightConv_rightTranslate_mem_of_isCuspSubrep F pins ξ tys V hV φ hφ h f hf hft,
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn F (rightTranslate F h φ)
      (continuous_rightTranslate F hφc h) f hf).1⟩

end SetAF8CuspSubrepConsumer
