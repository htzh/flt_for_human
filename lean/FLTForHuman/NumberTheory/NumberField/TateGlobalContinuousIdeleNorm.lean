/-
  The `continuous_ideleNorm` façade.

  Two consumed headlines, each stated from its pin `Theorems/` wrapper and proved by the
  shared `NumberField.TateGlobal.FujisakiC3` engine
  (`FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiC3.lean`):

  * `NumberField.TateGlobal.continuous_ideleNorm` — continuity of the idele norm;
  * `NumberField.TateGlobal.continuous_ideleNorm_det` — the `GL₂` corollary, the norm of
    the determinant through `Matrix.GeneralLinearGroup.det`.

  The thin façade exists so that consumers of the idele norm's continuity import the
  engine's cone only, and not the three T1 analytic-core caps; see
  `topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md` §4–§5.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`; the wrappers are
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm_det.lean
  and the proof silos are `P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm*.lean`
  of the same pin.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.FujisakiC3
import FLTForHuman.AutomorphicForm.Adelic.Basic
import Mathlib.Topology.Algebra.Group.Matrix

set_option autoImplicit false

open NumberField AutomorphicForm

namespace NumberField
namespace TateGlobal

theorem continuous_ideleNorm (F : Type) [Field F] [NumberField F] :
    Continuous (NumberField.TateGlobal.ideleNorm F) :=
  FujisakiC3.continuous_ideleNorm (F := F)

theorem continuous_ideleNorm_det (F : Type) [Field F] [NumberField F] :
    Continuous fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
  (continuous_ideleNorm F).comp Matrix.GeneralLinearGroup.continuous_det

end TateGlobal
end NumberField
