/-
  The integral lattice of cusp forms and the full-rank predicate.

  `intLattice N k` is the `ℤ`-span of the cusp forms whose `q`-coefficients are
  all integral; `HasIntegralStructure N k` says that span is all of the
  `ℂ`-space (the lattice is full-rank). Both are the pin's definitions, verbatim
  from `Definitions/Def_CuspForm_IntegralStructure.lean` (pinned `aa2d8b3`).

  The lattice-action targets are in `HeckeLattice.lean` (T9); the *existence* of
  `HasIntegralStructure` is T10. The weight-2 auxiliary vocabulary of T10's
  `Defs/IntegralLattice.lean` is a different object with different names.
-/
import FLTForHuman.ModularForms.HeckeQCoeff

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularFormClass

/-- The `ℤ`-span of the cusp forms with integral `q`-coefficients. Transcribed
verbatim from `Definitions/Def_CuspForm_IntegralStructure.lean`. -/
def intLattice (N : ℕ) (k : ℤ) : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  Submodule.span ℤ {f | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)}

/-- The lattice is full-rank: its `ℂ`-span is everything. Transcribed verbatim
from `Definitions/Def_CuspForm_IntegralStructure.lean`. -/
def HasIntegralStructure (N : ℕ) (k : ℤ) : Prop :=
  Submodule.span ℂ ((CuspForm.intLattice N k : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :
    Set (CuspForm (CongruenceSubgroup.Gamma0 N) k)) = ⊤

end CuspForm

end
