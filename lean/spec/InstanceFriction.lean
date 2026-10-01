/-
  The live half of the typeclass-instance friction register
  (`FLTForHuman/../instance-friction.md`).

  Every entry in that register gets one block here, and the block must **compile
  at the default `synthInstance` budget** so the *fix* stays cheap: if the fix is
  reverted the example stops elaborating. The *naive* form that timed out is kept
  as a comment beside it, never as a live command (a deliberate timeout would make
  this file's error count useless as a guard).

  This file is deliberately in `spec/`, outside every library: `lake build` does
  not see it, so an accumulating, occasionally slow harness can never slow or
  break the verified port. Run it by hand:

      cd lean
      lake env lean spec/InstanceFriction.lean 2>&1 | grep -c error     # want 0

  Adding an entry (keep the register and this file in step):

  1. add the row + section to `instance-friction.md` (`IF-NNN`, kind, where, goal,
     symptom, budget, cause, fix, status);
  2. add an `IF-NNN` block here: the fixed form as a compiling `example`, the
     naive form as a comment with its exact failure text;
  3. bound the snippet (`set_option synthInstance.maxHeartbeats N in` if it is
     genuinely slow) so the harness itself never becomes the hog.
-/
import FLTForHuman.ModularCurve.Degree.PlaceDegree

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField ModularCurve

namespace InstanceFriction

/-! ## IF-001 — `Algebra.IsAlgebraic` over an `adjoin` of a big subtype term

Search cost: the `Algebra.IsAlgebraic` goal below times out at the default 20000
heartbeats even when the element is named; supplying `Algebra.IsAlgebraic.of_finite`
explicitly is instant. The register entry has the full diagnosis. -/

/-- The `j(q)` element of the bar field, named once so the `adjoin … {jBar M}` term
in the `FiniteDimensional` instance and in the goal are syntactically equal. -/
private abbrev jBar (M : ℕ) [NeZero M] : modularFunctionFieldBar M :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full M)⟩

-- Naive form, for the record — `inferInstance` for this goal fails with:
--   failed to synthesize
--     Algebra.IsAlgebraic ↥(AlgebraicClosure ℚ)⟮jBar M⟯ ↥(modularFunctionFieldBar M)
--   (deterministic) timeout at `typeclass`, maximum number of heartbeats (20000)
--   has been reached
--
-- example (M : ℕ) [NeZero M]
--     [FiniteDimensional
--       (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar M} : Set (modularFunctionFieldBar M)))
--       (modularFunctionFieldBar M)] :
--     Algebra.IsAlgebraic
--       (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar M} : Set (modularFunctionFieldBar M)))
--       (modularFunctionFieldBar M) :=
--   inferInstance

/-- IF-001 guard: the explicit `of_finite` form elaborates at the default budget. -/
example (M : ℕ) [NeZero M]
    [FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar M} : Set (modularFunctionFieldBar M)))
      (modularFunctionFieldBar M)] :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar M} : Set (modularFunctionFieldBar M)))
      (modularFunctionFieldBar M) :=
  Algebra.IsAlgebraic.of_finite _ _

end InstanceFriction

end
