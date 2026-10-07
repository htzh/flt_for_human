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
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.WeierstrassCurve.Isogeny.IntermediateField

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

/-! ## IF-002 — applying `mem_intFormRatiosC` over a `Subgroup` coercion

Cost: the named-constructor application below does not finish within a bounded
budget; the pin's anonymous constructor (what the module uses) is instant. The
guard here is the *fixed* public form — the naive application is a timing failure,
not a compile failure, so it cannot be a live command in this file. -/

-- Naive form, for the record — applying the named constructor at the same
-- witnesses did not terminate within a 300 s wall bound:
--
-- example (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
--     jqModC K ∈ intFormRatiosC K Γ :=
--   mem_intFormRatiosC (e4cube Γ) (delta Γ) (isIntegralQExp_e4cube Γ) (isIntegralQExp_delta Γ)
--     (intSeriesC_delta_ne_zero K)

/-- IF-002 guard: the fixed headline form, which imports and elaborates cheaply. -/
example (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    jqModC K ∈ intFormRatiosC K Γ :=
  jqModC_mem_intFormRatiosC K Γ

/-! ## IF-003 — an instance keyed on a semireducible `def` (`WeierstrassCurve.baseChange`)

Search cost: `WeierstrassCurve.baseChange` is a semireducible `def`, so instance
search cannot unfold `E⁄R` to `E.map (algebraMap R R)` and so cannot reach
mathlib's `(W.map f).IsElliptic` instance. The pin bridges the two spellings with
`inferInstanceAs`, which elaborates at default transparency. The register entry has
the full diagnosis. -/

-- Naive form, for the record — `inferInstance` for the `⁄` spelling fails with:
--   failed to synthesize instance of type class
--     (WeierstrassCurve.baseChange E R).IsElliptic
--
-- example {R : Type} [Field R] (E : WeierstrassCurve R) [E.IsElliptic] :
--     (WeierstrassCurve.baseChange E R).IsElliptic := inferInstance

/-- IF-003 guard: the pin's `inferInstanceAs` bridge elaborates at the default budget. -/
example {R : Type} [Field R] (E : WeierstrassCurve R) [E.IsElliptic] :
    (WeierstrassCurve.baseChange E R).IsElliptic :=
  inferInstanceAs ((E.map (algebraMap R R)).IsElliptic)

end InstanceFriction

end
