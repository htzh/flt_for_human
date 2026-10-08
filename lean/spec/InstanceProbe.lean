/-
  The live *capture* half of the typeclass-instance friction register
  ([../instance-friction.md](../instance-friction.md)).

  One `#probe` per register entry, printing the term instance search picks — or
  `FAIL` when it picks none. Unlike `spec/InstanceFriction.lean` (whose job is to be
  green on the *fix*), a `FAIL` here is expected and is not an error: the point is to
  *watch* the search, including the searches that are supposed to fail. The file
  stays green and its `PROBE …` lines are the signal, which
  [`check_instance_probes.py`](check_instance_probes.py) compares against the
  recorded value:

      cd lean
      lake env lean spec/InstanceProbe.lean | grep '^PROBE'   # the raw capture
      python3 spec/check_instance_probes.py                   # compare + report

  Why this exists. An instance brick is a cache of a synthesis result (playbook §6,
  "capture what search picked"): its key is the goal's exact spelling and its value
  is the term search would have built. A stale key is *invisible* rather than wrong,
  and a wrong value for a data-valued class surfaces only much later as a hard
  `Type mismatch`. So the two things worth re-measuring after a mathlib bump or a
  spelling change are (a) that the failing spelling still fails, and (b) that the
  working spelling still yields the recorded term. That is exactly what this file
  pins. `#probe` is `#synth` with the failure caught and the answer labelled.

  Adding an entry: add the `#probe` here, add its name and expected line to the
  `EXPECTED` table in `check_instance_probes.py`, and record the captured term in
  the register. Keep the probe file cheap; a probe whose *type* is expensive to
  elaborate does not belong here.
-/
import Lean
import FLTForHuman.ModularCurve.Degree.PlaceDegree
import FLTForHuman.WeierstrassCurve.Isogeny.IntermediateField

open Lean Elab Command Term Meta

set_option autoImplicit false

/-- `#probe <name> : <type>` tries to synthesize an instance of `<type>` and reports
`PROBE <name> => OK <term>` or `PROBE <name> => FAIL`, never raising an error. -/
elab "#probe " n:ident " : " t:term : command => do
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_probe_cmd do
    let ty ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let res ← try
        let inst ← synthInstance ty
        pure (some inst)
      catch _ => pure none
    match res with
    | some inst => logInfo m!"PROBE {n.getId} => OK {inst}"
    | none      => logInfo m!"PROBE {n.getId} => FAIL"

noncomputable section

open AlgebraicCurve IntermediateField ModularCurve WeierstrassCurve

namespace InstanceProbe

/-! ## IF-001 — `Algebra.IsAlgebraic` over an `adjoin` of a big subtype term

The element of the bar field, named once so the `adjoin … {jBar M}` term in the
`FiniteDimensional` instance and in the goal are syntactically equal. -/

private abbrev jBar (M : ℕ) [NeZero M] : modularFunctionFieldBar M :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full M)⟩

variable (M : ℕ) [NeZero M]
  [FiniteDimensional
    (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar M} : Set (modularFunctionFieldBar M)))
    (modularFunctionFieldBar M)]

/- IF-001 naive form: expected `FAIL` — a `synthInstance` timeout at 20000, even
with the element named. There is no captured term for this entry: the fix bypasses
search with `Algebra.IsAlgebraic.of_finite _ _`, which is a direct application, not
an instance. If this ever prints `OK`, the entry can be retired. -/
#probe IF001_naive :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar M} : Set (modularFunctionFieldBar M)))
      (modularFunctionFieldBar M)

/-! ## IF-002 — applying `mem_intFormRatiosC` over a `Subgroup` coercion

No probe: the cost is a *named-constructor application* (`whnf`/defeq in the
elaborator), not an instance search, and it does not terminate rather than fail —
so there is no term to capture and no label to print. Its guard is the module build
plus `build_ladder.py --profile` ([../instance-friction.md](../instance-friction.md)
IF-002). -/

/-! ## IF-003 — an instance keyed on a semireducible `def` (`WeierstrassCurve.baseChange`)

`WeierstrassCurve.baseChange` is a semireducible `def`, so search — which runs at
reducible transparency — cannot unfold `E⁄R` to `E.map (algebraMap R R)` and cannot
reach mathlib's `(W.map f).IsElliptic`. The pin bridges the two spellings with
`inferInstanceAs`, which elaborates at default transparency. -/

variable {R : Type} [Field R] (E : WeierstrassCurve R) [E.IsElliptic]

/- IF-003 at the goal's own spelling: expected `FAIL` (at every budget). -/
#probe IF003_goal : (WeierstrassCurve.baseChange E R).IsElliptic

/- IF-003 at the spelling search can handle: the captured term the brick must
reproduce. `IsElliptic` is a `Prop`, so no `rfl` value guard is needed. -/
#probe IF003_map : (E.map (algebraMap R R)).IsElliptic

end InstanceProbe

end
