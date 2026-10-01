# Work order — P3.2f: the row-2 sibling atom tails (ℙ¹ residue endings)

**Status: ready to dispatch.** Row 2 residual of [PORTING-RR.md](../PORTING-RR.md) §3,
after 3.2e and the R1 definitions round ([PLAN-RECTIFY-DEFS.md](PLAN-RECTIFY-DEFS.md)
§5.1). Method: [porting-playbook.md](../porting-playbook.md) §2–§5; build economy
[PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3.

Baseline: checker **3645 identical / 0 mismatched / 0 missing / 30 own-proof**
(3675 checked); all modules green. Pin `anthropics/fermats-last-theorem@aa2d8b3`,
port mathlib `v4.34.0`.

## 0. Scope

The master ℙ¹ file is fully ported into the `P1/` chain
(`P1/EnginePrelude` … `P1/PerfectResidue` → `P1/Core`). Its three **sibling atom
files** still have unique tails. Port only those tails; the shared engine is already
in `P1/` and must be **imported, not re-proved**. Row 6 (the K ending) is **out of
scope**.

| # | pin file (`P2M/Sol/`) | ln | decls | measured delta |
|---|---|---:|---:|---|
| 1 | `S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero.lean` | 5,776 | 186 | 132 substituted (3,759 ln); 2 new private helpers |
| 2 | `S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean` | 2,150 | 108 | 43 substituted (908 ln); 3 new private helpers |
| 3 | `S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean` | 4,340 | 120 | 62 substituted (2,538 ln); 0 new helpers |

The measurements are already generated (do not re-run unless the target changes):
`tools/deps/build/p32f_{atom2,atom3,pfbase}.{json,log}`, from
`port_advise.py --target P2M/Sol/<file> --json build/p32f_<name>.json`.

## 1. Deliverables

Three new modules, each importing the `P1/` chain (import the narrowest sufficient
member; `P1/Core` is the chain head and is always safe):

| module | content |
|---|---|
| `FLTForHuman/AlgebraicCurve/P1/TwoPlace.lean` | the atom-2 two-place-cancellation tail (`…finitePlace_add_trace_localResidue_placeInfty_eq_zero`) |
| `FLTForHuman/AlgebraicCurve/P1/DivPow.lean` | the atom-3 tail (`…finitePlace_div_pow_eq_zero`) |
| `FLTForHuman/AlgebraicCurve/P1/PerfectBase.lean` | the PF base case `residueTheorem_ratFunc_of_perfectField` |

Statements **verbatim from the pin**, at the pin's binders. The pin's ℙ¹ files use
`placeInfty`; the port has both `RationalFunctionField.placeInfty` and the
`@[reducible]`/`rfl` twin `p1PlaceInfty`, with
`RationalFunctionField.placeInfty_eq_p1PlaceInfty : placeInfty = p1PlaceInfty`.
State the atom declarations at the pin's `placeInfty` spelling and discharge them
from the `p1PlaceInfty` versions with
`rw [RationalFunctionField.placeInfty_eq_p1PlaceInfty]` (or `rfl`) where needed.

**New public names** the checker must see (spell from the `Theorems/Thm_*` wrappers):
`RationalFunctionField.trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero`,
`RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero`,
`AlgebraicCurve.residueTheorem_ratFunc_of_perfectField` (and any other public rows
the tails add beyond the 237 already substituted).

## 2. Reuse (import, do not re-prove)

- `port_advise` reports 237 of the 414 declarations already identical in the port.
  Import them; never re-transcribe.
- The `placeInfty`/`p1PlaceInfty` name-variants are the pin's deliberate twins (the
  pin shipped the same engine under both spellings): prefer a one-line `rfl`/`rw`
  wrapper over a re-proof. `port_advise` §3 lists them per file.
- `ord_add_eq_min` and `ord_add_eq_left` are `private` in the port
  (`LocalResidue/Calculus.lean`, `P1/EnginePrelude.lean`). Per the stop-early
  protocol, **re-land them `private` verbatim in the consuming module** and report
  the pin `file:line` as promotion debt — do **not** promote a pin-private helper to
  public: the R1 round showed that exposing a re-landed private copy to the checker
  produced a binder mismatch (`Place.differentialCoeff_add''`).

## 3. Known genuinely-new helpers

| file | helper | pin line | ln |
|---|---|---:|---:|
| atom 2 | `ord_eq_neg_log_of_valuationSubring_eq` | 1643 | 37 |
| atom 3 | `gen` (def) | 1446 | 4 |
| atom 3 | `isIntegral_gen` | 1470 | 7 |
| atom 3 | `ord_neg'` | 1342 | 4 |

## 4. Build discipline (verbatim)

```bash
# edit loop: writes no .olean, recompiles nothing
timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>
# a finished module
flock /tmp/flt_for_human.lock timeout 240 lake build <module>
```

- Every set lands in **new** files; do not edit an existing module.
- No bare whole-tree `lake build`; serialize every build under `flock`/`timeout`.
- Never raise the heartbeat cap; no `sorry`/`admit`/`axiom`; no `import Mathlib` in a
  library module.

## 5. Checker wiring + verification

- `SOURCES` (`lean/spec/check_flt_statements.py`): append the three
  `Theorems/Thm_AlgebraicCurve_…` wrappers **first**, then the three
  `P2M/Sol/S_AlgebraicCurve_…` files, appended last so no earlier last-name match
  flips.
- `PORT_FILES`: append `P1/TwoPlace.lean`, `P1/DivPow.lean`,
  `P1/PerfectBase.lean` last.
- Statements verbatim; a substitution is imported, never re-stated.

```bash
cd lean
python3 spec/check_flt_statements.py                       # 0 mismatched / 0 missing
flock /tmp/flt_for_human.lock timeout 240 lake build FLTForHuman.AlgebraicCurve.P1.TwoPlace
flock /tmp/flt_for_human.lock timeout 240 lake build FLTForHuman.AlgebraicCurve.P1.DivPow
flock /tmp/flt_for_human.lock timeout 240 lake build FLTForHuman.AlgebraicCurve.P1.PerfectBase
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/RiemannRochConsumer.lean
```

## 6. Stop-early / gaps

If a proof reaches a declaration outside the four measured files, resolve it locally
`private` with the statement verbatim and report the pin `file:line` as promotion
debt. Do not inline new mathematics and do not edit a frozen module. If a public row
is already in the port under a different binder (the §3 generalise list), take the
pin wrapper's binders and adapt.

## 7. Report shape

Report: the three module paths and line counts; the checker line (identical /
mismatched / missing / own-proof); the per-module build results and `.olean` mtimes;
`#print axioms` on every public node; the promotion-debt list; the friction-log
entry; and any row that could not be discharged (with the reason).
