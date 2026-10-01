# Plan — row 3.3 (Tate agreement) and row 3.4 (trace-completion commutation)

**Status: 3.3a dispatched.** Row 3.3/3.4 of [PORTING-RR.md](../PORTING-RR.md) §3,
opened 2026-09-30 after 3.2f landed and the two row-2 headlines were found gated on
this row (see [PLAN-P3-2.md](PLAN-P3-2.md) §3.7 and
[WORKORDER-P3-2f-tails.md](WORKORDER-P3-2f-tails.md)). Row 6 (the K ending) is out of
scope.

Method: [porting-playbook.md](../porting-playbook.md) §2–§5; build economy
[PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3. Baseline: checker **3701
identical / 0 mismatched / 0 missing / 30 own-proof** (3731 checked). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib `v4.34.0`.

## 1. Measurement

`tools/deps/build/p33_advise.{log,json}` from
`port_advise.py --targets build/p33_targets.txt --pool sources`: 17 target files
(8 `S_` + 8 `Thm_` wrappers + the `Def_` file), 755 declarations; **89 declarations
already identical in the port (≈2,906 ln)**, 13 only as port-private, 25 under a
different statement. `tateAgreement`/`tateAgreement_v2` and
`residueTraceCompletionCommute`/`_v2` are byte-identical twins: port **one** name per
piece (`tateAgreement`, `residueTraceCompletionCommute`), drop the `_v2` spellings
(PORTING-RR §3 name policy). The ≈8,000-written row-3.3 estimate stands; per-set
measurement is the work order's first step.

## 2. Set boundaries

The four `tate*` files import only `Def_AlgebraicCurve_TateResidueCurrency` (plus the
instance for `tateAgreement`), **not each other** — so they are independent given the
shared defs. `residueTraceCompletionCommute` imports all four `tate*` wrappers.

| set | pin files (`P2M/Sol/`, `Definitions/`) | raw | decls | home |
|---|---|---:|---:|---|
| **3.3a** | `Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean` (449) + `S_AlgebraicCurve_tateCommFinite.lean` (1,257) | 1,706 | 27 + 53 | `Defs/TateResidueCurrency.lean` + `Tate/CommFinite.lean` |
| **3.3b** | `S_AlgebraicCurve_tateChainRule.lean` | 2,832 | 108 | `Tate/ChainRule.lean` |
| **3.3c** | `S_AlgebraicCurve_tateAgreement.lean` | 4,816 | 173 | `Tate/Agreement.lean` |
| **3.3d** | `S_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean` | 4,418 | 145 | `Tate/TraceCompat.lean` |
| **3.4** | `S_AlgebraicCurve_residueTraceCompletionCommute.lean` (1,109) + `S_AlgebraicCurve_completionTraceSum_of_isSeparable.lean` (867) | 1,976 | 15 + 38 | `Tate/TraceCompletionCommute.lean` + `Tate/CompletionTraceSum.lean` |
| **3.2g** | re-dispatch the two gated row-2 headlines | — | — | `P1/DivPow.lean` + `P1/PerfectBase.lean` |

New theory home: `lean/FLTForHuman/AlgebraicCurve/Tate/`. The shared definitions land
**once** in `Defs/TateResidueCurrency.lean` (the `tateComm`/`tateCommTrace`,
`kaehlerPullback`/`kaehlerCotrace`, `kwHgfV352_*`, `KwF4gRRTate*`, `KwF4R1V391a*`
rows), which is why every later set imports it rather than re-declaring.

## 3. Sequence

`3.3a` first (the shared defs + `tateCommFinite`). Then `3.3b`/`3.3c`/`3.3d` are
mutually independent and can be dispatched in parallel; `3.4` consumes all four;
`3.2g` consumes `3.4`.

## 4. Verification (per set)

`lake build` each new module under `flock`; no whole-tree build unless an existing
module is edited; checker `0 mismatched / 0 missing`; `#print axioms` on the public
nodes → `[propext, Classical.choice, Quot.sound]`; hygiene clean; `SOURCES` (wrappers
first, then `S_`/`Def_`) and `PORT_FILES` appended last; scratch removed; friction-log
entry.
