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

## 5. Pause note (2026-09-30)

Session paused on the hourly quota **before** the 3.3b/c/d review (human instruction:
hold review too). In flight when paused: three port workers dispatched in parallel —
3.3b `Tate/ChainRule.lean`, 3.3c `Tate/Agreement.lean`, 3.3d `Tate/TraceCompat.lean` —
each doing its own mathlib scouting and writing `AUDIT-mathlib-p3-3{b,c,d}.md` per the
WORKFLOW change (the parallel audit subagent was retired). Their reports may or may not
have landed before the pause.

**On resume:** run the review gate on each report (baseline checker **3779 / 0 / 0 /
30**, per-module `lake build`, `.olean` mtimes, `#print axioms`, hygiene), then set
**3.4** (`residueTraceCompletionCommute` + `completionTraceSum_of_isSeparable`) and
finally re-dispatch the two gated **3.2g** headlines
(`P1/DivPow.lean` + `P1/PerfectBase.lean`). No review was performed before the pause.

### Pause debt — parallel-set duplication (3.3b/c/d)

Each pin `tate*` `S_` file re-proves a shared prelude, so dispatching 3.3b/c/d in
parallel produced **name collisions**: `Tate/TraceCompat.lean` shares 37 last names
with `Tate/Agreement.lean` (3.3c) and 21 with `Tate/ChainRule.lean` (3.3b) — e.g.
`finrankTrace_comp_comm`, `SameRangeIdemProjectors`, `KwF4gRRTateProjectorIndep` /
`kwF4gRRTate_projectorIndep`, `tateProj_idem`, `alphaMap` / `mulOnRange` /
`deltaQuotFactor`, the `tateComm*_add_fst` family. A consumer importing two of the
three collides, and the checker's `identical` count is inflated by the copies. **On
resume, before 3.4:** hoist the shared prelude once (suggested `Tate/ProjectorPrelude.lean`
or into `Defs/TateResidueCurrency.lean`) and delete the per-set copies — a bounded
refactor round ending in one whole-tree build. The 3.3a InlineSpecific
`completionIdeal` chain (`private` in `Tate/CommFinite.lean`) is unchanged debt.

### Pause state — 3.3b/c/d all settled (unreviewed)

All three workers finished before the pause; none reviewed, none committed. Reported
modules: `Tate/ChainRule.lean` (3.3b, 1,097 ln), `Tate/Agreement.lean` (3.3c, 3,921 ln;
`_v2` twin dropped), `Tate/TraceCompat.lean` (3.3d, 3,205 ln). Last reported checker:
**4065 identical / 0 mismatched / 0 missing / 30 own-proof** (4095 checked); each
worker's own build green. Audits `AUDIT-mathlib-p3-3{b,c,d}.md` written by the workers.

**Resume debt to clear (before 3.4):**
1. **Parallel duplication** (see above) — hoist the shared projector/prelude once and
   delete the per-set copies.
2. **`kwHgfV352_localResidueCompletion` twice**: public in `Defs/TateResidueCurrency.lean`
   and `private` in `P1/DivPow.lean`; DivPow's public `_spec`/`_algebraMap` are stated
   about the private copy, so 3.3c re-proved `_spec₀`/`_algebraMap₀` privately. Drop
   the DivPow private def and restate those two facts about the Defs def.
3. **InlineSpecific chain** re-landed `private` in `Tate/CommFinite.lean` (3.3a) and
   `Tate/Agreement.lean` (3.3c); named future home `Place/Completion.lean`.

### Collision measurement (manager, 2026-09-30)

Declared-name detector over the three modules: **25 public FQNs duplicate between
`Tate/ChainRule.lean` and `Tate/TraceCompat.lean`**, all under
`ModularCurve.KwF4gRRTate.*` (`finrankTrace_{add,neg,zero,sub,congr,sub_eq,comp_comm,eq_trace_on_superspace}`,
`instFinDimRange{Add,Neg,Zero,Sub}`, `tateComm{,Restrict,Trace,Res}_add_fst`,
`alphaMap`/`finiteDimensional_range_alphaMap`/`range_{sub_le,comp_map_left}`,
`tateProj_idem`, the pole-window pair). `Tate/Agreement.lean` declares no public
overlap (its copies are private). So the dedup is bounded to these 25 and is a hard
prerequisite for any module importing both — which 3.4 does. Home: a new
`Tate/Prelude.lean` (theory; they are `finrankTrace`/`tateComm` lemmas over
`Defs/TateResidueCurrency`), or `Defs/TateResidueCurrency.lean` for the defs.

### Correction — the 3.3 dedup was incomplete (2026-09-30)

The first hoist round's detector keyed on fully-qualified names and wrongly reported
`Tate/Agreement.lean` as collision-free; its copies are **public**. A checker-faithful
detector found **22 more public collisions**: 5 Agreement↔Prelude (`tateProj_idem`,
`alphaMap`, `finiteDimensional_range_alphaMap`, `kwF4gRRTate_poleWindowImageFinite`)
and 17 Agreement↔TraceCompat (`principalPart_mul_zero_of_mem_integers`,
`tateCommRestrict_single_term`, `pA_fixes_range`/`pA'_fixes_range`,
`delta_zero_on_range`, `delta_range_subset`, `KwF4gRRTateProjectorIndep`,
`tateCommRestrict_diff`, `deltaQuotFactor{, _apply}`, `ker_pA'_inf_integers`,
`finiteDimensional_ker_pA'_inf_poleWindow`, `finiteDimensional_principalPart_pA'_range`,
`kwF4gRRTate_commFiniteGen`, `instFinDimRangeDeltaAlpha`,
`instFinDimRangeMulDeltaAlpha`, `finrankTrace_term_eq`, `kwF4gRRTate_projectorIndep`).
Set 3.4 does the bounded Agreement refactor (import Prelude+TraceCompat, delete the 22,
keep the headline and unique rows), then re-runs the detector across all four Tate
modules to confirm **0** shared public FQNs. Detector lesson: compare with the
checker's namespace tracking, not on `qual` alone.
