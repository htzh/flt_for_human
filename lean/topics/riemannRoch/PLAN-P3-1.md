# Phase 3 — the residue-theorem block: the work-item table is the phase map

**Status: phase 3.1 (row 1, `HasCanonicalLocalResidueKStar`) COMPLETE (2026-09-30).**
Phases 3.2–3.7 are planned only. Phase 3.1 landed `Defs/PlaceCompletion.lean` (541
ln) and `Defs/CanonicalLocalResidueInstanceV2.lean` (1,696 ln); checker 3060 → **3212
identical / 0 mismatched / 0 missing / 30 own-proof** (3090 → 3242 checked); forced
builds green (`PlaceCompletion` 6.8 s, `CanonicalLocalResidueInstanceV2` 12.4 s);
`instHasCanonicalLocalResidueKStar` `[propext, Classical.choice, Quot.sound]`; and
the consumer zone F runs clean, discharging the H3 differentials headline's
instance hypothesis.

The blueprint is [../PORTING-RR.md](../PORTING-RR.md) §3; the phase-1 operative
plan is [PLAN-P1.md](PLAN-P1.md); the phase-2 order is
[WORKORDER-P2-canonical.md](WORKORDER-P2-canonical.md). Method:
[../porting-playbook.md](../porting-playbook.md) §2–§5 — measure, audit mathlib,
dedup, write a work order, dispatch one set per subagent, review between sets.
Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

Baseline before phase 3: checker **3060 identical / 0 mismatched / 0 missing /
30 own-proof** (3090 checked); full `lake build` green (4837 jobs);
`spec/RiemannRochConsumer.lean` 0 errors.

## 0. The rows are phases

`PORTING-RR.md` §3 prices phase 3 as **one union of ≈34,000 written lines over
two endings**. That is far too large for one effort, and its seven-row work-item
table is really a phase map: each row is a self-contained mathematical block with
its own home, its own dispatch and its own review gate. Phase 3 is therefore
executed one row at a time, in table order. The phase-3.1 audit showed row 1 (the
residue instance) is **independent** of the shared core (rows 2–5): the pin's V2
file names nothing from `PlaceCompletion`, so 3.2 can proceed without waiting on
the instance, and 3.1 is not a prerequisite of the residue union.

| phase | row (PORTING-RR §3) | pin raw | written | status |
|---|---|---:|---:|---|
| **3.1** | `HasCanonicalLocalResidueKStar` — `Defs/PlaceCompletion` + `Defs/CanonicalLocalResidueInstanceV2` | 2,702 | **2,247** (551 + 1,696) | **COMPLETE** |
| 3.2 | ℙ¹ core + base case — three `trace_localResidue_*` + `residueTheorem_ratFunc_of_perfectField` + helpers | 29,118 | ≈17,300 | planned |
| 3.3 | Tate agreement — one `tateAgreement` + `tateTraceCompat_of_isSeparable` + `tateChainRule` + `tateCommFinite` | 13,323 | ≈8,000 | planned |
| 3.4 | trace-completion commutation — one `residueTraceCompletionCommute` | 1,109 | ≈525 | planned |
| 3.5 | perfect-field ending — `residueTheorem_of_…residueTraceCompletionCommute` + `residueTheorem_of_perfectField` + helpers | 9,075 | ≈7,050 | planned |
| 3.6 | K ending, marginal over the shared core — `residueTheoremK_ratFunc_of_isAlgClosed` + `residueTheoremK_of_isAlgClosed` + wrappers | 21,300 | ≈2,000 | planned |
| 3.7 | RR assembly — the pin's `MirrorAssembly` against the K ending | ≈300 | ≈400 | planned |

The rows overlap in their shared helpers (they sum to ≈38,000; the union is
≈34,000). The single-copy plan — one ℙ¹ core, one Tate agreement, one
trace-completion commutation, both endings — is the recorded decision of
PORTING-RR §3; the `_v2` names are dropped (one name per piece).

## 1. Phase 3.1 — the `HasCanonicalLocalResidueKStar` instance

### 1.1 What it is

The class `HasCanonicalLocalResidueKStar K F` and its API are **already in the
port** ([`Defs/LocalResidue.lean`](../../FLTForHuman/AlgebraicCurve/Defs/LocalResidue.lean),
landed by H3): `LocalResidueData`, `CanonicalLocalResidueDataK`,
`HasLocalResidue`, `HasCanonicalLocalResidueK`, the class
`HasCanonicalLocalResidueKStar` with `dataKStar`, `localResidue` and its
simp-lemmas, `kaehlerResidueTerm{,K,KFam}`, `weilOfKaehlerK`, and
`ResidueTheoremK`. What is missing is the **producer**: the unconditional
instance that every K-side result (and the `weilOfKaehler*` interface) consumes
as a hypothesis. Phase 3.1 constructs it from the pin's adic-completion
machinery, so later phases drop the hypothesis.

`HasSeparableResidue` is in the same file; phase 3.1 adds its
`of_perfectField` / `of_perfectField_of_isCurveOver` instances (pin V2 lines
19–27).

### 1.2 Measured scope (`port_advise`, frontier 608)

Two pin files, both `Definitions/`, no `Theorems/` wrappers:

| pin file | lines | decls | public | substitutions |
|---|---:|---:|---:|---:|
| `Definitions/Def_AlgebraicCurve_PlaceCompletion.lean` | 529 | 33 | 31 | 3 (≈29 ln) |
| `Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean` | 2,173 | 131 | 128 | 7 (≈71 ln) |

Raw 2,702 → projected **≈2,600 written**. `port_advise` reports **no shared
prelude between the two files** and essentially no removal: the construction is
new vocabulary, so it is transcription, not dedup.

The V2 file's public surface is the whole construction; its internal shape is
five blocks, all in-file and order-dependent:

1. `Place` pole/Laurent layer — `simplePoleSubmodule`, `poleSubmodule`,
   `laurentTailCoeff`, `higherPoleCorrection`, `canonicalLocalResidueDataKOfExtend`
   (+ `instHasCanonicalLocalResidueK`), `CoefficientFieldSection`,
   `CanonicalLocalResidueDataS` (pin lines 99–790);
2. `ModularCurve.Lg37` — `lg37_completion`, `lg37_residueHat`,
   `Lg37CompletionSection` (929–975);
3. `Mp72a102T1/T2/T3`, `Mp72a103T2`, `ModularCurve.KwNo6Section` — the Hensel /
   adic-completion / residue-calculus engine (981–1532);
4. `ModularCurve.KwNo6Pin` — `aCoeff*`, `clearedHat`, `resStar` and
   `canonicalLocalResidueDataKStar` (1541–2124);
5. `completionSection_nonempty_generic`,
   `instHasCanonicalLocalResidueKStar [IsCurveOver K F] [PerfectField K]`,
   `localResidue_eq_resStar{,ₗ}` (2133–2173).

The pin's V2 file **imports** `PlaceCompletion` but its dependency is *vacuous at
the name level*: `lg37_completion` is mathlib `AdicCompletion
(maximalIdeal v.toValuationSubring) v.toValuationSubring`, and no `kw_ffgc_*` /
`kwHgfV352_*` / `adicCompletion` name occurs in V2 (audit §4/§5 R2). So set 3.1b
drops the vestigial import and is independent of 3.1a. `PlaceCompletion` itself is
still real work for the later phases (the ℙ¹ core of 3.2 and the K ending of 3.6):
the `kw_ffgc_*` API — the `adicCompletionComap` ring hom, its
integrality/trace/completion-algebra instances,
`kw_ffgc_finiteDimensional_adicCompletion`, `kw_ffgc_completionTrace`, and the
residue-completion facts (`kwHgfV352_*`, `kw_ffgc_rankOne_adicCompletion`,
`kw_ffgc_absoluteValue`).

### 1.3 Homes and names

| new module | pin | content |
|---|---|---|
| `FLTForHuman/AlgebraicCurve/Defs/PlaceCompletion.lean` | `Def_AlgebraicCurve_PlaceCompletion.lean` | the completion layer, pin names kept (`Place.adicCompletion`, `kw_ffgc_*`, `kwHgfV352_*`, `ModularCurve.KwF4gRRTate.algebraMap_K_mem_adicCompletionIntegers`, …) |
| `FLTForHuman/AlgebraicCurve/Defs/CanonicalLocalResidueInstanceV2.lean` | `Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean` | the whole construction, pin namespaces kept |

Keep the pin's namespaces (`AlgebraicCurve.Place.*`, `ModularCurve.Lg37`,
`Mp72a102T1/T2/T3`, `Mp72a103T2`, `ModularCurve.KwNo6Section`,
`ModularCurve.KwNo6Pin`). The pin's `p2m_export`/`p2m_open`/`attribute
[-instance]`/`attribute [-simp]` scaffolding is dropped. **Never change a
statement to ease a proof.** The pin-private helpers stay `private`; the
public surface lands public.

**3.1a is landed and reviewed (2026-09-30).** `Defs/PlaceCompletion.lean`, 551 ln;
checker 3060 → **3091 identical / 0 mismatched / 0 missing / 30 own-proof**; forced
`lake build` green (6.8 s); public surface `[propext, Classical.choice,
Quot.sound]`; no `sorry`/`axiom`/`import Mathlib`. The pin's unported
`Def_DedekindDomain_AdicValuation_InlineSpecific.lean` (564 ln) is **not ported**:
its one needed declaration (the anonymous `IsRankOneDiscrete` instance at
InlineSpecific 215–219) is mathlib `v4.34.0`'s anonymous instance in
`Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean`, so 3.1a imports
that module (audit route R1). The pin's global anonymous `Algebra O L` instance
(pin line 9) is deliberately dropped, since mathlib now supplies it (route R3).
Both are manager-applied reuse wins recorded in
[WORKORDER-P3-1-residue-instance.md](WORKORDER-P3-1-residue-instance.md) §4 and the
friction log.

### 1.4 Reuse to import, not re-prove

`port_advise` substitutions, all importable from the port:

- `Place.ord_nonneg_of_mem` ← `Place.ord_nonneg_of_mem_vs` (`Canonical/HasCanonicalDivisor.lean`) — the pin's V2 private copy `ord_nonneg_of_mem` (line 208), the port names it `_vs`;
- `Place.mem_of_ord_nonneg`, `Place.mem_iff_ord_nonneg` ← `Defs/PushPull.lean` (binder spelling only);
- `Place.restrictSubringHom` ← `Place.restrictInclusion` (`Defs/PushPull.lean`);
- `Place.residueFieldMapRestrict` ← `Place.restrictResidueMap`;
- `Place.instAlgebra_restrictResidueField` ← `Place.instAlgebraResidueFieldRestrictPushforward`;
- `Place.instIsScalarTower_restrictResidueField` ← `Place.instIsScalarTowerResidueFieldRestrictPushforward`;
- `Place.uniformizerSubring` ← `Place.uniformizerSubring'` (`Canonical/HasCanonicalDivisor.lean`);
- `Place.adicCompletion` ← mathlib `IsDedekindDomain.HeightOneSpectrum.adicCompletion` (the port's `Place.adicCompletion` is the abbreviation to define here; the `port_advise` match against `CohCarrier.H1` is a false positive).

The pin's V1 shim `Def_AlgebraicCurve_CanonicalLocalResidueInstance.lean` (694 ln)
is **not ported**: it is the same development around the V1 import, its three
`private` lemmas are module-private duplicates, and the port keeps one name per
piece (PORTING-RR §3, name policy).

### 1.5 Route, risk, stop-early

- **The construction is transcription, not new mathematics** — the pin's own
  proof walks the same chain. The genuine work is import/name adaptation to
  `v4.34.0` and to the port's `Defs/`.
- **Scout gate (§2.6):** 3.1a's scout is closed (the InlineSpecific disposition
  above). For 3.1b, prototype in `ScratchP3b.lean` the spine
  `lg37_completion`/`Lg37CompletionSection` → `Mp72a102T1` Hensel root →
  `aCoeff`/`resStar` → `canonicalLocalResidueDataKStar` →
  `instHasCanonicalLocalResidueKStar`, and record the pre/post estimate.
- **Stop-early risks** (stop and report the pin `file:line`):
  1. ~~`PlaceCompletion` reaches a declaration of the pin's `InlineSpecific` prelude
     that the port's mathlib lacks~~ — **resolved, does not fire** (the one needed
     declaration is mathlib's; audit §2);
  2. the port's `Place.heightOneSpectrum` / `ramificationIndex` / `restrict`
     API drifts from the pin's by more than names — checked at the 3.1a call sites,
     no drift found (audit §8);
  3. the V2 proof reaches a declaration **outside** the two measured pin files
     (the H2/H3 measurement gap). **Resolve it locally `private` with the
     statement verbatim, and report it as promotion debt — do not inline new
     mathematics and do not edit a frozen module.** The manager closes the gap
     in the follow-up round;
  4. a `resStar`/`aCoeff` step needs a `simp`/`rw` set that the port's `Defs`
     does not expose; name the missing bridge rather than weakening a statement.
- `instHasCanonicalLocalResidueKStar` is an **instance**, and the checker's
  `DECL_RE` does parse `instance`, so its statement is diffed; but a
  statement-only check does not exercise the term, so it must also be used in a
  real consumer zone and `#print axioms`'d.

### 1.6 Closeout (2026-09-30)

Phase 3.1 is **ACCEPTED**. Measured, all independently re-run by the manager:

| item | value |
|---|---|
| modules | `Defs/PlaceCompletion.lean` 551 ln; `Defs/CanonicalLocalResidueInstanceV2.lean` 1,696 ln (3.1b-i 552 + 3.1b-ii 1,144) |
| checker | 3060 → **3212 identical / 0 mismatched / 0 missing / 30 own-proof** (3090 → 3242 checked) |
| builds | `PlaceCompletion` 6.8 s / 3407 jobs; `CanonicalLocalResidueInstanceV2` 12.4 s / 2688 jobs; whole-tree `lake build` **4853 jobs, green** |
| axioms | `instHasCanonicalLocalResidueKStar`, `completionSection_nonempty_generic`, the `localResidue_eq_resStar{,ₗ}` pair and the sampled engine all `[propext, Classical.choice, Quot.sound]` |
| consumer | `spec/RiemannRochConsumer.lean` zone F: `inferInstance` produces the instance over `[IsCurveOver K F] [PerfectField K]`, and the H3 differentials headline then consumes it **without** an explicit `HasCanonicalLocalResidueKStar` hypothesis — exit 0 |
| hygiene | no `sorry`/`admit`/`axiom`, no `import Mathlib`; the pin's V1 shim and `InlineSpecific` not ported; `p2m_*` scaffolding dropped |

**Carried debt — CLOSED (2026-09-30).** Both recorded duplications were collapsed
without moving a statement: `Place.uniformizerSubring'` moved down into
`Defs/CanonicalDivisor.lean` (so V2's pin-named `uniformizerSubring` is
`v.uniformizerSubring'`), and `hasSeparableResidue_of_perfectField` moved from
`Canonical/WeilDifferential.lean` to `Defs/LocalResidue.lean` (so V2's
`HasSeparableResidue.of_perfectField` instance is defined from it). Checker stayed
**3212 / 0 / 0 / 30**, whole-tree `lake build` green (4853 jobs); see
`../../logs/riemann-roch-friction.md` § Phase 3.2.

## 2. Phases 3.2–3.7 (planned)

The remaining rows and their homes are fixed in PORTING-RR §3. Phase 3.1 is not a
prerequisite of the shared core (see §0). Working order: 3.2 (shared ℙ¹ core) and
3.4 are the shared pieces; 3.3 (Tate agreement) is the largest single block; 3.5
and 3.6 are the two endings; 3.7 the RR assembly. The `_v2` names are dropped, so
the three files that reference them take a one-line reference edit (the rewiring
frontier of PORTING-RR §3).

## 3. Verification (per set, and the phase gate)

```bash
cd lean
python3 spec/check_flt_statements.py                    # 0 mismatched / 0 missing
flock /tmp/flt_for_human.lock timeout 240 lake build <module>
flock /tmp/flt_for_human.lock timeout 120 \
  lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>
```

Build discipline (copy into every work order): `lake env lean` needs
`-DmaxHeartbeats=4000000 -DautoImplicit=false`; one `lake build` per wave,
serialized with `flock` and bounded with `timeout`; never raise the cap; no
`sorry`/`admit`/`axiom`; no `import Mathlib` in a library module. At the 3.1 gate:
checker `0 mismatched / 0 missing`, `lake build` of the two modules green,
`#print axioms` on `PlaceCompletion`'s public surface and on
`instHasCanonicalLocalResidueKStar`'s witness, and a consumer zone instantiating
the instance over a real curve (`spec/RiemannRochConsumer.lean`).
**Do not run any git command.**

## 4. Reproduce

```bash
cd tools/deps
FLT_ROOT=~/proj/fermats-last-theorem python3 port_advise.py \
  --target Definitions/Def_AlgebraicCurve_PlaceCompletion.lean \
  --json build/rt_completion_advise.json
FLT_ROOT=~/proj/fermats-last-theorem python3 port_advise.py \
  --target Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean \
  --json build/rt_instance_advise.json
```

The measured outputs are `build/rt_completion_advise.txt` and
`build/rt_instance_advise.txt`; the phase-3 prices are also in
[../../../studies/riemann-roch-strategy.md](../../../studies/riemann-roch-strategy.md)
§5.4 and [../PORTING-RR.md](../PORTING-RR.md) §3.
