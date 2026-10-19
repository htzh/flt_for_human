# The WeightOne rectification — close-out and what actually remains

This file exists because the effort is **finished**, but two documents still say it is not,
and a stale figure ("≈7,000 lines of WeightOne duplication") is doing the rounds as if it were
current work. It states the facts, the two bookkeeping gaps, and the small residuals. Nothing
here is a plan for a new wave; the largest remaining item is a namespace-policy decision.

Plan: [TOPIC-weightone-rectify.md](TOPIC-weightone-rectify.md). Measured record, set by set:
[../../logs/weightone-rectify.md](../../logs/weightone-rectify.md) (769 lines). Set briefs:
[SET-W0](SET-W0.md) – [SET-W4](SET-W4.md).

## 1. The facts

**Current measurements** (2026-10-13, `tools/deps`):

| quantity | value |
|---|---:|
| port | 633 modules / 17,555 declarations (5,626 private, 11,929 public) / 260,742 lines |
| `port_graph.py --blocks 20` | **one** block in the whole port: 234 lines, `AlgebraicCurve.PrincipalDivisors.Transcendence ↔ WeierstrassCurve.Velu.RestrictAlong`. **No WeightOne cluster at all** |
| checker | 9,600 identical / 667 promoted / 0 mismatched / 0 missing / 38 own (9,638 checked) |
| `spec/WeightOneConsumer.lean` | exit 0 |
| homes, all present and building | `ModularForms/{QExpansionCoeff,DiscPow,QExpansionOrder}.lean`, `ModularForms/WeightOne/{Fricke,LevelField}.lean`, `ModularForms/WeightOne/Defs/{PeriodPair,PTorsion,Gamma}.lean` |

**The weight-one cluster's removable statement-identical duplication is 14 lines**, down from
the 7,242 the tool reported at the 2026-09 baseline — the log's final state, and consistent with
`--blocks` now showing no cluster there (its display threshold is ≥4 names and ≥100 lines).

## 2. Provenance of the "≈7,000 lines" figure — read this before quoting it

The figure comes from `tools/deps/README.md` under **"First readings (178 modules, …)"**, i.e.
the state *before* the rectification, and it was produced by the tool's **name-based** cost
model. The log's round-10 section records what that model was doing: two modules can declare
the same last name with *different statements* — `descent` at `ev X` against `ev id`,
`exists_rat_combination` in general `Fintype ι` against `Fin n` — and the tool charged each as if
one copy could be kept and the others deleted. Measured directly at the time:

| figure | lines |
|---|---:|
| tool's name-based `--blocks`, the two remaining clusters | 198 + 162 |
| statement-identical copies only, over 7 weight-one modules | 81 |
| after deleting those | **14** |
| `ModularCurve.Gamma0InvariantCore ↔ PhiGenDescent` statement-identical | 0 |

`port_graph.py`'s `_name_cost` was then fixed to match its own docstring ("lines removable by
keeping one copy"): it records a normalised statement and counts a group only when it spans two
or more modules. `--selftest` passes. **So the 7,242 was mostly a measurement artifact, not
duplicated mathematics**, and quoting it as outstanding work is a live error: it has been
carried into `lean/CARRY-FORWARD.md` §Cleanup families and into session prose on 2026-10-13
(both corrected). A future session that greps for "7,242" or "WeightOne dedup" will land here
and should stop.

## 3. What the rectification actually did

Sets W0–W4 plus post-W4 rounds, all recorded in the log. In outline: five homes created
(`Defs/PeriodPair`, `QExpansionCoeff`, `DiscPow` — which absorbed `Pole` — `Defs/PTorsion`,
`Fricke`, plus `Defs/Gamma` and `LevelField` later), the level family rewired onto them
(`Basic`, `WeierstrassPTorsion`, `LevelOneHauptmodul`, `FrickeFunction`, `LevelFraction`,
`LevelN` — one weight-one-wide rebuild, 6 min 19 s), the four Γ-modules rewired onto
`Defs/Gamma` (2 min 15 s), the width family homed, the remaining statement-identical copies
promoted or deleted, and the checker held at `0 mismatched / 0 missing` throughout. The plan's
§2.1 records the one reverted attempt (a namespace mismatch between the homes and the
consumers' spelling, which produced dangling qualified references).

## 4. What remains — two bookkeeping gaps and four small residuals

**Gaps in the record (no code, one session's reading):**

1. **`TOPIC-weightone-rectify.md`'s status line is stale.** It reads "**Status: planned
   (SET-W1 not started)**" while its own §3 table records W2 **done**, W3 **partial**, W4
   **started**, and the log records the finish. Rewrite it to point here.
2. **The log's `## After SET-W4` section is still the placeholder** "*(to be filled: final
   `--blocks`, checker total and the demotion reconciliation, the four …)*". It is the one hole
   in an otherwise complete record. The plan's §5 definition-of-done asks for exactly this
   before/after reconciliation, so filling it also closes §5.

**Residual mathematics and API, all small, none duplicated:**

3. **`isIntegralQExp_coeff`** — stays `private` in the weight-one layer; it has no registered
   pin source, so promoting it would add an unverifiable public name. This is the 14-line
   residue.
4. **`KPoleAt` / `KPole` / `orbitCoeff` / `levelGen` / `zetaN` in `FrickeFunction` stay
   private.** Promoting them made `LevelFraction`'s `KPoleAt` **ambiguous** with
   `UpperHalfPlaneAux.KPoleAt`; the promotion was reverted. Unblocking it is the namespace
   policy of the plan's §2.1 — a decision about exported spelling, not a proof.
5. **Γ0Rationality ↔ Gamma1Basis near-duplicates** (`descent`, `ev_prod_ne_zero`,
   `exists_ev_of_mem_adjoin`, `aeval_mem_adjoin`, `conj_mem_Gamma`, `adjoin_isDomain`,
   `ev_mem_adjoin`, `ratCast_mem`): the same `ev`-algebra argument instantiated against each
   module's own `ev`/`RatAt`. **Different statements, so this is generalisation work, not
   deletion** — it would mean one lemma over an abstract `ev`, with both modules deriving from
   it. `FrickeFunction ↔ LevelFraction` has the same shape.
6. **W4's own stated tail** (plan §3): "the `ModularFormClass` copies, adapters,
   checker/`PORT_FILES`/README, consumer, write-up". The consumer exists and passes and the
   homes are listed; what is not visibly done is the write-up, which item 2 covers.

## 5. Reproduce

```bash
cd tools/deps
python3 port_graph.py --blocks 20          # no WeightOne cluster; one 234-line block elsewhere
python3 port_graph.py --duplicates 900     # 839 names in >=2 modules: name-level, not lines
python3 port_graph.py                       # 633 modules / 17,555 declarations / 260,742 lines
cd ../lean
timeout 300 python3 spec/WeightOneConsumer.lean   # exit 0 (run via lake env lean for the options)
timeout 300 python3 spec/old_check_stmts.py  # 9600 / 667 / 0 / 0 / 38 own
```

## 6. The forward path

Nothing here needs a wave. The two gaps are documentation edits; residuals 3 and 4 are
one-line comments plus, for 4, a namespace decision already framed in the plan's §2.1;
residual 5 is optional generalisation that the log argues is not required for conformance.
The only thing to *avoid* is re-citing 7,242 as outstanding (§2).
