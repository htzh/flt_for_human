# Riemann–Roch port workflow — how to run the next block

**Audience:** the manager of the next Riemann–Roch port session. This is the
*operating procedure* distilled from phases 1, 2, 3.1 and 3.2a. The method in full
is [../porting-playbook.md](../porting-playbook.md); this file is the recipe, the
concrete commands, the review checklist and the failure modes that actually bit.
It sits in the topic dir with the plans and work orders.

**Current state (2026-09-30).** Phases 1, 2, 3.1 complete; 3.2a complete; row 2
blocks 3.2b–e and rows 3.3–3.7 remaining. Checker **3316 identical / 0 mismatched /
0 missing / 30 own-proof** (3346 checked). Pin `anthropics/fermats-last-theorem@aa2d8b3`
(local clone `~/proj/fermats-last-theorem`); port mathlib `v4.34.0` (prebuilt under
`lean/.lake/packages/mathlib`).

## 0. Where things live

| artifact | home |
|---|---|
| blueprint (all phases) | [../PORTING-RR.md](../PORTING-RR.md) §3 |
| phase plans (operative) | `PLAN-P1.md`, `PLAN-P3-1.md`, `PLAN-P3-2.md` … one per row |
| work orders | `WORKORDER-<set>.md`, one per dispatched set |
| mathlib audits | `AUDIT-mathlib*.md`, one per set |
| statement checker | `lean/spec/check_flt_statements.py` |
| consumer wire test | `lean/spec/RiemannRochConsumer.lean` |
| friction log | `lean/logs/riemann-roch-friction.md` |
| port modules | `lean/FLTForHuman/AlgebraicCurve/{Defs,PrincipalDivisors,Genus,RiemannRoch,Canonical,IsCurveOver,WeilExchange}/` |
| measurement inputs | `tools/deps/build/*` (gitignored) |

## 1. The model

**A phase ≈ one phase-3 table row.** `PORTING-RR.md` §3's seven work-item rows are
too large to be one effort, so each row is split into *sets*, each set is one
self-contained mathematical block, and a set is dispatched to **one** subagent
with a review gate before the next. A set must be ≤ ~1–3k written lines (the
staffing rule the playbook states as "roughly 1,000 lines per subagent").

**One set = one loop:**

```
measure  → audit → dedup → work order → dispatch → review → closeout
```

1. **Measure** — `port_advise` on the set's node list; record raw / substitutions /
   removable / projected written. Treat the number as a **lower bound** (see §6).
2. **Audit** — a *separate* subagent produces `AUDIT-mathlib-<set>.md` (playbook
   §2.2) **in parallel with the port worker**, and the manager folds it into the
   work order. Never dispatch a set without an audit running.
3. **Dedup** — home any shared prelude once, in a new file; never `private` per
   consumer. Use the audit's "port once" section plus the near-duplicates list.
4. **Work order** — write `WORKORDER-<set>.md` (template in §5) and hand the
   subagent *that plus the playbook*, never the whole plan.
5. **Dispatch** — one worker per set; it ports, builds per module, wires the
   checker, and reports in the work order's §7 shape.
6. **Review** — the manager re-runs the checker, forced per-module builds,
   `#print axioms`, hygiene, and reads the diff. Only then is the set *accepted*
   and the next order written against the modules that actually exist.
7. **Closeout** — update the plan (a closeout subsection), `PORTING-RR.md`, the
   friction log; delete scratch files; record refactor debt.

## 2. Commands

All from the workspace root unless noted.

```bash
# 1. measure a set (node list from the strategy/plan)
cd tools/deps
python3 port_advise.py --nodes "$(cat build/<set>_nodes.txt)" \
        --json build/<set>_advise.json > build/<set>_advise.log 2>&1
#    (read §1 substitutions, §2 port-once/removable, §4 drags)

# 2. the checker, after any port work (from lean/)
cd lean
python3 spec/check_flt_statements.py          # must end 0 mismatched / 0 missing

# 3. builds — the ladder (see §3)
timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>
flock /tmp/flt_for_human.lock timeout 240 lake build <module>

# 4. axioms on the public nodes
#    (a gitignored Scratch file with #print axioms; delete it at closeout)

# 5. consumer wire test
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/RiemannRochConsumer.lean

# 6. note hygiene
python3 tools/check_math_delimiters.py <changed notes>
```

## 3. The build economy (the single most important habit)

From [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3:

- **Every set lands in NEW files.** A new file imports downward and nothing
  imports it yet, so it writes only its own `.olean` and cannot cascade. Editing an
  *existing* module re-elaborates its dependents — that is a refactor round, done
  once, bounded, and verified with one whole-tree build.
- Edit loop `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`:
  writes no `.olean`, recompiles nothing.
- `lake build <module>` when a file is done: builds dependencies, never dependents.
- **No bare whole-tree `lake build` during a phase**; one at the milestone.
- Serialize `lake build` with `flock /tmp/flt_for_human.lock timeout <N>`.
- Never raise the heartbeat cap; no `sorry`/`admit`/`axiom`; no `import Mathlib` in
  a library module.
- Verify economy by the `.olean` mtimes: only the set's own modules should move.

Measured evidence: phase 3.1's two modules cost 6.8 s / 12.4 s per-module; the P3.1
debt round (existing files) cascaded and needed one 47 s whole-tree build; 3.2a's
three new modules cost 2.0 / 2.6 / 5.3 s with no whole-tree build at all.

## 4. Checker wiring

`lean/spec/check_flt_statements.py` diffs every port declaration's *statement*
against the pin, by last name, proof bodies ignored. For each new set append
**last** (order matters only to disambiguate same-last-name collisions):

- `SOURCES` — the pin files the port transcribes from: `Theorems/Thm_*` wrappers
  **first** (the interface copies whose binders the port's public names spell),
  then the `P2M/Sol/S_*` files (their prelude), then any `Definitions/Def_*` files
  with no wrapper.
- `PORT_FILES` — the new port modules.

Conventions that keep the checker honest:

- Statements are **verbatim from the pin**; never changed to ease a proof.
- A declaration the port imports (a substitute) is **omitted** from the port module;
  the checker does not require unported pin declarations.
- `private` pin helpers stay `private` (the checker skips them); a pin-*public*
  helper promoted from a private port copy may need the dotted-name fallback, and
  occasionally an `OWN_PROOFS` entry with a written reason (keep those rare).
- `instance` **is** parsed, so a named instance is statement-diffed — but only a
  real consumer `example` exercises its term.

## 5. Work-order skeleton

```markdown
# Work order — <set>: <one-line subject>
**Status: ready to dispatch.** <row/plan reference>; method playbook §2–§5;
build economy PORTING-DeligneSerre §3.
Baseline: checker N / 0 / 0 / 30.
## 0. Scope        — the mathematical block; pin files/lines/node list; measured
                     price; explicit exclusions; measurement gaps (if any).
## 1. Deliverables — new module paths, pin source, namespaces, private list.
## 2. Statements   — spell each public statement from its Thm_ wrapper.
## 3. Reuse/audit  — import, do not re-prove; mathlib substitutes; recorded
                     negatives; API drift; the audit's leads.
## 4. Build discipline — the §3 block, verbatim.
## 5. Checker wiring + verification commands.
## 6. Stop-early / gaps.
## 7. Report shape.
```

Every work order carries the build-discipline block verbatim and a stop-early
protocol: **if a proof reaches a declaration outside the measured files, resolve it
locally `private` with the statement verbatim and report the pin `file:line` as
promotion debt — do not inline new mathematics and do not edit a frozen module.**

## 6. The failure modes that actually bit

1. **The measurement is a lower bound.** `port_advise` reads the targets' own files;
   their proofs reach helper targets outside the measured set. 3.2a's 91-declaration
   reading missed the dropped `placeOfPoint` block (5 decls) and the whole
   `PlaceEvaluationAlgebra` layer (6 nodes / 160 ln). **The §2.2 audit is what
   closes this**, which is why it is mandatory and parallel.
2. **A name absent from the imported modules is not absent from mathlib.** The 3.1
   worker unioned an `IsRankOneDiscrete` instance "because mathlib lacks it"; it was
   in `NumberTheory/NumberField/Completion/FinitePlace.lean`, one import away. Search
   the tree, not the module's closure.
3. **A duplicated global instance is a diamond.** The pin's global
   `Algebra O L` instance and the V2 `uniformizerSubring` were both duplicated
   content; mathlib (resp. one shared home) is the fix. Prefer importing mathlib
   over transcribing a global instance.
4. **The checker's blind spots.** It skips `private`, `scoped`-prefixed and
   anonymous declarations, and it cannot see a *changed instance term*. A promoted
   pin-`private` helper may only resolve through the dotted-name fallback, or fail
   if the port's private copy has a different namespace — then transcribe at the pin
   name instead of promoting (this happened with `le_exp_neg_one_of_lt_one`).
5. **v4.34 API drift is small but real.** Expect renames
   (`dif_pos`→`dite_eq_left`, `Polynomial.degree_sub_lt`→`degree_sub_lt_left`,
   `AlgEquiv.coe_algHom`→`coe_toAlgHom`) and moved modules
   (`IsAdicComplete.henselianRing` in `RingTheory.Henselian`); `Finset.prod_zpow`
   takes explicit args. Some files have no `.olean` in this checkout
   (`RingTheory.Polynomial.Roots`) — import the sibling module instead.
6. **The pin's `p2m_*`/`attribute` scaffolding is dropped**, but its *instance
   disables* matter: `attribute [-instance]` lists tell you which instances blow up
   search. Alert downstream modules that take an instance hypothesis explicitly.
7. **A pin `variable` binder quirk can be a hard error.** `section DegInfty` opens
   `variable (K) [DecidableEq (RatFunc K)]`; the redundant `(K)` is a v4.34 error
   that suppresses the instance. Drop `(K)`; statement text is unchanged.

## 7. Review checklist (the gate)

Before accepting a set, the manager independently:

- [ ] `python3 spec/check_flt_statements.py` → `0 mismatched / 0 missing`, `30
      own-proof`.
- [ ] forced per-module `lake build <module>` green for each new module; **no
      whole-tree build** unless the set edited existing files.
- [ ] `.olean` mtimes confirm only the set's modules moved.
- [ ] `#print axioms` on every public node → `[propext, Classical.choice,
      Quot.sound]` (or a subset).
- [ ] hygiene grep: no `sorry`/`admit`/`axiom`/`import Mathlib`/heartbeat override.
- [ ] statements spot-checked against the pin (the checker covers all of them, but
      read a few).
- [ ] the consumer wire test still passes (and gained a zone if the set is on the
      interface).
- [ ] friction log entry; plan closeout; `PORTING-RR.md` status; scratch removed.

## 8. Refactor rounds

A set that needed a declaration from a frozen module resolves it `private` locally
and records it in the friction log. A **refactor round** (an H2-style pass) later
promotes the union and deletes the copies; it is the *only* thing allowed to edit
existing modules, it is bounded, and it ends with one whole-tree build. Phase 3.1's
debt round is the model: two duplications collapsed with no statement moved, checker
unchanged.

## 9. Current row-2 map (3.2)

Row 2 = the ℙ¹ residue core + PF base case (raw 29,118 ≈16–17k written). The
master ℙ¹ file shares **99%** of its declarations with row 6's K base file, so the
engine is written once and the two endings are small marginals. Blocks:

| set | content | status |
|---|---|---|
| 3.2a | ℙ¹ place/ord dictionary + `PlaceEvaluation` + `PlaceEvaluationAlgebra` | **DONE** (1,633 ln, 3 new modules) |
| 3.2b | ord/valuation algebra prelude (much already substitution) | next |
| 3.2c | local residue-at-∞ calculus | planned |
| 3.2d | principal parts + differential coefficients (`p0n22`/`mp72`/`ag9b`) | planned |
| 3.2e | the three `trace_localResidue_*` atoms + `residueTheorem_ratFunc_of_perfectField` | planned |
| row 6 | the K ending (marginal over the shared engine) | planned |

See [PLAN-P3-2.md](PLAN-P3-2.md) §3 for the measured boundaries and
[WORKORDER-P3-2a-p1-dictionary.md](WORKORDER-P3-2a-p1-dictionary.md) for a worked
example of a dispatched set.
