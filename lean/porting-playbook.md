# Porting FLT to mathlib — a playbook

The source of truth is the pinned FLT repository
(`anthropics/fermats-last-theorem`, currently `aa2d8b3`). The ports completed so
far are the Elliptic torsion port (`#E[n](K) = n²`), the
`functionFieldGeneration` definitions layer and its theorem cone, the `PhiGen`
splitting cone, the `ModularCurve` Hecke layer, the `AlgebraicCurve` divisor
exchange, the level/congruence-subgroup vocabulary, the T-side of `R = T`, the
Eichler–Shimura period map, the Sturm-bound cusp vanishing, the WeightOne
rectification, and the Vélu port (V1 + V2). Each has a per-effort *record* in
[logs/](logs/) and a closing *review* in `topics/*-retrospective.md`; §10 indexes
both with their measured numbers.

This file is the method those efforts share, so it is organised by principle
rather than by which port taught it. Read a record for what an effort did; read
this before starting the next one.

Three conventions run through everything:

- **The pin is the authority, and faithfulness is mechanical.** Every ported
  *statement* is diffed against the pin by `spec/check_flt_statements.py`, not
  trusted. Where prose and Lean differ, the Lean is right.
- **The port is ours.** A module is a mathematical role, not a source file;
  shared mathematics is written once and promoted; adapters stay `private`.
  FLT's declaration *names* and *statements* stay, so comparison against the pin
  remains mechanical.
- **A ported node is ported whole.** The pin file is the unit the frontier
  measures, and once a file is in scope its content is transcribed in full, not
  cherry-picked for the current target (§2.3). A partial port costs a revisit and
  makes the tooling's estimate for the next effort wrong.

Earlier records cite this file by section number under an older numbering (for
example "playbook §3.11" for build discipline, "§7.4" for faithfulness). The
[appendix](#appendix-section-map-from-earlier-revisions) maps every old reference
to its home here.

How to staff an effort with subagents is §0.2; how much of this file to apply, and
when to deviate, is §0.3.

## 0. Before you start

### 0.1 The checklist

**Plan for more than one round.** A port of any size is a sequence of sets, not a
single pass: build cost and duplication accumulate as the tower grows, and later
rounds will revisit earlier modules. The porting agent's build rules are
deliberately simple (§3.5); deeper build investigation is a separate subagent job
(§0.2).

Before coding — and first of all when a frontier figure looks surprising — check
[CARRY-FORWARD.md](CARRY-FORWARD.md) for deferred API and open follow-ups touching
the nodes in scope; a registered entry means the node's `lines`/`needed` does not
yet account for something its consumers need.

1. **Measure the cone** — files, raw and content lines, declarations, importers.
   From those numbers decide which whole nodes are in scope and whether each is a
   port, a re-derivation, or both (§2.1, §2.3).
2. **Audit the route** — build the FLT → mathlib map, with a recorded negative
   for every search that found nothing (§2.2).
3. **Find the duplication** — byte-identical private preludes get one home before
   the first module is written (§2.4).
4. **Write the blueprint** — scope, cone, dedup table, module layout, topics,
   risk register, verification recipe (§2.1, §2.5, §2.6).
5. **Scout the one piece of genuinely new mathematics** in `Scratch.lean` before
   dispatching it (§2.6).

While coding:

6. **A module is a role; a directory is a theory** (§3.1–§3.2).
7. **One topic at a time, each with a work order**, bottom-up, with the build
   ladder in §3.5.
8. **Port each in-scope node whole** — every declaration with a consumer, not
   only the ones the current target reaches (§2.3).
9. **Faithfulness from the first declaration** — statements spelled as the
   wrapper, added to `SOURCES`/`PORT_FILES`, consumer zones composing across
   modules (§4).
10. **Keep the friction log while you hit friction** (§3.6), and **drop nothing by
    inspection** — `grep -c` or `diff` (§2.4).

At the end:

11. Checker `0 mismatched / 0 missing`, consumer exit 0, `#print axioms` clean,
    no `sorry`, and (where a coverage report exists) coverage `0 / 0 / 0` (§4).

### 0.2 Working with subagents

Context is the binding constraint on a large port, and the manager's context is
best spent on the plan, the review and the capstone. Decompose and dispatch:

- **Above roughly 1,000 written lines, use subagents.** One agent carrying the
  whole cone spends its budget on accumulated detail; a set dispatched to a fresh
  agent starts from a clean, complete brief. Below that size the overhead and the
  review are not worth it — do the topic directly.
- **Give each subagent a synthesized instruction, not a pointer to this file.** A
  subagent shares none of the manager's context, so "read the playbook and the
  logs" produces confusion and burns its budget on reconnaissance. Hand it a
  self-contained work order (§3.3): subject; pin files and line ranges; exact
  statements to land; module and namespace; route with its recorded negatives;
  build bounds; verification commands; and what is explicitly out of scope.
- **Scope tightly, and bound the subagent's own scoping.** A subagent may do
  limited local reconnaissance — a mathlib search for one specific lemma, a
  `Scratch.lean` probe, a `#check` — but it must not re-plan the effort, re-pick
  the route, or roam the pin. Broad scoping is the manager's job *before*
  dispatch (§2); if the task cannot be stated without it, the plan is not ready.
- **One set per subagent; review before the next.** When the effort needs several
  sets (roughly 2,000+ lines), launch a single subagent for the first set, review
  its tree — build, checker, consumer, and the code itself — and only then write
  and launch the next set's order against the modules that actually exist (§3.4).
  Do not fan several sets out at once: they will duplicate preludes, collide in
  namespaces, and invalidate each other's builds.
- **Reserve integration for the manager.** The capstone and the final wire test
  are the review instrument; a subagent prepares a set, but assembly and
  judgement stay with the manager.
- **Ask for artifacts, not narration.** The return is the module(s), the measured
  table, and the friction-log entries; the manager folds the generalizable part
  into this file and the record.
- **Build investigation is a separate dispatch** whose whole brief is the
  build-cost note ([../notes/lean-build-cost.md](../notes/lean-build-cost.md))
  plus the tool interface — never folded into the porting agent's task (§0.4).

### 0.3 Discretion: this is a synthesis, not a contract

This file is distilled from several ports of very different sizes. Read it as
recorded judgement, not as a checklist to apply mechanically. Everything beyond
the three conventions above is a heuristic with evidence attached.

- **Match the process to the size.** A 200-line leaf topic needs a work order and
  a bounded build, not a blueprint, a correction ledger, a risk register and a
  scout; a 2,000-line cone needs all of them. Every instrument is cheap at the
  right size and wasteful at the wrong one.
- **Prefer the cheapest instrument that answers the question**: the checker and
  the consumer before a full build; a `Scratch.lean` probe before a topic; a
  `grep -c` before a rewrite.
- **The numbers and names here are evidence, not law.** The line counts, module
  names and specific renames are what those efforts measured; when the situation
  differs, measure again rather than quoting them.
- **When a rule and the mathematics conflict, the mathematics wins** — record the
  deviation and why, so the next reader can judge it.
- **Nothing here is exhaustive.** A situation this file does not cover is a gap to
  record, and to add here when it generalizes.

### 0.4 Build discipline, and the note behind it

Follow the per-work-order block in §3.5. When a build misbehaves beyond those
rules, do not investigate it inline: dispatch a subagent whose brief is
[../notes/lean-build-cost.md](../notes/lean-build-cost.md), which carries the
measurements, the recipes and the tools (`tools/deps/build_ladder.py --audit` /
`--profile`).

## 1. The cost model

**Expense is the route's distance from mathlib, not the size of the source.**
Every effort measured this, in both directions:

| effort | source size | written | why |
|---|---|---|---|
| Elliptic torsion | cone 3,671 lines | 3,362 lines | the engine (`ω` division polynomial, complement multiplication) had left mathlib; the 1,164-line counting module was the *cheapest per line* |
| `functionFieldGeneration` theorem | 11,312-line structural pin sum | ≈3.8k lines | reduced to three generic lemmas plus concretisation |
| `AlgebraicCurve` exchange | 5,423 raw `S_` lines | 5,559 module lines | line budget was accurate; risk register over-warned |
| `ModularCurve` Hecke | 10,569 raw lines | 7.6k content lines in band | four prelude cuts made it tractable |

Consequences for planning:

- **Budget content, not raw lines.** Raw is the pin's text; *content* subtracts
  the `p2m_*`/`attribute` scaffolding (28–35% of a pin cone, never written).
- **Budget in named shape risks, not rounds or lines alone.** A definitions layer
  dictated by pinned statements took 1 round against 20 budgeted; a 2,002-line
  file was the right size but its *route* was the whole cost. Risk registers
  over-warn, and the recurring real cost was API drift (§7).
- **A wrong statement is maximally expensive; a wrong proof is cheap.** Hence
  faithfulness is mechanical and front-loaded (§4), and the route is audited
  before any module is written.
- **A faithful port is not line-for-line smaller.** The saving is the compat
  shims, dead wrappers and repeated preludes never written. Whole-node porting
  (§2.3) spends lines a minimal port would skip and buys back a correct frontier
  and no revisit; it is not a licence to transcribe scaffolding.

## 2. Planning a port

### 2.1 Measure the cone

The blueprint (`PORTING-<X>.md`) is the planning record, and every one opens the
same way: a measured cone, taken as the transitive citation closure of the one
target theorem from the pin's doc-site graph, pinned to a sha and a mathlib
version. Use a coverage report (`studies/hecke-commute-bar-coverage.md` is the
model) and report every group as **three numbers — nodes, raw `S_` lines, content
lines** — with node-based and content-based headlines separate, since nodes
overstate a cone whose weight sits in a few large files. State the metric's bias:
a name-based "already ported" test is an upper bound that misses renamed ports,
and the **`ucl` closure is an upper bound in the other direction** — it cannot see
that a closure member's *mathematics* is already in the port under another name,
nor the pin's definitional imports.

**Walk the proof's definition uses, not only the import block.** A
`Definitions/Def_*.lean` import can be an *empty stub* while the `S_` proof still
consumes a public block of a different `Def_*` module the stub drags in
transitively — one division-field target imports only a stub yet needs the
≈1,750-line `Def_WeierstrassCurve_DivPolyMulFormula.lean`. The docs-site graph
carries the list per node (`fltdata.proof_defs`), so check it before calling a
definition layer empty. **Sweep the port by name and by `#check` before pricing
any closure member**: one wave priced four members at 1,246 / 911 / 58 / 269 lines
and wrote ≈15 lines for the last and nothing for the first three; a `ucl`-only
budget said ≈4 k where the truth was 1.6 k.

Then make the table *act*:

- **Partition by mathematical route group and assign each whole node to its first
  consumer**, so the group totals sum to the measured total; that table is the
  work-order cut.
- **Reachability decides which whole nodes enter the effort**, not which
  declarations inside an included node are ported (§2.3). Price the on-path node
  set, carry off-path nodes as a counted optional tail, and price the definition
  modules separately (lines, declarations, in-cone referenced fraction).
- Report the **outbound interface tier** (§2.3) and the **duplication already
  visible** in the pin (§2.4).
- **Close a measurement over proof-reached targets, not just the target files.**
  A cone built from the targets' own `S_` files is a lower bound: target proofs
  reach helper *targets* outside the measured set (the Riemann–Roch round found
  four, each later promoted). Measure the transitive closure over the targets'
  proof-reached public wrappers.
- **Ship a copy-pasteable regeneration recipe** with every measurement section; do
  not hand-maintain a number a script can reproduce.

Three ways a frontier figure misleads:

- **A citation-leaf is not a leaf.** `needed == 1` says nothing about
  *definitional* prerequisites, which the citation graph does not carry: a
  126-line leaf once needed three `Definitions/` modules. Measure the pin `S_`
  file's `Definitions/` import closure before trusting a leaf.
- **A pin `S_` file's `lines` is an upper bound on the headline's route.** A
  solution file may inline its prerequisites and carry an off-path silo — one
  2,248-line file had ~200 lines on the headline's path and ~1,400 in a
  place/Riemann–Roch/class-group silo. Grep the capstone region for the file's
  other declaration names; the silo is still ported whole (§2.3), but the
  headline's route cost excludes it.
- **File-granular edges shadow.** The citation graph's edges are file-granular
  while "already ported" is name-granular, so a partially ported file makes its
  citers read one node closer than they are. Porting the node whole (§2.3)
  removes the shadow; otherwise register the deferred surface in
  [CARRY-FORWARD.md](CARRY-FORWARD.md).

### 2.2 Audit the route, mathlib first

Build an FLT → mathlib table and test each entry for **definitional** equality
with `rfl`, not just mathematical agreement. A `rfl`-equal alias is legal; a
merely-equal one is a re-proof. The template is
[logs/card-torsion-port.md](logs/card-torsion-port.md) §3.

The audit has three outputs, all worth recording:

1. **Reuse wins** — FLT declaration replaced by a mathlib call
   (`RingEquiv.ofBijective`, `Submodule.torsionBy`, `Ideal.relNorm`, …).
2. **Route options** — where mathlib lacks the result, the candidate proofs, so
   the route decision is made before transcription (the `PhiGen` analytic kernel
   is the paradigm: the whole cone hangs on one `Φ_p` root description, and the
   blueprint names the alternative routes).
3. **Recorded negatives** — searches that found nothing, so nobody repeats them.
   Examples: mathlib has no `dedekindPsi`, no Γ₀ index formula, no
   `minpoly.map_eq_of_injective`; the `relNorm` norm block is irreducible.

**Adopt mathlib's type as the interface from the first declaration.** A target
type that exists in mathlib (`Submodule.torsionBy`, a `ValuationSubring`-based
`Place`, `LaurentSeries`) should be the port's interface immediately, rather than
mirroring FLT's internal wrapper and reconciling at the capstone. When a wrapper
is dropped it is a design decision, with the adaptation cost measured, not a
deletion.

Route selection is a measurement, not a preference:

- **Price the marginal closure under the substitution, not the headline cone.**
  Drop the route's outgoing edges and recompute; a graph-only estimate can be
  orders too large (one residual read 12 nodes / 5,595 lines where the truth was
  5 / 235).
- **Prefer a cone that is a subset of work the endgame needs anyway**
  (`cone ⊆ closure(branch)`), counting only the route-specific addition; retire a
  route that adds no coverage the chosen statement does not give.
- **Disambiguate same-named objects before pricing**, and verify a brief's named
  ingredient (name, hypotheses, crutch) against the pin — "the Eichler–Shimura
  layer" once named three cones, and one plan cited a lemma that does not exist.
- **The pin's `p2m_export`/`p2m_open` list is the FLT → mathlib gap list**; check
  every name against the pinned mathlib (a mathlib TODO comment is a reliable gap
  inventory).
- **Check a mathlib substitute's hypothesis strength against the source's** — a
  candidate can need primitivity where the cone has only `ζ^ℓ = 1`, or state a sum
  where the port needs a product.
- **Price the glue, not the mathlib-replaceable leaves** (a 199-line lemma with no
  replacement cost full price while a 76-line file collapsed to 8 lines).
- **Order the remaining nodes by outbound statement-demand, not file size**, and
  scope a topic from the pin's import graph over whole nodes: do not trim an
  in-scope node to its in-cone declarations (§2.3), and do not assume a
  declared-import set is self-contained.

### 2.3 What to port: whole nodes, then the gain test

**Port the whole node.** A *node* is a pin file, and the pin file is the unit the
frontier measures. Once a node is in scope, transcribe **all** of its content —
every declaration that has a consumer — not only the declarations the current
target reaches. Two things make partial porting a false economy:

- **It costs more than it saves.** A file taken in part is revisited in a later
  wave, and the revisit re-elaborates the module and re-establishes its context.
  One whole-node pass pays that once; the saving a partial port appears to buy is
  the same declarations, deferred and made more expensive.
- **It corrupts the estimate for the next effort.** `frontier.py` prices progress
  in source-file nodes. A file with a ported headline and an unported API prelude
  still reads as one unported node, so the remaining work is understated: the
  frontier says one node where the truth is a cluster. The citation graph's edges
  are file-granular for the same reason, so a partially ported file also makes its
  *citers* read one node closer than they are (§2.1).

The one thing a whole-node port leaves behind is content with **no consumer
anywhere** — a declaration dead in the pin as well as in the port (a
self-consumed lemma, a helper only `#check`ed in prose). "No consumer" is a claim
about the graph, so verify it mechanically (`grep -c` over the pin and the port,
or the pin's own citers) rather than by inspection. Everything else in the node is
ported, whether or not the current target uses it; the residue is registered per
node, not per declaration, so the next effort can see the frontier instead of
rediscovering it.

Then score the port on four gains — **organization, clutter never written,
mathlib alignment, truth** — never on line volume. Order the nodes by what each
*buys*, using **outbound indegree** (citers outside the cone) as the proxy for
the reusable surface the port purchases; small leaves can carry disproportionate
weight. Cautions: indegree is global (check the node is in the cone), a
library-shaped cone with a broad interface scores differently from a citation
chain, and an interface can be split across pin namespaces, so the checker must be
told which copy is the interface (§4). State which whole nodes are out of scope
in an out-of-scope table, and re-run the gain test when the blocking gate is
removed.

**Capstone shape follows from the premises, not from taste.**

- If the theorem's significant premises are not yet ported, build a *conditional*
  capstone: a proved artifact with no `sorryAx`, its fields a structure of named
  hypotheses. It checks the architecture, and the remaining work becomes an
  ordered list instead of a subtree (the `functionFieldGeneration` `Spine.lean`,
  debt 10 → 0). Keep the structure frozen once it lands; do not discharge fields
  opportunistically.
- If the premises are arguments or already-proved instances, do **not** add the
  device — the `AlgebraicCurve` layer is unconditional and a `Spine` there would
  be ceremony.

### 2.4 Deduplicate before coding, and drop by count

The pin repeats itself heavily: a private prelude copied into every `S_` file
that consumes it (the slot vocabulary in 38 files, the fibre dictionary in four,
the Fricke/inclusion prelude in three, the modular-unit `q`-expansion in four).
**Find those copies in the plan and give them one home before writing the first
module.** Detection is measurement, not inspection:

- **Diff normalized bodies** — strip imports, namespaces, `p2m_*` lines and the
  `solution` tail — and price the saving as `(copies − 1) × block content`. Find
  copy counts mechanically (byte-identical blocks, `difflib.SequenceMatcher`,
  per-declaration `grep`); `port_graph.py --blocks` is the port-side view,
  `port_advise.py` the pre-port view.
- **The pre-port view is name-anchored, so "already in the port" is a lower
  bound.** It looks up by *last name component*, so a port declaration doing the
  same work under another name is invisible; when a pin file's local names do not
  occur in the port, check the *statement* before pricing the block.
- **It is also an upper bound, and its worst false positives are `def … : Prop`.**
  The checker compares a `def`'s *type*, which for `def foo : Prop := P` is just
  `Prop`, so any same-last-name `Prop`-valued `def` reads as a substitute whatever
  its body. Read the pin body (or run `--prop-bodies`) on every such row.
- **Graph-node multiplicity undercounts copies** — one graph node can ship five
  times through hidden exports. Quantify a dedup by *duplicate lines shipped* (one
  895-line block: ~4,475 → 1,023), not by "a copy exists".
- **A large pin-`private` block re-exported by name mangling is a promotion**:
  write it once, publicly, at the pinned names, promoting the *union* of the
  duplicate preludes; an out-of-cone byte-identical duplicate is resolved by
  exposing one copy, not rewriting it.
- **"Which side stays" is the pin-public wrapper**; re-privatize the pin-private
  name and keep local aliases. Replace copies one file at a time, only where the
  statement matches — a copy carrying an extra hypothesis (`N ∣ 2`) is not a
  drop-in.
- **Count occurrences (`grep -c`) before dropping anything**, and review the
  port's own private layer after a module closes, not just the pin's copies:
  "redundant" is a claim about the graph. Keep a list of **deliberately not cut**
  items with their counts.
- **Do not merge a helper when sharing would invert the import graph**, and
  strengthen a statement from the pin, never from the port's own weakened private
  copy.

### 2.5 Risk register and budget

Write the budget as a **correction ledger**: structural sum → minus dedup
savings (explicit negative rows) → plus definition modules → range, then apply
the effort's measured written-lines ÷ content-lines ratio (`AlgebraicCurve`
1.25–1.45, `ModularCurve` 1.0–1.3). The budget *unit* is the named shape risk,
not lines. Name the risks in the order they will bite — a typeclass/coercion
mismatch, a defeq between concrete carriers, an instance diamond, a renamed API —
each with its mitigation, and mark each resolved or open with the measurement
that resolved it. Record **predicted non-events** too, so they are not budgeted
again. Measured outcomes:

- line budgets have been accurate to within ~10% (`AlgebraicCurve`: budgeted
  5.1k–5.9k, measured 5,559);
- risk registers have been pessimistic (an orbit count, an instance block,
  instance diamonds and a `PerfectField` requirement all failed to materialize as
  budgeted);
- the real recurring cost was **API drift**, which is cheap per item but
  numerous — keep the drift list (§7);
- record a route win as a *measured delta* and re-price, rather than banking it.

Before committing to a route, audit it as a named `logs/audit-*.md`, re-deriving
load-bearing claims rather than trusting the brief. The audits that did this
found a slot-count closed form worth ≈110–150 lines, that `rval_aux` was ~64%
irreducible, and that one `relNorm` route answered "no".

### 2.6 The scout gate

When exactly one topic carries genuinely new mathematics, prototype it in a
gitignored `Scratch.lean` before dispatching it. A scout is cheap insurance
against a whole topic being routed wrongly: one scout cost 3.2 s and converted
its biggest unknown into a known quantity, and the manager pre-checked the `Φ`
one-liners and the `qParam_coeff_unique` API the same way. Its output is a
**corrected estimate and work order**, not just go/no-go: record the pre-scout and
post-scout numbers. A scout may also **kill a route outright** — record the
missing ingredient and the unsupported figure. And a scout showing that the pin's
proof transcribes unchanged converts "new mathematics" into "transcription" and
de-risks the whole topic.

## 3. Executing a port

### 3.1 A module is a mathematical role, not a source file

FLT splits by artifact kind (`Def_`/`Thm_`/`S_`); the port splits by concept. One
`Def_` file covering four subjects becomes four modules. Consequences, all
binding:

- **Reading order is dependency order.** A reader walks the directory linearly.
- **Each module header states** its subject, the FLT source and pin, and what it
  assumes from earlier modules.
- **Docstrings carry the mathematics.** A name that does not state its content
  gets a one-line gloss; a construction gets a sentence saying what the object is.
- **Monomorphic helpers are documentation** — but write them the moment a `rw`
  reports no progress (§6), not before. A predicted rewrite-search gap never
  materialized, because FLT's own `[simp]` coefficient lemmas were already the
  named bridges.
- **Adopt mathlib's names where mathlib has them; keep FLT's where it does not**,
  and say which is which in the header.
- **No self-consumed lemmas.** A lemma whose only consumer is itself is not
  ported. This is the sole content a whole-node port leaves behind (§2.3): the
  node boundary is not a licence to carry its dead scaffolding.

### 3.2 Directory layout: one directory per theory

```
<Area>/
  Basic.lean        -- setup shared by every theory in the area, mathlib-only
  Defs/*.lean       -- shared vocabulary, when it is big enough to need a directory
  <Theory>/*.lean   -- one theory's modules, whatever role each plays in its proof
```

A directory holds **one theory**, with the area's shared vocabulary outside it.
The *second* theory is what triggers the `Defs/` split, not the first; until then
a move is churn, because the collision the rule prevents does not yet exist.
When the split is warranted it is mechanical: rename, fix importers, update the
record — the lakefile globs with `.submodules`, so no build-file change.

The tree should make the mathematics visible: if a proof has two independent
routes, the reader should see two directories meeting at a named module
(`AlgebraicCurve`: `WeilExchange/*` and `PrincipalDivisors/*` share only `Defs/`;
`ModularCurve`: `Analytic/*` and `Degree/*` meet at the cusp dichotomy and the
roof). **The mathematics should be a handful of abstract statements plus
concretisation** — `AlgebraicCurve`'s 5.5k lines are three statements,
`functionFieldGeneration`'s 3.8k are three generic lemmas. If that is not visible
in the tree, the split is wrong.

Two hygiene rules: keep imports specific (never `import Mathlib` in a library
module — two such files once took the planned build from 2,086 to 8,936 jobs), and
keep `spec/` outside the libraries so the library's green/no-`sorry`/seconds-warm
build stays meaningful.

### 3.3 One topic at a time, with a work order

A **topic** is the unit of work: one mathematical step, one module or a small
group, one work order. The order states, before any code: the subject, the pin
source, the exact statements to land, what it may import, the route/risk, the
verification commands, and the build bound. This forces the route decision before
transcription and gives the review something to check against.

The work-order template the topics converged on:

1. **Scope** — one paragraph, plus what is explicitly *not* this topic. State the
   in-scope nodes, and that each is taken whole (§2.3).
2. **Source** — pinned FLT files and line ranges; the wrappers for statements.
3. **Deliverable** — the module path and the declaration list, public vs
   `private`.
4. **Route** — the mathlib map, the alternatives, the recorded negatives, and a
   **stop-early risk list with a deviation protocol**: what, if found, means stop
   and re-scope rather than push on.
5. **Build discipline** — the bound and the ladder (§3.5); copy it in.
6. **Verification** — checker delta, consumer zones, `#print axioms`, `grep -c`
   of anything dropped.

Update the order's numbers in place when reconnaissance re-prices it (one
estimate was corrected 180–240 → ≈747 content lines inside the order). Re-cut a
topic that straddles several waves **by mathematical object** — construction,
then properties, then consequence — without splitting a node across waves.

### 3.4 Sets dispatched to agents, with review gates

Large efforts were run as **sets**: each set is one coherent
mathematical story dispatched to one agent, with the manager reviewing between
sets and writing the capstone. This is the mechanics; the staffing rule —
roughly 1,000 lines before subagents, one subagent per set, review before the
next — is §0.2. It worked, for reasons worth keeping:

- **Schedule on the real dependency fork, not the pin's section order.** After
  the shared prerequisite, independent routes run in parallel; prerequisites are
  real dependencies, so re-derive them instead of copying the pin's order. Keep
  topic numbering disjoint across parallel efforts.
- **Split on the mathematical fork, not on size.** Each set should carry one
  story and not need the other set's context. One effort split at its shared
  prerequisite, and the two routes' independent halves became a second set. A
  set's scope is a group of whole nodes; a node is not divided between sets
  (§2.3).
- **Write the next set's orders after the previous set is reviewed**, against the
  modules that actually exist. That is what makes a hand-off import real
  declarations instead of re-deriving them. Write the hand-off as part of
  finishing: the fixed names, instances and build budget the next set inherits.
- **The capstone is the review.** Writing it is the final wire test: a wrong
  binder, a missing lemma or a mis-stated hypothesis upstream surfaces as a
  compile failure in the reviewer's own file. Reserve it for the reviewer; in the
  larger efforts it compiled first try.
- **Re-scope a blocked topic; do not stall the effort.** Keep the tree green by
  setting the blocked file aside, write a focused follow-up order, re-dispatch.
  A `CuspDichotomy` re-scope solved in two rounds what the original topic could
  not.
- **Keep a per-set measured table** (rounds / declarations / lines / build /
  axioms / checker / consumer) and the friction log; when a set may not edit a
  consumer, record the replacement map and hand the dedup off. Close with a review
  (math clarity, clutter, what did not go to plan), a plan-vs-actual honesty
  section, and retire the blueprint to `topics/`.

### 3.5 The build ladder

Build time is the one unbounded cost, and the sessions paid full builds far more
often than needed. What a build costs is the **dependent cascade**, not the
breadth of the command: `lake env lean <file>` writes no `.olean` and recompiles
nothing; `lake build <module>` writes the `.olean` and builds dependencies, never
dependents; only building a dependent (or `lake build`) re-elaborates the cascade.
Measured here: 4–78 s to elaborate one file, 6–10 s per module build, 2–7 min per
wave cascade, 3.4 s for a fully cached whole-tree build. The full measurement,
the profiling, and the `maxHeartbeats := 4_000_000` global cap are in
[../notes/lean-build-cost.md](../notes/lean-build-cost.md).

**`lake env lean` must be given the package's options.** It runs Lean directly
and does **not** inherit the lakefile's `leanOptions`; `lake build` does. Without
`-DmaxHeartbeats=4000000 -DautoImplicit=false` the edit-loop check runs at the
default 200,000 cap and can report a timeout and a cascade of `unknown constant`
errors on a module `lake build` compiles happily — `WeightOne.Basic` fails at
30.7 s raw and compiles in 56.1 s with the options. Use the options, or
`tools/deps/build_ladder.py --tier check`, which supplies them.

| tier | when | command | cost |
|---|---|---|---|
| 0 edit loop | every edit | `timeout 60 lake env lean <opts> <file>` | no cascade; 4–78 s |
| 1 module done | file compiles | `timeout 90 lake build <module>` + checker | 6–10 s |
| 2 wave done | all wave edits in | one `lake build` (or its affected targets) | 2–7 min |
| 3 milestone | definition of done | full build + consumers + axioms | the tier-2 cost |

Four rules:

1. **Never `lake build` in the edit loop.** For a 2,500-line module the check is
   itself 78 s, so iterate on the declaration in `Scratch.lean` (§6).
2. **A wave edits each module once.** The cascade is the union of the edited
   modules' dependents; splitting a wave over one module pays it twice (a width
   family paid ~6 m 45 s twice).
3. **Price the cascade before triggering it** — dependent modules and lines; the
   build-cost helper in the unpublished `tools/deps/` tree reports 14 modules /
   20,732 lines ≈ 249 s for `WeightOne.Basic`, against the recorded 4 m 47 s.
4. **Serialize every `lake build`** with `flock`, and time it with wall **and**
   user/sys. Two agents on one tree contend rather than parallelize (a 4 m 34 s
   wall with 0.5 s user), and a heartbeat blow-up shows high user CPU. Never run
   builds concurrently.

If a build still misbehaves — a module that used to be fast is slow, a bound is
exceeded, a result looks wrong — do not investigate it inline: hand it to a
subagent whose brief is the build-cost note (§0.2, §0.4). Organisationally, keep
heavy modules at the leaves and shared hubs small and cheap, so later cost work
has less to do; the note holds the measurements and the recipes.

> **Build discipline (copy into each work order).** Edit loop `timeout 60
> lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
> `lake build <module>` per finished file; one `lake build` per wave; full build
> at the milestone. Serialize every `lake build` with `flock`, bound each with
> `timeout`, and time it: high user CPU is a blow-up, ~0 CPU is contention. Never
> raise `maxHeartbeats`.

Two traps the ladder exposes:

- **A stale `.olean` reads as a missing declaration.** After a `private` → public
  promotion, `lake env lean <consumer>` can report `Unknown constant …` because the
  defining module was not rebuilt; run `lake build <defining module>` first.
- **Importing a huge `.olean` is an edit-loop cost of its own.** `lake env lean`
  on a module that imports a 16 MB olean took 26 s before doing any work, so the
  per-file times above are a *lower* bound on such modules.

### 3.6 Keep the friction log while you hit friction

The API-drift list and the failure-mode write-ups were only cheap to produce
because they were appended to *during* the work. This is the highest-value
artifact for the next effort — more than the module list, which is derivable from
the code. Put it in the log as it happens; fold the generalizable part into §6–§7
at the end, and keep the rest in the record.

### 3.7 Porting order inside one effort, and the build economy

An effort's *internal* order is a planning object, not an accident of the pin's
file list. The order that carried the Deligne–Serre 54-node slice
([topics/PORTING-DeligneSerre.md](topics/PORTING-DeligneSerre.md); record
[logs/deligne-serre-port.md](logs/deligne-serre-port.md)):

1. **Definitions first**, in their own import order. Nothing can be stated before
   them, and they are leaves — cheap to build and to re-check.
2. **Shared blocks into *new* files second.** A new file touches nothing, so this
   phase cannot cascade. Scope it from `port_advise`, and scan by hand for
   repeated *definitions*: the tool's dedup counts proofs and misses a repeated
   `def`.
3. **Reconciliations in *existing* files third**, in one pass, then freeze them.
   This is the only phase that re-elaborates existing modules.
4. **Theorem sets, importees first**, over whole nodes — each set importing only
   levels below it, and a node never split between sets (§2.3).

Then execute it as sets (§3.4): one work order and one subagent per set, the
manager reviewing the tree before the next order is written. Two rules make the
hand-off real — a frozen file is never reopened (resolve locally, append to the
friction log, and let a final **refactor round** promote), and a worker who
reaches an unported prerequisite **stops at the boundary and reports** rather than
editing a closed file or weakening a statement.

**Why the order is a build-cost decision.** With a forward-import DAG a worker's
module is usually already built, so each set closes on per-module builds of
seconds and the only whole-tree build is the milestone: one ≈15,200-line effort
touched only its own eleven modules' `.olean`s, every set closed on 2–20 s builds,
and the milestone gate was 4,805 jobs in seconds. Transcribing pin files in
filesystem order instead puts each new file under a large cone that must be
re-elaborated, paying the full build at every step. The four ladder rules (§3.5)
are what keep it cheap.

## 4. Faithfulness, made mechanical

With a pinned source, correctness is checkable rather than trusted. Four
instruments, all cheap:

1. **The statement checker** (`spec/check_flt_statements.py`). It diffs every
   ported *statement* (signature up to the first top-level `:=`/`where`; for a
   `structure`, header plus ordered field names) against the pin, matching names
   after normalising namespace qualification. Proofs are ignored: the port adapts
   proofs, never statements. Target: `0 mismatched / 0 missing`, and the
   *identical* count is the per-topic progress metric — record its before → after
   move and reconcile any delta against the new public surface (any other delta is
   a bug). The instrument is text, so it has text-shaped rules:
   - **Verify the checker itself with a one-token mutation** — expect exactly
     `N identical / 1 mismatched / 0 missing` — then revert.
   - **A declaration that is ours** goes on an explicit exemption list *with the
     reason*, so "0 missing" keeps meaning something. Keeping auxiliary blocks
     `private` is what keeps the list short. A promotion of a pin-`private`
     declaration normally verifies through the checker's dotted-name fallback and
     needs no exemption; add an `OWN_PROOFS` entry only when the statement differs
     or the name is shadowed.
   - **A `scoped instance` is invisible to the checker on both sides** (`DECL_RE`
     admits only `private`/`noncomputable` before the kind), so it is neither
     matched nor reported missing. A `scoped instance` landed that way;
     downstream consumers activate it with `open scoped <Namespace>`. Keep
     `scoped` exactly where the pin has it — dropping it turns the declaration
     visible and creates a spurious `MISSING IN FLT`.
   - **Order `SOURCES` so the interface copy wins and append new entries last**,
     so a bare last-name match cannot flip; a shadowed last name is disambiguated
     by its dotted name (the exemption, when needed, is by full dotted name —
     widening the lookup key can break earlier promotions).
   - **The diff is textual, not elaborated.** A public declaration must spell its
     binders exactly as the copy the checker will match — in practice the
     `Theorems/` wrapper, not the `S_` file. The file builds either way because
     the elaborated types agree; only the checker notices. Take the binders from
     the wrapper and use the `S_` file only for the proof body. This rule recurred
     for four consecutive topics before it was applied from the start.
   - **A `def` whose pin binders came from a `variable` must keep them there.**
     Section variables — even when made explicit by `variable (…) in` — never
     appear in the raw source, so spelling them inline builds but reports
     **MISMATCH**. Transcribe the `variable … in` (or section) form verbatim for
     every `def`/`abbrev` that takes type/field arguments, and re-run the checker
     before trusting the build. Same class as "unused section variables are
     auto-omitted" (§6); the checker is the only instrument that sees it.
   - **The `kw_` prefix is erased on both sides, in the name *and inside the
     statement*.** A promoted helper is renamed at the prefix-stripped pin name,
     so the prefix is noise for a statement diff. The in-statement erasure is
     load-bearing, not cosmetic: a declaration whose statement *mentions* a
     promoted map could not be promoted at all without it, since the renamed map
     would change the statement text. Consequence: a one-token drift in a
     **promoted** declaration surfaces as `missing`, not `mismatched`, so when a
     column carries promotions, read `missing` as well as `mismatched`. The
     erasure must also fire after a `.` (a *method-style* reference
     `L.kw_toPointHom` must match `L.toPointHom`), and it is monotone — it can
     only turn a mismatch into a match.
   - **The checker reads modifiers from the declaration's own line and ignores
     `scoped`**, and it is text-only — it never invokes Lean, so it works on a
     module whose proofs do not elaborate. Run `raw_declarations` directly on a
     module not yet in `PORT_FILES` for a faithfulness probe (definition-only
     modules get coverage by name against the pin's `Definitions/` files), and
     when a module is stuck in a failing edit loop
     ([../notes/lean-build-cost.md](../notes/lean-build-cost.md) §2), run the
     checker first: a statement-shaped problem outranks the proof problem.
   - **`--` line comments mis-align the checker's namespace tracker**: block
     comments are stripped in one pass and line comments in a second, so a `--`
     comment shifts every later namespace event. The **primary** last-name lookup
     is unaffected, but the *dotted* name (used by `OWN_PROOFS` and
     `--prop-bodies`) is wrong. Write header prose in `/- … -/` blocks.
2. **A consumer** (`spec/<X>Consumer.lean`) outside every library. Its error
   count is the deliverable metric, and each zone must contain a **real, executed
   cross-module composition** — no `#check`s, no `sorry`; deleting any one module
   must make it fail. A module can build green and sit in no import chain at all,
   and nothing fails until it is used. Extend the zones per set, each zone
   recording a different kind of claim. Where a concrete instantiation needs
   unported hypotheses, state the test in hypothesis form and keep the named
   instance `private` inside the module; prefer zones whose hypotheses are all
   discharged from ported material, add a non-vacuity `example` when the port adds
   a corollary with no pin counterpart, and use `#eval` for numeric checks. A
   definitions layer needs a *concrete instantiation*, not just abstract-type
   applications.
3. **`#print axioms`** on every headline, to confirm no `sorryAx` crept in — the
   ports come back with `[propext, Classical.choice, Quot.sound]`. **`#print
   axioms` cannot see a `sorry` inside a `def`/`structure`/`instance`**, so those
   are never left `sorry`-closed; work definitions bottom-up, statements top-down
   from the wrappers, and count `sorry`s from the build's warnings rather than a
   grep over prose.
4. **A coverage report**, where one exists, closed to `0 / 0 / 0`.

When the capstone is conditional, track its debt counter as each field lands
(the `functionFieldGeneration` capstone: 7 → 0) and price the deferred cluster
separately. When every premise is an argument or already proved, the consumer's
abstract-square wire test is the capstone's analogue, and saying so is a finding
(the `AlgebraicCurve` port has no `Spine.lean`).

When a public helper moves or is demoted, two mechanical consequences: demotion
drops it from the compared count by exactly the number demoted (the expected
signal, not a silent loss), and a move must update `PORT_FILES` at the new path or
the declaration silently stops being verified.

## 5. Structure and sharing across theories

The aim is that **real mathematics is written once**. Expense is distance from
mathlib (§1), so a real result left `private` and re-derived in the next theory is
pure loss; glue and trivia are not worth exporting.

- **The measure is mathematical content relative to the project**, not size or
  today's consumer count; the test is what another theory would otherwise have to
  re-derive. `Defs/` is for structures that carry later mathematics
  (`IntegralStructure`, `Eigenform`, `HeckeOperator`), not a file of general
  lemmas or a trivial abbreviation. Share real math even with one consumer today,
  but keep glue and trivia unexported.
- **A theory exports only from its own domain.** A fact about `ZMod` residue
  classes or a `tsum` over `divisorsAntidiagonal` must not be reachable by
  importing the Eisenstein module.
- **A helper that only adapts another theory stays `private` in the consumer.**
  Unfolding mathlib's `eisSummand` or specialising the slash action is glue;
  exporting it makes callers depend on a theory they are not using. If such a
  helper is commonly needed, promote it in the theory it adapts.
- **Generalise near-duplicates, do not copy them.** Copies that differ only in
  binder spelling (a section variable vs an explicit binder) or in `[NeZero]`
  position become one lemma; the statement checker sees the text, the elaborator
  sees the binders, so fix both (§4). A `def … : Prop` class declared in two pin
  files under the **same name** but with different (unused) instance binders is the
  same case: declare the more general copy once — the one the pin's own proof
  produces — and let the stronger-binder consumers resolve to it; the checker
  matches any pin candidate, and the `--prop-bodies` pass confirms the body.
- **Namespace policy is decided before the wave, from the pin's own namespace and
  sibling vocabulary** (one directory was `ModularCurve/` because every pin file
  was `*_ModularCurve_*` and the shared `dedekindPsi` already lived there). A
  home's public names must be reachable under the spelling consumers use, or the
  wave breaks even when statements match; an internal namespace plus a
  consumer-namespace alias is fine if the two agree.
- **Check for co-import collisions before the consumer is designed.** Two modules
  can each be green while being **unimportable together** — a public name declared
  in both, or a plain and a `scoped` instance of the same class. No graph tool
  sees it; it surfaces as `environment already contains …` only when a consumer
  needs both cones. Grep the planned consumer's import set for duplicate
  declaration names, and register a collision in
  [CARRY-FORWARD.md](CARRY-FORWARD.md) rather than renaming a frozen public name
  mid-wave.
- **When a collision is between a pin name and one of ours, the fix is `private`,
  not a rename.** A `private` name is mangled (`_private.<Module>.<n>.<name>`), so
  it cannot clash at the environment level. Mark ours `private`: no rename, no
  shim, no `spec/` split, and the instance stays findable by search. Reconcile in
  the confirming build: the checker reads only non-private declarations (add it to
  `OWN_PROOFS` with its reason if it was compared), and consumers that relied on
  the instance by name must still elaborate. **Do not make the edit while another
  set is mid-check.**
- **`private` and local instances are a first-class build tool, and our
  verification does not depend on the elaborator.** Prefer a local `haveI`/`letI`
  or a `private` instance over making instance search find something globally: it
  is cheaper to elaborate, it cannot collide, and the statement checker is
  text-only, so nothing about faithfulness rests on a declaration being public.
  Reserve *public* for the pin's own names and the port's exported API.
  (`notes/lean-build-cost.md` §2 shows what instance search costs when it goes
  wrong.)
- **Home is a build-cost decision.** Promote to the module where the needed type
  is available, rename at promotion when the pin name is taken (keeping a local
  alias), and host a node on the leaf side of a hub boundary when the mathematics
  admits either home: moving two nodes from a 56-module / 39,742-line hub to a
  zero-dependency leaf changed the whole-tree build from ~14 min to 7 s. The
  checker is module-agnostic (it needs only the home in `PORT_FILES`). Record the
  deviation; do not use this to split a genuine theory across modules.
- **Name a promoted helper at the prefix-stripped pin name** (`kw_g₂_ofTau` →
  `g₂_ofTau`); the checker verifies the promotion through its `stripped_source`
  fallback, printing `RENAMED`. A declaration merely transcribed at its pin name
  keeps the pin's name, `kw_` included; a module-local helper is `private` with a
  content name. Never leave a declaration both public and stripped. Stripping a
  pin-public helper with consumers outside the effort is deferred, not skipped:
  record it in [CARRY-FORWARD.md](CARRY-FORWARD.md).
- **Export a topic's outbound interface so the next topic imports instead of
  copying** — one topic exported its `RealL`/closure and two Cauchy lemmas
  precisely because the pin duplicates them in the next topic's file.
- **Dissolve "externals"/"misc" modules into subject homes**, and give a generic
  cross-theory count its own top-level area rather than a theory's `Defs/`.
- **Keep an alternative or narrative route in a separate library that is built
  but not diffed** (`Reserve/…`, excluded from `PORT_FILES`), and never import the
  two routes together when they declare the same theorems.
- **Promotion shrinks its host module; measure it**, and a tight public surface
  is a deliberate cost — keep named instances and wire tests `private`.

## 6. Proof engineering: the failure modes that cost rounds

These are tactic- and kernel-level mismatches, not mathematics. Expect them; they
are cheaper to recognise than to rediscover.

**Rewrite-search gap.** mathlib's generic `map_sub`, `Jacobian.comp_smul`, etc.
may not fire under `rw`/`simp` when the function argument leaves implicit
instances unresolved, even when the pattern looks identical. The remedy is a
monomorphic helper proved by `exact`, which then rewrites:

```lean
lemma polyToField_comp_smul (P : Fin 3 → Poly) (u : Poly) :
    polyToField ∘ (u • P) = polyToField u • (polyToField ∘ P) :=
  Jacobian.comp_smul polyToField P u
```

Reach for this the moment a `rw`/`simp only` reports no progress on a goal whose
pattern you can see.

**`rw` and `simp_rw` do not unfold `abbrev`s.** Use `change` to state the
unfolded goal, or `simp only [name]`. This recurred across several ports.

**Prove the equality once, then rewrite through it.** When a lemma is stated
with a different but definitionally equal head, `rw` cannot match it. Prove the
identification by `rfl` and rewrite through it; trying to `change` the goal can
cost a multi-minute `whnf`.

**A goal stated against an abstract `*_aux` lemma can blow the defeq budget.**
FLT often ends a computation with `exact foo_aux h`; ported literally it can
time out (one instance was 299 s). Push everything into normal form first and
finish with `field_simp; ring`, supplying `field_simp`'s non-zero hypotheses
explicitly.

**`FunLike` at a bare function type.** A lemma quantified over `FunLike F ℍ ℂ`
instantiated at `ℍ → ℂ` unfolds `DFunLike.coe` without bound;
`UpperHalfPlane.qExpansion_coeff_unique` cost 5.1M reductions — and timed out at
*both* the 200,000 default and the project's 4,000,000 cap, so the cap is not the
lever. Pass the bundled form (or restate over the concrete function).

**A large slow module is usually cumulative, not one blow-up.** Bisect *by
milestone*, not by declaration: one 3,761-line module was 53 s of `lake env lean`,
4.5 s at the head and the rest spread across sections, with no single declaration
over the default cap. A genuine blow-up has one declaration and one error.
Attribute a slow module to defeq/instance synthesis and budget the next heavy
module accordingly.

**`backward.isDefEq.respectTransparency.types false` is often the pin's own
setting**, not a port hack — the pin sets it in eleven places, and without it the
pin's `simp` calls fail. Transcribe it where the pin has it rather than weakening
the proof.

**A kernel `Subtype.val` defeq between two concrete `IntermediateField.adjoin`
carriers.** Symptom: a `(kernel) deterministic timeout` on an `rfl`-looking
coercion lemma, then cascading `unknown constant` errors for later declarations.
Diagnose by isolation at a low cap, not by staring at the proof. The fix is a
generic coercion proved once at abstract carriers:

```lean
private def ifRE (S T : IntermediateField K L) (h : S = T) : ↥S ≃+* ↥T where
  toFun x := ⟨↑x, h ▸ x.2⟩
  invFun y := ⟨↑y, h.symm ▸ y.2⟩
-- then the concrete equivalence is `ifRE _ _ (eq_of_carriers …)`
```

`CuspDichotomy` went from 3 m 09 s to 16 s this way. Related: a cross-field
`algebraMap` `rfl` should go through
`IntermediateField.coe_algebraMap_apply` on both sides, and a propositional
`haveI` should be `have`.

**Instance-search timeouts** are fixed by explicit local instances
(`Algebra.IsIntegral.of_finite`, `Module.Free.of_divisionRing`), not a larger
budget, and sometimes by naming the element too: an `Algebra.IsAlgebraic (adjoin K
{t}) F` goal times out in the *search itself* until `t` is bound once (`private
abbrev`) **and** the instance supplied. Every such case is recorded, with a
re-runnable guard, in [instance-friction.md](instance-friction.md)
(`spec/InstanceFriction.lean`); add an entry and re-measure after a mathlib bump.

**Two `Algebra`-like instances in one context is a type error, not a cost.** A
`letI : Algebra ℚ K := DivisionRing.toRatAlgebra` in a declaration's *statement*
does **not** agree with an ambient `variable [Algebra ℚ K]`: they are different
`Algebra` structures, so `K₀ : IntermediateField ℚ K` denotes two different types
and the failure is a hard `Type mismatch` at the `∃`-intro — which downstream
misreads as `isDefEq`/`whnf` noise and misdiagnoses as a budget problem. Keep
exactly **one**: if the statement carries the pin's `letI`, its section must not
also carry `[Algebra ℚ K]`. Diagnose with a three-line `example` that `rfl`s the
two types; do not restructure the proof.

**An instance keyed on a semireducible `def` is invisible to search.** mathlib
supplies `instance : (W.map f).IsElliptic`, but a goal written `E⁄R` cannot reach
it: `WeierstrassCurve.baseChange` is a `def` (unlike `Affine.baseChange`, an
`abbrev`), so search — which runs at reducible transparency — never unifies
`baseChange E R` with `W.map f`, and no `maxHeartbeats` /
`synthInstance.maxHeartbeats` value helps. State the instance in the goal's
spelling and prove it at the unfolded spelling:

```lean
private instance … : (E₀⁄(↥K₀)).IsElliptic :=
  inferInstanceAs ((E₀.map (algebraMap (↥K₀) (↥K₀))).IsElliptic)
```

This is the pin's `scoped instance … := inferInstanceAs (…)` bridge pattern
(`S_:3566–3568`): a transcription must carry those bricks over, because dropping
them turns a one-line bridge into ten engine-call timeouts. Register:
[instance-friction.md](instance-friction.md) IF-003. The general rule: **when an
instance's head is a term built by a `def`, search cannot cross that `def`;
supply the brick explicitly.**

**Recipe: capture what search picked, then supply the instance by hand, so search
never runs.** This is the default response to an instance-shaped failure. A brick
is a **cache of a synthesis result**: a key (the goal's exact spelling — search
matches a local instance by syntactic head first), a value (the term search would
have built), and an invalidation rule.

1. **Capture the term** — `#synth <goal>` prints the instance it would use (or its
   failure text); `set_option trace.Meta.synthInstance true` / `diagnostics true`
   gives the path and the cost. Record the printed term: it is the *value* the
   brick must reproduce.
2. **Supply it in the goal's spelling** —
   `haveI : <goal, verbatim> := inferInstanceAs (<same type, spellable form>)`.
   A local instance is matched by syntactic key before any search, so the goal's
   cost drops to zero; one stated on the *unfolded* spelling does not match a goal
   written with notation.
3. **If no instance exists at any spelling, prove it.** The common case is a
   missing tower: `haveI : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq
   fun r => by rw [IsScalarTower.algebraMap_apply R K C,
   IsScalarTower.algebraMap_apply A K C, IsScalarTower.algebraMap_apply R A K]` —
   one `rw` per known tower. (A circular `rw` of the goal's own tower wastes the
   round.)
4. **Use `letI` when the instance carries further instance arguments** (e.g.
   `AbelTheorem W` carries a `GenusOnePlaceGate W`): `letI` *inlines* the value so
   the caller's terms become the use site's instance arguments, while `haveI`
   leaves a distinct local fvar and the argument check fails with "synthesized
   type class instance is not definitionally equal". The same applies to a
   `∀ [DecidableEq …]` block, where the pin's `subst hdec` aligns the two.

Capture the term with `#synth <goal>` (or `set_option trace.Meta.synthInstance
true` / `diagnostics true` on the failing declaration) in a gitignored `tmp/` probe
with the module's own imports, so the spellings match. For a problem the register
already knows, `spec/InstanceProbe.lean` holds one labelled `#probe` per entry and
`spec/check_instance_probes.py` diffs its output against the recorded terms
(`RECAPTURE` / `REGRESS` / `RETIRE?`); re-run it after a mathlib bump — a stale
brick is invisible, not wrong, so the guard, not the build, notices.

For a **data-valued** class (`Algebra`, `Module`, `SMul`, `Fintype`, …) the
capture is load-bearing: a type-only guard accepts a wrong brick, because e.g.
`DivisionRing.toRatAlgebra` and an ambient `inst✝` are different *values* that
coincide in type. Assert it:
`example : (<brick> : <class> <args>) = <captured term> := rfl`.

**Place the brick at the narrowest scope that hits it.** Call-site `haveI` →
section-scoped `private instance`/`letI` → module-level `private instance` →
public `instance`/`scoped instance`, widening only at a second site. A local
instance is tried by every search in its scope, so a broad head taxes the whole
region. Use `haveI` for a Prop-valued class, `letI` when the instance carries
further instance arguments (step 4).

Hand bricks are also the durable form: they make the module's instance
requirements explicit and reviewable. Being a cache, a brick is invalid after a
mathlib bump or when its home module or the goal's spelling changes. What bricks
do **not** fix is keyed rewriting between two spellings (`rw`/`erw`) — that is
term unification, not typeclass search.

**Two declaration-shape facts the checker cannot see.** Unused section variables
are auto-omitted, so a declaration under `variable (N : ℕ) [NeZero N]` whose body
never mentions `N` comes out without `[NeZero N]` — transcribe verbatim and check
the signature rather than "restoring" it. And `linter.style.haveILetI` fires on a
`haveI` in a `Prop` goal even when the instance is used; if it came from
`intro`/`rintro` it is redundant, otherwise prefer `have`.

**`private` is file-scoped but not dot-accessible across namespaces.** A `private`
declaration is reachable later in the same file, but only by its qualified name:
with `private theorem bar (s : Foo.S) …` in `namespace Foo`, `Foo.bar s` resolves
from `namespace Baz` while `s.bar` fails with `Invalid field … the environment does
not contain Foo.S.bar`. The pin gets away with bare names because its shared
prelude sits in one file with the namespace open. So a re-derived pin-`private`
helper used from another namespace in the same module must be written
`PeriodPair.mem_scale_lattice_iff L α`, not `L.mem_scale_lattice_iff` — a six-line
probe settles it.

**A "ported prelude" row in a work order is a claim to `grep -c`, not a fact.** Pin
prelude helpers listed as "ported; import" were often `private` in the port (hence
unimportable) or absent entirely, and one absent public name was missing from
`port_advise`'s substitution list too — only a declaration-line `grep -c` over
`FLTForHuman/` settles it. Re-derive the `private` ones in the consumer
(`private`, content name) and land missing public ones at their pin names.

**A generic cross-theory block belongs in its own top-level area.** The pin once
wrapped 21 `ℤ²`-lattice invariants in `namespace QuaternionAlgebra` for no
mathematical reason — they are mathlib-only. Re-homing them to
`Algebra/IntPairSubgroup.lean` cost one header (~15 lines) and bought a 244-line
leaf that compiles in ~3 s and cascades to one module; the checker matches by last
name, so no `SOURCES` work was needed. Do the generic module first and hold it
fixed.

**Iterate in a gitignored `Scratch.lean`.** Put experiments and `#check @name`
probes there; the most useful probe when a rewrite or instance fails is
`#check @name` on the lemma you think you are using.

**A `scoped notation` can shadow a *binder name*, and the failure is a parse
error far from the notation.** `open scoped Polynomial.Bivariate` brings
`scoped notation "Y" => …`, after which `Y` is a *token*: every `∃ X Y : ℂ → ℂ`
binder and `⟨…, X, Y, …⟩` pattern becomes a syntax error naming only the second of
a pair. Open such a scope per declaration (`open scoped … in …`), never file-wide,
and spell the expansion in proof terms where a `Y` binder is needed. Same class as
`open` name ambiguity: a scope changes how *identifiers* lex.

## 7. Drift checklist (mathlib `v4.34.0`)

API drift is the recurring real cost. The list below is the accumulated set; when
a new pin is taken, re-run it and append.

**The pin is not on this line.** `anthropics/fermats-last-theorem@aa2d8b3` is Lean
`v4.33.1` / mathlib `db584cd6` (the `v4.33.0` bump); the port is Lean `v4.34.0` /
mathlib `v4.34.0`. Expect drift in every set, and do not write "the pin is on the
same mathlib line" into a work order.

| old / expected | `v4.34.0` |
|---|---|
| `if_pos h`, `if_neg h` | `ite_eq_left h`, `ite_eq_right h` |
| `dif_neg h` | `dite_eq_right h` |
| `Polynomial.finite_setOf_isRoot` | `Polynomial.finite_setOfPred_isRoot` |
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` |
| `Affine.Nonsingular x y` | `W.toAffine.Nonsingular x y` (curve explicit) |
| `Submodule.card_bot` | does not exist — `AddSubgroup.card_bot` |
| `Submodule.mem_torsionBy_iff.mp` | takes explicit args: `(… _ _).mp` |
| `mul_cancel_left_mem_nonZeroDivisors` | `mul_left_cancel₀` in a domain |
| `Jacobian.map` | a separate def from `WeierstrassCurve.map` (defeq) |
| `Affine.Point.some_ne_zero` | does not exist — `cases` on the equality |
| `ext i` on `Fin 3 → MvPolynomial …` | recurses; use `funext i` |
| `nTorsion n` (`n : ℕ`) | `Submodule.torsionBy ℤ M n` takes `n : ℤ` |
| `HahnSeries.embDomain_notin_range` | `HahnSeries.embDomain_of_notMem_range` |
| `isIntegral_algebraMap_iff` | takes `FaithfulSMul`, not an injectivity proof |
| `Submodule.torsionBy.zmodModule` | does **not** exist — the instance is `AddSubgroup.torsionBy.zmodModule`, and search does not reach it from the `Submodule.torsionBy` carrier; keep the pin's local instance under its own name |
| `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` | argument order changed: `(f) (hf) (I)` |
| `Monoid`/`Group`/`Ring` projection chains `.1.1.1` | use `g.mul`, or `(g.mul, g.add)` |
| `Equiv.module` / `Equiv.linearEquiv` | `AddEquiv.*`, with instance diamonds needing explicit instance arguments |
| `TFAE.out` | 1-based: `.out 0 2` → `.out 1 3` |
| `continuous_add_right a` | does not exist — `continuous_id.add continuous_const` |
| `eventually_of_mem h …` | namespace-qualified: `Filter.eventually_of_mem h …` |
| `unfold yGen` (a `def` wrapping another `def`) | `unfold yGen yCoord` — the pin's one-name unfold leaves the inner `def` folded |
| `Polynomial.induction_on`'s `monomial` step | v4.34 states the step `motive (C a * X ^ n) → motive (C a * X ^ (n + 1))`; the pin's `monomial n a ih` proof transcribes unchanged |
| `range f`, `mem_univ`, `isPreconnected_univ` | `Set.range f` / `Set.mem_univ` unless the module `open Set`s (the pin does); `isPreconnected_univ` is unqualified |
| `Uncountable ℝ` (for `Complex.ofReal_injective.uncountable`) | an instance only once `Mathlib/Analysis/Real/Cardinality.lean` is imported, which is **not** transitive through `Analysis/Complex/Basic`; add the specific module |
| `Equiv.infinite_iff` | for `e : α ≃ β` it reads `Infinite α ↔ Infinite β`; check the direction at the call site (`e.infinite_iff.mp` from `Infinite α`) |
| `Prime.dvd_finset_prod_iff` | `Prime.dvd_finsetProd_iff` (the pin's `first \| … \| …` already falls through to it) |
| `ModularForm.coe_smul`, `ModularForm.coe_zero` | `FunLike.coe_smul`, `FunLike.coe_zero` (the `ModularForm.*` names are deprecated aliases in `v4.34.0`) |
| `Finite.of_equiv` / `Set.toFinite` | `Nat.finite_of_card_ne_zero`, with the `Finite` instance passed explicitly |
| `Nat.card_zmod` | no longer needs `NeZero m` — the pin's `haveI : NeZero m` is dropped, not suppressed |

The recurring *shapes* of drift, beyond a rename:

- **A rename is not the same as a re-typed or re-ordered lemma.** The `Ideal`
  ramification API moved argument order and module, and the deprecated module's
  replacement changed the sum's shape; three statements were kept on the old text
  under a reasoned `set_option linter.deprecated false`, with the migration
  recorded as a residual item.
- **A deprecated module can be dropped, and a module path is not always a module**
  (`Mathlib.LinearAlgebra.Quotient` is a directory — import `.Basic`; one
  `Mathlib.Tactic.Omega` path has no olean).
- **Blanket `import Mathlib` hides transitive dependencies** — expect 3–5 missing
  per file when converting to specific imports, and instances/notation are often
  not re-exported by a neighbouring module.
- **Tactics and terms can change shape silently**: `convert h2 using 1` reorders
  goals (use `h2.congr_deriv`), a `congr(...)` equation form yields a different
  equation, and a non-reducible `def` stops elaboration from unfolding (bind the
  value with `let`).
- **`open` can create name ambiguity** — qualify instead (`UpperHalfPlane.I`).
- **A `rfl` that used to close can instead burn the whole heartbeat budget.** A
  `rfl` for an `hq` equality ran a `whnf` to the 4,000,000-heartbeat cap before
  failing. The fix is not a bigger cap but naming the missing bridge in the
  `simp only` list (`Polynomial.map_X`, `IntermediateField.algebraMap_apply`).
  Treat a slow *definitional* step as an unfolding problem, and look for the lemma
  that states the equation the `rfl` used to see.
- **Self-base-change is not definitional in `v4.34.0`.** The pin lets
  `(E F)⁄F` be `E F` and computes with it; in the port carry
  `have hb : (E F).baseChange F = E F` and transport witnesses with `hb ▸ ⟨e⟩`
  (the adaptation at `WeierstrassCurve/Velu/CyclicCount.lean:429`). Two sets have
  now paid for this independently — read that file first.
- **Transcribe the pin's `linter.*` suppressions exactly; never its
  `maxHeartbeats`.** The lint options are part of the pin's declaration
  environment (86 landed modules carry
  `set_option linter.unusedSectionVars false`), and the review gate is a
  warning-free tier-1 elaboration. Lint classes the pin does *not* suppress are
  real: fix those as proof edits (`haveI` → `have`, dropping unused `simp`
  arguments), do not add suppressions.
- **The `haveI` style-linter fix is not universal**: instance search may not find
  a plain `have` where `haveI` works, so suppress the linter locally rather than
  weaken the proof.
- **`omit [NeZero M] in` and file-scope linter suppression keep a pin proof
  verbatim without changing the checker's text**; `set_option … in` cannot follow
  a doc comment (use `--` line comments there).
- **A pin's `set_option maxHeartbeats N in` is a claim to re-measure, not a
  fact.** The pin may carry `6_400_000` where the project-wide `4_000_000`
  suffices; time the port's own ceiling before budgeting a bump (and never raise
  the cap to make a declaration fit).
- **A pin's `synthInstance.maxHeartbeats` bump is the same kind of claim.** A
  capstone carrying `synthInstance.maxHeartbeats 1600000` / `maxHeartbeats
  16000000` elaborated under the global `4_000_000` cap, so neither bump was
  transcribed. A library theorem can also be cheap while its *concrete-instance*
  use is not: applying a headline at a concrete `weierstrassCurve` can exceed
  3 m 20 s through the `AdjoinRoot` defeq stack. Keep a `spec/` capstone zone
  hypothesis-form and put concreteness in the ground field.
- **`time` under-reports `lake env lean`.** `lake` forks `lean`, so the
  grandchild's CPU is not charged to the measured command; a run that reports
  `user 0m0.5s` can be elaborating hard. Treat wall time as the real figure (and
  do not conclude "hung").
- **`end A.B` closes *both* nested scopes.** Under `namespace A` / `namespace B`,
  `end A.B` also ends `A`, silently de-nesting every declaration after it; write
  two bare `end`s. The symptom appears *downstream* of the mistake (unknown
  identifiers from the de-nested namespace), so on a slow module it costs a full
  re-elaboration round to find.

Two cross-cutting facts worth remembering: `CuspForm` does not extend
`ModularForm` (bridge with `CuspForm.toModularFormₗ`), and
`(W.map f).IsElliptic` is all a base-change `IsElliptic` instance needs.

## 8. Tooling

The graph tools read FLT's own docs-site data and our port; none of them runs
Lean. They live in the unpublished `tools/deps/` tree.

| tool | answers |
|---|---|
| `fltdata.py`, `explore.py` | what a pinned theorem is, its premises, consumers, path |
| `prune.py` | which nodes a replacement lets the port drop (reachability, not closure) |
| `frontier.py` | how far a target still is from the ported frontier, in new **source-file** nodes — so a half-ported file still reads as unported (§2.3) |
| `port_graph.py` | our port's module/declaration graph: blobs, duplicated private proofs grouped into blocks, promotion candidates, closures |
| `port_advise.py` | before a port: what the port already has (substitute), what the target set re-proves (port once), what differs only by binders (generalise), and what each public declaration drags |
| `build_ladder.py` | the dependent cascade of an edit, the cheapest sufficient build under `flock`/`timeout`, a wave plan that re-edits a module, and (`--audit` / `--profile`) which modules are expensive to edit and which declarations cost the time |

The workflow loop: a coverage report from the pin graph chooses the target;
`port_advise.py` prices reuse and duplication before coding; `port_graph.py`
measures the redundancy the port created afterwards; the build ladder and the
checker are the per-wave gate. Because `frontier.py` prices in source-file nodes,
a partial node distorts every later estimate — the operational reason for the
whole-node rule (§2.3).

Two library-style uses worth knowing:

- **`fltdata` finds a pin module's consumers before scoping** —
  `d = FltData(); di = d.def_index[stem]; cons = [i for i in range(len(d.names))
  if di in d.stmt_defs(i) or di in d.proof_defs(i)]`.
- **The checker can be driven as a library** to diff a module that is not yet in
  `PORT_FILES` (load `spec/check_flt_statements.py` with `importlib` and call
  `raw_declarations`), and its `norm` is the reference for any statement
  comparison.

## 9. Open questions and recorded negatives

- **Hybrid vs faithful is a per-layer choice, and only a few mixes are measured.**
  No effort yet tested mathlib absorbing the core but not the periphery, or the
  reverse.
- **Round counts are not a cost model**; they track how often an agent stalled on
  a defeq or a name. Lines, declarations and named shape risks are stable.
- **Nothing is independently audited.** The "removed clutter" numbers are what
  each effort avoided writing, measured against FLT's own files, not a third-party
  check that the dropped items were dead.
- **Repo-wide prelude duplication is a separate effort.** Every port writes its
  own cone's shared prelude once; deduplicating the whole FLT repository (38
  files carry the slot prelude, 11 a parallel `jqModC` block) is larger than any
  single port and has not been attempted.
- **Recorded negatives are part of the method.** Examples to keep: mathlib has no
  `dedekindPsi`, no Γ₀ index formula, no short route from `CommonRoot`'s engines
  to `eq_of_isRoot_of_isLevel`; the `relNorm`/`normalizedFactors` norm block and
  `rval_aux` are irreducible as written.

## 10. Evidence: the efforts, their records and their reviews

| effort | target | measured | record |
|---|---|---|---|
| Elliptic torsion | `#E[n](K) = n²` | 13 modules / 3,362 lines / 292 decls | [logs/card-torsion-port.md](logs/card-torsion-port.md) |
| `functionFieldGeneration` definitions | Layer 0 (137 decls, 9 modules) | 1 round per layer against 20 budgeted | [logs/ffg-port.md](logs/ffg-port.md), [topics/ffg-retrospective.md](topics/ffg-retrospective.md) |
| `functionFieldGeneration` theorem | `functionFieldGeneration` | ≈3.8k lines, 304 statements | [logs/ffg-port.md](logs/ffg-port.md) |
| `PhiGen` splitting | `PhiGen.splits_prime_at_slot` | route decided before coding | [logs/phiGen-port.md](logs/phiGen-port.md) |
| `ModularCurve` Hecke | `ModularCurve.heckeOperatorsCommuteBar` | 26 modules, 1,240 statements, coverage 0/0/0 | [logs/mc-port.md](logs/mc-port.md), [topics/mc-retrospective.md](topics/mc-retrospective.md) |
| X₁ Hecke/diamond inputs | `ModularCurve.heckeDiamondInputsAll` | 11 modules / ≈3,550 lines; checker 4,436 identical, 0/0; cone 0/0/0; cover node 281 → 135 content via the tensor-product route; the `Pic0` action/torsion block **deferred** | [logs/x1-hecke-port.md](logs/x1-hecke-port.md), [topics/hecke/TOPIC-x1-hecke-diamond-inputs.md](topics/hecke/TOPIC-x1-hecke-diamond-inputs.md) |
| `AlgebraicCurve` exchange | the exchange reduction | 5,559 lines / 328 public decls, 618 statements | [logs/ac-port.md](logs/ac-port.md), [topics/ac-retrospective.md](topics/ac-retrospective.md) |
| Level vocabulary | `Γ_H`/`Γ₁`/cosets | — | [logs/level-port.md](logs/level-port.md) |
| T-side | `R = T` definitions | — | [logs/t-side-port.md](logs/t-side-port.md) |
| Eichler–Shimura | period-map injectivity | — | [logs/eichler-shimura-port.md](logs/eichler-shimura-port.md) |
| Sturm bound | weight-2 cusp vanishing | — | [logs/sturm-bound-port.md](logs/sturm-bound-port.md) |
| WeightOne rectification | refactor, no new math | 7,242 → 5,333 removable lines | [logs/weightone-rectify.md](logs/weightone-rectify.md), [topics/hecke/TOPIC-weightone-rectify.md](topics/hecke/TOPIC-weightone-rectify.md) |
| three small frontier nodes (factorisable test functions; `K(x)` `EssFiniteType`; Weierstrass principal divisors) | `AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn`, `AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional`, `WeierstrassCurve.Affine.hasPrincipalDivisors_functionField` | 8 modules / 50 public decls; the Weierstrass place/RR/class-group API (~941 content lines, 27 citers) was **deferred** here and is now ported (see the genus-one place gate row) | [CARRY-FORWARD.md](CARRY-FORWARD.md) |
| `ModularCurve.Period` API + equivariant primitive | `ModularCurve.exists_hasEquivariantPrimitiveOf` | 4 modules; the period vocabulary, the `Γ₀(N)` period lattice, the general `periodOf`/`periodMapOf` layer and the 182-content-line headline construction; Hecke-stability / `PeriodTransfer` / Petersson **deferred** | [CARRY-FORWARD.md](CARRY-FORWARD.md) |
| genus-one place gate | `WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem` | 5 modules / 1,004 written lines; pin `S_` 2,288 raw / 1,032 net new; checker +51 identical, 0/0; consumer 0; the deferred Weierstrass RR/class-group/Abel block taken | [logs/genus-one-place-gate-port.md](logs/genus-one-place-gate-port.md), [topics/riemannRoch/TOPIC-genusOnePlaceGate.md](topics/riemannRoch/TOPIC-genusOnePlaceGate.md) |
| Vélu V2 (gateways + Ribet side) | `WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed` and the two Mazur gateways | 9 new modules / 1,671 written + 344 consumer; checker `5750 → 5805 identical`, promoted `312 → 311`, 0/0; whole-tree `9,303 jobs / 12.3 s` (+9 leaves, no cascade); one additive edit `+39/−0` in a 0-dependency leaf; three closure members already present under other names | [logs/velu-port.md](logs/velu-port.md), [topics/velu/TOPIC-V2-gateways-and-ribet.md](topics/velu/TOPIC-V2-gateways-and-ribet.md) |

Planning records (retired blueprints) are `topics/PORTING-*.md`; the mathematics
each port targets is in `../math/` and `../base/`.

## Appendix: section map from earlier revisions

The records and work orders were written against earlier revisions of this file,
which numbered sections differently (a "§3.x" was one of eleven approaches, and
"§7.x" was the definitions-layer experience). Use this map to resolve an old
reference; the playbook's own links now point at the new numbers directly.

| old reference | topic | now |
|---|---|---|
| §1 | what an effort cost | §1 (cost model) |
| §2 | clutter removed | §2.4 (dedup) |
| §3.1 | map to mathlib first | §2.2 |
| §3.2 | trace the capstone, nature column | §2.1, §2.3 |
| §3.3 | prove for the universal object, `aeval` | §6 |
| §3.4 | do not state the goal against `*_aux` | §6 |
| §3.5 | monomorphic helper / rewrite search | §6 |
| §3.6 | prove the equality once, rewrite through | §6 |
| §3.7 | `rw`/`simp_rw` do not unfold `abbrev` | §6 |
| §3.8 | pick mathlib's API as the interface | §2.2 |
| §3.9 | iterate in `Scratch.lean` | §3.5, §6 |
| §3.10 | keep the friction log while you hit it | §3.6 |
| §3.11 | bound every build; heartbeat blow-up | §3.5, §6, [../notes/lean-build-cost.md](../notes/lean-build-cost.md) |
| §3.12 | the build ladder | §3.5 |
| §4 | `v4.34.0` drift checklist | §7 |
| §5 | checklist for the next port | §0.1 |
| §6 | open questions | §9 |
| §7.1 | module is a role; math clarity | §3.1 |
| §7.2 | overlap with the first port | §10 (evidence) |
| §7.3 | the calibration; price the route | §1, §2.5 |
| §7.4 | make faithfulness mechanical | §4 |
| §8 | directory layout: one theory per directory | §3.2 |
| §9 | promotion and sharing across theories | §5 |
