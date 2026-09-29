# Porting FLT to mathlib — a playbook

A synthesis of the ports completed so far: the Elliptic torsion port
(`#E[n](K) = n²`), the `functionFieldGeneration` definitions layer and its
theorem cone, the `PhiGen` splitting cone, the `ModularCurve` Hecke layer, the
`AlgebraicCurve` divisor exchange, the level/congruence-subgroup vocabulary, the
T-side of `R = T`, the Eichler–Shimura period map, the Sturm-bound cusp
vanishing, and the WeightOne rectification. The per-effort *records* are in
[logs/](logs/); the closing *reviews* are `topics/*-retrospective.md`; §10 indexes
both with their measured numbers. This file is the method the efforts share, so
it is organised by principle rather than by which port taught it. Read a record
for what an effort did; read this before starting the next one.

Two conventions run through everything:

- **The pin is the authority, and faithfulness is mechanical.** FLT
  (`anthropics/fermats-last-theorem`, pinned; currently `aa2d8b3`) is the source
  of truth. Every ported *statement* is diffed against it by
  `spec/check_flt_statements.py`, not trusted. Where prose and Lean differ, the
  Lean is right.
- **The port is ours.** A module is a mathematical role, not a source file; shared
  mathematics is written once and promoted; adapters stay `private`. FLT's
  declaration *names* and *statements* stay, so comparison against the pin remains
  mechanical.

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

Before coding:

1. **Measure the cone** — files, raw and content lines, declarations, importers.
   From those numbers decide: port, re-derivation, or both (§2.1).
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
8. **Faithfulness from the first declaration** — statements spelled as the
   wrapper, added to `SOURCES`/`PORT_FILES`, consumer zones composing across
   modules (§4).
9. **Keep the friction log while you hit friction** (§3.6), and **drop nothing by
   inspection** — `grep -c` or `diff` (§2.4).

At the end:

10. Checker `0 mismatched / 0 missing`, consumer exit 0, `#print axioms` clean,
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
- **Build investigation is a subagent with its own brief.** When the porting agent
  hits a build problem the simple rules (§3.5) do not settle, dispatch a fresh
  subagent whose whole instruction is the build-cost note
  ([../notes/lean-build-cost.md](../notes/lean-build-cost.md)) plus the tool
  interface — not this playbook. Keep it a separate dispatch; do not fold it into
  the porting agent's task.

### 0.3 Discretion: this is a synthesis, not a contract

This file is distilled from several ports of very different sizes. Read it as
recorded judgement, not as a checklist to apply mechanically:

- **The stable core is small**: the pin is the authority and faithfulness is
  mechanical (§4); expense is distance from mathlib (§1); a module is a role and
  a directory is a theory (§3.1–§3.2); real mathematics is written once (§5); and
  the build ladder bounds the one unbounded cost (§3.5). Everything else is a
  heuristic with evidence attached.
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

Follow the build discipline as a matter of course — it is the per-work-order
block in §3.5. Two facts are easy to get wrong: `lake env lean` needs the
package's options (`-DmaxHeartbeats=4000000 -DautoImplicit=false`) to match
`lake build`, and this project's global cap is 4,000,000, so a blow-up does not
surface in ~20 s — the wall bound is the protection.

When a build misbehaves anyway, do not investigate it inline. Dispatch a subagent
whose brief is [../notes/lean-build-cost.md](../notes/lean-build-cost.md); the note
carries the measurements, the recipes and the tools
(`tools/deps/build_ladder.py --audit` / `--profile`).

## 1. The cost model

**Expense is the route's distance from mathlib, not the size of the source.**
Every effort measured this, in both directions:

| effort | source size | written | why |
|---|---|---|---|
| Elliptic torsion | cone 3,671 lines | 3,362 lines | the engine (`ω` division polynomial, complement multiplication) had left mathlib; the 1,164-line counting module was the *cheapest per line* |
| `functionFieldGeneration` theorem | 11,312-line structural pin sum | ≈3.8k lines (T14–T20) | reduced to three generic lemmas plus concretisation |
| `AlgebraicCurve` exchange | 5,423 raw `S_` lines | 5,559 module lines | line budget was accurate; risk register over-warned |
| `ModularCurve` Hecke | 10,569 raw lines | 7.6k content lines in band | four prelude cuts made it tractable |

Consequences for planning:

- **Count two kinds of lines.** *Raw* is the pin's text; *content* subtracts the
  `p2m_*`/`attribute` scaffolding, which is 28–35% of a pin cone and is never
  written. Budget content.
- **Budget in named shape risks, not rounds or lines alone.** A definitions
  layer dictated by pinned statements took 1 round against 20 budgeted; a
  2,002-line file was the right size but its *route* was the whole cost. When a
  risk register is written, expect it to over-warn: across the FFG, AC and MC
  efforts the named risks mostly failed to materialize, and the recurring real
  cost was API drift (§7).
- **A wrong statement is maximally expensive; a wrong proof is cheap.** This is
  why faithfulness is mechanical and front-loaded (§4) and why the route is
  audited before any module is written.
- **A faithful port is not line-for-line smaller.** The saving is what never had
  to be written (compat shims, dead wrappers, repeated preludes) plus writing 13
  focused modules instead of inheriting a 1,869-line engine.

## 2. Planning a port

### 2.1 Measure the cone

The blueprint (`PORTING-<X>.md`) is the planning record, and every one opens the
same way: a measured cone, taken as the transitive citation closure of the one
target theorem from the pin's doc-site graph, pinned to a sha and a mathlib
version. Use a coverage report (`studies/hecke-commute-bar-coverage.md` is the
model) and report every group as **three numbers — nodes, raw `S_` lines, content
lines** — where content subtracts `import`/`attribute`/`namespace`/`section`/
`variable`/`p2m_*`/comments/blanks. Scaffolding is 28–35% of raw and is never
ported, so a single raw figure overstates a cone. Give node-based and
content-based headlines separately: nodes overstate a cone whose weight sits in a
few large files. State the metric's bias — a name-based "already ported" test is
an upper bound and misses renamed ports.

Then make the table *act*:

- **Partition by mathematical route group and assign each node to its first
  consumer**, so the group totals sum to the measured total; that table is the
  work-order cut.
- **Price the on-path node set, not the import-level closure.** Check each node
  for proof-path reachability from the target; prune off-path nodes or carry them
  as a counted optional tail.
- **Measure the definition modules separately** (lines, declarations, how many
  are referenced by the cone). A low referenced fraction means "take the
  majority; count the rest per topic", not "port the file".
- Report the **outbound interface tier** (§2.3) and the **duplication already
  visible** in the pin (§2.4).
- **Ship a copy-pasteable regeneration recipe** with every measurement section.
  Do not hand-maintain a number that a script can reproduce.


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
  Drop the route's outgoing edges and recompute; an estimate that reads the graph
  without the shortcut can be orders too large (one residual read 12 nodes /
  5,595 lines where the closure-accurate answer was 5 / 235).
- **Prefer a cone that is a subset of work the endgame needs anyway**
  (`cone ⊆ closure(branch)`), and count only the route-specific addition.
- **Retire a route that adds no coverage the chosen statement does not give**,
  however pleasant it is; a strictly stronger and smaller route supersedes a large
  blob.
- **Disambiguate same-named objects before pricing** — "the Eichler–Shimura
  layer" named three different cones of different sizes in one study.
- **Verify a brief's named ingredient against the pin before trusting it.** One
  plan cited a lemma that does not exist and another that the route did not need;
  re-scout the exact name, hypotheses and crutch before pricing.
- **The pin's `p2m_export`/`p2m_open` list is the FLT → mathlib gap list**: check
  every name on it against the pinned mathlib, and a mathlib TODO comment is a
  reliable gap inventory.
- **Check a mathlib substitute's hypothesis strength against the source's.** A
  candidate can need primitivity where the cone has only `ζ^ℓ = 1`, or state a
  sum where the port needs a product.
- **Price the glue, not the mathlib-replaceable leaves.** A 199-line lemma with
  no replacement cost full price while a 76-line file collapsed to 8 lines.
- **Order the remaining tiers by outbound statement-demand, not file size**, and
  measure a pin file's *live* public surface before inheriting it: of one file's
  23 public names, only `solution` had a consumer, so its ~300-line cluster was
  never ported.
- **Scope a topic from the pin's import graph, not from its file list.** A work
  order that declared a set self-contained still needed four lemmas assigned to a
  later set, and a single declared import was insufficient — both forced re-scopes.


### 2.3 The gain test: what to port

Score a port on four gains — **organization, clutter never written, mathlib
alignment, truth** — never on line volume, because a faithful port is not
line-for-line smaller. Then choose order by what a node *buys*, using **outbound
indegree** (citers outside the cone) as the proxy: that is the reusable surface
the port purchases. The interface-tier topic added nine 5–50-line leaves that
carried 520 of the cone's 946 ≥5-indegree weight, and every one transcribed first
try; a later out-of-cone tier of 24 declarations covered 69% → 94% → 100% of the
weight it targeted. Cautions: indegree is global (a node can be load-bearing
elsewhere while irrelevant here — check it is in the cone), a library-shaped cone
with a broad interface scores differently from a citation chain, and an interface
can be split across pin namespaces, so the checker must be told which copy is the
interface (§4). State what the port is *not* in an out-of-scope table, and re-run
the gain test when the blocking gate is removed.

**Capstone shape follows from the premises, not from taste.**

- If the theorem's significant premises are not yet ported, build a *conditional*
  capstone: a proved artifact with no `sorryAx`, its fields a structure of named
  hypotheses. It checks the architecture, and the remaining work becomes an
  ordered list instead of a subtree (the FFG `Spine.lean`, debt 10 → 0). Keep the
  structure frozen once it lands; do not discharge fields opportunistically.
- If the premises are arguments or already-proved instances, do **not** add the
  device — the AC layer is unconditional and a `Spine` there would be ceremony.

### 2.4 Deduplicate before coding, and drop by count

The pin repeats itself heavily: a private prelude copied into every `S_` file
that consumes it (the slot vocabulary in 38 files, the fibre dictionary in four,
the Fricke/inclusion prelude in three, the modular-unit `q`-expansion in four).
**Find those copies in the plan and give them one home before writing the first
module.** Duplication detection is measurement, not inspection:

- `diff` two candidate `S_` files over their declaration spans and count the
  differing lines; a block that differs only in `p2m_*` strings is one
  development. Find copy counts mechanically (byte-identical blocks,
  `difflib.SequenceMatcher`, per-declaration `grep`), and price the saving as
  `(copies − 1) × block content`. A cleaner first cut is to diff *normalized
  bodies* — strip imports, namespaces, `p2m_*` lines and the `solution` tail —
  which isolates the duplicate groups exactly. (`tools/deps/port_graph.py
  --blocks` is the port-side view; `tools/deps/port_advise.py` is the pre-port
  view.)
- **Graph-node multiplicity undercounts copies.** A block with one graph node can
  ship five times because hidden exports carry their own copies; grep a
  distinctive marker lemma at file level. Quantify a dedup by *duplicate lines
  shipped* (one 895-line block: ~4,475 → 1,023), not by "a copy exists".
- **A large pin-`private` block re-exported by name mangling is a promotion**:
  write it once, publicly, at the pinned names, and record the promotion. Promote
  the *union* of the duplicate preludes, including sub-blocks absent from any
  single copy.
- **An out-of-cone byte-identical duplicate is resolved by exposing one copy**,
  not by rewriting it.
- If two pin declarations have the same proof, port **one** general lemma, not
  two.
- **"Which side stays" is the pin-public wrapper**; re-privatize the pin-private
  name and keep local aliases so untouched consumers keep working. Replace
  copies one file at a time, only where the statement matches — a copy carrying an
  extra hypothesis (`N ∣ 2`) is not a drop-in.
- **Do not merge a helper when sharing would invert the import graph.** One
  generic module deliberately re-writes a helper per module rather than import a
  whole downstream cone.
- **Strengthen a statement from the pin, never from the port's own weakened
  private copy** — one private copy had silently dropped a conjunct the
  downstream step needed.
- **Count occurrences (`grep -c`) before dropping anything.** A truncated
  `grep | head` once declared a load-bearing helper dead. Every dropped
  definition-module declaration needs a corpus count and a reason; "redundant" is
  a claim about the graph, not about prose.
- **Review the port's own private layer after a module closes**, not just the
  pin's copies: a "large file, many private theorems" pass found five redundant
  private declarations and three mathlib re-derivations in one module.
- Keep a list of **deliberately not cut** items with their counts. A deferred
  public API consumed elsewhere in FLT is deferred, not worthless.

### 2.5 Risk register and budget

Write the budget as a **correction ledger**: structural sum → minus dedup
savings (explicit negative rows) → plus definition modules → range, then apply
the effort's measured written-lines ÷ content-lines ratio (AC 1.25–1.45, MC
1.0–1.3). The budget *unit* is the named shape risk, not lines. Name the risks in
the order they will bite — a typeclass/coercion mismatch, a defeq between
concrete carriers, an instance diamond, a renamed API — each with its mitigation,
and mark each resolved or open with the measurement that resolved it. Record
**predicted non-events** too, so they are not budgeted again. Measured outcomes:

- line budgets have been accurate to within ~10% (AC: budgeted 5.1k–5.9k,
  measured 5,559);
- risk registers have been pessimistic (T5's orbit count, T6's instance block,
  T8's diamonds, T9's `PerfectField` all failed to materialize as budgeted);
- the real recurring cost was **API drift**, which is cheap per item but
  numerous — keep the drift list (§7);
- record a route win as a *measured delta* and re-price, rather than banking it.

Before committing to a route, audit it as a named `logs/audit-*.md`, re-deriving
load-bearing claims rather than trusting the brief. The audits that did this
found a slot-count closed form worth ≈110–150 lines, that `rval_aux` was ~64%
irreducible, and that one `relNorm` route answered "no".

### 2.6 The scout gate

When exactly one topic carries genuinely new mathematics, prototype it in a
gitignored `Scratch.lean` before dispatching it. The AC effort's T5 scout cost
3.2 s and converted its biggest unknown into a known quantity; the MC manager
pre-checked the `Φ` one-liners and the `qParam_coeff_unique` API the same way.
A scout is cheap insurance against a whole topic being routed wrongly. Its output
is a **corrected estimate and work order**, not just go/no-go: record the
pre-scout and post-scout numbers. A scout may also **kill a route outright** —
record the missing ingredient and the unsupported figure. And a scout showing
that the pin's proof transcribes unchanged converts "new mathematics" into
"transcription" and de-risks the whole topic.

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
  reports no progress (§6), not before. The FFG rewrite-search gap was predicted
  to dominate and never appeared, because FLT's own `[simp]` coefficient lemmas
  were already the named bridges.
- **Adopt mathlib's names where mathlib has them; keep FLT's where it does not**,
  and say which is which in the header.
- **No self-consumed lemmas.** A lemma whose only consumer is itself is not
  ported.

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
routes, the reader should see two directories meeting at a named module (AC:
`WeilExchange/*` and `PrincipalDivisors/*` share only `Defs/`; MC: `Analytic/*`
and `Degree/*` meet at the cusp dichotomy and the roof). **The mathematics should
be a handful of abstract statements plus concretisation** — AC's 5.5k lines are
three statements, FFG's 3.8k are three generic lemmas. If that is not visible in
the tree, the split is wrong.

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

1. **Scope** — one paragraph, plus what is explicitly *not* this topic.
2. **Source** — pinned FLT files and line ranges; the wrappers for statements.
3. **Deliverable** — the module path and the declaration list, public vs
   `private`.
4. **Route** — the mathlib map, the alternatives, the recorded negatives, and a
   **stop-early risk list with a deviation protocol**: what, if found, means stop
   and re-scope rather than push on.
5. **Build discipline** — the bound and the ladder (§3.5); copy it in.
6. **Verification** — checker delta, consumer zones, `#print axioms`, `grep -c`
   of anything dropped.

Update the order's numbers in place when reconnaissance re-prices it (one L3
estimate was corrected 180–240 → ≈747 content lines inside the order). Re-cut a
topic that straddles several waves **by mathematical object** — construction,
then properties, then consequence — rather than by the pin's section buckets.

### 3.4 Sets dispatched to agents, with review gates

Large efforts were run as **sets** (SET-1, SET-M1, …): each set is one coherent
mathematical story dispatched to one agent, with the manager reviewing between
sets and writing the capstone. This is the mechanics; the staffing rule —
roughly 1,000 lines before subagents, one subagent per set, review before the
next — is §0.2. It worked, for reasons worth keeping:

- **Schedule on the real dependency fork, not the pin's section order.** After
  the shared prerequisite, independent routes run in parallel; prerequisites are
  real dependencies, so re-derive them instead of copying the pin's order. Keep
  topic numbering disjoint across parallel efforts.
- **Split on the mathematical fork, not on size.** Each set should carry one
  story and not need the other set's context. AC split at the shared
  prerequisite T2; the two routes' independent halves became SET 2.
- **Write the next set's orders after the previous set is reviewed**, against the
  modules that actually exist. That is what makes a hand-off import real
  declarations instead of re-deriving them. Write the hand-off as part of
  finishing: the fixed names, instances and build budget the next set inherits.
- **The capstone is the review.** Writing it is the final wire test: a wrong
  binder, a missing lemma or a mis-stated hypothesis upstream surfaces as a
  compile failure in the reviewer's own file. Reserve it for the reviewer; in MC
  and AC it compiled first try.
- **Re-scope a blocked topic; do not stall the effort.** Keep the tree green by
  setting the blocked file aside, write a focused follow-up order, re-dispatch.
  The MC `m5b` `CuspDichotomy` re-scope solved in two rounds what the original
  topic could not.
- **De-risk before dispatch.** The manager's own `Scratch` probes are cheap and
  keep the agent's context on implementation.
- **Keep a per-set measured table** (rounds / declarations / lines / build /
  axioms / checker / consumer) and the friction log, and when a set may not edit
  a consumer, record the replacement map and hand the dedup off.
- **Close with a review** (math clarity, clutter, what did not go to plan), a
  plan-vs-actual honesty section, and retire the blueprint to `topics/`.

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
errors on a module `lake build` compiles happily (`WeightOne.Basic`: fails at
30.7 s raw, compiles in 56.1 s with the options). Use the options, or
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
   modules' dependents; splitting a wave over one module pays it twice (W4's
   width family paid ~6 m 45 s twice).
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

> **Build discipline (copy this into each work order).** `lake env lean <opts> <file>`
> is the edit loop, with `<opts>` = `-DmaxHeartbeats=4000000 -DautoImplicit=false`
> (without them the check runs at the default cap and lies about heavy modules);
> `lake build <module>` when a file is done; **one** `lake build` per wave; the
> full build at the milestone. Bound every build (`timeout 60` / `90` / `300` /
> `180`), serialize every `lake build` with `flock`, and time it: high user CPU
> with a timeout is a real blow-up to bisect, ~0 CPU is contention. Never raise
> `maxHeartbeats`; this project's global cap is already 4,000,000, so a blow-up
> does **not** surface in ~20 s — the wall bound is the protection.

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
   - **Order `SOURCES` so the interface copy wins**, and **append new entries
     last** so a bare last-name match cannot flip.
   - **A shadowed last name is disambiguated by its dotted name**, and the
     exemption, when needed, is by full dotted name (widening the lookup key can
     break earlier promotions).
   - **The diff is textual, not elaborated.** A public declaration must spell its
     binders exactly as the copy the checker will match — in practice the
     `Theorems/` wrapper, not the `S_` file. The file builds either way because
     the elaborated types agree; only the checker notices. Take the binders from
     the wrapper and use the `S_` file only for the proof body. This rule recurred
     for four consecutive topics before it was applied from the start.
   - **The checker reads modifiers from the declaration's own line and ignores
     `scoped`**; run its `raw_declarations` directly on a module not yet in
     `PORT_FILES` when you want a faithfulness probe without wiring it in.
     Definition-only modules get coverage by name against the pin's
     `Definitions/` files.
2. **A consumer** (`spec/<X>Consumer.lean`) outside every library. Its error
   count is the deliverable metric, and each zone must contain a **real,
   executed cross-module composition** — no `#check`s, no `sorry`; deleting any
   one module must make it fail. A module can build green and sit in no import
   chain at all, and nothing fails until it is used. Extend the zones per set,
   each zone recording a different kind of claim. Where a concrete instantiation
   needs unported hypotheses, state the test in hypothesis form and keep the named
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
(FFG: 7 → 0) and price the deferred cluster separately. When every premise is an
argument or already proved, the consumer's abstract-square wire test is the
capstone's analogue, and saying so is a finding (AC has no `Spine.lean`).

When a public helper moves or is demoted, two mechanical consequences:
demotion drops it from the compared count by exactly the number demoted (the
expected signal, not a silent loss), and a move must update `PORT_FILES` at the
new path or the declaration silently stops being verified.

## 5. Structure and sharing across theories

The aim is that **real mathematics is written once**. Expense is distance from
mathlib (§1), so a real result left `private` and re-derived in the next theory
is pure loss; glue and trivia are not worth exporting.

- **The measure is mathematical content relative to the project**, not size or
  today's consumer count. The test: what would another theory otherwise have to
  re-derive?
- **`Defs/` is for structures that carry later mathematics** (`IntegralStructure`,
  `Eigenform`, `HeckeOperator`). A file of general lemmas does not belong there,
  however general; a trivial abbreviation does not either, because its content is
  trivial.
- **Share real math; do not re-derive it.** A rearrangement, identity,
  finiteness or summability result another theory could need gets a public home
  even with one consumer today.
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
  sees the binders, so fix both (§4).
- **Namespace policy is decided before the wave.** A home's public names must be
  reachable under the spelling consumers already use, or the wave breaks even
  when statements match. A home may keep an internal namespace and export an
  alias in the consumers' namespace, but the two must agree.
- **Choose the directory and namespace from the pin's own namespace and sibling
  vocabulary**, not from the managing effort: one topic was retargeted to
  `ModularCurve/` because every pin file was `*_ModularCurve_*`, its headlines
  were `ModularCurve.*`, and the shared `dedekindPsi` already lived there.
- **Promote to the module where the needed type is available**, even if the work
  order says otherwise, and **rename at promotion when the pin name is already
  taken publicly**, keeping a local alias for existing consumers.
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

**A large slow module is usually cumulative, not one blow-up.** Before bisecting,
bisect *by milestone*: one 3,761-line module was 53 s of `lake env lean`, of which
4.5 s was the head and the rest spread across successive sections, with no single
declaration over the default cap. Compare with a genuine blow-up, which has one
declaration and one error. Attribute a slow module to defeq/instance synthesis
(a tensor-product/`Localization` module ran 41 s against 2–5 s for its
neighbours), and budget the next heavy module accordingly.

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
(`Algebra.IsIntegral.of_finite`, `Module.Free.of_divisionRing`), not by a larger
budget.

**Two declaration-shape facts the checker cannot see.** Unused section variables
are auto-omitted, so a declaration under `variable (N : ℕ) [NeZero N]` whose body
never mentions `N` comes out without `[NeZero N]` — transcribe verbatim and check
the signature rather than "restoring" it. And `linter.style.haveILetI` fires on a
`haveI` in a `Prop` goal even when the instance is used; if it came from
`intro`/`rintro` it is redundant, otherwise prefer `have`.

**Iterate in a gitignored `Scratch.lean`.** Put experiments and `#check @name`
probes there; the most useful probe when a rewrite or instance fails is
`#check @name` on the lemma you think you are using.

## 7. Drift checklist (mathlib `v4.34.0`)

API drift is the recurring real cost. The list below is the accumulated set; when
a new pin is taken, re-run it and append.

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
- **The `haveI` style-linter fix is not universal**: instance search may not find
  a plain `have` where `haveI` works, so suppress the linter locally rather than
  weaken the proof.
- **`omit [NeZero M] in` and file-scope linter suppression keep a pin proof
  verbatim without changing the checker's text**; `set_option … in` cannot follow
  a doc comment (use `--` line comments there).

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
| `frontier.py` | how far a target still is from the ported frontier, in new nodes |
| `port_graph.py` | our port's module/declaration graph: blobs, duplicated private proofs grouped into blocks, promotion candidates, closures |
| `port_advise.py` | before a port: what the port already has (substitute), what the target set re-proves (port once), what differs only by binders (generalise), and what each public declaration drags |
| `build_ladder.py` | the dependent cascade of an edit, the cheapest sufficient build under `flock`/`timeout`, a wave plan that re-edits a module, and (`--audit` / `--profile`) which modules are expensive to edit and which declarations cost the time |

The workflow loop: a coverage report from the pin graph chooses the target;
`port_advise.py` prices reuse and duplication before coding; `port_graph.py`
measures the redundancy the port created afterwards; the build ladder and the
checker are the per-wave gate.

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
| `AlgebraicCurve` exchange | the exchange reduction | 5,559 lines / 328 public decls, 618 statements | [logs/ac-port.md](logs/ac-port.md), [topics/ac-retrospective.md](topics/ac-retrospective.md) |
| Level vocabulary | `Γ_H`/`Γ₁`/cosets | — | [logs/level-port.md](logs/level-port.md) |
| T-side | `R = T` definitions | — | [logs/t-side-port.md](logs/t-side-port.md) |
| Eichler–Shimura | period-map injectivity | — | [logs/eichler-shimura-port.md](logs/eichler-shimura-port.md) |
| Sturm bound | weight-2 cusp vanishing | — | [logs/sturm-bound-port.md](logs/sturm-bound-port.md) |
| WeightOne rectification | refactor, no new math | 7,242 → 5,333 removable lines | [logs/weightone-rectify.md](logs/weightone-rectify.md), [topics/hecke/TOPIC-weightone-rectify.md](topics/hecke/TOPIC-weightone-rectify.md) |

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
