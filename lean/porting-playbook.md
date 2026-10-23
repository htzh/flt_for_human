# Porting FLT to mathlib — a playbook

The source of truth is the pinned FLT repository (`anthropics/fermats-last-theorem`,
currently `aa2d8b3`). This file is the method the completed ports share; each has a *record*
in [logs/](logs/) and some a *review* in `topics/*-retrospective.md`, indexed with measured
numbers in §10. Read a record for what an effort did; read this before starting the next one.

Three conventions. **The pin is the authority and faithfulness is mechanical**: every ported
*statement* is diffed against the pin by `spec/check_port.py`, never trusted; where
prose and Lean differ, the Lean is right. **The port is ours**: a module is a mathematical
role, not a source file; shared mathematics is written once and promoted; adapters stay
`private` — while FLT's declaration *names and statements* stay, so comparison stays
mechanical. **A node is ported whole** (§2.3). Earlier records cite an older numbering
("§3.11" build discipline, "§7.4" faithfulness); the
[appendix](#appendix-section-map-from-earlier-revisions) maps them.

## The six principles

1. **Port whole nodes.** A node is a pin file; once in scope it is transcribed in full —
   every declaration with a consumer, not just what the current target reaches (§2.3).
   Exception: a node that would drag in a large amount of out-of-scope code is cut, and the
   deferred surface registered.
2. **Home by subject, and let mathematical clarity decide.** A module is a mathematical
   role, a directory is a theory; the tree should make the mathematics visible (§3.1–§3.2).
3. **The manager scopes, ports the definition layer, and settles every promotion and
   hub-edit question.** A subagent never opens one; it reports and stops (§3.4).
4. **Proof bodies go to subagents under a written work order**, sized at roughly **1,500
   content lines per dispatch** — and expect that dispatch to be hours of wall time, so give it
   time rather than counting rounds (§0.2). Hand over a complete, self-contained brief, then
   leave the agent alone — no polling, no micromanaging — and review when it reports (§0.2,
   §3.3, §3.4).
5. **The manager owns the statement check.** A module declares its pin sources in its own
   header (`spec-pin:`), and `spec/check_port.py` diffs every public declaration against them;
   a declaration that is renamed or deliberately spelled differently is recorded in the central
   `spec/decl_markers.tsv` (checker metadata, never source). Public theorems (the API) stay
   public: never make real mathematics `private`, and never add a module, to make a diff go
   away (§4, §5).
6. **Enforce the build discipline: plan, then edit in waves.** Build time is the one
   unbounded cost; keep the edit-loop cap low and fix what exceeds it — almost always an
   instance-inference defect — rather than raising it (§3.5, §6).

## 0. Before you start

### 0.1 The checklist

**Plan for more than one round**: a port is a sequence of sets, and later rounds revisit
earlier modules. When a frontier figure surprises, check
[CARRY-FORWARD.md](CARRY-FORWARD.md) first.

Before coding: **measure the cone** (§2.1); **audit the route** mathlib-first, with a
recorded negative for every failed search (§2.2); **find the duplication** and give it one
home (§2.4); **write the blueprint** — scope, cone, dedup table, layout, topics, risk
register, verification (§2.1, §2.5, §2.6); **scout the one genuinely new piece** in a
gitignored `Scratch.lean` (§2.6). While coding: module = role, directory = theory
(§3.1–§3.2); one topic at a time with a work order (§3.3), its format copied from the most recent
landed order rather than an older one (§3.3); each in-scope node whole (§2.3);
faithfulness from the first declaration (§4); friction logged as it is hit (§3.6); nothing
dropped by inspection — `grep -c` or `diff` (§2.4). At the end: checker `0 mismatched / 0
missing`, consumer exit 0, `#print axioms` clean, no `sorry`, coverage `0 / 0 / 0` where a
report exists. A whole-tree build is *not* a wave gate: it is the session's last act and must
be agreed with the user, never started unilaterally (§3.5).

### 0.2 Working with subagents

Context is the binding constraint; the manager's is best spent on the plan, the review and
the capstone.

- **Dispatch above roughly 1,500 content lines, and size each order at that.** Below it the
  briefing and review cost more than they save; above it a fresh agent beats one
  accumulating detail. This is a **sizing** rule, not an effort model — a small set can cost
  more than a large one (§1).
- **Give a synthesized instruction, never a pointer to this file.** A subagent shares no
  context, so "read the playbook and the logs" burns its budget on reconnaissance. Hand it
  the work order (§3.3).
- **Bound its own scoping**: local reconnaissance (a mathlib search, a `Scratch.lean` probe,
  a `#check`) is fine; re-planning, re-routing and roaming the pin are not. If the task
  cannot be stated without broad scoping, the plan is not ready (§2).
- **Tell it what counts as a blocker, and to raise one at first belief.** A subagent has no
  context beyond its order, so it cannot know that a one-place hub edit is cheap for the manager,
  or that its diagnosis is not the deliverable. Instruct it explicitly: on first belief that a
  name cannot be matched, a prerequisite is unported, or an existing-module edit is needed, send a
  **short** message — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`" — and keep working on
  whatever is independent. It must not grind out a complete diagnosis first, and must never work
  around a hub defect locally. The edit is cheap while the worker is still in context; a full
  report arriving a wave later has lost that context.
- **A port turn is long, and a round is not its unit.** A 1,000–1,500-line set is hours of an
  agent's wall time — transcription, the low-cap edit loop, the per-file builds, the axiom probe —
  while a round-based driver (a goal loop that re-prompts on a fixed cadence, a scheduled
  check-in) runs on a much shorter clock. So a round boundary is a **status**, never a
  completion gate: do not split a set to fit one, do not re-plan because a round found the worker
  still working, and do not read "the agent has not reported" as a stall. At a round boundary the
  manager makes progress on something independent — the next order, the definition layer, the
  topic note — and waits for the worker's own report (§3.4, §9).
- **Leave it alone while it works** — no polling, no progress churn; it reports at the set's
  end or at a stop condition, and the manager then reviews its tree (build, checker, consumer,
  code) before writing the next order (§3.4).
- **Integration is the manager's**: the capstone and the checker run are the review instrument.
- **Ask for artifacts, not narration** — modules, measured table, friction entries.
- **Build investigation is a separate dispatch** briefed on
  [../notes/lean-build-cost.md](../notes/lean-build-cost.md) (§0.4).

### 0.3 Discretion: this is a synthesis, not a contract

Beyond the pin conventions and the six principles this is recorded judgement, matched to the
job's size. **Match the process to the size** (a 200-line leaf needs a work order and a
bounded build; a 2,000-line cone needs the blueprint too). **Prefer the cheapest instrument
that answers the question** — checker and consumer before a full build, a `Scratch.lean` probe
before a topic, `grep -c` before a rewrite. **The numbers and names are evidence, not law**;
measure again when the situation differs. **When a rule and the mathematics conflict, the
mathematics wins** — record the deviation. **Nothing here is exhaustive**; record the gap, and
add it here when it generalizes.

### 0.4 Build discipline, and the note behind it

Follow the block in §3.5. When a build misbehaves beyond those rules, do not investigate
inline: dispatch a subagent briefed on
[../notes/lean-build-cost.md](../notes/lean-build-cost.md) (`build_ladder.py --audit` /
`--profile`).

## 1. The cost model

**Expense is the route's distance from mathlib, not the size of the source.** Every effort
measured this, in both directions: a cone whose engine has left mathlib collapses to a few
generic lemmas, while a cone with an accurate line budget can still be dominated by its route.

**Effort is not proportional to lines.** Line counts predict *output*, not cost. The cost is
charged per declaration of **mathlib adaptation** — API drift (§7) and instance alignment — so a
small module can cost several times a large one: a ~1,200-line definition node whose statements had
to be re-tied to a changed instance took far longer than a ~1,400-line straight transcription, and
a thirty-line instance body gated the last half of a wave. Budget the shape risks, not the lines.

- **Budget content, not raw lines**: content subtracts `p2m_*`/`attribute` scaffolding
  (28–35% of a pin cone, never written).
- **Budget named shape risks, not rounds, lines or time.** Line budgets landed within ~10%, risk
  registers over-warned; the recurring real cost is **API drift** (§7).
- **A wrong statement is maximally expensive, a wrong proof cheap** — hence mechanical
  faithfulness front-loaded (§4) and the route audited before any module is written.
- **A faithful port is not line-for-line smaller.** The saving is the shims, dead wrappers and
  preludes never written; whole-node porting (§2.3) is not a licence to transcribe scaffolding.

## 2. Planning a port

### 2.1 Measure the cone

The blueprint (`PORTING-<X>.md`) opens every effort with a measured cone: the transitive
citation closure of the one target theorem, from the pin's doc-site graph, pinned to a sha and
a mathlib version. Use a coverage report (`studies/hecke-commute-bar-coverage.md` is the
model), report every group as **three numbers — nodes, raw `S_` lines, content lines** — and
keep node- and content-based headlines separate, since nodes overstate a cone whose weight sits
in a few large files. State the bias: a name-based "already ported" test misses renamed ports,
and the **`ucl` closure is an upper bound the other way** — it cannot see that a member's
*mathematics* is already in the port under another name, nor the pin's definitional imports.

**Walk the proof's definition uses, not only the import block**: a `Def_*.lean` import can be
an *empty stub* while the `S_` proof consumes a public block of another `Def_*` module the stub
drags in transitively (`fltdata.proof_defs` carries the list per node). **Sweep the port by
name and by `#check` before pricing any member** — a `ucl`-only budget badly overestimates one
whose mathematics is already there.

- **Partition by route group and assign each whole node to its first consumer**, so the group
  totals sum to the measured total; that table is the work-order cut.
- **Reachability decides which whole nodes enter**, not which declarations inside one are
  ported (§2.3): price on-path nodes, carry off-path nodes as a counted optional tail, and
  price definition modules separately.
- Report the **outbound interface** the cone must export and the **duplication already visible**
  in the pin.
- **Close the measurement over proof-reached targets, not just the target files** — target
  proofs reach helper *targets* outside the set (the Riemann–Roch round found four).
- **Ship a copy-pasteable regeneration recipe** with every measurement.

Three ways a frontier figure misleads: **a citation-leaf is not a leaf** (`needed == 1` says
nothing about *definitional* prerequisites — check the `Definitions/` closure first); **a pin
`S_` file's `lines` is an upper bound on the headline's route** (a solution file may inline
prerequisites and carry an off-path silo, still ported whole, §2.3); and **file-granular edges
shadow** (a partly ported file makes its citers read one node closer than they are — whole-node
porting removes the shadow, otherwise register the deferred surface).

### 2.2 Audit the route, mathlib first

Build an FLT → mathlib table and test each entry for **definitional** equality with `rfl`: a
`rfl`-equal alias is legal, a merely-equal one is a re-proof (template:
[logs/card-torsion-port.md](logs/card-torsion-port.md) §3). Three outputs, all worth recording
— **reuse wins** (`RingEquiv.ofBijective`, `Submodule.torsionBy`, `Ideal.relNorm`); **route
options** where mathlib lacks the result, so the route is chosen before transcription (the
`PhiGen` kernel is the paradigm: the whole cone hangs on one `Φ_p` root description);
**recorded negatives** — mathlib has no `dedekindPsi`, no Γ₀ index formula, no
`minpoly.map_eq_of_injective`, and the `relNorm` norm block is irreducible.

**Adopt mathlib's type as the interface from the first declaration.** A type mathlib already
has (`Submodule.torsionBy`, a `ValuationSubring`-based `Place`, `LaurentSeries`) should be the
port's interface immediately, not FLT's wrapper reconciled at the capstone; a wrapper dropped
is a design decision with the adaptation cost measured. Route selection is a measurement:

- **Price the marginal closure under the substitution, not the headline cone**; **prefer a
  cone that is a subset of work the endgame needs anyway**, counting only the route-specific
  addition, and retire a route that adds no coverage.
- **Disambiguate same-named objects before pricing**, and verify a brief's named ingredient
  against the pin.
- **The pin's `p2m_export`/`p2m_open` list is the FLT → mathlib gap list**; a mathlib TODO
  comment is a reliable gap inventory.
- **Check a substitute's hypothesis strength against the source's** — a candidate can need
  primitivity where the cone has only `ζ^ℓ = 1`.
- **Price the glue, not the mathlib-replaceable leaves**, and order the remaining nodes by
  outbound statement-demand, not file size.

### 2.3 What to port: whole nodes, then the gain test

**Port the whole node.** A *node* is a pin file, and the pin file is the unit the frontier
measures; once in scope, transcribe **all** of it — every declaration that has a consumer, not
only those the target reaches. Partial porting is a false economy twice over: it costs more
than it saves (the file is revisited, re-elaborating the module and its context), and it
corrupts the next estimate, since `frontier.py` prices in source-file nodes and a file with a
ported headline and an unported API prelude still reads as unported — its citers read one node
closer than they are too (§2.1).

The **exception** is a node that would drag in a large amount of out-of-scope code: cut it,
state it in the out-of-scope table, and register the deferred surface per node in
[CARRY-FORWARD.md](CARRY-FORWARD.md). The other residue is content with **no consumer
anywhere**, dead in the pin as well as the port — a claim about the graph, so verify it
mechanically (`grep -c` over pin and port), not by inspection.

Then score the port on four gains — **organization, clutter never written, mathlib alignment,
truth** — never on line volume, ordering nodes by what each *buys* (**outbound indegree**,
citers outside the cone, as the proxy for reusable surface; small leaves can carry
disproportionate weight). Indegree is global (check the node is in the cone), a library-shaped
cone scores differently from a citation chain, and an interface split across pin namespaces
must be pointed out to the checker (§4). Re-run the gain test when the blocking gate is
removed.

**Capstone shape follows from the premises.** If significant premises are unported, build a
*conditional* capstone — a proved artifact with no `sorryAx`, its fields a structure of named
hypotheses — so the remaining work becomes an ordered list (the `functionFieldGeneration`
`Spine.lean`, debt 10 → 0), and freeze it once it lands. If the premises are arguments or
already proved, do **not** add the device; the `AlgebraicCurve` layer needs no `Spine`.

### 2.4 Deduplicate before coding, and drop by count

The pin copies a private prelude into every `S_` file that consumes it. **Find those copies in
the plan and give them one home before writing the first module.** Detection is measurement:

- **Diff normalized bodies** (strip imports, namespaces, `p2m_*` lines, the `solution` tail)
  and price the saving as `(copies − 1) × block content`; `port_graph.py --blocks` is the
  port-side view, `port_advise.py` the pre-port view.
- **The pre-port view is name-anchored, so "already in the port" is a lower bound** — a port
  declaration doing the same work under another name is invisible; check the *statement*.
- **It is also an upper bound, and its worst false positives are `def … : Prop`** — the
  checker compares a `def`'s type, which for `def foo : Prop := P` is just `Prop`; read the pin
  body, or diff it with the legacy checker's `--prop-bodies`, on every such row.
- **Graph-node multiplicity undercounts copies**; quantify by *duplicate lines shipped*.
- **A large pin-`private` block re-exported by name mangling is a promotion**: write it once
  publicly at the pinned names, promoting the *union* of the duplicates. **"Which side stays"
  is the pin-public wrapper**; re-privatize the pin-private name and keep local aliases.
  Replace copies one file at a time, only where the statement matches (`N ∣ 2` is not a
  drop-in).
- **`grep -c` before dropping anything**, review the port's own private layer after a module
  closes, and keep a list of **deliberately not cut** items with their counts.
- **Do not merge a helper when sharing would invert the import graph**, and strengthen a
  statement from the pin, never from the port's own weakened copy.
- **This is the whole pre-code pass, and it is about duplicates, not about the unused.** Whether a
  declaration is *reachable* is not a porting question: the pin's unreachable mathematics is
  transcribed with everything else and shelved afterwards (§3.8), so the only thing to measure
  before coding is how much text the pin copies twice.

### 2.5 Risk register and budget

Write the budget as a **correction ledger**: structural sum → minus dedup savings (explicit
negative rows) → plus definition modules → range, then apply the measured written ÷ content
ratio (`AlgebraicCurve` 1.25–1.45, `ModularCurve` 1.0–1.3). The budget *unit* is the named shape
risk: name the risks in the order they will bite — a typeclass/coercion mismatch, a defeq
between concrete carriers, an instance diamond, a renamed API — each with its mitigation and
resolved/open mark, and record **predicted non-events** so they are not budgeted again. Record
a route win as a *measured delta* and re-price rather than banking it. Before committing to a
route, audit it as a named `logs/audit-*.md`; an audit may answer "no" and retire the route.

### 2.6 The scout gate

When exactly one topic carries genuinely new mathematics, prototype it in a gitignored
`Scratch.lean` before dispatching it. The output is a **corrected estimate and work order**, not
just go/no-go (record the pre- and post-scout numbers). A scout may **kill a route outright**
(record the missing ingredient), or show that the pin's proof transcribes unchanged, converting
"new mathematics" into "transcription".

## 3. Executing a port

### 3.1 A module is a mathematical role, not a source file

FLT splits by artifact kind (`Def_`/`Thm_`/`S_`); the port splits by concept: one `Def_` file
covering four subjects becomes four modules. All binding: **reading order is dependency order**,
each header stating the subject, the FLT source and pin, and what it assumes from earlier
modules; **a new header does not point at the notes** — no `playbook §…`, no `logs/…`, no
`CARRY-FORWARD.md`: the source states the mathematics, its pin source and its assumptions, and the
plan and the records carry the cross-references (existing citations are grandfathered; strip them
when the module is next edited); **docstrings carry the mathematics** (a one-line
gloss for a name that does not state its content, a sentence for a construction); **adopt mathlib's
names where it has them, keep FLT's where it does not**, and say which is which; **generated name
tokens are rectified, not carried** — the pin's proof-search labels (`F4CutWords`, `PartB8`, `FarmE26`),
its compressed defs (`Ecf`, `ρc`, `Qc`, `cutc`, `CA`, `CB`) and its `kw_*` prefixes are artefacts of how
the pin was written, so the port's engine carries descriptive names and its section structure is by
subject, never by the pin's grouping (`check_port.py` already rejects `kw*` names outright); only a
*pin-public statement* keeps the pin's name, and a rectified public declaration gets a `pin:` row in
`spec/decl_markers.tsv`; **monomorphic
helpers are documentation**, written the moment a `rw` reports no progress (§6), not before; **no
self-consumed lemmas** — the node boundary is not a licence to carry dead scaffolding the port
itself invents (the pin's *unreachable* mathematics is a different thing: it is ported with the
rest and shelved later, §3.8).

### 3.2 Directory layout: one directory per theory

```
<Area>/
  Basic.lean        -- setup shared by every theory in the area, mathlib-only
  Defs/*.lean       -- shared vocabulary, when it is big enough to need a directory
  <Theory>/*.lean   -- one theory's modules, whatever role each plays in its proof
```

A directory holds **one theory**, the area's shared vocabulary outside it. The *second* theory
triggers the `Defs/` split, not the first; until then a move is churn. The split is mechanical —
rename, fix importers, update the record — and the lakefile globs with `.submodules`, so no
build-file change. The tree should make the mathematics visible: two independent routes should
be two directories meeting at a named module (`AlgebraicCurve`'s `WeilExchange/*` and
`PrincipalDivisors/*` share only `Defs/`). **The mathematics should be a handful of abstract
statements plus concretisation** — `AlgebraicCurve`'s 5.5k lines are three statements,
`functionFieldGeneration`'s 3.8k are three generic lemmas. If that is not visible, the split is
wrong. Hygiene: imports stay specific (never `import Mathlib` in a library module), and `spec/`
stays outside the libraries.

### 3.3 One topic at a time, with a work order

A **topic** is the unit of work: one mathematical step, one module or a small group, one work
order, stating before any code the subject, pin source, exact statements, imports, route/risk,
verification and build bound. The template: **(1) Scope** — one paragraph plus what is
explicitly *not* this topic, the in-scope nodes, and that each is taken whole (§2.3); **(2)
Source** — pinned files and line ranges and the wrappers that carry the statements, the module's
`spec-pin:` header lines, and a `spec/decl_markers.tsv` entry only where one is needed (`pin:`
for a rename or a copy outside the header, `own:` for a deliberate restatement — §4);
**(3) Deliverable** —
module path and declaration list, public vs `private`; **(4) Route** — the mathlib map, the
alternatives, the recorded negatives, and a **stop-early risk list with a deviation protocol**;
**(5) Build discipline** — the bound and the ladder (§3.5), copied in; **(6) Verification** —
checker run (`0 mismatched / 0 missing`), consumer zones, `#print axioms`, `grep -c` of anything
dropped. Update the
numbers in place when reconnaissance re-prices; re-cut a topic that straddles waves **by
mathematical object** — construction, properties, consequence — without splitting a node.

**Copy the format from the most recent files, never from a convenient old one.** The workflow has
changed several times, and the topic files and work orders of earlier eras still carry instructions
that were later retired (in-source `-- pin:` markers instead of the module's `spec-pin:` wire, the
`unwired` register, an engine split by wire rather than by subject). A new order is written from the
**most recently landed** order in the same subject area — its status line, its gate block and its
statement of what `public`/`private` means are the current shape — and this playbook's §4 is the
authority when the two disagree. An older order that prescribes a different mechanism is the record
of what was done then, not a template: if a reader could be misled by it, say so in the new order's
header (as `WORKORDER-RP1` now does for its §1 provenance comments and its §6 register gate). A
landed order is read for its *mathematics and its measured numbers*; its *workflow* is only current
if it is recent.

### 3.4 Sets dispatched to agents, with review gates

Large efforts ran as **sets**: one coherent mathematical story per agent, the manager reviewing
between sets and writing the capstone. The staffing rule (dispatch at ~1,500 content lines, one
subagent per set, review before the next, no polling) is §0.2.

- **Schedule on the real dependency fork, not the pin's section order**; keep topic numbering
  disjoint across parallel efforts.
- **Split on the mathematical fork, not on size**: one story per set, no node divided between
  sets (§2.3).
- **Write the next set's orders after the previous set is reviewed**, against the modules that
  exist; the hand-off names the fixed names, instances and build budget the next set inherits.
- **The capstone is the review**: a wrong binder or mis-stated hypothesis upstream surfaces as a
  compile failure in the reviewer's own file. Reserve it for the reviewer.
- **Re-scope a blocked topic; do not stall** — keep the tree green, write a focused follow-up
  order, re-dispatch. A worker raises a blocker at first belief and never works around it
  (§0.2); the manager's job is to answer the blocker (often a hub edit, which is the manager's
  own, done once with the price known — §3.7) rather than to let the set die at its end.
- **Size a set in wall time as well as in lines** (§0.2), and say who finished which part. A
  set the manager has to interrupt is still one set: keep it whole, and at each interruption do
  independent work rather than re-cutting it. If a driver's cadence fits the work badly, either
  widen the cadence or take the tail in hand — the archimedean Casimir set landed that way: one
  dispatch, interrupted at the verification step, with the manager finishing the private/public
  decision, the drift fixes and the statement check. Record it in the set's own table, not as a failure.
- **Keep a per-set measured table** (rounds / declarations / lines / build / axioms / checker /
  consumer, and for an interrupted set the split between worker and manager) and the friction
  log; close with a review, a plan-vs-actual honesty section, and retire the blueprint to
  `topics/`.

### 3.5 The build ladder

Build time is the one unbounded cost. What a build costs is the **dependent cascade**, not the
command's breadth: `lake env lean <file>` writes no `.olean` and recompiles nothing; `lake build
<module>` builds dependencies but never dependents; only building a dependent (or `lake build`)
re-elaborates the cascade. The whole-tree build is therefore a **once-per-session** action,
taken at the end and only with the user's explicit agreement (rule 5); measurements and
profiling are in [../notes/lean-build-cost.md](../notes/lean-build-cost.md).

**The edit loop runs on a deliberately low cap.** `lake env lean` does **not** inherit the
lakefile's `leanOptions`; `lake build` does. Run the edit loop with `-DautoImplicit=false
-DmaxHeartbeats=200000` and a wall timeout. A declaration that will not fit is a symptom to
diagnose, not a bound to raise: a build-time blow-up is instance inference — a `def` that
blocks unification, a search that unfolds a coercion, an instance diamond — and the low cap
finds it (`set_option trace.Meta.synthInstance true` / `diagnostics true` on that one
declaration). Fix the inference and re-run; a genuinely long proof is restructured, not
exempted. `lake build`'s higher cap is not a target, and **no module carries a
`set_option maxHeartbeats`** — including one transcribed from the pin.

**A cap override inside a file is a defect marker, not a budget.** It is there because something in
that file does not fit, and it hides that thing from every later reader. Remove it and re-bound the
file at the project cap: if the file stops fitting, you have found the bug you were looking for. The
cautionary case is `WeierstrassCurve/Isogeny/TwoCurveDescent.lean`: a 12× override
(`maxHeartbeats 48000000`, `synthInstance.maxHeartbeats 8000000`, transcribed from the pin) sat in
`section GateDescent`, the record attributed the module's multi-minute elaboration to the declaration
that carried the bump, and the real cost was a zeta-blind `isDefEq` in a *different* declaration
([../notes/instance-friction-case-study.md](../notes/instance-friction-case-study.md)). Bisect before
trusting any attribution, including an old one.

**Bound, do not measure.** The only question a build command ever answers is *"does it finish inside
`timeout N`?"*. Never `time`, never chase a duration, never compare 33 s with 40 s: a number you do not
need costs a turn, and one threshold decides pass or fail. Profile **once** per module when the
attribution is unknown, keep the trace file, and work from it afterwards — a second profiling run
buys nothing. Any compile that can plausibly run a minute is a **background job with its own
`timeout` and its full output redirected to a log file**; read the log, never a `tail`/`grep` of the
live stream, because a foreground turn is killed at its shell cap mid-elaboration — which loses the
turn and can leave an orphan holding the build lock.

**Diagnosing a blow-up: the probe ladder.** A timeout is a probe first and a diagnosis second. Every
step is a `lake env lean` turn of seconds, none re-elaborates the module at the library cap, and
every probe stays on the low cap — the cap is a *bisector*, not only a detector, because it turns a
minute-long elaboration into a one-second abort. Worked example: the `ZLattice` pair's three
`PeriodizeLift` statements, 429 s → 5.5 s at the same declarations
([logs/poisson-summation-statements.md](../logs/poisson-summation-statements.md)).

1. **Statement or proof?** Stub the suspect declaration's *proof* with `sorry` and re-run the edit
   loop. The body is skipped but the statement still elaborates: if the timeout survives, the cost
   is in the *type* and no tactic change can move it — and `trace.Meta.synthInstance` will show
   nothing, because no search runs.
   Before bisecting at all, run that probe on the **whole module** — every theorem proof `sorry`,
   statements, `def`s and instances verbatim — which gives the module's *floor* in one run. If the
   floor is over the bound, no proof-side edit can reach it: the cost is in the frozen types, and the
   levers are deleting the section variables no statement uses (§6) or naming the types (a statement
   change, and for a wired module an `own:` decision — not an agent's call).
2. **Isolate the declaration.** With no `.olean` of the module, `import` is not available: build a
   scratch file from the module's imports plus the definitions the declaration needs. Replace the
   *proofs* of the declarations before the target with `sorry` — keep their statements, the target
   needs the names and types — keep the target's own statement, and put one `example` per candidate
   behind a `-- PROBE <label>` comment. One run then reports every offender at once, and the labels
   give the attribution. Stubbing the *prelude's proofs* is what makes the probe cheap; truncating
   the file at a prefix line and appending `end`s does not, and usually does not parse either. When
   the module's own `.olean` exists there is a cheaper pair: `one:<line>` (only the target's proof
   kept, every earlier proof stubbed) and `keepafter:<line>` (only the target's proof stubbed, the
   rest kept). Bound each, and the attribution is settled without profiling anything.
3. **Shrink the statement, not the file.** The same application can be free in a `have` or a `def`
   body and expensive in a declaration's *type*; bisect the statement's terms, not the module's.
4. **Read the counters.** `set_option diagnostics true` on the one declaration prints the reduction
   table (`ContinuousMap.instNorm ↦ 3854`, `Elem ↦ 10283`, …); `set_option trace.Meta.isDefEq true`
   at a *tiny* cap (`-DmaxHeartbeats=3000`) prints the comparisons just before the abort and names
   the subterm that will not unify.
5. **Classify, then fix.** Instance *search* (`synthInstance` timeout) → the §6 brick recipe.
   Instance *terms* compared by an argument check (`isDefEq`/`whnf` timeouts, no search goal, a big
   instance such as `Norm C(α,E) = dist x 0` unfolding `sInf`/`Finset.sum`) → give the type one
   syntactic form: name it once and use the name where it is **bound**; the statement text then
   deviates, so it is a registered `own:` deviation (§4), not a bump. Its mirror image: when the
   comparison differs from its goal only by **zeta** — a local `let` in the working context — nothing
   needs a name, and naming more makes it worse: *remove* the `let`s, state the intermediates at the
   explicit terms, and `rw` with the `rfl`-level projection lemmas (§6). A `≤`/`⊆`-lemma whose
   *result* is a membership, applied inside a statement that is itself large, is the same class:
   state the element form once (`SetLike.le_def.mp`) and apply that at the site. Arithmetic defeq →
   the pin's bump rule (§6). A genuine proof cost → restructure.

A probe that cannot finish inside a minute is the *probe's* fault, not the file's: it is still
elaborating what it should have stubbed.

| tier | when | command | cost |
|---|---|---|---|
| 0 edit loop | every edit | `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` | no cascade; the low cap is the instance-inference detector |
| 1 module done | file compiles | `timeout 90 lake build <module>` + checker | 6–10 s |
| 2 wave done | all wave edits in | the wave's affected targets, not a bare `lake build` | 2–7 min |
| 3 session end | session closing, **agreed with the user** | full build + consumers + axioms | the tier-2 cost |

Five rules:

1. **Never `lake build` in the edit loop**; iterate on the declaration in `Scratch.lean` (§6).
2. **A wave edits each module once** — the cascade is the union of the edited modules'
   dependents, so splitting a wave over one module pays it twice.
3. **Price the cascade before triggering it** (`build_ladder.py --edit`).
4. **Serialize every `lake build`** with `flock`, timed with wall **and** user/sys; two agents
   on one tree contend rather than parallelize.
5. **The whole-tree build is the session's last act and must be coordinated with the user —
   never start one on your own initiative.** It is the most expensive action in the project and
   it grows with the port, because every new module joins some build cone: what used to be
   minutes is now **over 20 minutes** and keeps climbing. Coordination means agreeing *when* it
   runs. Each wave is covered by its own affected-target build (tier 2); a bare `lake build`
   between waves pays the full cascade for a tree the next wave is about to change, then makes
   you read a stale result. Run it once, when nothing further will be edited, and only with the
   user's explicit agreement — a "just to verify" run counts.

If a build still misbehaves, hand it to a subagent briefed on the build-cost note (§0.2, §0.4),
and keep heavy modules at the leaves and shared hubs small and cheap.

> **Build discipline (copy into each work order).** Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` —
> the cap is **low on purpose**: a declaration that exceeds it has an
> instance-inference defect, and the low cap is what finds it. Never raise
> `maxHeartbeats`, never add a module `set_option maxHeartbeats`. `lake build
> <module>` per finished file, serialized with `flock` and bounded with `timeout`.
> Per wave, build only the wave's affected targets — **never a bare whole-tree
> `lake build`**. A whole-tree build happens once, at the session's end, only after
> the user agrees to it, and never on the agent's own initiative.

Three traps: **a stale `.olean` reads as a missing declaration** (after a `private` → public
promotion, `lake build <defining module>` before the consumer); **importing a huge `.olean` is an
edit-loop cost of its own**; and **a `set_option` in a file is a defect marker** — see the paragraph
above, and remove it before you believe anything the module's cost is telling you.

### 3.6 Keep the friction log while you hit friction

The API-drift list and the failure-mode write-ups were only cheap because they were appended to
*during* the work. This is the highest-value artifact for the next effort — more than the
module list, which is derivable from the code. Record every friction as it is hit in the
append-only [logs/frictions.md](logs/frictions.md) — one tagged, greppable entry per friction; an
instance-shaped one goes to [instance-friction.md](instance-friction.md) with its harness. Fold
what generalizes into §6–§7 at the end and keep the effort-specific rest in the set's record.

### 3.7 Porting order inside one effort, and the build economy

An effort's *internal* order is a planning object, not an accident of the pin's file list. The
order that carried the Deligne–Serre slice
([topics/PORTING-DeligneSerre.md](topics/PORTING-DeligneSerre.md); record
[logs/deligne-serre-port.md](logs/deligne-serre-port.md)): **(1) definitions first**, in their
own import order — nothing can be stated before them and they are leaves; **(2) shared blocks
into *new* files second**, which cannot cascade (scope from `port_advise`, and scan by hand for
repeated *definitions*, since the tool counts proofs and misses a repeated `def`); **(3)
reconciliations in *existing* files third**, in one pass, then freeze them — the only phase that
re-elaborates existing modules; **(4) theorem sets, importees first**, over whole nodes, each
importing only levels below it and never splitting a node (§2.3).

Then execute as sets (§3.4). Two rules make the hand-off real: a frozen file is never reopened
(resolve locally, log the friction, let a final **refactor round** promote), and a worker
reaching an unported prerequisite **stops at the boundary and reports** rather than editing a
closed file or weakening a statement. **The order is a build-cost decision**: with a
forward-import DAG a worker's module is usually already built, so sets close on per-module
builds of seconds and the only whole-tree build is the session's last (§3.5).

### 3.8 Dead code: port the mathematics, shelve it later, bin the plumbing

Two different things get called dead, and only one of them is a porting-time question.

- **The pin's unreachable mathematics** — the mirror half of a symmetric construction, a lemma
  behind an abandoned route, a strengthened form nobody restates. **Port it.** It is the pin's
  text, it transcribes at the same cost as everything else, and *finding* it is a reachability
  analysis over a module whose text is not final yet. So the porting-time pass is **dedup only**
  (§2.4); unused declarations are not searched for, and a pin statement is never restated to
  avoid one.
- **The port's own dead plumbing** — `P2MW.S_` staging, dropped wrappers, shims, self-consumed
  lemmas, an unused section variable, a `private` twin of a headline. **Prune it any time, no
  shelf**: the port wrote it and it is not the pin's mathematics (§3.1's "no self-consumed
  lemmas" is about exactly this, not about the pin's unreachable content).

**The shelf rule is for the *specialized* mathematics, not for the general.** A shelf earns its
file when the content is expensive *because it is far from mathlib* (§1) and exists nowhere else —
the project's own objects and the lemmas about them (`IsFactorizableTestFn`, `AdelicGL2`, the arch
chart `archDerivAt`, `ArchEntry`). Where mathlib already owns the subject — `Matrix` inverses and
adjugates, `ContDiff` of a determinant, a `Fin 2` identity — a dead theorem is **general**, and
there it is judgement on **subject area and general applicability**, which the tool cannot supply:

- **keep it in place** if it rounds out a general API and buys completeness — they are what a
  reader of the module is glad to find, they cost lines and nothing else, and they are recoverable
  if ever cut, so a shelf would only preserve the cheap;
- **prune it** if mathlib already states it or it is one `simp` from something mathlib has — that
  is a §2.4 duplicate, not dead content, and the answer there is deletion, not a shelf.

Record the general lemmas kept on purpose, with the reason, in the effort's order — otherwise the
next dead-code scan reopens them (§2.4's "deliberately not cut" list is the same idea).

**The sweep, when it happens, is one tool run, and unreachable *specialized* mathematics goes to a
shelf, not to the bin.** Triage the reported set before `--apply`: `--select names` over the
specialized part is the shelf, and a general lemma is either kept in place (and recorded) or
deleted by hand.

```
python3 tools/deps/move_dead.py --source lean/FLTForHuman/…/A.lean \
    --target lean/Reserve/<Area>/<Module>Dead.lean --select dead --copy \
    --header-file lean/tmp/header.txt --apply
```

`--copy` is the shape this needs, because a dead tail's premises are usually `private` helpers the
live headline also uses: the source loses only the dead set, the shelf receives that set **closed
under its premises**, cut out of a copy of the source so sections and `variable` lines travel, and
the shelf imports the port's public API — never the module it came from. The alternatives are each
worse: `--expose` puts a private engine on the public API for a shelf's sake, a hand copy
reconstructs the section context the tool preserves, and deleting throws away specialized
mathematics the pin has and the port already paid to transcribe. The duplicated premises are the
accepted price (FTF1: 43 per shelf, 528 lines, which `dedup.py --cross` reports as 43 clusters by
design).

**What a shelf looks like.** `Reserve/<Area>/<Module>Dead.lean`, mirroring the port's own paths; the
declarations `private` as in the pin, at the pin's statements; a header carrying the provenance (pin
file, pinned sha, which half of the development, the rename map) and why it is off the critical
path; **no `spec-pin:` wire**, so `check_port.py` does not diff it — built (Reserve is a default
build target, so it stays green) but unwired, its statements unchecked text, which is the accepted
trade because they are the pin's and Lean still elaborates them; a row in
[Reserve/README.md](Reserve/README.md), with the pass's counts in the effort's order (its landed
section, §10); and for a declaration the pass left with no home at all, an
entry in [CARRY-FORWARD.md](CARRY-FORWARD.md) rather than a quiet deletion.

**Measure reachability, not "unreferenced".** A `grep` for a name counts the module header that
mentions it and misses a declaration referenced only by another dead one; FTF1's order recorded 1
real and 20 complex dead declarations, and the reachability pass found 25 and 24. Two corollaries:
a dead set is closed under its dead referrers, so cut the cluster and not a leaf (a partial cut
leaves the survivors unreachable in turn); and the two mirrors of a symmetric development are
swept in the same run, or they stop being mirrors — FTF1's earlier partial cut had already made the
pair carry different subsets before the shelf existed.

**What the sweep does not decide** is whether that mathematics should have a *public* home. A shelf
is a reading copy whose declarations are `private`; promoting one (or copying it back) is the
one-line edit a consumer makes, and that promotion is §5's decision, not this one's.

## 4. Faithfulness, made mechanical

With a pinned source, correctness is checkable rather than trusted. Four instruments:

1. **The statement checker** (`spec/check_port.py`) diffs every ported *statement* (signature up
   to the first top-level `:=`/`where`; for a `structure`, header plus ordered field names)
   against the pin. Proofs are ignored: the port adapts proofs, never statements. Target
   `0 mismatched / 0 missing` per module, and read a `missing` as carefully as a `mismatched`.

   **The module declares its own check.** The leading `/- … -/` block carries one
   `spec-pin: <pin file>` line per pin source; the checker reads those files from the pinned
   corpus (below) and resolves each public declaration against them by name, then by statement.
   List the copy whose statement text the port transcribes — in practice the `Theorems/` wrapper,
   not the `S_` file — because a copy the header names whose text differs is a `MISMATCH`, not a
   fallback.

   **A declaration that is renamed or deliberately respelled gets a recorded exception, in the
   table, never in the source (2026-10-20).** `spec/decl_markers.tsv` is keyed by
   `(module, full declaration name)` and carries either `pin: <name> (<file>:<line>)` — a
   rename, or a copy in a file the header does not list — or `own: <reason>` — a statement that is
   ours, not the pin's. The grandfathered in-source `-- pin:` / `-- own:` comments are still read
   and must not be added. The table is checker metadata: editing it never changes a Lean build, and
   an entry that no longer names a declaration is reported (`--strict-markers` makes it fail).

   The **frozen** `spec/old_check_stmts.py` is being retired; it still owns the modules its
   legacy lists name, and its parser is the shared definition of "the same statement". Do not
   add an entry to either list. One caveat remains: a legacy module that moves must have its path
   updated there, or its declarations silently stop being verified.

   Rules:
   - **Never make real mathematics `private`, and never add a module to please the checker.** A
     `private` engine is one the next theory must re-derive (§5); a module written only to hold a
     headline buys a file, an import and a frozen name for no gain in verification. Both were
     tried on the archimedean Casimir set and both were reverted; the landed shape is one module
     — three headlines at their pin statements, the shared engine public beside them (§5, §9).
   - **The parser has its own test** — `python3 spec/statement_db.py selftest` checks the
     signature view, the hashes and every query path against the legacy parser, so it is run when
     the parser or the corpus format changes, not per set. A deliberate deviation is an `own:`
     row with its reason, never a marker invented to make a diff disappear.
   - **Keep `scoped` exactly where the pin has it** (invisible to the checker on both sides, so
     dropping it creates a spurious `missing`).
   - **The diff is textual, not elaborated**: spell binders exactly as the pin's copy — in
     practice the `Theorems/` wrapper, not the `S_` file — and keep a `def`'s pin binders in their
     `variable … in` form, since section variables never appear inline and spelling them out
     builds but reports **MISMATCH**.
   - **The `kw_` prefix is erased on both sides, name and statement**, so a one-token drift in a
     **promoted** declaration surfaces as `missing`, not `mismatched` — read `missing` too.
   - **Write header prose in `/- … -/` blocks**: the `spec-pin:` lines are read from the leading
     block, and a `--` line comment mis-aligns the legacy checker's namespace tracker.
   - **Ask whether the diff could be degenerate** — a truncated signature, or a `def … : Prop := P`
     whose statement is the bare type `Prop`, looks clean in the count. Read those bodies
     yourself (the legacy checker's `--prop-bodies` diffs them). The checkers never invoke Lean,
     so a statement-shaped problem outranks a proof problem and is checkable on a module stuck in
     a failing edit loop.
2. **A consumer** (`spec/<X>Consumer.lean`) outside every library. Its error count is the
   deliverable metric, and each zone must contain a **real, executed cross-module composition**
   — no `#check`s, no `sorry`; deleting any one module must make it fail. Extend the zones per
   set, each recording a different kind of claim; where a concrete instantiation needs unported
   hypotheses, state the test in hypothesis form and keep the named instance `private`. A
   definitions layer needs a *concrete instantiation*, not just abstract-type applications.
3. **`#print axioms`** on every headline, confirming `[propext, Classical.choice, Quot.sound]`
   and no `sorryAx`. It cannot see a `sorry` inside a `def`/`structure`/`instance`, so those are
   never left `sorry`-closed; work definitions bottom-up, statements top-down from the wrappers,
   and count `sorry`s from build warnings, not prose greps.
4. **A coverage report**, where one exists, closed to `0 / 0 / 0`.

**Reading a pin statement.** Do not grep the 1.1 GB pin tree to find a signature:
`python3 spec/statement_db.py build` flattens the pin once into a single text corpus,
`tmp/flt-statements/statements.tsv` -- 718,874 lines, 472 MB, git-ignored, one line
per declaration (`path`, `line`, `kind`, `flags`, `name`, statement hash, raw
signature). `show <name>` prints a signature with its `file:line` and pinned link,
`file` gives one pin file's declarations, `grep` searches the corpus, and
`rg -n 'Coprime [A-Z] [A-Z]' tmp/flt-statements/statements.tsv` is the pattern path
(signatures are raw, so qualified names are searchable; the hash column makes
"the same statement elsewhere" an exact `rg -F`). A 7 MB `statements.idx` records
each pin file's byte range, so a checker reads the one or two files a module names
instead of the whole tree, and the `statements.json` stamp (pin commit, checker and
parser digests) makes `check` catch a stale corpus. `verify` proves every file the legacy lists
name parses identically on both sides, so it is the same text both checkers diff. The corpus is
a build artifact, never a source: regenerate it, do not edit it.

**Running the checker.** `spec/check_port.py` reads the `spec-pin:` lines out of the module, so
it needs no registration: `python3 spec/check_port.py <module>` checks one module (and replays
its stored verdict when nothing moved), `--changed` scans only modules whose content or corpus
stamp moved, `--all` re-checks everything, `--force` re-checks an unchanged module, `--timestamps`
prints the per-module stamp, `--include-legacy` reaches a module the frozen lists still own, and
`--markers PATH` selects another marker table. State is `tmp/check-port/state.json`, which a
corpus rebuild invalidates. It hashes the port statement the way the corpus does and matches by
exact name, promoted key, `kw_` strip, then content, so a faithful-but-renamed copy verifies and a
same-name statement that differs is a `MISMATCH` (with an identical statement elsewhere reported
as a hint). A module is its own unit of check: every public declaration it makes is either diffed
or carries a recorded exception.

When the capstone is conditional, track its debt counter as each field lands (the
`functionFieldGeneration` capstone: 7 → 0) and price the deferred cluster separately. When every
premise is an argument or already proved, the consumer's abstract-square test is the capstone's
analogue. When a public helper moves or is demoted, re-key its `spec/decl_markers.tsv` entries in
the same change (the table is keyed by the module path), and treat the demotion as a decision
about the mathematics (§5), not as a way to change the number of statements compared.

## 5. Structure and sharing across theories

**Real mathematics is written once.** Expense is distance from mathlib (§1), so a real result
left `private` and re-derived in the next theory is pure loss; glue and trivia are not worth
exporting.

- **The measure is mathematical content relative to the project**, not size or today's consumer
  count. `Defs/` is for structures that carry later mathematics (`IntegralStructure`, `Eigenform`,
  `HeckeOperator`), not general lemmas; share real math even with one consumer today, keep glue
  and trivia unexported.
- **A theory exports only from its own domain** — a `ZMod` residue fact or a `tsum` must not be
  reachable by importing the Eisenstein module. A helper that only adapts another theory stays
  `private`; if commonly needed, promote it in the theory it adapts.
- **Generalise near-duplicates, do not copy them** — copies differing only in binder spelling or
  `[NeZero]` position become one lemma (the checker sees the text, the elaborator the binders, so
  fix both, §4), and a `def … : Prop` declared twice under one name with different unused instance
  binders becomes the more general copy once.
- **Namespace policy is decided before the wave.** When a pin chapter wraps sub-theories
  (`M4aLocalCFT.X`), rename the chapter to the theory's namespace and **keep `X` as a
  sub-namespace** (two can carry the same name with different statements, so merging collides),
  and make a home's public names reachable under the spelling consumers use.
- **Check co-import collisions before the consumer is designed**: two green modules can be
  **unimportable together** (a name declared in both, or a plain and a `scoped` instance). Grep the
  consumer's import set and register the collision in [CARRY-FORWARD.md](CARRY-FORWARD.md) rather
  than renaming a frozen public name mid-wave; for a pin-name clash the fix is `private` (mangled),
  not a rename — and never while another set is mid-check.
- **`private` and local instances are a first-class build tool**: prefer `haveI`/`letI` or a
  `private` instance over global instance search (cheaper, collision-free, the checker is
  text-only), reserving *public* for the pin's names, the exported API and a shared engine — which
  is exported on purpose, not hidden (§4)
  ([../notes/lean-build-cost.md](../notes/lean-build-cost.md) §2).
- **Home is a build-cost decision**: promote where the needed type is available, rename at
  promotion when the pin name is taken (keeping a local alias), and prefer the leaf side of a hub
  boundary when the mathematics admits either home — but never split a genuine theory.
- **Name a promoted helper at the prefix-stripped pin name** (`kw_g₂_ofTau` → `g₂_ofTau`; the
  checker matches it through its `kw_` strip). A transcribed declaration keeps the pin's name, `kw_`
  included; a module-local helper is `private` with a content name. Never leave one both public and
  stripped; defer a pin-public strip with external consumers.
- **Export a topic's outbound interface so the next topic imports instead of copying**; dissolve
  "externals"/"misc" modules into subject homes; give a generic cross-theory count its own
  top-level area or a `Reserve/` library built but not diffed.
- **One engine, public — not `private`, and no shell module.** When the pin writes the same
  development k times (the `CasCore17` triple: 2,342 raw lines of three near-identical files →
  1,208 net), write it once as a public engine and put the headlines verbatim at their wrappers'
  names in that same module (§4). A `private` engine costs the next theory the re-derivation the
  dedup was meant to save. A second module is a *subject* decision, never a verification one: a module
  that states mathematics the engine does not — another object, another cut — is a module in its own
  right, and the engine stays headline-free for its other consumers. What is not a module is a shell
  that only restates the engine's headlines: it costs a file, an import and a frozen name for nothing,
  because `spec-pin:` already diffs whatever the module states.
- **Promotion shrinks its host module; measure it**, and keep named instances and consumer tests
  `private`, while real mathematics stays public (§4).

## 6. Proof engineering: the failure modes that cost rounds

Accumulated tactic- and kernel-level mismatches, not mathematics. Each is a one-line fix; the
longer write-ups are in the records, and the instance-shaped ones, with re-runnable guards, in
[instance-friction.md](instance-friction.md).

- **Rewrite-search gap** — a generic lemma (`map_sub`, `Jacobian.comp_smul`) may not fire under
  `rw`/`simp` when the function argument leaves instances unresolved: prove a monomorphic helper
  by `exact` and rewrite through it.
- **`abbrev`** — `rw`/`simp_rw` do not unfold it: use `change` or `simp only [name]`.
- **A different but defeq head** — prove the identification by `rfl` and rewrite through it.
- **An `*_aux`-stated goal** — normalise and finish with `field_simp; ring`.
- **A `rfl` that now burns the budget** — name the missing bridge in `simp only`.
- **`FunLike` at a bare function type** (`ℍ → ℂ`) — pass the bundled form.
- **A kernel `Subtype.val` defeq between concrete `adjoin` carriers** — prove a generic coercion
  once at abstract carriers.
- **A slow module is usually cumulative, but not always** — bisect by milestone, and run the
  ladder's isolation probes (§3.5) before accepting *any* attribution, including one in an old
  record: `TwoCurveDescent`'s cost was a single declaration, and the record named another one.
- **A `show`/`exact` that differs from its goal only by zeta** (a local `let ψ := …` in the working
  context) — `isDefEq` abandons the syntactic path and unfolds the tower (`FunctionField =
  FractionRing (CoordinateRing ·)`; the reduction table shows `CoordinateRing ↦ 592`,
  `inferInstance ↦ 120`). The cure removes names rather than adding them: drop the `let`s, state the
  intermediates at the explicit terms, and `rw` with the `rfl`-level projection lemmas
  (`AlgHom.comp_apply`, `AlgHom.restrictScalars_apply`, `IsScalarTower.toAlgHom_apply`,
  `Algebra.TensorProduct.includeLeft_apply`). Worked twice — `KernelBaseChange`'s `bcIota₁_compat` and
  `TwoCurveDescent`'s `descentBCIota_compat`
  ([../notes/instance-friction-case-study.md](../notes/instance-friction-case-study.md)).
- **A `≤`-shaped lemma applied to a membership inside a large statement** — `f : F`, `h : F ≤ G`,
  `h f` unfolds `SetLike.le`, and inside a four-conjunct statement that can cost the whole edit-loop
  budget in one `isDefEq` while the statement itself elaborates in a second. Prove the element form
  once (`SetLike.le_def.mp`) and apply that at the site
  ([logs/qexp-regular-prolongation.md](../logs/qexp-regular-prolongation.md) §3).
- **A statement that will not elaborate at any proof budget** — a hypothesis whose instance *terms*
  `isDefEq` must compare (`hf : ∀ K : Compacts α, Summable fun n => ‖(f.comp …).restrict K‖`, with
  `Norm C(↥K, ℂ) = dist x 0` unfolding `BoundedContinuousFunction`/`sInf`/`Finset.sum`). Naming the
  type once and using the name where it is bound fixes the elaboration; the binder then deviates
  from the pin, so register the `own:` rows. Worked example:
  [logs/poisson-summation-statements.md](../logs/poisson-summation-statements.md).
- **Instance timeout** — supply the instance explicitly (`Algebra.IsIntegral.of_finite`), sometimes
  naming the element too (`private abbrev` **and** the instance).
- **A type alias that unifies two spellings of one object breaks instance search.** The same curve is
  `W⁄A` (`baseChange`) in the engine and `W.map f` in a `K₀ ≤ K` section; aliasing both into one
  `private abbrev` makes the alias a *semireducible* wrapper that `.instances` transparency cannot unfold
  (`failed to synthesize Algebra (CoordinateRing …)`), and rewrites over the alias fail too. Alias only
  the types whose spelling already agrees with the file's own uses; unifying two spellings is a sweep,
  not an alias.
- **A `show` that strips a double coercion is not a zeta artefact — keep it.** `(↑↑(f)).toFun …` (a
  `RingHom`-valued function coerced twice, into `FunLike`) has no `rw`-reachable goal shape, so the
  `show` is the only way to present `commutes'`; deleting it in the "spell the terms" style breaks the
  goal rather than cheapening it. Check whether the `show` is a zeta step (removable) or a coercion step
  (load-bearing) before removing it.
- **A module whose *types* are the floor** — Lean keeps section variables as syntax and re-elaborates
  their types for every command in scope, so a few expensive hypotheses (an `IsDomain (F ⊗ K)` over a
  `FractionRing` tower, an `AlgHom` between function fields) are paid once per command. Cheapest cure
  first: a variable that no *statement* mentions belongs inside the proof that needs it (`haveI`), not
  in the section — that is statement-neutral and it removes the cost from every command; then
  `private abbrev` type aliases for the private declarations; then accept the floor. `TwoCurveDescent`
  is the worked case: with all 48 theorem proofs stubbed it still failed a 20 s bound and passed 40 s,
  so the floor was the statements, not the proofs.
- **Two `Algebra`-like instances in one context** — a hard type error, not a cost; keep exactly one.
- **An instance keyed on a semireducible `def`** (mathlib's `(W.map f).IsElliptic` against a goal
  written `E⁄R`) — invisible to search, and no budget helps: state it in the goal's spelling and
  prove it at the unfolded one, the pin's `scoped instance … := inferInstanceAs (…)` bridge.
- **Brick recipe** — `#synth` the term, then `haveI : <goal, verbatim> := inferInstanceAs (…)` at
  the narrowest scope that hits it; `letI` when the instance carries instance arguments; guard a
  data-valued class with `example : (<brick> : <class> <args>) = <captured term> := rfl`.
- **Unused section variables are auto-omitted** — transcribe verbatim, do not "restore" them.
- **A `_` inside an `@`-application is not free.** `@Submodule.projectionOnto … _ _ h`, with `_` for
  `[AddCommGroup]`/`[Module]` on a `MonoidAlgebra` carrier, leaves a metavariable that `isDefEq`
  discharges by unfolding the algebra: >200k hearts, no search goal, so `trace.Meta.synthInstance`
  shows nothing. Write the pin's own `inferInstance` and the cost is zero
  (`ArchCutProjector.projCA_apply_left`/`_right`). Same class as the defeq rows below: the fix is one
  syntactic form, and the statement does not move.
- **`private` is not dot-accessible across namespaces** — write the qualified name.
- **"Ported prelude" is a claim to `grep -c`** — re-derive the ones that are `private`.
- **A `scoped notation` can shadow a binder name** — open the scope per declaration.

## 7. Drift checklist (mathlib `v4.34.0`)

The checklist is [topics/TOPIC-mathlib-drift.md](topics/TOPIC-mathlib-drift.md): the rename table, the
recurring shapes (narrowing lemmas, transparency and `def`-vs-`abbrev`, unused binders, the
`maxHeartbeats` rule, the `end` discipline) and the two cross-cutting facts. Work orders that say
"the playbook's §7 table" mean that file. Re-run it when a new pin is taken and append **there** — a
drift row belongs in that table, not in a work order.

The one fact to carry before opening it: API drift is the recurring real cost, and **the pin is not on
this line** — `anthropics/fermats-last-theorem@aa2d8b3` is Lean `v4.33.1` / mathlib `db584cd6`, the port
Lean `v4.34.0` / mathlib `v4.34.0`. Do not write "the pin is on the same mathlib line" into a work
order.

## 8. Tooling

The graph tools read FLT's docs-site data and our port; none runs Lean, and they live in the
unpublished `tools/deps/` tree.

| tool | answers |
|---|---|
| `fltdata.py`, `explore.py` | what a pinned theorem is, its premises, consumers, path |
| `prune.py` | which nodes a replacement lets the port drop (reachability, not closure) |
| `frontier.py` | how far a target still is from the ported frontier, in new **source-file** nodes — so a half-ported file still reads as unported (§2.3) |
| `port_graph.py` | our port's graph: blobs, duplicated private proofs grouped into blocks, promotion candidates, closures |
| `port_advise.py` | before a port: what the port already has (substitute, by *shape* — byte-identical text and "same conclusion, same hypotheses, binder-only spelling" are two tiers, and the shape tier is the reuse answer), what the set re-proves (port once), what differs only by binders (generalise), what each public declaration drags |
| `build_ladder.py` | the dependent cascade of an edit, the cheapest sufficient build under `flock`/`timeout`, a wave plan, and (`--audit` / `--profile`) which modules and declarations cost the time |
| `dedup.py`, `move_dead.py` | whether a declaration duplicates another (by identity, within or across modules), and — for the sweep of §3.8 — which declarations a module's public API cannot reach, moved to a `Reserve/` shelf and cut from the source in one run (`--copy`) |

**Instrument vs tool, when it comes to caching.** `spec/check_port.py` is the instrument: it
re-reads the module and the corpus stamp on every run and caches only its own per-module verdicts
(`tmp/check-port/state.json`), so a verdict is never trusted past the text it was computed from. A
tool may cache its own reconnaissance under `build/` and offer `--rebuild` to rescan, but its
decisions stay text-derived — computed from the same parse the checker reads, not by invoking the
checker (a subprocess couples the tool to the instrument and costs seconds per call — §4).

The loop: a coverage report from the pin graph chooses the target; `port_advise.py` prices reuse
and duplication before coding; `port_graph.py` measures the redundancy afterwards; the ladder
and the checker are the per-wave gate. The `fltdata` object answers "who consumes this pin
module" before scoping (`d.def_index[stem]` against `d.stmt_defs(i)` / `d.proof_defs(i)`), and
`spec/check_port.py <module>` diffs any module as soon as its header names its pin sources.

## 9. Open questions and recorded negatives

- **Hybrid vs faithful is a per-layer choice, and only a few mixes are measured.** No effort yet
  tested mathlib absorbing the core but not the periphery, or the reverse.
- **Round counts are not a cost model**; they track how often an agent stalled on a defeq or a
  name. Lines, declarations and named shape risks are stable. Nor is a *driver's* round a measure
  of a set: a port turn is hours of wall time, so a cadence that re-prompts sooner than that is a
  status request, not a checkpoint (§0.2, §3.4).
- **A `private` engine to keep the checked surface small is the wrong trade**, and so is a shell
  module added for the checker's sake. Both were tried on the Casimir set and reverted: the landed
  shape is one module — its three headlines diffed at the pin's statements, the shared engine
  public beside them — where `private` would have hidden real mathematics and a shell would have
  added a file (§4, §5). The two questions are separate and both are about consumers: *is this
  declaration used outside its module?* decides `public`/`private`, and *does this module state
  mathematics the engine does not?* decides whether it is a module at all. Neither is a way to shape
  a diff — a `private` declaration is simply not diffed.
- **Nothing is independently audited.** The "removed clutter" numbers are what each effort
  avoided writing, measured against FLT's own files, not a third-party check that the dropped
  items were dead.
- **Repo-wide prelude duplication is a separate effort** (38 files carry the slot prelude, 11 a
  parallel `jqModC` block), larger than any single port and not attempted.
- **Recorded negatives are part of the method**: mathlib has no `dedekindPsi`, no Γ₀ index
  formula, no short route from `CommonRoot`'s engines to `eq_of_isRoot_of_isLevel`; the
  `relNorm`/`normalizedFactors` norm block and `rval_aux` are irreducible as written.

## 10. Evidence: the efforts, their records and their reviews

Each landed effort has a measured *record* in [logs/](logs/) and some a closing *review* in
`topics/*-retrospective.md`; the column plans are `topics/PORTING-*.md` (retired blueprints), and
the mathematics each port targets is in `../math/` and `../base/`. The per-effort numbers stay
with the effort they describe — read the record, not a table here. Read an old record for its
numbers and its mathematics; its *workflow* is only current if the file is recent (§3.3).

## Appendix: section map from earlier revisions

Earlier records and work orders cite this file under an older numbering; the playbook's own links
point at the new numbers. The old "§3.x" (eleven approaches) maps to §2.2 and §6: "§3.1" (map to
mathlib first) and "§3.8" (mathlib's API as the interface) to §2.2, "§3.2" to §2.1/§2.3, and
"§3.3"–"§3.7" (`aeval`, `*_aux`, rewrite search, equality-once, `abbrev`) to §6. The old build
entries — "§3.9" `Scratch.lean`, "§3.10" friction log, "§3.11" build bounds, "§3.12" the ladder —
are §3.5 and §3.6, and "§3.11" also points at
[../notes/lean-build-cost.md](../notes/lean-build-cost.md). The old "§7.x" definitions-layer
experience is §3.1, §3.2, §3.5 and §4. Top level: old "§1" is §1, "§2" §2.4, "§4" §7, "§5" §0.1,
"§6" §9, "§8" §3.2, "§9" §5.

**The number "§3.8" was retired and is now in use again**: an old citation to it means §2.2
(mathlib's API as the interface), and the current §3.8 is the dead-code entry, which postdates
every one of those citations.
