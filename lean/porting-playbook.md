# Porting FLT to mathlib — a playbook

The source of truth is the pinned FLT repository (`anthropics/fermats-last-theorem`,
currently `aa2d8b3`). This file is the method the completed ports share; each has a *record*
in [logs/](logs/) and some a *review* in `topics/*-retrospective.md`, indexed with measured
numbers in §10. Read a record for what an effort did; read this before starting the next one.

Three conventions. **The pin is the authority and faithfulness is mechanical**: every ported
*statement* is diffed against the pin by `spec/old_check_stmts.py`, never trusted; where
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
5. **The manager owns the checker wiring, and the wire is the surface you choose to diff, not
   every public declaration.** Public theorems (the API) stay public; a module is listed for the
   statements that must stay verified, and the rest of its public surface — a shared engine, a
   family of helpers — is recorded behind a declaration-level `pin:` marker. New work keeps
   that marker in the central `spec/decl_markers.tsv` (checker metadata, not source); the legacy
   modules keep the grandfathered `-- pin:` comments and the old register. Never make real
   mathematics `private`, and never add a module, to make the checker's delta smaller (§4.1, §5).
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
(§3.1–§3.2); one topic at a time with a work order (§3.3); each in-scope node whole (§2.3);
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
- **Integration is the manager's**: the capstone and the wire test are the review instrument.
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
- Report the **outbound interface tier** and the **duplication already visible** in the pin.
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
  body or run `--prop-bodies` on every such row.
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
modules; **docstrings carry the mathematics** (a one-line gloss for a name that does not state
its content, a sentence for a construction); **adopt mathlib's names where it has them, keep
FLT's where it does not**, and say which is which; **monomorphic helpers are documentation**,
written the moment a `rw` reports no progress (§6), not before; **no self-consumed lemmas** — the
node boundary is not a licence to carry dead scaffolding.

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
Source** — pinned files and line ranges, the wrappers for statements, and the `pin:
<name> (<file>:<line>)` provenance entry in `spec/decl_markers.tsv`, owed **only on public
declarations** (§4.1); no marker comment is added to the Lean source for new work;
**(3) Deliverable** —
module path and declaration list, public vs `private`; **(4) Route** — the mathlib map, the
alternatives, the recorded negatives, and a **stop-early risk list with a deviation protocol**;
**(5) Build discipline** — the bound and the ladder (§3.5), copied in; **(6) Verification** —
checker delta, consumer zones, `#print axioms`, `grep -c` of anything dropped. Update the
numbers in place when reconnaissance re-prices; re-cut a topic that straddles waves **by
mathematical object** — construction, properties, consequence — without splitting a node.

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
  decision, the drift fixes and the wiring. Record it in the set's own table, not as a failure.
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
exempted. `lake build`'s higher cap is not a target, and no module carries a
`set_option maxHeartbeats`.

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

Two traps: **a stale `.olean` reads as a missing declaration** (after a `private` → public
promotion, `lake build <defining module>` before the consumer), and **importing a huge
`.olean` is an edit-loop cost of its own**.

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

## 4. Faithfulness, made mechanical

With a pinned source, correctness is checkable rather than trusted. Four instruments:

1. **The statement checker** (`spec/old_check_stmts.py`) diffs every ported *statement*
   (signature up to the first top-level `:=`/`where`; for a `structure`, header plus ordered
   field names) against the pin, matching names after normalising namespace qualification.
   Proofs are ignored: the port adapts proofs, never statements. Target `0 mismatched / 0
   missing`; the *identical* count is the progress metric, its delta reconciled against the
   **new wired public surface**. **This checker is frozen and is no longer the registry.**
   Its `PORT_FILES`/`SOURCES` lists are the grandfathered set: do not add an entry to either.
   A new module is wired in its own header (`spec-pin:`, below) and checked by
   `spec/check_port.py`; a module is handed over by adding those lines and deleting its
   `PORT_FILES` entry in the same change. While an entry remains, the old checker owns the
   module and the new one exempts it. **Wiring is the manager's and is not owed to every public
   declaration**: the API is wired so it stays verified, while the rest of a module's surface is
   marked and registered rather than either wired or hidden. **Tier 3 is not "unlisted module".** A *listed* module may carry public
   declarations the checker does not diff: a declaration-level marker records it — a `pin:` entry
   in `spec/decl_markers.tsv` for new work, or the grandfathered `-- pin: <name>
   (<file>:<line>)` comment above it — and a declaration whose marker names a pin file absent
   from `SOURCES` is counted `UNWIRED` rather than reported `MISSING IN FLT`. (The legacy register
   `spec/UNWIRED-PUBLIC.md` is generated by `spec/unwired_register.py` and is **not committed**:
   regenerate it with that script, never edit it by hand. New modules do not need it.) So a
   module can be listed for the statements that must stay verified — its headlines — while its
   shared engine stays public, importable and findable. A marker is a **fallthrough**, not a
   suppression: when the marker names a listed file, the marker's name is the copy diffed, and
   when any `SOURCES` file already provides the same name and statement the declaration is diffed
   anyway, so a marker can only remove a `missing`/`mismatch` that no listed source could justify.
   The policy is *everything wired is checked; no public statement is forced to be wired*.

   The marker is therefore owed on every **public** declaration and nowhere else — a `private`
   helper is filtered out before its provenance is read, so it may carry a marker for
   traceability but owes nothing. Decide the wire deliberately, at the module level: wire the
   headlines, and record the rest with a marker.

   **Declaration markers live outside the source (2026-10-20).** New work does **not** write
   `-- pin:` or `-- own:` above a declaration. Put the entry in the central
   `spec/decl_markers.tsv`, keyed by `(module, full declaration name)`, with a `pin:` or `own:`
   directive. `spec-pin:` stays in the module header: it is the module's wire, not a
   per-declaration exception. The old in-source comments exist only in grandfathered modules and
   are still read; do not add new ones. The table is checker metadata — editing it never changes
   a Lean build, and a stale entry is reported by `check_port` (`--strict-markers` makes it fail)
   rather than by the compiler. Text-shaped rules:
   - **Never make real mathematics `private` to shrink the delta, and never add a module to please
     the checker.** A `private` engine is one the next theory must re-derive (§5); a façade split
     into "engine module + headline module" exists only so that the headline is the whole wire,
     which the marker makes unnecessary. Both were tried on the archimedean Casimir set and both
     were reverted; the landed shape is one listed module, three wired headlines and 128 public
     declarations registered tier 3 (§5, §9).
   - **The checker's own unit test covers its mutation sensitivity** —
     `python3 spec/old_check_stmts.py --selftest` mutates a statement in memory and asserts
     exactly the one `mismatched` a full run would report. It is a test of the instrument, run when
     the checker changes, not a per-set manual mutation-and-revert. Put a declaration that is ours
     on an exemption list *with the reason* — add an `OWN_PROOFS` entry only when the statement
     differs or the name is shadowed.
   - **Keep `scoped` exactly where the pin has it** (invisible to the checker on both sides, so
     dropping it creates a spurious `MISSING IN FLT`) and **order `SOURCES` so the interface copy
     wins, appending new entries last**.
   - **The diff is textual, not elaborated**: spell binders exactly as the copy the checker will
     match — in practice the `Theorems/` wrapper, not the `S_` file — and keep a `def`'s pin binders
     in their `variable … in` form, since section variables never appear inline and spelling them
     out builds but reports **MISMATCH**.
   - **The `kw_` prefix is erased on both sides, name and statement**, so a one-token drift in a
     **promoted** declaration surfaces as `missing`, not `mismatched` — read `missing` too.
   - **`--` line comments mis-align the checker's namespace tracker**, spoiling the dotted names
     used by `OWN_PROOFS` and `--prop-bodies`; write header prose in `/- … -/` blocks.
   - **Ask whether the diff could be degenerate** (a truncated signature or an extracted `Prop` type
     looks identical in the count), and remember the checker never invokes Lean: on a module not yet
     in `PORT_FILES`, or stuck in a failing edit loop, run `raw_declarations` directly — a
     statement-shaped problem outranks the proof problem.
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
parser digests) makes `check` catch a stale corpus. `verify` proves every `SOURCES`
file's rows equal the checker's own parse, so it is the same text the checker would
diff; its statement hash resolves the whole checked surface (10,767 of 10,770
non-own declarations, 2026-10-19), which is what a successor to the checker keys on.
The corpus is a build artifact, never a source: regenerate it, do not edit it.
`spec/unwired_register.py` reads the same corpus (its `--rebuild` rebuilds it), so
the tier-3 register and the statement index are one scan, not two.

**Per-module checking (the successor, migrating one module at a time).**
`spec/check_port.py` takes the wire from the module itself: one `spec-pin: <pin
file>` line per pin source in the leading `/- … -/` block. Declaration-level
exceptions live in the central `spec/decl_markers.tsv` — a `pin: <name>
(<file>:<line>)` for a rename or a source outside the header, and an `own:
<reason>` for a tier-2 statement. A central entry takes precedence; the old
in-source `-- pin:` / `-- own:` comments are still read when no central entry
exists. New work should not add them. `--markers PATH` selects another table and `--strict-markers` fails
on an entry that no longer names a declaration. The table is checker metadata:
editing it never affects a Lean build. It hashes the
port statement the way the corpus does and matches by exact name, promoted key,
`kw_` strip, then content, so a faithful-but-renamed copy verifies and a
same-name statement that differs is a `MISMATCH` (with the identical statement
elsewhere reported as a hint). One file at a time, cache-aware:
`python3 spec/check_port.py <module>` skips an unchanged module,
`--changed` scans only modules whose content or corpus stamp moved, `--all`
re-checks everything, `--timestamps` prints the per-module stamp. State is
`tmp/check-port/state.json`; a corpus rebuild invalidates it. A module has one
owner, and the exempt list is the frozen registry itself: every module in
`old_check_stmts.py`'s `PORT_FILES` is a ported file that predates the protocol,
so `--changed`/`--all` skip it **by path without opening the file** (617 of 751
modules today) and read only the rest; there is no second list to maintain, and
the exemption shrinks with each handoff. `--include-legacy` overrides, and an
explicit path is always checked. The handoff is one change — `spec-pin:` lines in,
`PORT_FILES` entry out. The pilot, now the
first module the new checker owns, is
`FLTForHuman/ModularForms/CohCarrier/CommTriplet.lean` (three wrappers, three
statements, 0 mismatched); its tier-3 engine stays unlisted, as a module without a
`spec-pin:` line is tier 3 by definition.

When the capstone is conditional, track its debt counter as each field lands (the
`functionFieldGeneration` capstone: 7 → 0) and price the deferred cluster separately. When every
premise is an argument or already proved, the consumer's abstract-square wire test is the
capstone's analogue. When a public helper moves or is demoted: demotion drops it from the
compared count by exactly the number demoted (the expected signal), and a move must update
`PORT_FILES` at the new path or the declaration silently stops being verified.

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
  is exported on purpose and registered rather than hidden (§4.1)
  ([../notes/lean-build-cost.md](../notes/lean-build-cost.md) §2).
- **Home is a build-cost decision**: promote where the needed type is available, rename at
  promotion when the pin name is taken (keeping a local alias), and prefer the leaf side of a hub
  boundary when the mathematics admits either home — but never split a genuine theory.
- **Name a promoted helper at the prefix-stripped pin name** (`kw_g₂_ofTau` → `g₂_ofTau`; verified
  through the checker's `stripped_source`). A transcribed declaration keeps the pin's name, `kw_`
  included; a module-local helper is `private` with a content name. Never leave one both public and
  stripped; defer a pin-public strip with external consumers.
- **Export a topic's outbound interface so the next topic imports instead of copying**; dissolve
  "externals"/"misc" modules into subject homes; give a generic cross-theory count its own
  top-level area or a `Reserve/` library built but not diffed.
- **One engine, public, registered — not `private`, and not a façade.** When the pin writes the
  same development k times (the `CasCore17` triple: 2,342 raw lines of three near-identical files
  → 1,208 net), write it once as a public engine and wire only the headlines; the register keeps
  the wire honest without hiding the engine (§4.1). A `private` engine costs the next theory the
  re-derivation the dedup was meant to save; a façade module costs a file, an import and a frozen
  name for no gain in verification. The measurable check: the checker's `identical` delta equals
  the wired headline count and its `UNWIRED` count equals the public engine.
- **Promotion shrinks its host module; measure it**, and a tight *wire* is a deliberate cost —
  keep named instances and wire tests `private`, but let real mathematics be public and
  registered (§4.1).

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
- **A slow module is usually cumulative** — bisect by milestone, do not hunt one blow-up.
- **Instance timeout** — supply the instance explicitly (`Algebra.IsIntegral.of_finite`), sometimes
  naming the element too (`private abbrev` **and** the instance).
- **Two `Algebra`-like instances in one context** — a hard type error, not a cost; keep exactly one.
- **An instance keyed on a semireducible `def`** (mathlib's `(W.map f).IsElliptic` against a goal
  written `E⁄R`) — invisible to search, and no budget helps: state it in the goal's spelling and
  prove it at the unfolded one, the pin's `scoped instance … := inferInstanceAs (…)` bridge.
- **Brick recipe** — `#synth` the term, then `haveI : <goal, verbatim> := inferInstanceAs (…)` at
  the narrowest scope that hits it; `letI` when the instance carries instance arguments; guard a
  data-valued class with `example : (<brick> : <class> <args>) = <captured term> := rfl`.
- **Unused section variables are auto-omitted** — transcribe verbatim, do not "restore" them.
- **`private` is not dot-accessible across namespaces** — write the qualified name.
- **"Ported prelude" is a claim to `grep -c`** — re-derive the ones that are `private`.
- **A `scoped notation` can shadow a binder name** — open the scope per declaration.

## 7. Drift checklist (mathlib `v4.34.0`)

API drift is the recurring real cost; re-run this list when a new pin is taken and append. **The
pin is not on this line**: `anthropics/fermats-last-theorem@aa2d8b3` is Lean `v4.33.1` / mathlib
`db584cd6`, the port Lean `v4.34.0` / mathlib `v4.34.0`. Do not write "the pin is on the same
mathlib line" into a work order.

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
| `Submodule.torsionBy.zmodModule` | does **not** exist — the instance is `AddSubgroup.torsionBy.zmodModule`; keep the pin's local instance under its own name |
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
| `Equiv.infinite_iff` | for `e : α ≃ β` it reads `Infinite α ↔ Infinite β`; check the direction at the call site |
| `Prime.dvd_finset_prod_iff` | `Prime.dvd_finsetProd_iff` |
| `ModularForm.coe_smul`, `ModularForm.coe_zero` | `FunLike.coe_smul`, `FunLike.coe_zero` (the `ModularForm.*` names are deprecated aliases) |
| `Finite.of_equiv` / `Set.toFinite` | `Nat.finite_of_card_ne_zero`, with the `Finite` instance passed explicitly |
| `Nat.card_zmod` | no longer needs `NeZero m` — the pin's `haveI : NeZero m` is dropped, not suppressed |
| `Isometry.antilipschitz.properSpace` | `Isometry.antilipschitzWith.properSpace` (same proof, warning-free) |
| a "statement-identical" substitute offered by `port_advise` | check the **direction**: the port's `RealIwasawa.rot θ` is the transpose of the pin's local `rotMat θ` (= `rot (-θ)`). Substituting at `+θ` compiles and silently flips every downstream character identity; substitute at `-θ` and let the pin's statements stay verbatim |
| a short last name (`add`, `smul`, `zero`, `sum`) on a pin-**public** declaration | it cannot be registered tier 3: the marker is a fallthrough, so a listed `SOURCES` file that carries an unrelated `add` turns the marker into a `MISMATCH`. Keep those `private` (they are structure lemmas of a local namespace) and say so in the note |
| `exists_subset_nhds_of_isCompact'` with a pointwise `(hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x)` | v4.34 takes set-relative `(hU : U ∈ 𝓝ˢ (⋂ i, V i))`; wrap the pin's lambda in `mem_nhdsSet_iff_forall.mpr` — the proof content is unchanged |
| `zero_le'`, `not_lt_zero'` | `zero_le`, `not_lt_zero` (the primed forms are deprecated aliases) |
| a literal pair passed where `AdeleRing R K` is expected, and `.1`/`.2` of it taken by `rfl` | `AdeleRing` is a plain `def` (`InfiniteAdeleRing K × FiniteAdeleRing R K`), so the pair is an adele only at *default* transparency: `rw`/`simp` fail with "not type-correct under the implicit transparency level". Bind it once — `set x : AdeleRing R K := (…) with hx` — then rewrite on `x.1`/`x.2` via `show … from by rw [hx]` (`by rw [hx]` already closes it). `erw` is a trap: it unfolds far enough to also unfold the definition under study, and the following projection rewrites then find nothing |
| `⟨dConjMat ℓ γ, ⋯⟩` as an `SL(2, ℤ)` element inside a `Subgroup` membership goal | `Matrix.SpecialLinearGroup` is a semireducible `def` (a `Subtype`) in v4.34, so the anonymous constructor elaborates at `{A // A.det = 1}` and the following `rw [Gamma_mem]` fails with "target expression is not type-correct under the implicit transparency level". Bind it first — `let x : SL(2, ℤ) := ⟨…, h⟩` — then `rw [Gamma_mem]` (or `mem_Lam0`) and `show` the entrywise conjunction; it also removes the pin's `simp only [Matrix.SpecialLinearGroup.coe_mk, …]` blocks |

The recurring *shapes*, beyond a rename:

- **A rename is not a re-typed or re-ordered lemma**: an API move can change argument order, its
  module, and the shape of a sum. A pin statement kept under a reasoned
  `set_option linter.deprecated false` is a residual item, not a silent pass.
- **A lemma can *narrow*: same name, stronger hypotheses** (e.g. `Integrable.mul_prod` gaining
  `[SFinite ν]`), and the gap can run through a whole API. Then the pin statement has no route
  through mathlib: isolate the missing input, keep a port-only lemma, defer with a
  [CARRY-FORWARD.md](CARRY-FORWARD.md) entry — never weaken the statement.
- **A module path is not always a module** (`Mathlib.LinearAlgebra.Quotient` is a directory —
  import `.Basic`), and **blanket `import Mathlib` hides transitive dependencies** (expect 3–5
  missing per file).
- **An unused *statement* binder** (a hypothesis the pin's proof never uses) is silenced by
  `have _ := h` in the proof, not by `clear h` — the linter counts the binding, and `clear` removes
  it. Renaming the binder is the one thing not to do: the checker diffs the statement text.
- **An unused variable is a warning, not a defect**: a pin lemma that does not use
  `[NumberField F]` (e.g. a `rfl`-shaped identity) needs `omit [NumberField F] in` above it, not a
  weaker signature; and a lambda whose binder is unreferenced (`fun v => rfl` in a `∀ v, …` slot)
  becomes `fun _ => rfl`. Both are `linter.unusedVariables` in v4.34.0 and neither touches the
  statement.
- **Tactics and terms change shape silently**: `convert h2 using 1` reorders goals (use
  `h2.congr_deriv`), `congr(...)` yields a different equation, a non-reducible `def` stops
  unfolding (bind with `let`), and `open` can create ambiguity — qualify instead.
- **Self-base-change is not definitional in `v4.34.0`**: carry `have hb : (E F).baseChange F = E
  F` and transport with `hb ▸ ⟨e⟩`.
- **Transcribe the pin's `linter.*` suppressions exactly; never its `maxHeartbeats`** (86 landed
  modules carry `set_option linter.unusedSectionVars false`). The gate is a warning-free tier-1
  elaboration, and classes the pin does *not* suppress are real — fix those as proof edits; the
  `haveI` style-linter fix is not universal, so suppress locally rather than weaken the proof.
- **A pin's `set_option maxHeartbeats N in` and its `synthInstance.maxHeartbeats` bump are claims
  to re-measure, not facts**; every one met elaborated at the low cap once the inference was
  found — and some needed no inference found at all: a transparency setting
  (`backward.isDefEq.respectTransparency false`) or a bulk budget was carrying an ill-shaped proof,
  and the fix was to restructure the proof, not to supply an instance. A library theorem can be
  cheap while its *concrete-instance* use is not: keep a `spec/` capstone zone hypothesis-form and
  put concreteness in the ground field.
- **`time` under-reports `lake env lean`** (the forked grandchild's CPU is not charged).
- **`end A.B` closes *both* nested scopes**, silently de-nesting every later declaration; write
  two bare `end`s, since the symptom appears downstream.

Two cross-cutting facts: `CuspForm` does not extend `ModularForm` (bridge with
`CuspForm.toModularFormₗ`), and `(W.map f).IsElliptic` is all a base-change `IsElliptic` instance
needs.

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

**Instrument vs tool, when it comes to caching.** The statement checker is published and does
its own live scan of `SOURCES` on every run: it never caches. A tool may cache its own
reconnaissance. `unwired_register.py` is the one that must read the pin's whole `SOURCES` list, so
it caches that scan under `build/` — the parse, ~13 MB of statements, plus a stamp of the
`SOURCES` list and every source file's size+mtime (0.04 s to verify) — and re-reads only the port
each run: ~7 s → 0.45 s, with `--rebuild` to rescan. Keep the boundary when adding tooling, and
keep a tool's own decisions text-derived: the register's tier-3 predicate is the marker **plus**
"no `SOURCES` counterpart by name and statement", which it computes from the same parse, not by
running the checker (§4.1, §9).

The loop: a coverage report from the pin graph chooses the target; `port_advise.py` prices reuse
and duplication before coding; `port_graph.py` measures the redundancy afterwards; the ladder
and the checker are the per-wave gate. The `fltdata` object answers "who consumes this pin
module" before scoping (`d.def_index[stem]` against `d.stmt_defs(i)` / `d.proof_defs(i)`), and the
checker can be driven as a library — load `spec/old_check_stmts.py` with `importlib` and
call `raw_declarations` — to diff a module not yet in `PORT_FILES`.

## 9. Open questions and recorded negatives

- **Hybrid vs faithful is a per-layer choice, and only a few mixes are measured.** No effort yet
  tested mathlib absorbing the core but not the periphery, or the reverse.
- **Round counts are not a cost model**; they track how often an agent stalled on a defeq or a
  name. Lines, declarations and named shape risks are stable. Nor is a *driver's* round a measure
  of a set: a port turn is hours of wall time, so a cadence that re-prompts sooner than that is a
  status request, not a checkpoint (§0.2, §3.4).
- **A `private` engine to keep the checker delta small is the wrong trade**, and so is a façade
  module added for the checker's sake. The tier-3 marker is the mechanism; measured on the
  Casimir set, the one-module shape gives delta +3 with 128 registered declarations, where
  `private` would have hidden real mathematics and a façade would have added a file (§4.1, §5).
- **The register's tier-3 predicate is not "marker into an unlisted file".** The checker consults
  a marker only as a fallthrough, so the predicate also needs "no `SOURCES` counterpart by name and
  statement — public or pin-`private`". Guessing it from `SOURCES` membership alone over-collected
  461 declarations across 39 modules; deriving it by running the checker instead worked but cost a
  7 s subprocess and coupled the tool to the instrument (§8).
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
with the effort they describe — read the record, not a table here.

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
