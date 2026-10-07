# D-6 (P-3), the two-curve countable descent: a constructed proof, and what the route missed

**Status (snapshot, 2026-10-06; the set is landed).** D-6 is the D row's tail — the headline
`WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`.
It was **not** transcribed from the pin's 3,729-line silo; it was reconstructed by reusing what
D-1/D-2/D-5 had already landed. That route decision was right, and it is what the port's own
playbook asks for (§2.4, "port the general, derive the special"). The execution nevertheless cost
two sessions and a large number of rounds, and the reasons are generalizable. This note is the
record of what actually happened, which fixes worked, and what to change next time. Sources: the
session record `session-72f9acf6` ("Confirm duplicate Velu frontier silo"), the current module
[`TwoCurveDescent.lean`](../lean/FLTForHuman/WeierstrassCurve/Isogeny/TwoCurveDescent.lean), the
pin `anthropics/fermats-last-theorem@aa2d8b3`, and both pinned mathlib checkouts
(`db584cd6` for the pin, `5ed2965256` for the port).

## 1. The decision, and why it was right

`frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --rank-by silo
--ready` ranked the node first at **3,729 silo lines with an unported closure of 0** — the tell
that a node's whole closure is the column just shipped. `port_advise` found **107 of the pin
file's 183 declarations already identical in the port**, and at source level 62% of the
substantive lines were verbatim in the five pin files P-2 had landed. So the file is the D row
restated in two-curve form, not new mathematics.

The route was therefore: promote the handful of D-2 helpers the two-curve proof names (D-2 kept
them `private` in `IntermediateField.lean`), land the pin's `iotaDescent*` family, reuse D-5's
landed kernel-transport seam, and write the two-curve descent itself as a **port-own** `private`
generalization of D-2's one-curve construction. The measured outcome vindicates it: the landed
leaf is **1,299 lines against the pin's 3,729**, and the checker confirms every statement it
lands is faithful.

The one genuinely new piece the route did identify, correctly, is the pin's **`NoAC` base-change
engine**: D-5 landed only the `General` twin, whose section carries `[IsAlgClosed F] [IsAlgClosed
F']` and four gate blocks and so cannot be instantiated at the subfield `K₀` where the two-curve
descent needs it. The worker found this and transcribed the gate-free engine privately (≈320
lines). That discovery was real and is recorded as an open refactor in
[`CARRY-FORWARD.md`](../lean/CARRY-FORWARD.md).

## 2. What the route did not carry — the misses

The route was right about *what* to reuse. It did not carry three things, and all three are
things the statement checker cannot see.

### 2.1 The pin's instance/attribute/budget scaffolding is part of the port

The statement checker diffs statement *text*. It is blind to `set_option`, `instance`,
`attribute`, `letI`/`haveI`, and `subst`/`clear`. The work order treated the pin's scaffolding as
disposable:

* It first asserted D-6 could **import** D-5's engine. Wrong; corrected mid-flight after the
  worker measured the `General`-only section.
* It first instructed the worker to **drop `s13DecEqAlgebraicClosure`** along with the gate
  device. Wrong, and it cost a round: the pin's global
  `scoped instance … : DecidableEq (AlgebraicClosure K₀) := Classical.decEq _`
  (`S_:603`) is not part of the gate machinery, and without it ~25 sites failed.
* The pin's **heartbeat budgets were never considered at all**. The pin runs the whole `S_` file
  at `maxHeartbeats 3200000` / `synthInstance.maxHeartbeats 1600000` (`S_:38–39`), the two-curve
  region at 6.4M/3.2M (`S_:3014–3015`), and `kw_surgehgf4_hfgkd_hKD_of_kerTransport` at
  **48M/8M** (`S_:2882–2885`). The port's project cap is `maxHeartbeats 4000000` and
  `synthInstance` stays at the Lean default **20 000**. The declaration the pin budgets at 48M is
  exactly the port's `gateDescent_of_descent`, and it is where the landed module's 4 m 49 s goes.
* The pin's `scoped instance … := inferInstanceAs (…)` bridges (`S_:3566–3568`) were not carried
  either. They matter because of §2.2.

### 2.2 No spelling contract for base-changed objects

The pin writes `E₀⁄K` as sugar. For `WeierstrassCurve` that notation expands to
`WeierstrassCurve.baseChange`, a **semireducible `def`** (`Weierstrass.lean:236`), while for
`Affine` the same notation expands to `Affine.baseChange`, a **reducible `abbrev`**
(`Affine/Basic.lean:264`) — in *both* pinned mathlibs, identically. The consequence is the whole
of D-6's difficulty:

* `E⁄R = E` is `rfl` at **default** transparency, but not at **reducible** transparency — and
  `isDefEq` in unification, typeclass search, and `rw`/`erw` keyed matching all run at reducible.
  So a step that "plainly" holds by `rfl` is invisible to search and to rewriting.
* mathlib's instance for elliptic curves is `instance : (W.map f).IsElliptic`; a goal written
  `(E⁄R).IsElliptic` therefore **cannot be synthesized at all**, at any heartbeat budget.

The port's private helpers mixed the two spellings. The knowledge was already in the tree: D-2
had met the identical wall and recorded both the diagnosis and the workaround in the module
header and body — `IntermediateField.lean:107–114` (the comment) and, decisively, `:960–966`
(`htmul`, a `have` restated in the plain spelling) and `:1009–1020` (the pin's `calc` replaced by
an explicit `Eq.trans` chain because "a `calc` step would have to unify `(E).toAffine.FunctionField`
with `(E₀⁄K).FunctionField` … at too low a transparency"). The work order cited D-2's *helpers*
for promotion but not D-2's *proof idiom*. The worker transcribed the pin's `erw`/`calc` forms
instead, and they could never close.

### 2.3 One instance per type per context

The pin's `letI : Algebra ℚ K := DivisionRing.toRatAlgebra` lives inside a `Prop`
(`∀ (K) [Field K] …, letI …`, `S_:2391`) that carries **no** ambient `[Algebra ℚ K]`; its proof
helper receives the instance only as an implicit argument at the call site. The port put its
two-curve helpers in a section that carried `[Algebra ℚ K]` **and** kept the statement `letI`.
The two are not definitionally equal, so `K₀ : IntermediateField ℚ K` denoted two types, and the
failure was a hard `Type mismatch` at the `∃`-intro — which downstream reads as `whnf` noise and
gets misdiagnosed as a budget problem.

### 2.4 Diagnostic discipline and cost as a design input

Two process misses, both visible only in hindsight:

* The first response to a red module was **restructure or raise the cap**, not *isolate the shape
  in three lines*. Most of D-6's "heartbeat" sites were *impossible* unifications, not slow ones.
* The leaf was written as one 1,300-line module whose every check cost ~15 minutes. Iteration was
  unaffordable, so the session guessed and the guesses cost rounds. The playbook already says the
  repeating cost is re-elaboration; a module with a known-hard core should be split by region.

## 3. What actually happened

### 3.1 Phase A — the "Confirm duplicate" session

1. Silo surfaced; manager confirmed a near-duplicate, recorded the scoping caution in
   `CARRY-FORWARD.md`, and proposed the reuse route.
2. Work order P-3 written from the P-2e template; one subagent dispatched (the port's rule: one
   set, one agent, serialized).
3. The worker wrote `TwoCurveDescent.lean` (1,227 lines), the ten-helper promotion in
   `IntermediateField.lean`, the consumer and the checker wiring. It found the `General`/`NoAC`
   engine gap (correct), was corrected twice by the manager on the scaffolding, and then hit the
   wall. **It never landed.** Statements were faithful and checked; elaboration was red.
4. The worker deliberately left the red leaf in the tree so the checker's verified statements
   stayed counted; the tree was therefore red on exactly that target.
5. The manager's goal loop ran to its **30-round limit** and blocked. Its closing §9 diagnosis —
   "the pin's tower-at-`R₀` defeq cost, which the pin pays for with 6.4M/19.2M heartbeats and the
   port's frozen 4,000,000 cap does not cover" — was **wrong**.

### 3.2 Phase B — this session

1. Read the session record, the module, the pin's `S_` file and **both pinned mathlib checkouts**.
   Found the recorded diagnosis false: `WeierstrassCurve.baseChange` is a `def` and
   `Affine.baseChange` an `abbrev` in *both* mathlib revisions, so no reducibility difference and
   no cap raise was involved.
2. Probed three shapes in `Scratch.lean`: the `letI`-vs-section-instance clash (a hard type
   error, `rfl`-refuted); `E⁄R = E` under `with_reducible rfl` (fails at reducible, succeeds at
   default); and `inferInstance : (E⁄R).IsElliptic` (fails at 20 000 and at 3 200 000 alike).
3. Applied the **single `Algebra ℚ K`** fix and restored the pin's `⁄`-spelling `IsElliptic`
   bridges. Five sites cleared; nine remained, and the check had grown to **14 m 41 s** at the
   project cap against the worker's 9 m 11 s.
4. Adopted a **low-`maxHeartbeats` diagnostic loop**: 200 000 → 2 m 30 s, 1 000 000 → 5 m 22 s,
   same target lines (plus the engine's own heavy declarations timing out, which are identifiable
   cap artefacts in a distinct line block).
5. **Restated** the two `erw` blocks in D-2's plain-spelling idiom. Both cleared.
6. Then hit a **masking chain** (§5): three latent defects surfaced one after another as earlier
   failures were removed — the tower brick (wrong spelling → invisible; right spelling → worked,
   exposing two `show`/`rw` patterns), the 48M budget (statement `whnf` → worked, exposing the
   `DecidableEq` clash and the gate-instance argument mismatch), and finally `subst` + `letI`
   bridges.
7. Landed and verified (§6).

## 4. Fixes tried, and their outcomes

| fix | outcome |
|---|---|
| restructure the proof / raise the port cap (worker's attempts) | **failed**; the sites were type-level, not budget |
| probe the pin's own 6.4M/3.2M budget | **diagnostic only**: 14 sites → 7, and **slower**; every type-level site stayed |
| `attribute [local reducible] WeierstrassCurve.baseChange` | **rejected**: needs `set_option allowUnsafeReducibility true`, and even then `with_reducible rfl` still fails; it perturbs `simp`/instance indexing |
| `backward.isDefEq.respectTransparency false` | **no effect** — it does not reach instance search, and `with_reducible rfl` still failed |
| **one `Algebra ℚ K`** (drop the section variable where the statement carries the pin's `letI`) | **worked**; cleared the `:937`/`:938` hard type error and its cascade |
| the pin's `⁄`-spelling `IsElliptic` bridges as `private instance … := inferInstanceAs (…)` | **worked** for the instance goals it targeted |
| tower brick stated as `(W.map …).toAffine.FunctionField` | **invisible** — instance search keys local instances syntactically, so a brick in the wrong spelling is never tried |
| tower brick stated as `((W.toAffine)⁄K).FunctionField` | **worked**, and exposed two `show`/`rw` patterns that had been masked |
| **restatement** in the plain spelling: a `have` proved by one direct application, plus `Eq.trans` instead of `erw` | **worked**, both `erw` groups |
| `classical` in place of the explicit local `DecidableEq` | **no** — the clash persisted |
| `clear hdecAC` after the `intro` | **impossible** — `ι₀` was defined earlier and depends on the instance |
| **`subst`** (`have hdec_eq : instDec = hdecAC := Subsingleton.elim _ _; subst hdec_eq`) | **worked** — the pin's own device |
| gate-instance bridges with `haveI` | **type mismatch** — `IsCentred`/`AbelTheorem` carry the `GenusOnePlaceGate` instance as an argument, and `haveI` leaves a distinct fvar |
| gate-instance bridges with **`letI`** | **worked** — `letI` inlines the value, so the seam's instance arguments become literally the caller's terms |
| transcribe the pin's **48M/8M** budget for `gateDescent_of_descent` | **worked** — the statement-level `whnf` (the pin's own 48M site) cleared |

## 5. The masking chain, and why it matters for review

The most transferable lesson of the episode is that **a failing module's error list is a
frontier, not an inventory**. When a declaration fails, Lean does not add its constant; every
later declaration that depends on it fails earlier or differently, so its own defects are never
elaborated. D-6's sequence was:

| after fixing… | the next defect surfaced |
|---|---|
| the `hχ` restatement | a `DecidableEq (AlgebraicClosure K₀)` identity clash at the final `kerTransport_s17` application — previously unreachable |
| the tower brick (right spelling) | two `show`/`rw` patterns in `twoCurve_chiCompChiEqPhi` that could not match across the `⁄` spelling |
| the statement `whnf` (48M) | the gate-instance argument mismatch in the seam — the caller's instances are on `E₀.map …`, the seam's on `(E₀⁄K)` |

Consequences:

* **Plan for N iterations, and do not treat the first error list as complete.** The landed count
  was four substantive fixes, but the *number of debugging rounds* was roughly double that.
* **A red module cannot be fully reviewed by reading.** The manager's Phase-A review checked the
  route, the public surface and the checker — correctly — but the instance defects were
  invisible until the earlier failures were removed. "Review the code before writing the next
  order" cannot substitute for elaboration.
* **Fix the earliest failure first, then re-measure.** Every later "error" is suspect until the
  declarations it depends on elaborate.

## 6. Cost, measured

| configuration | wall | result |
|---|---:|---|
| worker's revision, 4,000,000 cap | 9 m 11 s | 14 sites, red |
| after single `Algebra ℚ K` + `IsElliptic` bridges, 4,000,000 | **14 m 41 s** | 9 sites, red (and slower) |
| the same, 1,000,000 (diagnostic) | 5 m 22 s | same target lines |
| the same, 200,000 (diagnostic) | **2 m 30 s** | same target lines |
| **landed, 4,000,000** | **4 m 49 s** | **green, 0 errors** |
| landed, `lake build` of the module | — | 9,039 jobs, success |
| landed, whole-tree `lake build` | 2 m 25 s | 9,317 jobs, success |

Verification of the landed state: checker
`6054 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6090 checked)`,
**identical to the pristine tree** (every fix is inside a `private` proof);
`spec/TwoCurveDescentConsumer.lean` exit 0; `#print axioms` on the headline and on
`ModularCurve.exists_twoCurveDescent` both `[propext, Classical.choice, Quot.sound]`; no `sorry`.

The 4 m 49 s is essentially the one declaration the pin budgets at 48M hearts. That is a
fidelity transcription, not a cap exception — but it is also the natural target of the
engine-promotion refactor in §8.

## 7. Implications for future porting

Ordered by leverage. The first five should become planning-checklist items; the last two are
already in the playbook.

1. **Enumerate the pin's scaffolding, and carry it.** Before writing an order for a region, list
   its `set_option maxHeartbeats`/`synthInstance.maxHeartbeats`, its `scoped instance …
   := inferInstanceAs`, its `attribute [-instance] … in`, and its `subst`/`haveI` walls. Then
   decide, per item, *carry*, *promote*, or *drop with a reason* — and note that the statement
   checker will never flag a wrong decision. The port's convention of never transcribing
   `maxHeartbeats` is defensible in general but silently starves `synthInstance` (the project sets
   only `maxHeartbeats`), and the pin's 48M declaration is a case where the budget *is* the
   content.
2. **Write a spelling contract into the module header.** Choose one canonical spelling for
   base-changed objects (`E.map (algebraMap K₀ K)`, not `E⁄K`) for the port's own declarations, and
   forbid mixing. Where an imported pin-transcribed lemma forces the other spelling, bridge once,
   at the boundary: either restate the lemma's conclusion in a `have` (the D-2 idiom) or provide
   the instance in the goal's spelling with `inferInstanceAs`.
3. **One instance per type per context.** A statement `letI` plus a section `[Algebra ℚ K]` gives
   two `IntermediateField ℚ K`. If the statement carries the pin's `letI`, the section must not.
4. **Treat local instances as a first-class build tool** (`private`/`local` instances are already
   in the playbook for the environment-collision problem). Specifically: bricks must be stated in
   the goal's exact spelling; `letI` when the instance carries further *instance arguments*
   (it inlines, so the arguments become the caller's terms); `inferInstanceAs` when the instance's
   head is built by a semireducible `def`; the pin's `subst` to discharge a `∀ [DecidableEq …]`
   block against a local `classical` instance.
5. **Diagnose before restructuring.** A "timeout at maxHeartbeats" reports two different things:
   genuine compute, and a unification the elaborator cannot make. Three lines in `Scratch.lean`
   separate them. Corollaries: a low `-DmaxHeartbeats=` is a *diagnostic* (it turns a 15-minute
   check into a 2-minute one and still shows the target lines); and if the pin needs a much larger
   budget at a site, that is a signal to find the cheaper proof, not to raise the cap.
6. **Split leaves with a known-hard core.** Keep the unit of checking small enough that a
   hypothesis costs minutes, not a coffee break.
7. **Checker-green is not "landed".** `check_flt_statements.py` diffs statement text; it cannot
   see an instance or a spelling defect. D-6 was "faithful, 0 mismatched / 0 missing" and did not
   compile. A set is landed when the checker, a bounded `lake env lean`, `lake build`, the
   consumer and `#print axioms` all agree.

## 8. Implications for refactoring

1. **Under-generalized landings are the expensive kind of debt.** D-5 landed the engine
   `General`-only; D-6 then paid ≈320 private lines to get the `NoAC` twin. D-1 had already
   resolved the identical `General`/`NoAC` split in the *prelude* by making the `NoAC` name the
   primitive and the `General` name a one-line invocation. The rule to adopt: when a block is
   landed with a `General` section, land the gate-free primitive in the same round and make
   `General` the invocation — the *next* set's need is predictable from the pattern.
2. **A private copy is a receipt for a missing promotion.** D-6's engine copy, its `⁄`-spelling
   scaffolding (113 `⁄` occurrences, 9 `inferInstanceAs`, 21 `letI`) and the 48M budget are all
   candidates to shrink once the engine is promoted gate-free. Re-measure the declaration after
   the promotion; do not assume the budget or the scaffolding must stay.
3. **Refactor at the leaf, price the cascade.** `KernelBaseChange.lean` is a leaf, so the
   promotion's cascade should be small; `build_ladder.py --edit` is the tool, and the follow-up
   is recorded in [`CARRY-FORWARD.md`](../lean/CARRY-FORWARD.md) (now unblocked).

## 9. Process notes, honestly

* **The 30-round goal limit was consumed by an unfixable loop.** The manager could review, but it
  could not debug: the worker held the module, the checks took 15 minutes each, and the
  serialization rule ("one agent at a time") forbade a parallel probe. The low-cap loop is what
  broke the deadlock; it should have been available from round one. A work order for a heavy leaf
  should specify the *diagnostic* bound as well as the build bound, and a failing heavy module
  should be handed back with a truncated copy the manager can iterate on.
* **Two work-order mis-statements cost a round each.** Both were about the pin's scaffolding
  (§2.1), and both were corrected mid-flight by the worker's measurements. The lesson is not
  "measure more" so much as "the scaffolding is a first-class object of the plan".
* **The Phase-A closing diagnosis was confident and wrong.** It named a cause (reducibility) that
  a five-minute comparison of the two pinned mathlib checkouts refutes. Recorded in
  [`logs/velu-port.md`](../lean/logs/velu-port.md) with the section marked SUPERSEDED; the
  playbook §6 and [`instance-friction.md`](../lean/instance-friction.md) IF-003 now carry the
  correct rules and a live guard.
* **A stale checker figure propagated.** The recorded `37 own, 6091 checked` is not reproducible:
  the current checker gives `36/6090` on the pristine tree too. Figures copied forward without a
  re-run drift; the landed record now states the measured value and the discrepancy.

## 10. Reproduce

```
cd lean
python3 spec/check_flt_statements.py                       # 6054 (313, 83), 0/0, 36 own, 6090
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false \
  FLTForHuman/WeierstrassCurve/Isogeny/TwoCurveDescent.lean   # green, ~4 m 49 s
lake build FLTForHuman.WeierstrassCurve.Isogeny.TwoCurveDescent # 9039 jobs
lake env lean spec/TwoCurveDescentConsumer.lean             # exit 0
lake env lean spec/InstanceFriction.lean                    # exit 0 (IF-003 guard)
```

Diagnostic loop for a red heavy leaf (do this before restructuring):

```
cd lean
lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>   # ~2.5 min, target lines visible
```

The engine-promotion follow-up is in [`CARRY-FORWARD.md`](../lean/CARRY-FORWARD.md) under "The
`General`/`NoAC` split in the base-change **engine**".
