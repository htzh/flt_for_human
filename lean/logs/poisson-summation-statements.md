# The Poisson-summation statement blow-up — three declarations, one hypothesis type

**Status: landed 2026-10-20.** The `ZLattice` pair's blocker
`SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace` (563 pin lines, draft at `lean/tmp/zlattice/`) was
measured at the library cap once, at 429 s, and the old profile attributed 237 s to "typeclass
inference", which sent the handover down the wrong route ("pin the instance the search is guessing").
This session re-measured it **without building the module** — `lake env lean` on the draft at
**low** caps, with declarations stubbed by `sorry` — and the cost is not a search at all: it is the
elaboration of the **statements** of three declarations, where checking a locally bound hypothesis
against a definition's signature forces Lean to unfold the norm on a restricted continuous map. The
fix is to **name the hypothesis type once**; it brings the whole 614-line module under 20,000
hearts in ~6 s. The price is 6 statement deviations plus the new type name — 7 `own:` rows in
`spec/decl_markers.tsv` — recorded in §6. The pair is now in the library as
`FLTForHuman/Analysis/Fourier/PoissonSummationPi.lean` (613 lines) and
`PoissonSummationZLattice.lean` (293 lines): the first builds in **5.5 s** (3,189 jobs), the second
in 5.4 s (3,202 jobs), both with 0 warnings; the checker reads **31 ok / 0 mismatch / 0 missing /
7 own** and **2 ok**, and `--all` **2,884 ok / 11 own over 109 wired modules** (was 2,851 / 4 / 107).

Companion registers: [build-time-issues.md](build-time-issues.md) §2 (the entry this corrects),
[../porting-playbook.md](../porting-playbook.md) §5–§6 (the probe and cap rules),
[../instance-friction.md](../instance-friction.md) (the fix-shaped register, with re-runnable probes),
[../CARRY-FORWARD.md](../CARRY-FORWARD.md) (the deferred pair). Column state:
[../topics/PORTING-DeligneSerre.md](../topics/PORTING-DeligneSerre.md) §5.

## 1. The measurement

`lake env lean` on the draft (imports cached, no `.olean` written, no `lake build`):

| run | cap | wall | result |
|---|---|---|---|
| draft | 20,000 | ~10 s | 3 declarations time out, at their **statement** lines |
| draft | 200,000 | 51.8 s | the **same 3**, still timing out |
| draft, their 3 proofs `sorry` | 20,000 | 7.9 s | the **same 3**, still timing out |
| draft, one statement (no proof) | 1,000,000 | 82.8 s | still timing out — one statement alone is over 1M hearts |
| draft, hypothesis type named | 20,000 | **5.96 s** | 0 errors |
| draft, hypothesis type named | 200,000 | 5.73 s | 0 errors |

The three are `periodizeCM_apply`, `periodizeLiftFun_toUnitAddTorus`,
`periodizeLift_toUnitAddTorus` (draft lines 315–364, the pin's `section PeriodizeLift`), and at
20,000 hearts they fail as `timeout at isDefEq` / `whnf` / `whnf`. Everything else in the module
elaborates inside 20,000. At 4,000 hearts ten declarations exceed the cap; after the fix, seven —
the same seven ordinary ones (draft numbering: lines 163, 212, 467, 509, 520, 605, 611), with
exactly the three statements removed.

So the 429 s of the old profile is those three statements: its three `elaboration took` lines sum to
190 s, and its typeclass-inference counter (237 s) is the same statements' unfolding, counted in a
separate profiler category — see §3 for why that counter fires. The rest of the 614-line module is
~10 s, measured at 20k. The three are far over the 200,000 diagnostic and over 1M; the library's 4M
is enough for them (the module completes at 4M), it is just slow.

## 2. It is the statements, not the proofs

Replacing the three proofs with `sorry` and re-running at 20,000 hearts reproduces the three
timeouts at the statement lines (`319:18 isDefEq`, `332:23 whnf`, `352:20 whnf` in the stubbed
copy; `336`/`363` in the draft). A `sorry` body is skipped but the statement is still elaborated —
so the whole cost is in the type.

The failing operation is the **application of a definition to a locally bound hypothesis**. Isolated
in one file (prefix = lines 1–313 of the draft, i.e. through the body of `periodizeCM`):

| probe | cap | result |
|---|---|---|
| `example (f) : (⇑f) x = (⇑f) x := rfl` | 20k | ok |
| `example (f) (hf : <the hypothesis type>) : True := trivial` | 20k | ok |
| `example (f) (hf) (x) : periodize (⇑f) x = 0 := sorry` | 20k | ok |
| `example (f) (hf) : periodizeCM f hf = periodizeCM f hf := rfl` | 20k | **timeout** |
| `example (f) (hf) (x) : periodizeCM f hf x = 0 := sorry` | 20k | **timeout** |

The binder alone is free, `periodize` is free; the *application to `hf`* is not — and it does not
even need the `x`. The same equation is also free inside a proof (`have h : periodizeCM f hf =
periodizeCM f hf := rfl` passes at 20k), and the same application appears for free in the *body* of
`def periodizeLiftFun`. It is expensive only in a **declaration-type** position: the same equation
stated as a `def`'s or `theorem`'s type times out, as a `have`'s type does not. That is why the
three *statements* are the hotspot and why no tactic or proof-level change can move it.

The hypothesis in question is

```lean
(hf : ∀ K : Compacts (d → ℝ),
  Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
```

and the pin writes it in this spelling in every one of the six `PeriodizeLift` declarations.

## 3. The mechanism

Two cheap diagnostics on the failing single statement (`set_option diagnostics true`, and
`set_option trace.Meta.isDefEq true` at a 3,000-heart cap so the trace is short):

* the declaration-level counters are all **reduction**, not search:
  `ContinuousMap.instNorm ↦ 3854`, `Set ↦ 3864`, `Elem ↦ 10283`, `Membership.mem ↦ 7718`,
  `instTopologicalSpaceSubtype ↦ 3852`, `dist ↦ 2569`, `sInf ↦ 1286`, `Multiset.map ↦ 550`,
  `Finset.sum ↦ 70`; the only instance "used" is `ContinuousMap.instNorm`;
* the trace's final comparisons are

  ```
  ‖ContinuousMap.restrict (↑K) (f.comp (ContinuousMap.addRight (intVec b)))‖
    =?= ‖ContinuousMap.restrict ?m.25 (f.comp (ContinuousMap.addRight (intVec b)))‖
  ```

  i.e. the two spellings of the hypothesis agree everywhere except the **set argument of
  `ContinuousMap.restrict`**: one side has the coercion `↑K`, the other still has a metavariable.
  `↑K =?= ?m.25` is reported `[nonassignable]`, so `isDefEq` gives up assigning it and falls back to
  unfolding: `ContinuousMap.restrict`'s structure (`toFun`, `continuous_toFun`), then the `Norm` on
  `C(↥K, ℂ)`, which mathlib defines as `dist x 0`
  ([Compact.lean#L161](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Topology/ContinuousMap/Compact.lean#L161));
  `dist` on a continuous map is the `BoundedContinuousFunction` distance, `sInf` over `Set.range`,
  whose comparison descends into `Finset.sum`/`Multiset` (`Quot.lift`, `List.foldr`). That is the
  3.9k–10k unfolding counts and the 4M hearts: *instance terms* being compared and unfolded, not
  instance search.

Hence the old reading "the cost is instance inference, so fix it by pinning the guessed instance
argument" is half right: instance inference is where the time is *counted*, but there is nothing to
pin — no `synthInstance` goal is slow here, and the `(f := toUnitAddTorus)` pin that did help (on
the four `Function.surjInv` and one `Function.surjInv_eq` in the same section) is a different,
already-landed hotspot. The remaining cost is in the *type*, at the argument check, and the
metavariable is why the check cannot short-circuit.

## 4. What the pin does

The pin sets `maxHeartbeats 3200000` file-wide and **`16000000` on `section PeriodizeLift`
exactly** — [S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.lean#L255-L257](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.lean#L255-L257)
— and that section is precisely these six declarations. So the pin hit the same wall and paid it
with a 16M bump; the port inherited the wall. The 16M is **precaution**: the port's own 4M is
enough (the draft completes at 4M), so this is not the "arithmetic defeq, keep the pin's bump"
case of the column policy — no `set_option` is needed. What blocks the landing is iterability: it is
~190 s of statement elaboration in a 614-line module, which no edit loop can pay inside 2 minutes.

## 5. The fix that works

Name the hypothesis type once, and use the name in the three definitions and the three theorems:

```lean
def LocSum (f : C((d → ℝ), ℂ)) : Prop :=
  ∀ K : Compacts (d → ℝ),
    Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖
```

then `(hf : LocSum f)` in `periodizeCM`, `periodizeCM_apply`, `periodizeLiftFun`,
`periodizeLiftFun_toUnitAddTorus`, `periodizeLift`, `periodizeLift_toUnitAddTorus`. Both `def` and
`abbrev` work (measured 5.96 s and 6.42 s at 20k). With the name, the argument check compares
`LocSum f` with `LocSum f` — the same constant at the same arguments — and never descends into the
map's norm. Nothing else in the module changes: the literal spelling still flows in wherever a
caller binds it (proof-position checks are free, as §2 measured), so `periodize_eq_tsum_piFourierIntegral`
and the `SchwartzMap` wrappers keep the pin's binder text and still elaborate at 20k.

A verified copy of the whole module in this shape is parked as `PoissonSummationPi.locsum.lean`
next to the draft. It is the pin's transcription with the six binders renamed — no proof, no
statement *content* and no import changed.

## 6. The price, and the register

`spec/check_port.py` on the faithful draft: **37 ok, 0 mismatch, 0 missing**. On the named-hypothesis
copy: **31 ok, 6 mismatch, 1 missing** — the 3 definitions, the 3 theorems, and the new `LocSum`.
The landing therefore carries **7 deviations**, and they are in the central register
([../spec/decl_markers.py](../spec/decl_markers.py), whose data file is `spec/decl_markers.tsv`),
keyed by the module's tree path at landing and the full declaration name, with an `own:` reason
naming the build-time cause. The module's home is fixed by the sibling draft's import:
`FLTForHuman/Analysis/Fourier/PoissonSummationPi.lean`. The row for the new name and the row for
`periodizeCM` are shown; the five siblings are the ones named in §5's list (columns are
tab-separated):

```
FLTForHuman/Analysis/Fourier/PoissonSummationPi.lean  P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.PiPoissonSummation.LocSum  own: build-time name for the PeriodizeLift hypothesis type (defeq)
FLTForHuman/Analysis/Fourier/PoissonSummationPi.lean  P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.PiPoissonSummation.periodizeCM  own: binder type named LocSum, defeq — the pin spelling needs >1M hearts in the statement
```

The statements are defeq to the pin's — only the binder's *name* differs — so this is a
presentational deviation, not a weakened statement, and the reason field should say so. The alternative (keep the pin's six
spellings) needs no `set_option` — the library's 4M suffices — but pays the three statements' cost on
every elaboration of the module; per §5 of the column note, a module that cannot be iterated inside 2
minutes does not land, so the choice is the 7 deviations versus ~190 s of statement work per edit.

## 7. Reproduce

All probes are `< 60 s`, none builds:

```bash
cd lean
# 1. the draft at a low cap: three statement timeouts
timeout 100 lake env lean -DmaxHeartbeats=20000 tmp/zlattice/PoissonSummationPi.lean
# 2. the same with the three proofs stubbed: still the same three (prefix/sorry isolation)
#    the stubbed copy kept for the record is tmp/zlattice/probe/stub3.lean
# 3. the named-hypothesis copy: 0 errors, ~6 s
timeout 100 lake env lean -DmaxHeartbeats=20000 tmp/zlattice/PoissonSummationPi.locsum.lean
# 4. the mechanism, on one statement
#    set_option diagnostics true            in the file -> the unfolding table of §3
#    set_option trace.Meta.isDefEq true      at -DmaxHeartbeats=3000 -> the restrict/↑K vs ?m line
```

Declaration-level probing was done with a labelled `example` file built from the draft's prefix
(lines 1–313, through `def periodizeCM`) — the draft's own helpers, so a probe costs the helpers
only, not the module. The harness is at `lean/tmp/zlattice/probe/` (`run_probes.py`, plus the
variants kept for the record).

## 8. What this changes

* for the `ZLattice` pair: the `SchwartzMap` module is no longer "429 s and unknowable". The three
  hotspots are named, each fails in its statement, and the named-hypothesis shape elaborates in
  ~6 s at 20k. The pair can now be iterated; `PoissonSummationZLattice.lean` (the two `ZLattice`
  headlines) declares no `hf` binder of its own and is blocked only on this module's `.olean`.
* for the method: a heartbeat timeout is not automatically a slow *proof*. The first cut is
  "replace the proof with `sorry` and re-probe" — if the statement still times out, the cost is a
  term in the type and the fix is a *name*, not a pinned search. This is now a bullet in the column
  note §5.
* for the register: the `ZLattice` entry in [build-time-issues.md](build-time-issues.md) §2 and the
  deferred-pair paragraph in [../CARRY-FORWARD.md](../CARRY-FORWARD.md) no longer recommend pinning
  instance arguments for these three declarations.
* for the second draft: it was checked for the first time this session and had **two hard name
  errors** (§9), now fixed in the parked copy; its own head is a proof just over the 20,000 edit-loop
  cap, far under the 200k diagnostic.

## 9. The second module — two hard errors on its first elaboration

`PoissonSummationZLattice.lean` (293 lines, the two `ZLattice` headlines) had **never been
elaborated** — it needs the first module's `.olean`, which does not exist. It was checked here by
putting its body after the fixed first module in one file (same imports, same names an `.olean` would
export), which is equivalent for name resolution and elaboration. Two hard errors showed up; both are
consequences of the *dedup decision* recorded in its header (the pin's two `S_` files re-declare the
`PiPoissonSummation` engine, so the pin never needed a cross-file spelling; the port imports the
engine from module 1 instead, and that spelling was never checked):

* `open PiPoissonSummation` — **unknown namespace**. Module 1 keeps the engine under
  `P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.PiPoissonSummation`; the bare name only
  exists inside the pin's own file. Fix: the fully qualified `open`.
* in the first proof, the qualified
  `PiPoissonSummation.SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral` — **unknown
  identifier**. With the right `open`, the short name
  `SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral` resolves.

Both are proof/name fixes that do not touch a statement: the checker reads **2 ok, 0 mismatch**
on the landed file. A third, cosmetic drift came out of the landing: the pin's `hpair` proof carries
an unused `Finset.sum_ite_eq` in its `simp only`, which the port's 0-warning policy drops. With the
fixes, both headlines elaborate and their axioms are `[propext, Classical.choice, Quot.sound]`.

Its own cost profile is different from module 1's: the head is the **proof** of
`ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral`, which fails at 20,000 hearts and
passes at 21,000 — a hair over the edit-loop cap, far under the 200,000 diagnostic; the second
headline and the module body are under it. Module 1 + module 2 together elaborate at 30,000 hearts
in ~7 s. So module 2 is not a build-time blocker once module 1's statements are fixed; its landing
is blocked only by module 1's `.olean` and by the 7 register rows of §6.

One structural fact worth knowing for the landing: module 1 never closes its
`namespace P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace` (the pin's `S_` file does not
either — Lean accepts an unclosed namespace at EOF). Harmless through an import, but anything
appended to that file lands inside the namespace, and a bare `open scoped SchwartzMap` appended
there resolves to the *inner* `SchwartzMap` namespace instead of mathlib's scope.

### Landing chores in the two files

* module 1 carries **one warning** under the 0-warning policy — the pin's
  `linter.unusedSectionVars` note on `toUnitAddTorus_eq_iff` (the pin disables that linter
  file-wide; the port wants `omit [Fintype d] in` on that one declaration);
* module 1's header lists **18 imports, 6 of them repeated** (12 distinct) — the pin's duplicate
  block came across; dedup at landing;
* both modules are `sorry`-free and their headlines' axioms are `[propext, Classical.choice,
  Quot.sound]` (checked on the fixed copies);
* `set_option autoImplicit false` is set in both files although the lakefile already sets it
  (harmless, but redundant).
