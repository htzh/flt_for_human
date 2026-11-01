# Typeclass-instance friction register

The **instances and instance-search goals** in this port that cost real elapsed
time, keep costing it on every elaboration, and are the kind of thing that
silently accumulates into a build-time hog. Kept apart from:

* [porting-playbook.md](porting-playbook.md) §6 — which states the *fixes* (this
  register says where a fix was needed and whether it holds);
* [../notes/lean-build-cost.md](../notes/lean-build-cost.md) — which holds the
  *measurement method* (`--profile`, `--audit`, heartbeat semantics);
* [logs/build-time-issues.md](logs/build-time-issues.md) — the D-S column's register of open build-time
  issues (over-budget declarations, olean gaps, lock/memory rules, measurement traps).

The list is expected to grow, so every entry below must be **re-runnable**, in two
halves:

* the *fix*, as a compiling `example` in
  [`spec/InstanceFriction.lean`](spec/InstanceFriction.lean) — revert the fix and
  the example stops elaborating;
* the *capture*, as a labelled `#probe` in
  [`spec/InstanceProbe.lean`](spec/InstanceProbe.lean) compared against the
  recorded terms by [`spec/check_instance_probes.py`](spec/check_instance_probes.py)
  — this is what notices a stale spelling or a changed term after a mathlib bump.

Both live in `spec/`, deliberately outside every library, so neither can slow or
break the verified build.

## What qualifies

Record an entry when *instance search or an instance declaration* is the cost:

* a `synthInstance` timeout (`deterministic timeout at typeclass, maximum number
  of heartbeats …`) — record the budget;
* a `set_option synthInstance.maxHeartbeats …` bump kept in the tree;
* an explicit `haveI`/`letI` wall added where instance search would otherwise run;
* an instance declaration that `build_ladder.py --profile` puts near the top of a
  module's cost, or that `--audit` flags as a `scoped instance` candidate.

An ordinary `failed to synthesize` message is a **missing** instance, not
friction: that is a gap in the library, not a hog. Do not record it here — with
one exception: when the instance *exists* but is keyed on a head the goal cannot
be seen to match (IF-003: the goal is `foo (bar x)` with `bar` a semireducible
`def`), the fix is an explicit brick (`inferInstanceAs`/`haveI`), and it belongs
here.

One case deliberately stays in the build-time register instead of this table: a
**statement-level** blow-up, where `isDefEq` compares two spellings of a
hypothesis type and unfolds the instance *terms* (the profiler counts it as
typeclass inference, but no search goal runs, so there is no budget to record and
nothing to pin — the fix is to name the type). First instance, bisection and the
register rows: [logs/poisson-summation-statements.md](logs/poisson-summation-statements.md).

## How to detect

1. **`tools/deps/build_ladder.py --profile MODULE`** — ranks the expensive
   declarations of a module. If the top lines are `instance`/`scoped instance`,
   it is a candidate.
2. **`tools/deps/build_ladder.py --audit`** — per-module `lake env lean` time and
   edit cascade. A module that got slow *after* an instance change shows up here;
   the `scoped instance` scan lists the deletions worth trying.
3. **A timeout in the edit loop** — the direct signal. Record the goal, the
   budget, and the fix.
4. **The coding friction log** (playbook §3.6) — instance-shaped items are
   promoted into this register; the rest stays in `logs/`.

## Schema

One table row per entry; the long form is a section below the table.

| id | kind | where | goal / declaration | symptom | budget | cause | fix | status |
|---|---|---|---|---|---|---|---|---|
| IF-001 | search | `ModularCurve/Degree/PlaceDegree.lean` | `Algebra.IsAlgebraic (adjoin K {t}) F` from a local `FiniteDimensional` | timeout in the `deg_eq_one_modularFunctionFieldBar` proof | times out at 20000; instant via `of_finite` | the `Algebra.IsAlgebraic` search itself, over an `adjoin` of a large `coeffEmb` subtype term | name the element (`private abbrev jBar`) **and** pass `Algebra.IsAlgebraic.of_finite _ _` | fixed |
| IF-002 | application | `ModularCurve/JqIntegralRatios.lean` | applying `mem_intFormRatiosC` to build `jqModC K ∈ intFormRatiosC K Γ` | elaboration exceeds a 300 s wall bound | does not finish; anonymous constructor is instant | unification of the `Subgroup`/`mapGL` coercion and implicit weight `k` in the constructor's type | use the anonymous constructor (pin's form); keep the named one public | workaround |
| IF-003 | search | `WeierstrassCurve/Isogeny/TwoCurveDescent.lean` | `(E₀⁄(↥K₀)).IsElliptic` (and `(E₀⁄K)`) at the base-change engine boundary | search **fails outright** (`failed to synthesize`), then the surrounding engine calls spin | fails at 20000 and at 3200000 alike; instant via `inferInstanceAs` | the instance is keyed on `W.map f`, but the goal writes `E⁄R` — `WeierstrassCurve.baseChange` is a semireducible `def`, invisible to search at reducible transparency | state the instance in the `⁄` spelling, proved by `inferInstanceAs ((E.map (algebraMap R R)).IsElliptic)` (the pin's `scoped instance`, `S_:3566–3568`) | fixed |
| IF-004 | search | `ModularCurve/ModularPolynomialCoset.lean` | `Algebra K (LaurentSeries (AlgebraicClosure K))` inside order C's `solution` | a `rfl`-failure on the pin's closing `convert hp using 2` (lhs `(algebraMap L E).comp (algebraMap K L)`, rhs `algebraMap K E`) | no timeout; wrong instance only | `Algebra K (HahnSeries · K)` is a Mathlib diamond and the pin's local `letI` is not transcribable (the `haveILetI` linter) | write the pin's `letI` as a plain `let` — `have`/`let` register local instances, and a `let`-bound instance is zeta-reducible, so the composite *is* defeq to `algebraMap K E` | fixed |
| IF-005 | search | `ModularCurve/LevelN/GenusFF.lean` | `Module.Free ↥((AlgebraicClosure ℚ)⟮y⟯) (laurentBaseChange …)` inside `main_K`'s `FiniteDimensional` step (the pin's `synthInstance.maxHeartbeats 1600000`, its line 26) | `failed to synthesize` (no `of_divisionRing` in the closure) → after importing `Mathlib.LinearAlgebra.Basis.VectorSpace`, a **deterministic timeout at 20000**; `-DmaxHeartbeats` does not raise the `synthInstance` budget | >20000 at the concrete `adjoin`; **instant** at a variable `E`; hand-supplying the instance fails | the goal's `Module.Free` is keyed on `(SubsemiringClass.toCommSemiring …).toSemiring` while `Module.Free.of_divisionRing _ _`'s is `DivisionRing.toRing.toSemiring` — instance *paths* are data, so no hand-built chain matches; and with the concrete `adjoin` term the search has to unify the whole `IntermediateField` term for every candidate instance | state the fact at a **variable** intermediate field: `private theorem finiteDimensional_of_finrank_pos_intermediate (E : IntermediateField L M) (h : 0 < finrank E M) : FiniteDimensional E M`, then apply it at `E := ℚ̄⟮y⟯` — the search is then keyed on a variable and is instant, and the pin's 6.4M on `main_K` is not needed either | fixed |

**budget** is the cost proxy: the `synthInstance.maxHeartbeats` value at which the
naive form fails (or the measured seconds, for an instance declaration). Re-measure
both when the naive form starts working anyway (then the entry can be retired) and
when a mathlib bump makes it worse.

Each entry also records the **captured term** — what `#synth` prints for the fix's
goal at the spelling that resolves — and, beside it, the exact failure text at the
spelling that does not. The loop that produces both is playbook §6's recipe,
*capture what search picked, then provide the instance by hand*. The failure text
alone is not
enough: for a *data-valued* class (`Algebra`, `Module`, …) the brick has to
reproduce the term, not merely the type, so where the class carries data the entry
also carries a `rfl` **value guard** in the harness:

```
example : (<brick> : <class> <args>) = <the captured term> := rfl
```

a *type-only* `example` accepts a wrong brick, and the mismatch surfaces one
context later as a hard `Type mismatch` (D-6 §2.3).

## Re-measure cadence

The register is pinned to mathlib `v4.34.0`. After a mathlib bump, and after any
change to an entry's home module, re-run the harness:

```
cd lean
lake env lean spec/InstanceFriction.lean 2>&1 | grep -c error     # want 0
python3 spec/check_instance_probes.py                             # want "all entries match"
python3 spec/check_instance_probes.py --update                    # re-capture after an intended change
```

Then update each row's **budget** and **status**. `build_ladder.py --profile` on
the home module is the second reading for instance *declarations*, and the probe
checker is the reading for *search*: a brick whose goal spelling moved is invisible
rather than wrong, so the capture — not the build — is what notices. The checker
distinguishes the three drifts, each with its own action: `RECAPTURE` (term changed
— update the register and any brick naming it), `REGRESS` (a working spelling
stopped synthesizing), `RETIRE?` (a failing spelling started synthesizing — the
entry is no longer needed).

## Entries

### IF-001 — `Algebra.IsAlgebraic` over an `adjoin` of a big subtype term

**Where.** `FLTForHuman/ModularCurve/Degree/PlaceDegree.lean`, the
`deg_eq_one_modularFunctionFieldBar` proof (the T21 port of the pin's
`S_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean`).

**Goal.** From a local `FiniteDimensional (adjoin (AlgebraicClosure ℚ) {t})
(modularFunctionFieldBar M)`, synthesize

```
Algebra.IsAlgebraic (adjoin (AlgebraicClosure ℚ) {t}) (modularFunctionFieldBar M)
```

where `t` is the `j(q)` element of the bar field,
`⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange … (jq_mem_full M)⟩`.

**Symptom.** `synthInstance` timeout at the default 20000 heartbeats (the pin's
`B2Deg.deg_eq_one_of_isAlgebraic_adjoin` call site).

**Cause.** Two things, and the second is the surprising one:

* the element is written twice — once in the `FiniteDimensional` instance's type
  and once in the goal — as two *definitionally* equal but not *syntactically*
  equal `⟨coeffEmb …, proof⟩` terms, so instance search has to compare them;
* even after naming the element once (`private abbrev jBar`), the search for
  `Algebra.IsAlgebraic` itself still times out at 20000. Naming is necessary (so
  the `Module.Finite` premise of `of_finite` matches syntactically) but **not
  sufficient** — the fix has to bypass the search.

**Fix.** Name the element once with `private abbrev jBar`, and supply the instance
explicitly:

```lean
haveI := finiteDimensional_adjoin_jBar M
haveI : Algebra.IsAlgebraic (adjoin (AlgebraicClosure ℚ) ({jBar M} : Set …)) … :=
  Algebra.IsAlgebraic.of_finite _ _
```

**Captured term.** None — nothing is synthesized at either spelling, so there is no
term for a brick to reproduce and no value guard to write; `#synth` times out at
20000 and the fix is the explicit proof `Algebra.IsAlgebraic.of_finite _ _`.

**Guard.** The positive form is a live `example` in
[`spec/InstanceFriction.lean`](spec/InstanceFriction.lean) and elaborates at the
default `synthInstance` budget; the naive `inferInstance` form is kept as a
comment there with its exact failure.

### IF-002 — applying a set-membership constructor over a `Subgroup` coercion

**Where.** `FLTForHuman/ModularCurve/JqIntegralRatios.lean`, the
`jqModC_mem_intFormRatiosC` proof (the T22 port of the pin's
`S_ModularCurve_jqModC_mem_intFormRatiosC.lean`).

**Goal.** Build `jqModC K ∈ intFormRatiosC K Γ` by applying the named constructor
`mem_intFormRatiosC` to the five witnesses (`e4cube Γ`, `delta Γ`, …).

**Symptom.** Elaboration does not terminate within a 300 s wall bound; the module
build times out. The *statement* is instant, and so is the pin's anonymous
constructor — only the named-constructor application is the hog.

**Cause.** The constructor's expected type mentions
`ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k`; applying it forces unification of
the `Subgroup`/`mapGL` coercion and of the implicit weight `k` against the
witnesses, and that defeq search blows up. The anonymous constructor elaborates the
same term with the expected type already fixed by `intFormRatiosC K Γ`.

**Fix.** Use the anonymous constructor (the pin's own form) in the headline; keep
`mem_intFormRatiosC` public as the vocabulary it is (the checker diffes it against
`Def_ModularCurve_X1.lean`). If a future consumer needs the named form, supply the
implicits explicitly (`mem_intFormRatiosC (K := K) (Γ := Γ) (k := 12) …`).

**Guard.** The headline's own module build is the guard — it is the timing signal,
not a compile signal: the naive form does not fail, it fails to finish. A
`build_ladder.py --friction` run (see below) over
`FLTForHuman.ModularCurve.JqIntegralRatios` is the mechanical check; the harness
records the fixed form.

### IF-003 — an instance keyed on a semireducible `def` (`WeierstrassCurve.baseChange`)

**Where.** `FLTForHuman/WeierstrassCurve/Isogeny/TwoCurveDescent.lean`, the two-curve base-change
engine boundary (`section TwoCurveBcIota`, and `gateDescent_of_descent`).

**Goal.** `(E₀⁄(↥K₀)).IsElliptic` — and its twins `(E₀'⁄(↥K₀))`, `(E₀⁄K)`, `(E₀'⁄K)` — for
`E₀ : WeierstrassCurve K₀`, `K₀ : IntermediateField ℚ K`, from the ambient `[E₀.IsElliptic]`.

**Symptom.** Not a timeout first: `inferInstance` **fails** —
`failed to synthesize instance of type class (E⁄R).IsElliptic` — at the default 20000 *and* at
`synthInstance.maxHeartbeats 3200000`, so the budget is not the lever. The downstream symptom is
the block of `whnf`/`tactic execution` timeouts at the engine call sites
(`TwoCurveDescent.lean:842`, `:850`, `:853`, `:1148`–`:1151`).

**Cause.** mathlib supplies `instance : (W.map f).IsElliptic` (`Weierstrass.lean:456`). The port
writes the curve as `E⁄R`, i.e. `WeierstrassCurve.baseChange E R`, which is a **semireducible
`def`**; instance search runs at reducible transparency and cannot unfold it, so the instance's
head `W.map f` never matches `baseChange E R`. The asymmetry is easy to miss because
`WeierstrassCurve.Affine.baseChange` *is* an `abbrev` (reducible), so the same `W⁄R` notation is
fine on an `Affine` — which is exactly why the same trap keeps reappearing in different spots.

**Fix.** State the instance at the `⁄` spelling and prove it by naming the `map` spelling, which
elaborates at *default* transparency:

```lean
private instance twoCurveBcE₀K₀_isElliptic : (E₀⁄(↥K₀)).IsElliptic :=
  inferInstanceAs ((E₀.map (algebraMap (↥K₀) (↥K₀))).IsElliptic)
```

This is the pin's `scoped instance kw_surgehgf4_cfe_instE₀'K₀` / `…_instE₀'K`
(`S_:3566–3568`), which the port had dropped; four such bridges fix the region.

**Captured term.** `#synth (E₀.map (algebraMap (↥K₀) (↥K₀))).IsElliptic` prints
`instIsEllipticMap E₀ (algebraMap (↥K₀) (↥K₀))`; the goal at its own spelling,
`#synth (E₀⁄(↥K₀)).IsElliptic`, prints `failed to synthesize (E₀⁄(↥K₀)).IsElliptic`
— at 20000 and at 3200000 alike. `IsElliptic` is a `Prop`, so the bridge needs no
`rfl` value guard: any two proofs of it are defeq, and `inferInstanceAs` already
checks the one it is given.

**Guard.** `IF-003` in [`spec/InstanceFriction.lean`](spec/InstanceFriction.lean): the bridge form
compiles at the default budget; the naive `inferInstance` form is kept as a comment with its exact
failure text.

**Resolved (D-6 landed, 2026-10-06).** The same set then met the *generalisation*: the kernel-
transport seam (`KwD5BetweenCurvesKerTransportAlongEmbed`) carries the gate instances as
**arguments** (`[GenusOnePlaceGate (E₀⁄F₂).toAffine]`, …), and the caller's are keyed on
`E₀.map (algebraMap K₀ K)` while the seam wants `(E₀⁄K)`. Two extra rules fell out, both recorded
in the playbook §6 recipe: (i) the bridge must be `letI`, not `haveI` — `letI` inlines the value,
so the seam's instance arguments become literally the caller's terms, where `haveI` leaves a
distinct fvar and the check fails with "synthesized type class instance is not definitionally
equal"; and (ii) to discharge a `∀ [DecidableEq …]` block against a local `Classical.decEq`
instance, use the pin's `subst` (`Subsingleton.elim` + `subst`) — proof irrelevance is only
*propositional*, and `clear` is impossible once an earlier `let` depends on the instance.


### IF-004 — the `HahnSeries` algebra diamond again, in a *proof*: a local `let`-bound `Algebra K (LaurentSeries L)` is defeq to the composite, `powerSeriesAlgebra` is not

**Where.** `FLTForHuman/ModularCurve/ModularPolynomialCoset.lean`, order C's `solution` (the pin is
`P2M/Sol/S_…_separable_map_ratFunc_of_natCast_ne_zero.lean`; the row is
`ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero`, RS3 order C).

**The seam.** The pin needs a *specific* spelling of the `K`-algebra on `E := LaurentSeries
(AlgebraicClosure K)`: it writes
`letI : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra` and then proves the
transfer along the transcendental generator `x = qExpand L N (jqModC L)`. Without that pin
`algebraMap K E` elaborates at `HahnSeries.powerSeriesAlgebra`, which is a *different* (though
mathematically equal) structure, and the last step

```lean
  rw [Polynomial.aeval_def] at hp
  convert hp using 2
```

fails with "Tactic `rfl` failed: The left-hand side `(algebraMap L (LaurentSeries L)).comp
(algebraMap K L)` is not definitionally equal to the right-hand side `algebraMap K E`".

**Why `letI` is not available.** `linter.style.haveILetI` (on by default, and the port's gate is
zero warnings) rejects `haveI`/`letI` whose main goal is a proposition.

**The rule.** Use a plain `let`: Lean 4 registers local instances from `have`/`let`, and a
`let`-bound instance is zeta-reduced by `whnf`, so it *is* definitionally equal to the composite
(this is the opposite direction of the note above: `letI`'s *inlining* was what an earlier seam
needed, and `let`'s *local definition* is what this one needs — both have the property that the
instance argument of the elaborated term reduces to the caller's term). Diagnostics: with `letI`
the pin's trailing `try with_reducible_and_instances rfl` is exercised; with `let` it is dead, and
Lean says so (`linter.unusedTactic` + `linter.unreachableTactic` on that exact tail) — that pair is
the signal that the local instance was found and unfolded, not that the proof is broken.

**Guard.** `spec/ModularCurveReady3ZoneC.lean` consumes the row's public conclusion (its error
count is the zone's gate) and the module's own `lake build` is green at the port's caps; the
headline's axioms are `[propext, Classical.choice, Quot.sound]`.


### IF-005 — `Module.Free` at a *concrete* `IntermediateField.adjoin` term: instance paths are data, and one import short

Order B's pin carries `set_option synthInstance.maxHeartbeats 1600000` at module level, which the
work order forbids transcribing. The one search that needs it is

```lean
  have hfin : FiniteDimensional ((AlgebraicClosure ℚ)⟮y⟯)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := by
    apply Module.finite_of_finrank_pos
    rw [hfull]; exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
```

`Module.finite_of_finrank_pos` needs `[Module.Free ↥E FF]`. Measured, in this order:

1. `Module.Free` over a division ring is `Module.Free.of_divisionRing`
   (`Mathlib/LinearAlgebra/Basis/VectorSpace.lean`), **not in this module's closure**; before the
   import the search *fails outright* (it has no constructor for a vector space), after it the same
   goal times out at the default `synthInstance.maxHeartbeats = 20000`.
2. Supplying the chain by hand does not work, and the reason is worth recording: `Field ↥E`,
   `Algebra ↥E FF`, `Module ↥E FF`, `DivisionRing ↥E`, `StrongRankCondition ↥E`,
   `IsTorsionFree ↥E FF` all synthesize quickly at the concrete `E`, but
   `Module.Free.of_divisionRing _ _` is *rejected* — "has type `@Module.Free ?m ?m' DivisionRing.toRing.toSemiring …`
   but is expected to have type `@Module.Free ↥E FF (SubsemiringClass.toCommSemiring ↥E).toSemiring …`".
   The two `Semiring` structures on `↥E` are propositionally but not definitionally equal, and
   `Module.Free`'s instance arguments are **data**, so there is no way to hand the instance over at
   this spelling.
3. The fix is to state the *fact* at a variable intermediate field, where the instance is not a
   concrete `adjoin` term and the search is instant (measured: silent at 20000):

```lean
private theorem finiteDimensional_of_finrank_pos_intermediate {L M : Type*} [Field L] [Field M]
    [Algebra L M] (E : IntermediateField L M) (h : 0 < Module.finrank E M) :
    FiniteDimensional E M := by
  apply Module.finite_of_finrank_pos
  exact h
```

A `have hfin : FiniteDimensional ↥(adjoin …) FF := finiteDimensional_of_finrank_pos_intermediate _ …`
in the local context *is* then found by instance search at the call sites
(`finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin`,
`isCurveOver_of_transcendental_of_perfectField`) — verified by an `inferInstance` probe.

**Consequence for pricing.** A pin `synthInstance.maxHeartbeats` bump is not automatically "add an
explicit instance": when the target is a concrete `adjoin`/`Submodule`/`map` term, the explicit
instance often cannot be *stated* (instance-path mismatch). Price the general-level restatement
instead — it is 5 lines and, here, removed the pin's 6.4M `maxHeartbeats` on `main_K` entirely
(`main_K` elaborates whole inside the 200k edit loop).

**Guard.** `spec/ModularCurveReady3ZoneB.lean` (0 errors) and the module's own `lake build`
(green); the headline's axioms are `[propext, Classical.choice, Quot.sound]`.

## Backlog (known heavy spots, not yet written up)

Pointers, not entries — each needs a current measurement before it gets a row:

* the ~30-instance `LevelFraction` block (`IsDedekindDomain`, `CharZero`,
  `FiniteDimensional`, …), profiled in
  [../notes/lean-build-cost.md](../notes/lean-build-cost.md); the `C1_carrier`
  sub-block was applied, several candidates reverted because same-file proofs use
  them.
* the `scoped instance` candidates listed by `build_ladder.py --audit`
  (`delete → build → keep-or-revert`).
