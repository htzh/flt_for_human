# Typeclass-instance friction register

The **instances and instance-search goals** in this port that cost real elapsed
time, keep costing it on every elaboration, and are the kind of thing that
silently accumulates into a build-time hog. Kept apart from:

* [porting-playbook.md](porting-playbook.md) §6 — which states the *fixes* (this
  register says where a fix was needed and whether it holds);
* [../notes/lean-build-cost.md](../notes/lean-build-cost.md) — which holds the
  *measurement method* (`--profile`, `--audit`, heartbeat semantics).

The list is expected to grow, so every entry below must be **re-runnable**: the
live form lives in [`spec/InstanceFriction.lean`](spec/InstanceFriction.lean)
(next to the consumers, deliberately outside every library, so it can never slow
or break the verified build).

## What qualifies

Record an entry when *instance search or an instance declaration* is the cost:

* a `synthInstance` timeout (`deterministic timeout at typeclass, maximum number
  of heartbeats …`) — record the budget;
* a `set_option synthInstance.maxHeartbeats …` bump kept in the tree;
* an explicit `haveI`/`letI` wall added where instance search would otherwise run;
* an instance declaration that `build_ladder.py --profile` puts near the top of a
  module's cost, or that `--audit` flags as a `scoped instance` candidate.

An ordinary `failed to synthesize` message is a **missing** instance, not
friction: that is a gap in the library, not a hog. Do not record it here.

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

**budget** is the cost proxy: the `synthInstance.maxHeartbeats` value at which the
naive form fails (or the measured seconds, for an instance declaration). Re-measure
both when the naive form starts working anyway (then the entry can be retired) and
when a mathlib bump makes it worse.

## Re-measure cadence

The register is pinned to mathlib `v4.34.0`. After a mathlib bump, and after any
change to an entry's home module, re-run the harness:

```
cd lean
lake env lean spec/InstanceFriction.lean 2>&1 | grep -c error     # want 0
```

Then update each row's **budget** and **status**. `build_ladder.py --profile` on
the home module is the second reading for instance *declarations*.

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

## Backlog (known heavy spots, not yet written up)

Pointers, not entries — each needs a current measurement before it gets a row:

* the ~30-instance `LevelFraction` block (`IsDedekindDomain`, `CharZero`,
  `FiniteDimensional`, …), profiled in
  [../notes/lean-build-cost.md](../notes/lean-build-cost.md); the `C1_carrier`
  sub-block was applied, several candidates reverted because same-file proofs use
  them.
* the `scoped instance` candidates listed by `build_ladder.py --audit`
  (`delete → build → keep-or-revert`).
