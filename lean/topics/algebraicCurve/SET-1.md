# SET 1 — the `AlgebraicCurve` vocabulary, interface and transport (AC0, T1–T4)

**Status (2026-09-22): work orders written, not started.** This is the run brief for
the **first** of the two coding sets of the effort planned in
[PORTING-AC.md](../../PORTING-AC.md). It authorizes exactly five topics:

| order | work order | object | ≈ port |
|---|---|---|---|
| 1 | [TOPIC-ac0-vocabulary.md](TOPIC-ac0-vocabulary.md) | the `AlgebraicCurve/Defs/` vocabulary | 1,900–2,200 |
| 2 | [TOPIC-t1-ord-interface.md](TOPIC-t1-ord-interface.md) | the `Place` ord/valuation interface (19 nodes) | 520–580 |
| 3 | [TOPIC-t2-fibre-dictionary.md](TOPIC-t2-fibre-dictionary.md) | the promoted fibre dictionary, `fiberOver`, `le_finrank`, `inertiaDeg_pos` (3 nodes) | 500–570 |
| 4 | [TOPIC-t3-galois-ramification.md](TOPIC-t3-galois-ramification.md) | Galois ramification/inertia (7 nodes) | 210–240 |
| 5 | [TOPIC-t4-transport.md](TOPIC-t4-transport.md) | along-map transport + `Pic0` descent (16 nodes) | 160–190 |

**Do not start T5–T9.** They are SET 2, and their work orders will be written (and
corrected against what SET 1 actually produced) only after SET 1 is reviewed. T7 is
the capstone and is reserved for the human reviewer. If a SET-1 topic turns out to
need a SET-2 declaration, prove a local `private` helper instead and record it in
the log — do not open the SET-2 module.

## 0. The one-paragraph orientation

`math/009`'s Weil-exchange reduction needs a *generic* curve layer with no schemes:
places as valuation subrings, divisors, `Pic0`, push/pull, and the exchange
identity `pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`. FLT
proves all of it in its `AlgebraicCurve.*` layer; the cone on the path of
`ModularCurve.heckeOperatorsCommuteBar` is **63 `AlgebraicCurve.*` theorem nodes
(5,210 raw `S_` lines) plus 2 generic group-theory nodes (213 raw)**, spelled over
**6 definition modules (2,823 lines) plus two out-of-table declarations**
(`RationalFunctionField.placeInfty` in `Def_AlgebraicCurve_RatFuncPlaceInfty.lean`,
`Place.ord_algebraMap` in `Def_AlgebraicCurve_ConstantReduction.lean:57`). SET 1
writes the vocabulary, the four high-indegree `ord` lemmas, the fibre-centre
dictionary and the transport layer; SET 2 (T5, T6, T8, T9) proves the bifibre
count, the local exchange and the principal-divisors route; the human does T7.

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3`, cloned locally at
  `~/proj/fermats-last-theorem`. Read it directly with the read tool; never copy
  its `P2M/` scaffolding.
- For node *N*, the statement is in `Theorems/Thm_<dotted name with `_`>.lean`
  (the wrapper) and the proof is in `P2M/Sol/S_<dotted name with `_`>.lean`. The
  wrapper is the statement authority: **take the binders from the wrapper**, use
  the `S_` file only for the proof body (playbook §7.4 — the checker is textual).
- Definition modules are `Definitions/Def_AlgebraicCurve_*.lean`. Their
  declarations have no `Thm_` wrapper; the checker diffs them against the
  `Definitions/` file directly.
- Ignore, but do not be confused by, `P2M.Dup.AlgebraicCurve.*` aliases: a handful
  of wrappers are declared under that alias (e.g. `Place.mem_iff_ord_nonneg`,
  `Place.ord_algebraMap`, `Place.isEquiv_adicValuation_ofHeightOneSpectrum`,
  `RationalFunctionField.deg_ofHeightOneSpectrum`). Match the **unaliased**
  `AlgebraicCurve.*` name; the declaration's last-name component is what the
  checker matches, and the statement is the wrapper's.
- mathlib is the pinned `v4.34.0` of `lean/lake-manifest.json`.

## 2. Build discipline — read this first

Every build is bounded and a blow-up is quarantined, not waited on. mathlib is
already built in this checkout: a green `lake env lean <module>` on a module of
port size is **~4 s**, `lake build <module>` with dependencies cached **~2–5 s**,
and the full `lake build` at the baseline is 3,874 jobs / green.

**This lakefile sets `maxHeartbeats` to 4,000,000 globally** (`lean/lakefile.lean`),
so — unlike a stock project — a deterministic `whnf`/defeq blow-up does **not**
error at ~20 s; it can run for minutes. The `timeout` bound is therefore
load-bearing:

- Run every build under a bound: `timeout 60 lake env lean <file>` and
  `timeout 120 lake build <module>`. **Non-return at 60 s is a blow-up**, not a
  slow build.
- On a timeout, quarantine immediately: comment the declaration out and bisect, or
  reproduce in the gitignored `lean/Scratch.lean`. Do not re-run the same file
  hoping for a different result.
- **Never add a local `set_option maxHeartbeats`, and never raise the lakefile's.**
  The usual cause is a `FunLike`-quantified lemma instantiated at a bare function
  type (then `DFunLike.coe` unfolds without bound) — restate the lemma over the
  concrete function instead. The worked example is in
  [`../phiGenSplitting/TOPIC-r1-kernel.md`](../phiGenSplitting/TOPIC-r1-kernel.md):
  `UpperHalfPlane.qExpansion_coeff_unique` cost 5.1M `DFunLike.coe` reductions at
  `ℍ → ℂ`, and the fix was to restate its content over the concrete function, not
  to raise the cap.
- `Scratch.lean` is gitignored. Use it for `#check` probes and for
  type-hunting (`lake env lean Scratch.lean`, ~3 s).
- Do **not** `import Mathlib` anywhere. Keep every import specific; the whole
  layer is meant to sit on `Mathlib.RingTheory.Valuation.*`,
  `Mathlib.RingTheory.DedekindDomain.*`, `Mathlib.FieldTheory.*` and
  `Mathlib.FieldTheory.RatFunc.*`.

Other standing traps, from [porting-playbook.md](../../porting-playbook.md) §3:

- **The rewrite-search gap (§3.5).** mathlib's generic `map_*`/`comp_*` often will
  not fire under `rw`/`simp` when an implicit instance is unresolved. Write a
  monomorphic helper proved by `exact` and rewrite through it.
- **`rw`/`simp_rw` do not unfold `abbrev`s (§3.7).** Use `change` or
  `simp only [name]`.
- **Do not state a goal against an abstract `*_aux` lemma (§3.4).** That is the
  usual source of a multi-minute defeq check.
- **Watch the build clock.** A jump from seconds to minutes is a defeq blowup; find
  the `exact`/`convert`.

## 3. Layout, namespace, and the two hard conventions

```text
lean/FLTForHuman/AlgebraicCurve/
  Defs/
    Place.lean            -- AC0 + T1's ord interface
    Divisor.lean          -- AC0
    PushPull.lean         -- AC0
    PlacesOverDVR.lean    -- AC0
    Correspondence.lean   -- AC0
    SemilinearAut.lean    -- AC0 + T3's action lemmas
    RatFuncPlaces.lean    -- AC0 + T8's P¹ vocabulary
    PlaceDictionary.lean  -- T2 (the promoted fibre dictionary)
  WeilExchange/
    OrdInterface.lean     -- T1
    FiberOverCount.lean   -- T2
    GaloisRamification.lean -- T3
    Transport.lean        -- T4 (also the shared prelude T5/T6/T7 import)
```

The **namespace is `AlgebraicCurve`** (with the pin's existing sub-namespaces
`Place`, `Divisor`, `Pic0`, `RationalFunctionField`, `SemilinearAut`), matching
FLT so declaration names line up. The **path** is
`FLTForHuman.AlgebraicCurve.WeilExchange.Transport` while the declarations stay
`AlgebraicCurve.*`: directory names the theory, namespace names the mathematics.

Two conventions that are non-negotiable here:

- **`autoImplicit` is false project-wide.** Bind every variable explicitly (the
  pin does; transcribe its binders literally).
- **Keep the pin's `letI`/`haveI` walls and its `@[reducible]`/`abbrev`
  attributes literal.** They are load-bearing for instance search in T2/T3/T4/T6;
  see the risk table in [PORTING-AC.md](../../PORTING-AC.md) §8. The
  `linter.style.haveILetI` warnings that follow are disabled at module level in
  the pin's own cone-algebra files; do the same rather than rewriting the
  instances.

### 3.1 v4.34.0 API drift, measured (manager's recon, 2026-09-22)

Three findings that change the work orders; they were confirmed with `#check`
against the pinned mathlib:

- **Never import `Mathlib.NumberTheory.RamificationInertia.Basic`.** That module is
  itself deprecated (it prints an import warning that cannot be silenced by
  `set_option`, because options cannot precede imports), and it is the only home of
  the old `Ideal.sum_ramification_inertia`. Import
  `Mathlib.NumberTheory.RamificationInertia.Inertia` and
  `Mathlib.NumberTheory.RamificationInertia.Ramification` for the primed constants,
  and `Mathlib.RingTheory.RamificationInertia.Basic` for the new sum theorem.
- **The pin's deprecated `Ideal` names, and their actual replacements:**

  | pin | v4.34 | warning? |
  |---|---|---|
  | `Ideal.ramificationIdx'` | same | no |
  | `Ideal.ramificationIdx_spec` | `Ideal.ramificationIdx'_spec` | yes (old name) |
  | `Ideal.inertiaDeg'` | `Ideal.inertiaDeg` (new shape `q.inertiaDeg R`) | yes |
  | `Ideal.inertiaDeg_algebraMap` | `Ideal.inertiaDeg'_algebraMap` | yes (old name) |
  | `Ideal.inertiaDeg'_pos` | `Ideal.inertiaDeg_pos` (new shape `q.inertiaDeg R`) | yes |
  | `Ideal.sum_ramification_inertia` (Finset/`finrank K L`) | `Ideal.sum_ramification_inertia_eq_finrank` (`∑ q : p.primesOver S`, `finrank R S`) | yes, and its module is deprecated |

  So `PORTING-AC.md` §8 risk 4's "write against the new API from the first
  declaration" is **not a drop-in rename**: the new `Ideal.inertiaDeg` and the new
  sum theorem changed argument order and statement shape. **Statements stay the
  pin's** (so `spec/check_flt_statements.py` remains an exact textual diff); the
  affected modules carry `set_option linter.deprecated false` with a one-line
  reason, and the *proofs* are migrated to the new lemmas. This decision and its
  evidence go in `logs/ac-port.md`; the follow-up (migrate the statements and let
  the checker normalise the rename) is a recorded residual item.
- **`Place.adicValuation_isRankOneDiscrete` is mathlib's instance application**
  `IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F` — there is no
  `HeightOneSpectrum.valuation_isRankOneDiscrete`. Similarly
  `MulAction.index_stabilizer` / `MulAction.index_stabilizer_of_transitive` (not
  root-level), and `PerfectField.ofCharZero` (T9).

## 4. Per-topic deliverables

Each topic's work order contains its own scouted inventory (every node with its
pin file, raw/content size, external indegree and verbatim statement), its route
notes, its budget and its definition of done. The shared definition of done for
every topic in this run:

1. `timeout 300 lake build` is green, **0 warnings, no `sorry`** anywhere in
   `FLTForHuman/`.
2. `timeout 120 lake env lean spec/AlgebraicCurveConsumer.lean` reports the
   zone's expected error count, and the zone's wire test is a real (not
   `sorry`-terminated) composition.
3. `python3 spec/check_flt_statements.py` reports **0 mismatched, 0 missing**, with
   the topic's wrappers (and definition files where needed) appended to `SOURCES`
   and any port-authored declaration named in the topic's work order added to
   `OWN_PROOFS` with a reason.
4. `#print axioms` on the topic's headline (and on `hasPrincipalDivisors*` once
   T9 lands) is `[propext, Classical.choice, Quot.sound]`.
5. `logs/ac-port.md` gains the topic's measured section (see §6 below).
6. `README.md`'s module table and the `PORTING-AC.md` status line are updated.

## 5. Instrumentation this run must build (AC0 and T1 own it)

- **`spec/AlgebraicCurveConsumer.lean`** — the deliverable measure, outside every
  library (nothing globs `spec/`). Model it on
  [`spec/ModularCurveConsumer.lean`](../../spec/ModularCurveConsumer.lean). Zones:
  - **A `[vocab]`** (after AC0): `Place`, `Divisor`, `Pic0` are inhabited; the
    `Place` ↔ `ValuationSubring` ↔ `HeightOneSpectrum` bridge typechecks; `#check`
    against the pinned signatures of `Place`, `Place.ord`, `Place.deg`,
    `Divisor.degree`, `Divisor.IsPrincipal`, `HasPrincipalDivisors`, `Pic0.mk`,
    `Place.ofHeightOneSpectrum`, `Place.fiberOver`.
  - **B `[interface]`** (after T1): T1's four high-indegree leaves at their pinned
    statements, plus a cross-module wire test — a concrete `ord`/degree
    computation that consumes a `Place` lemma from `Defs/Place.lean` and a
    `Divisor` lemma from `Defs/Divisor.lean`.
  - **C `[dictionary]`** (after T2): the promoted dictionary's
    `ramificationIndex_eq_ramificationIdx_fiberCenter` and
    `inertiaDeg_eq_inertiaDeg_fiberCenter` at their pin statements, plus
    `sum_ramificationIndex_mul_inertiaDeg_le_finrank` applied to a concrete
    (possibly abstract) separable extension; T3/T4 extend it with the Galois and
    transport checks.
  - **D `[exchange]`** (after T4, closed by the human's T7) and **E `[principal]`**
    (after T9) are SET 2's and the human's. Leave the file compiling at 0 errors
    with only deliberately documented `sorry`s.
- **`spec/check_flt_statements.py`** — the `norm` function currently strips only
  `ModularCurve.`; AC0 must also strip `AlgebraicCurve.`. Append the topic's
  `Theorems/Thm_AlgebraicCurve_*.lean` wrappers to `SOURCES`, and for the
  definition modules append `Definitions/Def_AlgebraicCurve_*.lean` (the checker
  matches on the last name component, so the definition files must be listed
  **after** the wrappers that share a last name, and the AC wrappers after the
  existing `ModularCurve` sources). Beware last-name collisions across the AC
  namespaces (`restrict`, `mk`, `deg`, `degree`, `ord`, `ext` are the obvious
  ones): when a collision makes the checker disagree, add the more specific
  wrapper file and re-run; do not exempt the declaration. Record every
  `OWN_PROOFS` addition with its one-line reason, as the FFG list does.
- **`logs/ac-port.md`** — the measured record, modelled on
  [`logs/ffg-port.md`](../../logs/ffg-port.md): a status header, a §0 topic table
  (`layer | scope | status | measure`), a per-topic section with `goal rounds`,
  `tool calls`, `wall clock`, `declarations`, `lines written`, `build` result, and
  a table `module | lines | decls | FLT source`. Add a **friction log** section and
  keep it current *while* the friction happens (playbook §3.10): every rename,
  instance-wall and non-proving tactic belongs there.

## 6. What to report back

Report concise, measured facts, not prose. For the run as a whole:

1. The per-topic table above, filled in: lines written, declarations, goal rounds,
   build result, consumer zone errors, checker line (`N identical, 0 mismatched,
   0 missing`).
2. **The measured `Def_` drop list**: per definition module, the declarations
   actually ported and the ones dropped, each dropped name with its `grep -c`
   count in the 65-node corpus (recipe in
   [PORTING-AC.md](../../PORTING-AC.md) §9.1). "Not needed" is not evidence; a
   count is.
3. **Whether the named shape risks materialized** — for T1 the `exp`/`log` `rfl`
   identifications and the deprecated `Ideal` aliases; for T2 the `letI`/`haveI`
   walls and the `IsFractionRing` instance; for T4 the `algebraAlong` unfolding.
   Say which did *not*, too: recorded non-events are information.
4. **Any statement that could not be matched**, quoted, rather than weakened. A
   wrong statement is maximally expensive; a wrong proof is cheap.
5. The **interface table** for T1: declaration → external indegree → port module,
   re-derived rather than copied.
6. The exact commands you used for the final verification, so the review can
   re-run them.

## 7. Constraints

- **Do not `git commit` or `git push`.** Only the human commits this repository;
  the working tree is the hand-off.
- Do not edit `PORTING-AC.md`; report deviations from it and the human will fold
  them in. Do edit `README.md`'s status table and `logs/ac-port.md`.
- Do not cross-reference an untracked local file from a tracked one: everything
  under `lean/topics/`, `lean/logs/`, `lean/spec/` and `lean/FLTForHuman/` is
  tracked except `lean/Scratch*.lean`. `tools/` is gitignored and must not be
  cited by path from tracked files.
- FLT citations in tracked files use the public raw URLs pinned to `aa2d8b3` (see
  `AGENTS.md`), not `~/proj/...` paths.
