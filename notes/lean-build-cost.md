# Lean build cost, and the ladder that contains it

Why the 2026-09 porting sessions spent most of their wall time on `lake build`
even though a full build almost never failed, what the cost actually is, and the
build ladder that replaces "rebuild the world after every edit". The reusable
policy is [../lean/porting-playbook.md](../lean/porting-playbook.md) §3.5; this
note is the measurement behind it.

All numbers are from this machine, mathlib `v4.34.0` prebuilt, on the
`lean/FLTForHuman` + `Reserve` trees (~189 modules, ~82k lines). Tools named in
`tools/deps/` live in the unpublished tool tree; the recipes here are
self-contained.

## 1. The three different things people call "a build"

1. **Elaborate a file** — `lake env lean <file>`. Lean parses, elaborates and
   kernel-checks the file against the `.olean`s of its imports. It writes *no*
   `.olean` for the file itself (confirmed by `.olean` mtime), so it invalidates
   nothing. It re-runs the file's own proofs every time.
2. **Build a module** — `lake build <module>`. Writes the module's `.olean` and
   `.trace`, and builds the module's **dependencies** (already cached). It does
   **not** build its dependents.
3. **Build the tree** — `lake build` (no target). Builds every default target;
   after an edit this re-elaborates every **stale dependent**, i.e. the transitive
   dependents of every edited module. That set is the *cascade*.

Lake decides staleness from a module's `.trace`: the source hash plus the traces
of its dependencies. Any edit — including a proof-only edit that does not change a
statement — changes the source hash, so every dependent is rebuilt. Lean has no
"interface-only" `.olean` separation to exploit; the only lever is *how often* the
cascade is paid.

## 2. The measurements

Per-file elaboration (`lake env lean`), against cached imports:

| module | lines | wall |
|---|---|---|
| `WeightOne/LevelFraction` | 2,573 | **78 s** |
| `WeightOne/Gamma1Basis` | 3,863 | 34 s |
| `WeightOne/FrickeFunction` | 2,926 | 36 s |
| `WeightOne/LevelN` | 1,694 | 18 s |
| `WeightOne/LevelOneHauptmodul` | 2,023 | 11 s |
| `WeightOne/Defs/PeriodPair` (small) | ~250 | 20 s |

Whole-tree timings:

| command | jobs | wall |
|---|---|---|
| `lake build` fully cached, no edits | 4,653 | **3.4 s** |
| `lake build <WeightOne capstone>` fully cached | 4,112 | 9.3 s |
| `lake build <module>` after touching that module only | — | 6–10 s |
| cascade after editing `WeightOne.Basic` | — | **4 m 47 s** (430 s CPU) |
| cascade per WeightOne rectification wave (recorded) | — | **2 m 15 s – 6 m 53 s** |

So the fixed cost of invoking Lake is seconds. The minutes are the cascade's
sum of per-file elaborations. Editing `Basic` reaches 13 dependents / 19k lines,
which is where the ~4m47s comes from.

**Contention is a separate failure, and looks identical on the wall clock.** The
`ModularCurve` log records a 4 m 34 s stall with **0.5 s user CPU** while another
agent built the same tree. High user CPU + timeout is real compute (or a
heartbeat blow-up); near-zero CPU is lock contention. Every bounded build should
be timed with `time` (or `/usr/bin/time -v`) so the two are told apart.

**A failing check can be slower than a succeeding one, and can exceed every bound
above (measured 2026-10-06, set D-6).** `WeierstrassCurve/Isogeny/TwoCurveDescent.lean`
(1,231 lines, importing `IntermediateField` + `KernelBaseChange`) was checked with
`lake env lean` three times on three successive revisions, while its two-curve region
mis-scoped three `haveI`s and left one universe level unbound:

| revision | wall | user | sys | outcome |
|---|---:|---:|---:|---|
| `tmp/w2.log` | 254 s | 239 s | 26 s | 1 error (typeclass timeout at the *default* 20,000) |
| `tmp/w3.log` | 438 s | 957 s | 32 s | 1 error (`whnf` at 4,000,000) |
| `tmp/w4.log` | **1,119 s** | 2,361 s | 130 s | 17 error sites: 10 heartbeat timeouts, 2 type mismatches, 1 missing instance, 1 unbound universe |

Two things to take from it. First, the wall time is **not** bounded by the per-file
figures in the table above: 18.6 minutes for one file, with **`USER ≈ 2 × WALL`** —
Lean elaborates in parallel, and a `whnf`/`isDefEq` blow-up burns *hearts*, i.e. CPU, so
the cost grows with the very unification work that is failing. A module in this state
breaks the ladder's tier-0 assumption (`timeout 60`): the check cannot be bounded by
60 or 90 s and still complete, so any iteration on it costs ~19 minutes. Second, that is
the argument for playbook §3.5 rule 1 with teeth — **do not iterate on such a module;
isolate the declaration in `Scratch.lean` and iterate there**, and see §8 for the levers
once the blame is placed. The per-file figures above remain right for modules whose
proofs elaborate; treat them as a *lower* bound when instance search or `whnf` is in play.

## 3. Why the big modules are slow (the root cause)

Profiling `LevelFraction` (`lake env lean -Dprofiler=true`) gives 332 timed
events summing to ~82 s. The cumulative breakdown:

| category | cumulative |
|---|---|
| typeclass inference | **92.4 s** |
| type checking | 15.6 s |
| tactic execution | 11.5 s |
| elaboration | 6.2 s |
| import | 4.1 s |

It is death by typeclass search: repeated `CommRing`, `Algebra`, `IsDomain`,
`IsPrincipalIdealRing`, `GroupWithZero` instance searches of 0.1–2 s each, plus
many ~0.5 s kernel `type checking` blocks. There is no single 60-second
declaration to bisect; the module is uniformly heavy. This is the same family as
the two blow-up failure modes already documented in the playbook: a `FunLike`
lemma instantiated at a bare function type (`DFunLike.coe` unfolding), and a
kernel `Subtype.val` defeq between two concrete `IntermediateField.adjoin`
carriers (fixed once by a generic `ifRE (S T) : ↥S ≃+* ↥T` coercion, 3 m 09 s →
16 s).

**The global heartbeat cap hides this.** `lean/lakefile.lean` sets
`maxHeartbeats := 4_000_000` for the whole package — 20× Lean's 200,000 default —
and the WeightOne modules deliberately omit the pin's local bumps, relying on it.
Consequences:

- the playbook's claim that a blow-up "errors in ~15–20 s" does **not** hold in
  this project; a non-terminating elaboration may run ~20× longer before erroring.
  The wall-clock `timeout` is the only real protection;
- long successful elaborations are not made longer by a high cap (heartbeats are
  a limit, not a budget), but the declarations that *need* >200k are exactly the
  slow ones, and the cap makes them succeed rather than fail loudly.

The durable fix for build time is therefore the proof-engineering program, not a
wider budget: localize the cap to the declarations that need it (transcribe the
pin's `set_option maxHeartbeats` at that declaration, or restate the lemma so it
does not need it), and remove the concrete-carrier defeqs and bare-function-type
instantiations. Until then, the ladder below stops the same elaborations being
paid repeatedly.

## 4. The waste, named

Three patterns account for the sessions' build time:

1. **`lake build` in the edit loop.** Only `lake build` writes `.olean`s and
   invalidates dependents; `lake env lean` gives the error without the cascade.
   The logs pair every `lake build <module>` (6–10 s) with a full `lake build`.
2. **A wave split across a shared module.** The cascade is the union of the
   edited modules' dependents, so editing the same module in two waves pays its
   cascade twice. The WeightOne W4 width family was split into two waves over the
   same Γ/level modules and paid ~6 m 45 s twice; the modules were
   `Gamma0Integral`, `Gamma0Rationality`, `Gamma1Basis`, `LevelN`.
3. **Concurrent builds on one tree.** They do not compute in parallel; they
   serialize on Lake's lock and cross-invalidate.

## 5. The ladder

| tier | when | command | cost |
|---|---|---|---|
| 0 — edit loop | every edit | `timeout 60 lake env lean <file>` | 4 s small, 11–78 s big; no cascade |
| 1 — module done | file compiles | `timeout 90 lake build <module>` + `python3 spec/check_flt_statements.py` | 6–10 s |
| 2 — wave done | all wave edits in | one `lake build` (or its affected targets) | 2–7 min |
| 3 — milestone | definition of done | full build + consumers + `#print axioms` | the tier-2 cost |

Rules:

1. **Never `lake build` in the edit loop.** The loop wants an error, not a
   `.olean`. For a 2,500-line module even the check is 78 s, so iterate on the
   declaration in a gitignored `Scratch.lean` that imports the module.
2. **A wave edits each module once**, and its sub-tasks are merged if they share
   a module.
3. **Price the cascade before triggering it**: count the transitive dependents
   and their lines.
4. **Serialize every `lake build`** with `flock`, and time it so contention is
   named rather than bisected.

The affected target set to name in tier 2 is the **maximal elements** of the
edited modules plus their dependents, under the import relation: building those
builds every affected module as a dependency. On a clean tree that recompiles the
same modules as a full `lake build` (unrelated modules are cached), so the ladder
saves wall time mainly by *not running it more than once*, and by not recompiling
unrelated modules that another session left stale.

## 6. The tool

`tools/deps/build_ladder.py` makes the ladder mechanical:

```bash
python3 build_ladder.py --selftest
python3 build_ladder.py --edit FLTForHuman/ModularForms/WeightOne/Basic.lean
python3 build_ladder.py --run --tier module --edit <module>
python3 build_ladder.py --run --tier wave   --edit <module> [...]
python3 build_ladder.py --run --tier full
python3 build_ladder.py --waves wave1.txt wave2.txt
```

- `--edit` prints the dependent modules, lines and an order-of-magnitude
  seconds figure. Calibration: `WeightOne.Basic` reports 14 modules / 20,732
  lines ≈ 249 s against the recorded 4 m 47 s; the estimate is `0.012 s/line`.
- `--run` executes the chosen tier through `flock -n` and `timeout`, and prints
  wall and user/sys with a verdict (`green` / `CONTENTION` / real compute).
- `--waves` flags a module listed in two waves and prices the cascade that
  repeats.

## 7. Reproducing the measurements

**`lake env lean` does not inherit the package's `leanOptions`; `lake build` does.**
The lakefile sets `maxHeartbeats := 4_000_000` and `autoImplicit := false`, so a
raw `lake env lean <file>` runs at the default 200,000 cap. On a module that needs
the raised cap this is not a slow check — it is a *wrong* one: `WeightOne.Basic`
fails at 30.7 s with a heartbeat timeout and a cascading `unknown constant`,
while with the options it compiles in 56.1 s. Pass the options explicitly (the
build-cost tool's `--tier check` and `--profile` now do):

```bash
cd lean
OPT="-DmaxHeartbeats=4000000 -DautoImplicit=false"
# per-file elaboration, with the project's options, timed and bounded
for f in FLTForHuman/ModularForms/WeightOne/{Basic,LevelFraction,Gamma1Basis,LevelN}; do
  /usr/bin/time -f "%e s  %U user  $f" timeout 150 lake env lean $OPT "$f.lean"
done
# is the .olean touched?  (it is not)
ls -l --time-style=+%T .lake/build/lib/lean/FLTForHuman/ModularForms/WeightOne/Defs/PeriodPair.olean
lake env lean $OPT FLTForHuman/ModularForms/WeightOne/Defs/PeriodPair.lean
ls -l --time-style=+%T .lake/build/lib/lean/FLTForHuman/ModularForms/WeightOne/Defs/PeriodPair.olean
# cached vs edited cost
timeout 180 lake build            # no-op: ~3 s
```

## 8. Optimizing a heavy unit

Method: per-declaration elaboration times, then the dependency graph.

```bash
cd tools/deps
python3 build_ladder.py --profile FLTForHuman.ModularForms.WeightOne.LevelFraction --top 20
python3 build_ladder.py --audit --scope WeightOne --refresh     # rank anomalies and cascades
```

`--profile` runs `-Dtrace.profiler` and ranks the `[Elab.command]` lines.
`LevelFraction`'s ~80 s is not spread over its 250 declarations; it is
concentrated in about thirty **typeclass instances**, and the top of the list is
the same in `LevelField` (which duplicates the block). The accumulating register of
individual instance-search/timeout cases — each with a re-runnable guard — is
[../lean/instance-friction.md](../lean/instance-friction.md); this note is the
method, that register is the log:

| declaration | LevelFraction | LevelField |
|---|---|---|
| `scoped instance : IsDedekindDomain ↥(levelIntClosure N)` | 10.0 s | 10.0 s |
| `scoped instance : FiniteDimensional ↥(ratJ N) (levelField N)` | 5.5 s | 5.4 s |
| `scoped instance : IsDedekindDomain ↥(polyJ N)` | 3.7 s | 3.9 s |
| `noncomputable scoped instance algebraRatJ` | 2.9 s | 3.4 s |
| `scoped instance grp_smulDistribClass` | 2.7 s | 3.1 s |
| `scoped instance : CharZero ↥(ratJ N)` | 2.7 s | 2.9 s |
| `abbrev levelIntClosure` | 2.1 s | 2.1 s |

The cost is **instance synthesis and defeq over concrete `Subalgebra` /
`IntermediateField` subtype carriers**, not the proofs. Three concrete cuts, all
measured in a scratch copy of `LevelFraction` (control 69.9 s):

| change | wall | delta |
|---|---|---|
| delete the two `IsDedekindDomain` instances + `levelIntClosure` | 59.6 s | **−15%** |
| delete the eight-instance `C1_carrier` block (`IsDomain`, `IsPrincipalIdealRing`, both `IsDedekindDomain`, both `CharZero`, `FiniteDimensional`, `IsSeparable`, `levelIntClosure`) | 51.3 s | **−27%** |
| `set_option backward.isDefEq.respectTransparency.types false` at the top | 69.2 s | none |

The eight-instance `C1_carrier` block was a **true positive and is applied**:
its `scoped instance`s sit in `LevelFraction`'s nested
`WLightS9.S_….WLight` namespace, which no code reaches, and the module builds
green without them. Measured after the change: `lake env lean` **78.5 s → 59.7 s**
(−18.8 s, −24%), and the module's `[Elab.command]` total **98.8 s → 81.6 s**
(261 commands). The checker is unchanged at 2058 identical / 0 mismatched /
0 missing — it never matched these declarations anyway, because its `DECL_RE`
does not accept `scoped`, so removing them is not a demotion.

**The "never-opened namespace" heuristic is a candidate list, not a dead list.**
A `scoped instance` is active *inside its own file/namespace block*, so a
namespace that nothing opens elsewhere does not mean the instance is unused. A
sweep of all 44 candidates across eight modules confirmed this the hard way:
`Basic` (5), `ModularPolynomialIrreducible` (1), `Defs/GammaRational` (3),
`Gamma0Rationality` (1), `Gamma1IntegralBasis` (3), and 26 more in `LevelFraction`
all had to be reverted — the instances were used by proofs in the same file. Only
the `C1_carrier` block was genuinely inert.

So a maintenance pass treats the scan as a **starting list** and applies
delete → `lake build` → keep-or-revert per batch. Two mechanical cautions from
the sweep: a declaration whose attribute sits on a separate line (`@[simp]` then
`lemma …`) is invisible to naive line-span deletion, which then eats the
following declaration; and `Basic` is a hub, so a bad deletion there fails dozens
of downstream modules at once. Revert, do not patch.

The broader audit (`--audit`, WeightOne, median 15.2 ms/line) gives the general
picture:

| module | lines | wall | anomaly | cascade CPU | dependents |
|---|---|---|---|---|---|
| `LevelField` | 978 | 67.5 s | **4.5×** | 85 s | 1 |
| `Defs/PTorsion` | 134 | 6.0 s | 3.0× | 343 s | 12 |
| `Defs/Gamma` | 95 | 4.0 s | 2.8× | 191 s | 7 |
| `Defs/PeriodPair` | 99 | 3.9 s | 2.6× | 344 s | 13 |
| `LevelFraction` | 2,574 | 78.5 s | 2.0× | 266 s | 7 |
| `Basic` | 1,579 | 56.1 s | 2.3× | 353 s | 8 |
| `Fricke` | 338 | 6.4 s | 1.3× | **347 s** | 12 |
| `FrickeFunction` | 2,927 | 37.6 s | 0.8× | 304 s | 8 |
| `LevelOneHauptmodul` | 2,024 | 10.4 s | 0.7× | 335 s | 10 |
| `MonicRel` | 647 | 8.9 s | 0.9× | 234 s | 8 |

Two different anomalies: a unit can be **heavy** (high ms/line; `LevelField`,
`LevelFraction`, the small `Defs/` homes) or **a hub** (small itself, enormous
edit cost; `Defs/PeriodPair` is 99 lines and editing it re-elaborates 344 s of
CPU). `Basic` is both.

## 9. The flat-versus-tower pattern

FLT keeps its `S_` files flat: each re-proves its own private prelude, so editing
one recompiles one file — deliberate build isolation for a parallel agent swarm.
The deduplicated port writes shared mathematics once, which is better for
comprehension but turns every shared module into a cascade hub: editing the
99-line `Defs/PeriodPair` re-elaborates 20,637 dependent lines.

Neither extreme is right. The reconciling rules, in order of leverage:

1. **Measure the cascade, not the module.** Rank by `cascade CPU` from `--audit`;
   a hub's own size and speed are irrelevant to what editing it costs.
2. **Keep heavy blocks in leaves.** A module that is both heavy and has
   dependents (`LevelOneHauptmodul`, `FrickeFunction`, `LevelFraction`) should be
   split into a thin interface mid-tower and the heavy proof bodies in leaves.
3. **Keep hubs small, stable, and cheap to elaborate.** Sharing trivial
   vocabulary is fine and good; sharing expensive instances is not. If a home
   carries instances that take seconds each, fix or delete them first.
4. **Provide an instance where it is used.** A `haveI`/`letI` at the few sites
   that need it avoids both the declaration's elaboration and the global
   search overhead of a public instance.
5. **Delete truly-inert declarations — with the build as the judge.** A `scoped
   instance` whose namespace nothing opens is a *candidate* (the scan lists
   them), but it is still active inside its own file, so most candidates turn out
   to be used. Only the `LevelFraction` `C1_carrier` block was genuinely inert
   (≈18.6 s); apply delete → build → keep-or-revert, never a heuristic alone.
6. **Give `lake env lean` the project's options** (§7), or the tight-loop check
   lies about the heavy modules.
7. **Flatten deliberately where coupling is expensive.** If a trivial piece of
   vocabulary couples a frequently-edited hub to a heavy module, duplicating the
   vocabulary in the heavy module can cost less than the cascade it avoids — a
   measured, per-case exception to "write it once".

## 10. Running a build-cost pass

Build cost accumulates with the tower, so a pass that only reacts to a visible
problem leaves most of it in place. The procedure:

1. `build_ladder.py --audit --scope <area> --refresh` ranks per-line anomalies
   (heavy units) and edit cascades (hubs); `--profile` the worst few to see
   whether the time is instances or proofs.
2. Cut the low-risk items first: `scoped instance` candidates (the static list in
   `--audit`), unreferenced declarations, instances replaceable by a `haveI` at
   their use sites, and duplicated per-package preludes.
3. Reshape only against a measurement: heavy blocks to leaves, hubs kept small and
   cheap, a thin interface mid-tower (§9).
4. **`lake build` is the proof.** A batch that breaks the tree is reverted, not
   patched around. For instance candidates the loop is delete → build →
   keep-or-revert: the scan is a starting list and most candidates are used in
   their own file (§8).
5. Record what was cut and its before/after cost. A checker-count drop only
   happens if a matched declaration is removed; `scoped instance`s are not
   matched by the checker at all.

Two experiences worth repeating: `LevelFraction`'s `C1_carrier` block was the one
true positive in a 44-candidate sweep (≈19 s), and a bad deletion in a hub
(`Basic`) fails dozens of downstream modules at once — revert rather than debug.

## 11. Pointers

- [../lean/porting-playbook.md](../lean/porting-playbook.md) — the reusable
  policy, including the proof-engineering failure modes this note measures.
- [../lean/logs/weightone-rectify.md](../lean/logs/weightone-rectify.md) — the
  recorded wave builds (2 m 15 s – 6 m 53 s) and the `Basic` edit at 4 m 47 s.
- [../lean/logs/mc-port.md](../lean/logs/mc-port.md) — the contention incident
  (4 m 34 s wall / 0.5 s user) and the `CuspDichotomy` defeq fix.
- [../lean/porting-playbook.md](../lean/porting-playbook.md) §7 — the
  `v4.34.0` renames that cost build-and-fix rounds.
