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

```bash
cd lean
# per-file elaboration, timed and bounded
for f in FLTForHuman/ModularForms/WeightOne/{LevelFraction,Gamma1Basis,LevelN}; do
  /usr/bin/time -f "%e s  %U user  $f" timeout 150 lake env lean "$f.lean"
done
# is the .olean touched?  (it is not)
ls -l --time-style=+%T .lake/build/lib/lean/FLTForHuman/ModularForms/WeightOne/Defs/PeriodPair.olean
lake env lean FLTForHuman/ModularForms/WeightOne/Defs/PeriodPair.lean
ls -l --time-style=+%T .lake/build/lib/lean/FLTForHuman/ModularForms/WeightOne/Defs/PeriodPair.olean
# where the time goes in a slow module
lake env lean -Dprofiler=true FLTForHuman/ModularForms/WeightOne/LevelFraction.lean 2>&1 | tail -40
# cached vs edited cost
timeout 180 lake build            # no-op: ~3 s
```

## 8. Pointers

- [../lean/porting-playbook.md](../lean/porting-playbook.md) — the reusable
  policy, including the proof-engineering failure modes this note measures.
- [../lean/logs/weightone-rectify.md](../lean/logs/weightone-rectify.md) — the
  recorded wave builds (2 m 15 s – 6 m 53 s) and the `Basic` edit at 4 m 47 s.
- [../lean/logs/mc-port.md](../lean/logs/mc-port.md) — the contention incident
  (4 m 34 s wall / 0.5 s user) and the `CuspDichotomy` defeq fix.
- [../lean/porting-playbook.md](../lean/porting-playbook.md) §7 — the
  `v4.34.0` renames that cost build-and-fix rounds.
