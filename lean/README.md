# lean/ — FLT fragments as a Lean project

Companion to the `base/` and `math/` notes. Where those explain a step in prose,
`lean/` re-runs selected pieces of the [FLT formalization][flt] as our own Lean
code: a claim can then be checked rather than taken on faith, and a proof can be
restated in a form we find easier to read.

## Ground rules

- **Fragments only.** We copy small, self-contained definitions and lemmas out of
  FLT and adapt them. We do **not** `require` the FLT project or `import` its
  modules — a single FLT import can pull in a very large dependency cone and a
  build measured in hours. Every module here imports mathlib only.
- **Adapt, do not mirror.** The FLT proof stays the source of truth for
  correctness ([PROOF-PATH.md][proof-path]: "Where this prose and the Lean
  differ, the Lean is right"), but the presentation is ours: we may restate a
  lemma, generalize it, split it, or take a different mathlib route.
- **Cite the origin.** Each module opens with a header comment naming the FLT
  file it came from, pinned to `aa2d8b3` (never `/main`), and saying what we
  changed.
- **No silent gaps.** A module either compiles or carries an explicit, commented
  `sorry`; nothing is left merely asserted.

## Toolchain and mathlib

| component | version | where |
|---|---|---|
| Lean | `leanprover/lean4:v4.34.0` | `lean-toolchain` |
| mathlib | `v4.34.0` | `lakefile.lean` |

We pin a **mathlib release tag** so `lake exe cache get` can fetch the
community-built `.olean`s instead of compiling mathlib from source (hours of
work). We deliberately do not track FLT's own mathlib pin (`v4.33.0`): since we
rewrite fragments rather than import them, matching FLT exactly buys nothing,
and the current release is the better long-term base.

## Building

```bash
cd lean
lake build                   # the default target, FLTForHuman (both efforts)
```

The prebuilt mathlib oleans are already in place for the pinned release, so a
build needs no download. On a fresh checkout, fetch them once first:

```bash
lake exe cache get   # one-off: download the prebuilt mathlib oleans
```

### The mathlib cache

`lake exe cache get` is the only step that uses the cache. It downloads `.ltar`
archives into a pool and decompresses the oleans into
`.lake/packages/mathlib/.lake/build/`. Builds read oleans from `.lake` and never
touch the pool, so **the pool's location does not affect `lake build`**.

The pool lives at the standard per-user location, `~/.cache/mathlib` — 8906
archives, ~450 MB, shared with any other mathlib4 checkout. The server is
missing 2 of the 8908 archives; those modules simply compile locally on the first
build.

A re-fetch is needed only when the mathlib revision changes or `lean/.lake` is
removed (mathlib's `post_update` hook also runs `cache get` automatically after
`lake update`). A session that cannot write to `~`, such as the sandboxed agent,
must point `MATHLIB_CACHE_DIR` at a writable directory for that one command:

```bash
MATHLIB_CACHE_DIR="$PWD/.cache/mathlib" lake exe cache get
```

Such an override creates a second, project-local pool; `.cache/` is gitignored
alongside `.lake/` in case it does.

## Where things live

The documentation has four roles, and they are kept apart on purpose:

| path | role |
|---|---|
| any plan still at the top level | an **active plan** — the blueprint for work in progress. A finished effort's plan is retired into `topics/` (see below); the `functionFieldGeneration` plan is now [topics/PORTING-FFG.md](topics/PORTING-FFG.md) |
| `topics/<effort>/TOPIC-*.md` | **work orders, then executed plans**: one per topic. New work orders open with the mandatory build-discipline block (playbook §3.11); finished ones keep the record of what was learned and what it cost |
| `logs/` | the **linear record** of what happened, in order — `card-torsion-port.md` for the first port, `ffg-port.md` for this one |
| `porting-playbook.md` | the **reusable method**, not tied to any one effort |
| `spec/` | the **deliverable measures**: the consumer and the statement checker |
| `Reserve/` | the **reserve library**: verified modules kept off the critical path (superseded routes, deferred API). It may import `FLTForHuman`; `FLTForHuman` must never import it. Built by default so it stays compiled; reserve modules that duplicate a main-tree statement are deliberately **not** in `PORT_FILES` |
| `CARRY-FORWARD.md` | the **carry-forward register**: API deliberately left unported (the counterpart of `Reserve/`, which holds deferred API that *has* been ported), open follow-ups, and the scoping cautions that are not yet playbook method. Grep it for a node name before pricing that node |

An executed plan is not deleted: it is the record of a decision and its cost, and
`logs/` cross-references it. When an effort finishes, its plan is retired from the
top level into `topics/`, and the log gains the entry that summarises it.
`topics/functionFieldGeneration/` holds the seven topics of the
`functionFieldGeneration` effort, and `topics/phiGenSplitting/` holds the nine
topics of its Φ_p splitting / R1 sub-effort, whose plan
[PORTING-PhiGen.md](topics/PORTING-PhiGen.md) is retired there. That effort is now
**complete** too: its plan [PORTING-FFG.md](topics/PORTING-FFG.md) is retired to
`topics/` (with a RETIRED banner), and
[ffg-retrospective.md](topics/ffg-retrospective.md) is the closing review of its
decisions, clarity and redundancy cuts. The R1 work orders
[TOPIC-r1-kernel.md](topics/phiGenSplitting/TOPIC-r1-kernel.md),
[TOPIC-jq-model.md](topics/phiGenSplitting/TOPIC-jq-model.md),
[TOPIC-hauptmodul.md](topics/phiGenSplitting/TOPIC-hauptmodul.md) and
[TOPIC-phiGen-descends.md](topics/phiGenSplitting/TOPIC-phiGen-descends.md) are
complete (R1 is done and the cone's (c) is discharged), the cone-algebra topics
[TOPIC-integrality.md](topics/phiGenSplitting/TOPIC-integrality.md) through
[TOPIC-splitting.md](topics/phiGenSplitting/TOPIC-splitting.md) are complete (the
cone is closed), and [logs/phiGen-port.md](logs/phiGen-port.md) is the
sub-effort's record.

## Sources

- FLT: <https://github.com/anthropics/fermats-last-theorem>, local clone pinned at
  `aa2d8b3`. Per-file raw URLs follow
  `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/<path>`;
  the generated module glosses are served at
  <https://tianyipeng.github.io/fermats-last-theorem/>.
- mathlib at `v4.34.0`:
  <https://github.com/leanprover-community/mathlib4/tree/v4.34.0>.

[flt]: https://github.com/anthropics/fermats-last-theorem
[proof-path]: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/PROOF-PATH.md
