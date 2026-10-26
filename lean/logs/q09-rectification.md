# The `Q09` rectification — stripping a generated namespace family (2026-10-25)

**Status: done.** Five namespaces, 173 declarations, 159 occurrences in 11 modules; the family is
gone from the port's names, the six modules that carry it are wired to the current statement
checker, and `check_port` now rejects a residual family name. Checker after: **5836 ok,
0 mismatch, 0 missing, 31 own, 0 kw over 262 modules** (before: 5637 ok over 254 modules, the
difference being the 199 declarations this sweep brought under the wire). Builds: 13 targets,
green, 0 warnings.

## 1. Why

`Q09`, `Q09AIarch`, `Q09AIarchC`, `Q09AIarchG` and `Q09RowIso` are the pinned corpus's **informal
question number and workspace labels** — `Q09` names the question the development answers, and the
`AI`/`C`/`G`/`RowIso`/`Dock` tails are workspace abbreviations. None of them is mathematics, and
the sub-tokens are not even readable: `AI` and `C` and `G` mean nothing outside the pin's scaffold.
They are the same class as the `kw*` family (which had its own sweep, [topics/kw-rectification.md](../topics/kw-rectification.md)),
but they were invisible to both that sweep and `check_port`, because the normaliser erases only
`kw*` and the `ModularCurve.`/`AlgebraicCurve.` prefixes: a `Q09*` name is not `kw`-prefixed, and
because it is a *namespace* on declarations whose last names are already the pin's, no statement
diff ever saw it. It surfaced only on a direct grep.

Unlike a pure wrapper namespace, the family is not only decoration: the port's declarations are
spelled *inside* statements (`[MeasurableSpace (Q09AIarch.Kprod L)]`, `Q09AIarch.Kprod L → ℂ`), so
stripping it is a checker-relevant change — one statement in the whole port (`exists_contDiff_dconvWith`)
names a member.

## 2. The mapping

Each port namespace is the subject; the pin's partition is kept where merging would collide.

| pin | port | declarations |
|---|---|---:|
| `Q09` | `ArchApproxIdentity` | 101 |
| `Q09AIarch` | `ArchInfra` | 34 |
| `Q09AIarchC` | `ArchInfraTopology` | 7 |
| `Q09AIarchG` | `ArchEntryBall` | 30 |
| `Q09RowIso` | `ArchEntryBall` | 1 |

`ArchApproxIdentity` is the shared engine namespace the four movements (type reproducer,
convolution limit, instantiation, and one Haar fact) re-open in their own files; `ArchInfra` and
`ArchInfraTopology` stay apart because three of their names coincide (`archGLMeasurableSpace`,
`archGLBorelSpace`, `locallyCompactSpace_archGL` — the pin itself declares both copies); the
closing `Q09RowIso` block folds into `ArchEntryBall`, whose subject it shares (no name clashes).

The one junk *last* name in the family went too: `Q09.main` (the pin's private assembly step) is now
`ArchApproxIdentity.exists_tendsto_integral_of_mem_archCutSubmodule`, which is what it proves.

## 3. What it cost the checker

Two changes, both recorded here because they are amendments:

* **One `CANONICAL_NAMES` entry**, `'ArchInfra': 'Q09AIarch'`: the single statement that mentions a
  member of the family still has to hash against the pin's text, and the map restores the pin's
  spelling on the port side only (on the pin side it is a no-op, so no corpus rebuild). The
  `…C`/`…G`/`RowIso` merges need no entry because no statement mentions them; a statement that
  ever does will fail loudly (`MISMATCH`), never match silently.
* **A residual-name guard**, `Q09_FAMILY_RE` in `spec/lean_parser.py` and its use in
  `spec/check_port.py`'s name check (the same place the `kw*`/`Kw*` guard sits): a `Q09…` segment in
  a wired module's declaration or namespace name is now a `KW-NAME`-class failure, so the family
  cannot creep back in on a later import.

No `pin:` rows were needed: every declaration was found by its own last name (or by content), and
the two type-only `def`s as before.

## 4. Brought up to standards (the touched modules)

The rename touched 11 modules. Eight of them were **tier 3** — imported and statement-invisible —
and are now wired, which is the substantial part of this wave: 199 public declarations are diffed
for the first time, and all of them matched.

| module | wire | ok |
|---|---|---:|
| `RepTheory/TypeReproducer.lean` | the pin `S_…archCutSubmodule.lean` | 76 |
| `RepTheory/ConvolutionLimit.lean` | same | 24 |
| `AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean` | same | 48 |
| `AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean` | same | 36 |
| `AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean` | same (+ the `ArchInfra` map entry) | 10 |
| `AutomorphicForm/Adelic/ArchApproxIdentity.lean` (façade) | the `Theorems/` wrapper + the `S_` copy | 1 |
| `AutomorphicForm/Adelic/UnitFactorizableEngine.lean` | its three `Theorems/` wrappers + `S_` copies | 3 |
| `AutomorphicForm/Adelic/ArchKFiniteFamily.lean` | its `Theorems/` wrapper + `S_` copy | 1 |

The remaining three (`ArchCompactOrbit`, `ArchDualCut`, `Cusp/ArchTypeSpan`) were already wired and
only needed their references updated.

**Legacy exit.** `AutomorphicForm/Adelic/ArchApproxIdentity.lean` was the last module of this topic
owned by the frozen checker; its `PORT_FILES` entry in `spec/old_check_stmts.py` is replaced by a
note that the whole topic is on the current wire. The exempt count fell 521 → 520 and the wired
count rose 254 → 262.

**Markers.** 252 grandfathered in-source `-- pin:` comments were dropped. They named the pin file
by *basename*, which the current checker cannot resolve (it reads the wire from the header's full
path), and every one of them named the declaration's own last name — so each was redundant once the
module was wired. None renamed anything; the two that did (`main`, `solution`) are covered by the
content-hash tier.

**Headers.** The naming paragraphs of `ArchInfra`, `EntryBall` and the façade are rewritten: they
said "the pin's declarations land here keeping the pin's own sub-namespaces `Q09`/`Q09AIarchC`/…"
and "the four supporting movements stay tier 3"; both claims are now false. The prose that remains
is the pin's own section labels quoted as provenance (`Q09AIDock.ArchFinSplit`, six occurrences in
`UnitFactorizableEngine`'s section headers, and the pin namespace names in the two naming
paragraphs) — documentation of where the mathematics was transcribed from, not a port identifier.

## 5. `dedup` and `move_dead` on the touched modules

`python3 tools/deps/dedup.py --cross` over the five engines: **4 clusters, 39 removable lines** of
pin-copied prelude — `archGLMeasurableSpace` and `archGLBorelSpace` (public + a private
re-derivation in `ArchInfra`, plus `EntryBall`'s local-instance copy), `t2Space_archMatrix` (three
copies under two spellings), and `continuous_archEntries` (`EntryBall`'s private helper and
`Instantiate`'s local re-derivation). **No mathematics is involved** — every one is an `abbrev` +
`attribute [local instance]` that the pin itself declares once per namespace — so this is an
either-way choice on 39 lines of plumbing and is **neither cut nor carried forward**; it is
recorded here only so the next `dedup.py` run does not read as a fresh finding.

`move_dead.py --dry-run` over the same set: **0 dead declarations** in six modules, and one in
`ArchKFiniteFamily` (18 lines, an arch-component extensionality lemma). It **stays in place**: it
rounds out the arch-component API, and shelving it would need `--expose` of the private helper
`eq_of_forall_archComponent_eq` for a line-count gain only.

## 6. What this does not cover

The *engine tokens* (`Ecf`, `ρc`, `ℂK`, `cutc`, `cutM`, `CA`, `CB`, `QM`, `Qc`, `underSub`) are a
different family and stay the pin's: stripping them was attempted in the DC1 wave and reverted,
because unlike `Q09` they are load-bearing in *statements the pin made public*, so a rename buys
nothing the canonical map does not already cost — see
[automorphicForm/WORKORDER-DC1-arch-dual-cut.md](../topics/automorphicForm/WORKORDER-DC1-arch-dual-cut.md) §5
and the open debt in [CARRY-FORWARD.md](../CARRY-FORWARD.md).

Reproduce:

```
cd lean
grep -rn "Q09" FLTForHuman | grep -v '/-!\|--'        # expect nothing
python3 spec/check_port.py --all                       # 5836 ok, 0 mismatch, 0 missing
python3 spec/statement_db.py selftest                  # ok
```
