# Study 003 — tree-sitter on FLTForHuman: does the port parse better than the pin?

**Status: measured 2026-10-18 on the current `lean/FLTForHuman` tree and a random
sample of the pin `aa2d8b3`; tool `tools/parser` (MoonBit + tree-sitter Lean grammar
`f309609`).** This is the follow-up to
[001-tree-sitter-lean-validation.md](001-tree-sitter-lean-validation.md), which
validated the approach on the pin's `Theorems/` files and deferred the corpus-scale
question.

## Verdict

**Yes, but for a narrower reason than "the port avoids the resistant syntax".**

The port removes the two constructs that dominated the pin's parse failures — the
`p2m_*` macro commands and the `attribute [-…]` erasure walls — and that is the main
driver behind the retention rise from **73.8%** (pin sample) to **91.8%** (port) on
the normal extraction path. The remaining failures are mathlib *notation* (`‖`, `⁄`, `⧸`,
`⟮…⟯`, `↥`, `∞`, …), which the port still uses heavily: 667 of its 20,235
declarations mention `‖`, and 98.8% of those have a parse error.

Two extractor bugs also surfaced, and without fixing them the comparison would be
misleading:

1. extraction only looked at **root children** of the parse tree, so declarations
   that tree-sitter's recovery nested inside an `ERROR` node vanished;
2. error collection walked **named children only**, so 18 files with `has_error:
   true` reported zero error nodes, and `ERROR` subtrees hid their nested failures.

Both are fixed. With a chunked **`--resync`** mode that parses each top-level
declaration independently, retention reaches **98.7%** on the port and **96.4%** on
the pin sample. The parser still cannot *trust* every statement: **8.9%** of the
port's statements are damaged (parse error inside the type, or silently truncated
at a hostile token) and **28.9%** of proofs contain errors.

## 1. Corpus and method

| | FLTForHuman (port) | pin `aa2d8b3` (sample) |
|---|---|---|
| files | 709 | 300 sampled, 295 unique |
| lexical declarations | 20,511 | 4,796 |
| source size | ≤ 192 KB/file | ≤ 0.6 MB/file |
| Lean/mathlib | mathlib `v4.34.0` | Lean `v4.33.1`, mathlib `db584cd6` |

The declaration count is a **lexical baseline**, not a Lean parse: a comment- and
string-aware line scan for declaration keywords (`theorem`, `lemma`, `def`,
`abbrev`, `instance`, `example`, `structure`, `class`, `inductive`, `axiom`,
`opaque`, `constant`, including modifiers such as `private`/`scoped`/`local` and
`set_option … in`). It is an upper bound on what a correct extractor should find;
a handful of upstream files show slightly more parsed declarations than baseline
matches, because the line scan is not a Lean parser and misses some attribute /
modifier spellings.

The pin sample is 300 files drawn with a fixed seed from the local clone of
`https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b3` (69,992 `.lean`
files). Its shape is bimodal: 168 files have ≤ 2 declarations, while 22 files have
> 50 (the largest single file contributes 452). That is *not* the same sample as
study 001's 300 files — 617 declarations there, 403 of them from one 1.6 MB file —
so absolute numbers are not comparable across the two studies; the pin sample here
was re-measured with the same build as the port.

By file size the normal-path retention is:

| declarations/file | pin sample | FLTForHuman |
|---|---|---|
| 1–2 | 180 / 176 (102%) | 121 / 127 (95.3%) |
| 3–10 | 218 / 261 (83.5%) | 903 / 950 (95.1%) |
| 11–50 | 1,391 / 1,642 (84.7%) | 8,396 / 8,786 (95.6%) |
| > 50 | 1,751 / 2,717 (64.4%) | 9,404 / 10,648 (88.3%) |
| **all** | **3,540 / 4,796 (73.8%)** | **18,824 / 20,511 (91.8%)** |

The gap is widest exactly where the pin's scaffolding lives: the large generated
`P2M/Sol` and `Definitions` files.

## 2. Headline numbers

| metric | pin sample (295) | FLTForHuman (709) |
|---|---|---|
| lexical declarations | 4,796 | 20,511 |
| declarations, root-only scan (study 001 behaviour) | 3,355 (69.9%) | 17,852 (87.0%) |
| declarations, whole-tree walk (fix 1) | 3,540 (73.8%) | 18,824 (91.8%) |
| declarations, `--resync` (fix 2) | 4,621 (96.4%) | **20,235 (98.7%)** |
| files with ≥ 1 parse error | 253 / 295 (85.8%) | 653 / 709 (92.1%) |
| declarations with a parse error (`--resync`) | 1,912 / 4,621 (41.4%) | 8,145 / 20,235 (40.3%) |
| statements with a parse error (`--resync`) | 505 / 4,621 (10.9%) | 1,682 / 20,235 (8.3%) |
| statements untrustworthy (error **or** truncation) | 578 / 4,621 (12.5%) | **1,793 / 20,235 (8.9%)** |
| proofs with a parse error (`--resync`) | 1,347 / 4,621 (29.1%) | 5,847 / 20,235 (28.9%) |

For theorems only, the port's `--resync` result is 15,748 theorems, of which
1,462 (9.3%) have a damaged statement and 5,107 (32.4%) a damaged proof.

Two readings matter:

- **Retention improves a lot** on the port before any new machinery (87.0% vs
  69.9%), and both corpora become near-complete with `--resync`. An index built
  from the normal path alone silently loses one declaration in eight in the port
  and one in four in the pin.
- **Statement quality improves only modestly** (8.9% vs 12.5% untrustworthy).
  The port did not get rid of mathlib notation; it got rid of FLT-specific
  scaffolding.

## 3. The extractor bugs the port exposed

### 3.1 Root-only extraction

`extract_decls` iterated `root.named_children()` and kept only direct
`declaration` children. When a top-level command fails, tree-sitter can nest the
following declarations inside an `ERROR` node rather than returning to the root
state. Example: `lean/FLTForHuman/Patching/PatchingConstruction.lean` has 367
`declaration` nodes in its tree, but only 284 were root children — the other 83 were
invisible. Walking the whole tree and stopping at each `declaration` recovers them
(284 → 367).

### 3.2 Error collection

`collect_errors` had two blind spots, both visible in the port:

- it recursed through **named** children only; an `ERROR`/missing node can sit under
  an anonymous node, and `has_error` is inherited from it. 18 files reported
  `has_error: true` with `error nodes: 0`.
- the port's 9 `attribute [-…]` lines parse to a **hidden** missing token: the sexp shows `(identifier (MISSING _plain_ident))`, but `children()`
  returns an empty child list for that `identifier`, because the missing token is a
  hidden (`_`-prefixed) rule. Traversal cannot see it; the walker now detects
  "node says `has_error`, no child reports an error" and emits a
  `hidden missing token in <node>` entry.

The walker also descends into `ERROR` nodes instead of stopping at them, so nested
failures stay visible: the whole-file error in
`AutomorphicForm/Adelic/PeterssonSlabPairing.lean` now reports 508 nodes rather
than 1.

### 3.3 Chunked resync

One hostile token can make tree-sitter fail the **start rule**: the file's root node
is a single `ERROR` spanning line 1 to EOF, and no `declaration` nodes exist at all.
`AutomorphicForm/Adelic/PeterssonSlabPairing.lean` (1,067 lines, 78 lexical
declarations) parses to zero declarations this way; so do
`AlgebraicCurve/RadialRegion/Engine/GridGeometry.lean` (195 declarations, tree
contains 29) and `WeierstrassCurve/IsogenyEndDatum/RestrictAlongAdd.lean`
(103 → 26).

`extract_decls_resync` splits the source at comment/string-aware top-level
declaration lines and parses each chunk separately, shifting rows and byte offsets
back to whole-file coordinates. Results on the worst files:

| file | lexical | tree | resync |
|---|---|---|---|
| `AlgebraicCurve/RadialRegion/Engine/GridGeometry.lean` | 195 | 29 | 187 |
| `AutomorphicForm/Adelic/PeterssonSlabPairing.lean` | 78 | 0 | 78 |
| `WeierstrassCurve/IsogenyEndDatum/RestrictAlongAdd.lean` | 103 | 26 | 100 |
| `Patching/PatchingConstruction.lean` | 378 | 284 (367 tree nodes) | 374 |
| `ModularForms/WeightOne/EisensteinChiNegThree.lean` | 458 | 365 | 451 |
| `AutomorphicForm/Adelic/IsotypicCuspSpace.lean` | 124 | 59 | 123 |

Only 165 of 709 files still differ from the lexical baseline under `--resync`,
and every sampled mismatch is a declaration the line scan misses or one the grammar
cannot build a node for (§7), not a duplicate or a phantom: the chunks are
disjoint, and the parser emits no declaration whose start line is not a
declaration line.

### 3.4 Statement vs proof

A declaration can be perfectly extractable while its *proof* is broken. The old
`has_error` flag conflated the two, which made the earlier "statement extraction is
unaffected" claim untestable. Each declaration now carries:

- `statement_has_error`, `proof_has_error` — error inside the `type` / `body` field;
- `statement_start/end`, `proof_start/end` — byte offsets into the source (UTF-8,
  `-1` when absent).

The byte spans are what make truncation measurable: if the bytes between
`statement_end` and `proof_start` are anything other than `:=` or a `where`
clause, the statement was cut short even when the tree reports no error in the
`type` field.
**Kind note.** The grammar has no `lemma` or `class` node kind: `lemma` is
reported as `theorem` and `class` as `structure` (the port has 803 `lemma` lines
and 28 `class` declarations; the 128 `structure` results include them). Consumers
that need the source keyword must read the declaration line, not `kind`.

## 4. Why the port helps: the scaffolding is gone

| construct | pin clone | FLTForHuman |
|---|---|---|
| `p2m_*` command lines | 145,303 | 0 |
| `attribute [-…]` lines | 233,171 | 9 |
| `lemma` lines | 70,520 | 803 |

The pin writes its proofs through the P2M harness: every theorem is a `p2m_*`
command, and attribute erasure is used in bulk to fight instance search. The port
states ordinary `theorem`/`lemma` declarations and transcribes only nine
`attribute [-…]` lines. Since tree-sitter has no rule for the macros and only a
partial rule for erasure, this is the single largest source of the retention gap —
and the reason the port's advantage is largest in files with > 50 declarations.

## 5. What still resists: mathlib notation

Counting error *nodes* is misleading here — nested `ERROR`s inside one swallowed
region multiply the count (48,503 nodes on the port, 4,425 of them missing
tokens). A declaration-level count says which notation is actually fatal. A
declaration "uses" a token when the token occurs in its source span, and is
"affected" when that declaration carries any parse error:

| token | declarations using it | with a parse error | rate |
|---|---|---|---|
| `‖ … ‖` (norm) | 667 | 659 | 98.8% |
| `⁄` (Kähler `Ω[F⁄K]`) | 517 | 514 | 99.4% |
| `⧸` (quotient) | 377 | 369 | 97.9% |
| `⟮ … ⟯` (adjoin brackets) | 163 | 160 | 98.2% |
| `∞` (`ℝ≥0∞`, limits) | 252 | 251 | 99.6% |
| `→₀` (finitely supported) | 187 | 185 | 98.9% |
| `⁰` (superscript) | 181 | 178 | 98.3% |
| `ᶠ`, `ʳ`, `ᵐ`, `ᵥ`, `₊` | 442 | 426 | 96.4% |
| `↥` (subtype coercion) | 646 | 511 | 79.1% |
| `⇑` (coercion) | 708 | 444 | 62.7% |

The first eight rows are damning: essentially every declaration that mentions
`‖`, `⁄`, `⧸`, `⟮…⟯`, `∞` or `→₀` fails somewhere. `↥` and `⇑` are used
in many declarations that parse fine, so their rate is lower but the absolute
number of affected declarations is still large.

The same test on the pin sample gives the same picture: `‖` 228/232 (98.3%),
`↥` 239/322 (74.2%), `⧸` 109/109, `∞` 104/108 (96.3%), and `p2m_` 90/178 (50.6%,
the lowest rate of any construct measured). What differs
between the corpora is the *mix*: the pin also has 145k `p2m_*` command lines and
233k `attribute [-…]` lines outside declarations, which is where its retention loss
comes from.

The `‖` rule is a deliberate grammar omission, not an oversight: a symmetric
delimiter around an unbounded term does not converge in LR generation
(`grammar.js`: "norm was measured at 39 min"). It is also the source of most silent
truncations (§6), because the grammar builds a partial type field and puts the
error outside it.

There remain 4,931 declarations with a parse error whose span contains none of the
tokens above. Those are the command/tactic-syntax failures (`where` clauses,
`omit … in`, `set … with`, `classical`, structure-instance syntax) and pure
recovery artifacts whose error span starts after the culprit.

## 6. Silent statement truncation

`statement_has_error` alone under-reports. With `‖` the grammar often builds a
*partial* type field and reports the error outside it. In
`lean/FLTForHuman/Algebra/LaurentSeriesXAdic.lean:71`:

```lean
theorem norm_X_lt_one : ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F)‖ < 1 := by
```

the extracted statement is

```text
HahnSeries.single (1 : ℤ) (1 : F)
```

— the type field ends inside the norm brackets, the rest (`‖ < 1`) falls into the
gap before `:=`, and `statement_has_error` is `false`. On the port:

| | normal path | `--resync` |
|---|---|---|
| statement has a parse error | 1,545 (8.2%) | 1,682 (8.3%) |
| statement truncated (gap ≠ `:=`/`where`) | 195 (1.0%) | 204 (1.0%) |
| unbalanced statement brackets | 31 | 29 |
| **union (untrustworthy)** | **1,648 (8.8%)** | **1,793 (8.9%)** |

(The unbalanced cases are already contained in the other two rows, so the union is
the error-or-truncation count.)

A consumer must therefore check the gap, not just the flag. The parser exposes the
byte spans needed for that check; making it a first-class
`statement_terminated` field is a small next step (§8).

## 7. Declarations the grammar cannot build at all

About 1.3% of declarations have no `declaration` node in *any* window, so even
chunking cannot recover them. Example:
`lean/FLTForHuman/WeierstrassCurve/GenusOnePlaceGateCentred.lean:38` — the theorem
parses as one `ERROR` spanning the whole declaration (`(module (ERROR …))`) because
the term after `:=` contains a structure-instance construction the grammar does not
accept. Similar cases: `ModularForms/WeightOne/Defs/PeriodPair.lean` has no
declarations at all (comments/imports only, so this file is a non-issue),
`GaloisRep/Defs/DeformationRingData.lean`'s `structure` and
`GenusOnePlaceGateCentred.lean`'s theorem are real losses.

For these the options are a grammar fix or a lexical fallback that records name,
kind and line range but marks the statement as unreliable.

## 8. Recommendations

1. **Use `--resync` for any corpus index** (dependency extraction, statement
   search, theorem inventories). The normal path is fine for single-file
   diagnostics and gives cleaner `has_error` semantics.
2. **Do not treat a statement as trustworthy without the gap check.** 8.9% are
   damaged on the port; the flag alone catches 8.3%, the gap check another 0.5%.
   Add `statement_terminated` (or `statement_complete`) to `Decl` and gate the
   reader on `!statement_has_error && statement_terminated`.
3. **Patch the grammar's token set**, in descending value: `‖`/`|` (a bounded
   interior or an operator-token treatment rather than a symmetric `seq` over
   `_term`), `⧸`, `⁄`, `⟮`/`⟯`, `↥`, `∞`, the superscript/subscript modifier
   letters, `→₀`, `⇑`. The `‖` rule alone is 2,034 error nodes and the source of
   most silent truncations.
4. **Keep the `p2m`-free port as the parser test corpus.** It is a cleaner
   measure of grammar coverage: 92.1% of port files still emit errors, but almost
   none of those errors are FLT-specific commands — they are mathlib syntax that
   any Lean corpus would hit.
5. Once (1)–(2) are in place, study 001's deferred next step — extracting
   identifiers from `body` and building the dependency index — is viable at
   ~98.7% declaration coverage.

## 9. Reproduction

The scan harness used a local, untracked scratch workspace (per-file JSON from
both paths, per-file `--errors` dumps, the comment/string-aware declaration
counter, and the comparison scripts). The parser itself is under `tools/parser`;
`moon test --target native` covers the new behaviour (statement/proof flags and
byte spans, resync coordinates, hidden missing tokens).

Commands used for the headline table (native build):

```bash
parser <file.lean> --json            # normal path
parser <file.lean> --json --resync   # chunked recovery
parser <file.lean> --errors          # ERROR + missing nodes, nested
```

Wall time for the 709-file port: 10.7 s for the normal path, 13.0 s for `--resync`
(one process per file, process startup included; the largest file, 192 KB, takes
0.10 s / 0.19 s).
