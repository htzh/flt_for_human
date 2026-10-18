# Study 003 — tree-sitter on FLTForHuman: does the port parse better than the pin?

**Status: measured 2026-10-18 on the current `lean/FLTForHuman` tree and a random
sample of the pin `aa2d8b3`, with tool `tools/parser` (MoonBit + tree-sitter Lean
grammar [`Julian/tree-sitter-lean`](https://github.com/Julian/tree-sitter-lean) at
`916c44f`, 2026-10-04).** This is the follow-up to
[001-tree-sitter-lean-validation.md](001-tree-sitter-lean-validation.md), which
validated the approach on the pin's `Theorems/` files and deferred the corpus-scale
question. The first pass of this study ran on the then-pinned grammar `f309609`;
§3 measures what the grammar bump bought. The pin sample here is from the same pin
as study 001, so the parser comparison is apples to apples, but the absolute
numbers are not comparable to study 001's sample (see §1).

## Verdict

**Yes, and now for two separate reasons: the port dropped the pin's scaffolding,
and the grammar now understands norm notation.**

- The port has **0** `p2m_*` command lines and **9** `attribute [-…]` lines, versus
  145,303 and 233,171 in the pin clone. That is the main driver behind the
  retention rise from **64.6%** (pin sample) to **91.8%** (port) on the normal
  extraction path.
- The grammar bump to `916c44f` added `‖x‖`/`‖x‖₊` via an external scanner (plus
  `⟪x, y⟫` and restriction/box-product operators). Norm-only declarations with a
  statement error fell from **52.8%** to **10.0%**, and silent statement
  truncations halved (204 → 100).
- With chunked **`--resync`** extraction, retention reaches **98.8%** on the port
  and **96.6%** on the pin sample. **7.0%** of statements contain a parse error
  inside the type, but the statement *text* is complete for **98.75%** of
  declarations. 254 statements (1.25%) lose text — 155 drop a leading token, 99 a
  trailing one — and **182 of those are silent** (no error flag). **28.5%** of
  proofs contain errors.

Two extractor bugs surfaced during the first pass and are fixed (they mattered
more than the corpus difference):

1. extraction only looked at **root children** of the parse tree, so declarations
   that tree-sitter's recovery nested inside an `ERROR` node vanished;
2. error collection walked **named children only**, so 18 files with `has_error:
   true` reported zero error nodes, and `ERROR` subtrees hid their nested failures.

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
> 50 (the largest single file contributes 450 under resync). That is *not* the
same sample as study 001's 300 files — 617 declarations there, 403 of them from one
1.6 MB file — so absolute numbers are not comparable across the two studies; the
pin sample here was re-measured with the same build as the port.

By file size the normal-path retention is:

| declarations/file | pin sample | FLTForHuman |
|---|---|---|
| 1–2 | 180 / 176 (102%) | 121 / 127 (95.3%) |
| 3–10 | 219 / 261 (83.9%) | 908 / 950 (95.6%) |
| 11–50 | 1,392 / 1,642 (84.8%) | 8,381 / 8,786 (95.4%) |
| > 50 | 1,309 / 2,717 (48.2%) | 9,419 / 10,648 (88.5%) |
| **all** | **3,100 / 4,796 (64.6%)** | **18,829 / 20,511 (91.8%)** |

The gap is widest exactly where the pin's scaffolding lives: the large generated
`P2M/Sol` and `Definitions` files. One pin file
(`S_QuadraticForm_exists_rat_ternary_pureNrd_…`) lost 444 of its 454 declarations
to a single whole-file `ERROR` under the new grammar (§3), which is most of the
`> 50` drop; resync recovers 450 of them.

## 2. Headline numbers

| metric | pin sample (295) | FLTForHuman (709) |
|---|---|---|
| lexical declarations | 4,796 | 20,511 |
| declarations, whole-tree walk | 3,100 (64.6%) | 18,829 (91.8%) |
| declarations, `--resync` | 4,633 (96.6%) | **20,261 (98.8%)** |
| files with ≥ 1 parse error (tree) | 251 / 295 (85.1%) | 652 / 709 (92.0%) |
| declarations with a parse error (`--resync`) | 1,858 / 4,633 (40.1%) | 7,926 / 20,261 (39.1%) |
| statements with a parse error (`--resync`) | 443 / 4,633 (9.6%) | 1,425 / 20,261 (7.0%) |
| statements untrustworthy (error **or** text loss) | 537 / 4,633 (11.6%) | **1,607 / 20,261 (7.9%)** |
| proofs with a parse error (`--resync`) | 1,347 / 4,633 (29.1%) | 5,775 / 20,261 (28.5%) |

For theorems only, the port's `--resync` result is 15,766 theorems, of which
1,115 (7.1%) have a statement parse error and 5,072 (32.2%) a proof parse error.

"Untrustworthy" above is the union of two different failures: only **254** of the
port's 1,607 are losses of statement *text*; the other 1,353 have complete text and
a broken internal tree. §6 separates the two.

Two readings matter:

- **Retention improves a lot** on the port before any recovery machinery (91.8%
  vs 64.6%), and both corpora become near-complete with `--resync`. An index built
  from the normal path alone silently loses one declaration in twelve in the port
  and one in three in the pin.
- **Statement quality improves only modestly** (7.9% vs 11.6% untrustworthy). The
  port did not get rid of mathlib notation; it got rid of FLT-specific scaffolding.

## 3. What the grammar bump bought

The first pass pinned `f309609` (2026-09-04). Upstream `916c44f` (2026-10-04)
merged norm notation via an external scanner, `⟪x, y⟫`, and restriction/box-product
operators. Measured with the same extractor on both sides:

| metric | `f309609` | `916c44f` |
|---|---|---|
| port declarations, tree / resync | 18,824 / 20,235 | 18,829 / 20,261 |
| port statements with error | 1,682 (8.3%) | **1,425 (7.0%)** |
| port text loss (head or tail) | 481 (2.4%) | **254 (1.3%)** |
| port silent text loss | 224 | **182** |
| port untrustworthy (error or text loss) | 1,906 (9.4%) | **1,607 (7.9%)** |
| port proofs with error | 5,847 (28.9%) | 5,775 (28.5%) |
| port error nodes | 48,503 | 35,687 |
| pin declarations, tree / resync | 3,540 (73.8%) / 4,621 | 3,100 (64.6%) / 4,633 |
| pin text loss | 195 (4.2%) | **139 (3.0%)** |
| pin untrustworthy (error or text loss) | 619 (13.4%) | **537 (11.6%)** |
| norm-only declarations with error | 461 / 468 (98.5%) | 266 / 491 (54.2%) |
| norm-only statements with error | 247 / 468 (52.8%) | 49 / 491 (10.0%) |

"Norm-only" means the declaration's span contains `‖` and none of the other
hostile tokens in §5, so it isolates the grammar change. The norm fix is real:
`theorem norm_X_lt_one : ‖(… : LaurentSeries F)‖ < 1` now extracts its full
statement with `statement_has_error = false`, and the file's error count drops from
15 to 3 (the rest is tactic syntax).

The caveat is on the pin's normal path: the new grammar's recovery is *worse* for
one huge generated file (454 → 10 declarations; resync recovers 450), so the pin's
tree-only retention fell from 73.8% to 64.6% even though resync improved slightly
(96.4% → 96.6%). Lesson: **use `--resync` for the index**; the normal path is a
diagnostic, not a reliable inventory, and its recovery behaviour can move when the
grammar does.

## 4. The extractor bugs the port exposed

### 4.1 Root-only extraction

`extract_decls` iterated `root.named_children()` and kept only direct
`declaration` children. When a top-level command fails, tree-sitter can nest the
following declarations inside an `ERROR` node rather than returning to the root
state. Example: `lean/FLTForHuman/Patching/PatchingConstruction.lean` has 367
`declaration` nodes in its tree, but only 284 were root children — the other 83 were
invisible. Walking the whole tree and stopping at each `declaration` recovers them.

### 4.2 Error collection

`collect_errors` had two blind spots, both visible in the port:

- it recursed through **named** children only; an `ERROR`/missing node can sit under
  an anonymous node, and `has_error` is inherited from it. 18 files reported
  `has_error: true` with `error nodes: 0`.
- the port's 9 `attribute [-…]` lines parse to a **hidden** missing token: the sexp
  shows `(identifier (MISSING _plain_ident))`, but `children()` returns an empty
  child list for that `identifier`, because the missing token is a hidden
  (`_`-prefixed) rule. Traversal cannot see it; the walker now detects "node says
  `has_error`, no child reports an error" and emits a
  `hidden missing token in <node>` entry.

The walker also descends into `ERROR` nodes instead of stopping at them, so nested
failures stay visible: the whole-file error in
`AutomorphicForm/Adelic/PeterssonSlabPairing.lean` now reports 508 nodes rather
than 1.

### 4.3 Chunked resync

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
| `Patching/PatchingConstruction.lean` | 378 | 367 | 374 |
| `ModularForms/WeightOne/EisensteinChiNegThree.lean` | 458 | 370 | 451 |
| `AutomorphicForm/Adelic/IsotypicCuspSpace.lean` | 124 | 61 | 123 |

Only 152 of 709 files still differ from the lexical baseline under `--resync`.
Every sampled mismatch is a declaration the line scan misses or one the grammar
cannot build a node for (§7), not a duplicate or a phantom: the chunks are
disjoint, and the parser emits no declaration whose start line is not a declaration
line. Resync has one known trade-off in the other direction: on
`GaloisRep/Defs/DeformationRingData.lean` the whole-file parse returns a *partial*
`structure` (header only, rows 19–23) while the chunk parse returns nothing, so
resync misses the one declaration that the tree half-recovers.

### 4.4 Statement vs proof

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

## 5. What still resists: mathlib notation

Counting error *nodes* is misleading here — nested `ERROR`s inside one swallowed
region multiply the count (35,687 nodes on the port, 4,440 of them missing
tokens). A declaration-level count says which notation is actually fatal. A
declaration "uses" a token when the token occurs in its source span, and is
"affected" when that declaration carries any parse error:

| token | declarations using it | with a parse error | rate |
|---|---|---|---|
| `‖ … ‖` (norm) | 692 | 441 | 63.7% |
| `⁄` (Kähler `Ω[F⁄K]`) | 517 | 514 | 99.4% |
| `⧸` (quotient) | 377 | 368 | 97.6% |
| `⟮ … ⟯` (adjoin brackets) | 163 | 160 | 98.2% |
| `∞` (`ℝ≥0∞`, limits) | 253 | 252 | 99.6% |
| `→₀` (finitely supported) | 186 | 184 | 98.9% |
| superscript/subscript `⁰`, `ᶠ`, `ʳ`, `ᵐ`, `ᵥ`, `₊` | 626 combined | 582 | 93.0% |
| `↥` (subtype coercion) | 648 | 512 | 79.0% |
| `⇑` (coercion) | 708 | 444 | 62.7% |

The norm row needs its own reading: 63.7% of norm-using declarations still have an
error, but only 10.0% of *norm-only* declarations have a statement error (down
from 52.8%), and the error is usually elsewhere in the proof. Norm is no longer a
blocker; the remaining statements are.

The rows from `⁄` to `→₀` are the blockers now: essentially every declaration that
mentions `⁄`, `⧸`, `⟮…⟯`, `∞` or `→₀` fails somewhere. `↥` and `⇑` are used in many
declarations that parse fine, so their rate is lower, but the absolute number of
affected declarations is still large (512 and 444).

The same test on the pin sample gives the same picture: `⧸` 109/109, `∞` 105/109
(96.3%), `↥` 239/322 (74.2%), `‖` 174/244 (71.3%), and `p2m_` 85/178 (47.8%, the
lowest rate of any construct measured). What differs between the corpora is the
*mix*: the pin also has 145k `p2m_*` command lines and 233k `attribute [-…]` lines
outside declarations, which is where its retention loss comes from.

There remain 4,960 declarations with a parse error whose span contains none of the
tokens above. Those are the command/tactic-syntax failures (`where` clauses,
`omit … in`, `set … with`, `classical`, structure-instance syntax) and pure
recovery artifacts whose error span starts after the culprit.

## 6. Text extraction vs tree parsing

An `ERROR` node says the *tree* failed to reduce; it does not mean the *text* is
unavailable. The extractor slices the source with byte offsets, so a statement can
be byte-exact even when its subtree is broken. Two boundary checks detect the
cases where the text is *not* byte-exact:

- **head**: the first non-space byte before `statement_start` must be `:`, the
  type colon. Anything else means the type field started mid-term and a leading
  token was dropped.
- **tail**: the first non-space bytes after `statement_end` must be `:=` or
  `where`. Anything else means the type field stopped early and the rest of the
  type sits in the gap before the body.

Cross-tab for the port with `--resync`:

| | statements | share |
|---|---|---|
| complete text, no error | 18,654 | 92.1% |
| complete text, error inside the type | 1,353 | 6.7% |
| text loss, no error (silent) | 182 | 0.9% |
| text loss, error flagged | 72 | 0.36% |

Text is complete for **20,007 / 20,261 (98.75%)**. The 254 losses split into 155
head and 99 tail (no overlap); **182 of the 254 are silent**. The normal path is
18,592 / 18,829 complete (98.74%), 237 losses (139 head, 98 tail), 167 silent.

Concrete cases:

- head loss, silent: `ModularForms/HeckeLattice.lean` `qCoeff_zero'` has type
  `qCoeff ⇑(0 : CuspForm …) n = 0`, extracted as `⇑(0 : CuspForm …) n = 0` — the
  leading `qCoeff` is dropped and the flag is `false`.
- tail loss, silent: `lean/FLTForHuman/AlgebraicCurve/Defs/Place.lean:117`,
  `def adicValuation : Valuation F ℤᵐ⁰ := …` extracts `Valuation F ℤ` with both
  flags `false`.
- loss + flag: `lean/FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean:948`,
  `K⟮t⁻¹⟯ = K⟮t⟯` extracts `K⟮t⁻¹⟯ = K⟮t`, `statement_has_error = true`.

So the two capabilities are:

- **Text extraction**: 98.75% of declarations yield a complete statement; 1.25%
  lose text at a boundary, and 182 of those are invisible to the error flag. A
  further 250 declarations (1.2%) never get a node at all (§7).
- **Full parsing of the statement's structure**: 1,425 statements (7.0%) contain
  an `ERROR`, so an AST consumer sees a broken subtree. The damage is usually
  local — coverage of the statement's bytes by `ERROR`/missing nodes:

| ERROR coverage of the statement | statements | share |
|---|---|---|
| 0% | 64 | 4.9% |
| < 5% | 558 | 42.3% |
| 5–25% | 538 | 40.8% |
| 25–50% | 60 | 4.5% |
| 50–90% | 7 | 0.5% |
| > 90% | 92 | 7.0% |

Median coverage **5.5%**, p90 33.3%, mean 13.9% (normal path, 1,319 error-flagged
statements with spans). The 92 statements above 90% are mostly declarations inside
a whole-file `ERROR`; for those the text is complete but the tree is effectively
unparsed.

Implication for consumers: statement text is usable for indexing, search, display
and similarity work at ≈98.75% coverage, but the boundary checks are mandatory —
the error flag alone catches only 72 of the 254 text losses. Dependency extraction
from the statement's *AST* is a stricter job: 7% of statements need a fallback
(lexical identifier scan over the text), and ~0.5% of all statements are
essentially unparsed even though their text is intact. The grammar fixes in §8
reduce both numbers by shrinking the `⧸`, `⁄`, `⟮…⟯`, `∞` error regions, not by
changing the extraction model.

## 7. Declarations the grammar cannot build at all

About 1.2% of declarations (250 of 20,511) have no `declaration` node in any
window, so even chunking cannot recover them. Examples:
`lean/FLTForHuman/WeierstrassCurve/GenusOnePlaceGateCentred.lean:38` still parses
as one `ERROR` spanning the whole declaration (`(module (ERROR …))`) because the
term after `:=` contains a structure-instance construction the grammar does not
accept. `AlgebraicCurve/RadialRegion/Engine/GridGeometry.lean` is 187/195 under
resync (the missing 8 are declarations whose headers contain `⟮…⟯`), and
`GaloisRep/Defs/DeformationRingData.lean` is the resync trade-off noted in §4.3.
(`ModularForms/WeightOne/Defs/PeriodPair.lean` has no declarations at all —
comments/imports only — so it is a non-issue.)

For these the options are a grammar fix or a lexical fallback that records name,
kind and line range but marks the statement as unreliable.

## 8. Recommendations

1. **Use `--resync` for any corpus index** (dependency extraction, statement
   search, theorem inventories). The normal path is fine for single-file
   diagnostics and gives cleaner `has_error` semantics, but its recovery can move
   when the grammar moves (the pin's 454 → 10 file).
2. **Do not treat a statement as trustworthy without both boundary checks.** 254
   statements (1.25%) lose text on the port; the error flag catches only 72 of
   them (28%), and 182 are silent. Check that the byte before `statement_start`
   is `:` and that the bytes after `statement_end` are `:=`/`where`. Add a
   `statement_complete` field to `Decl` and gate the reader on
   `!statement_has_error && statement_complete`.
3. **Patch the grammar's token set**, in descending value: `⁄`, `⧸`, `⟮`/`⟯`,
   `∞`, the superscript/subscript modifier letters (`⁰`, `ᶠ`, `ʳ`, `ᵐ`, `ᵥ`, `₊`),
   `→₀`, `↥`, `⇑`. The norm scanner from `916c44f` is the model: an external
   scanner can decide open/close from parser context. `⁄` alone is 517
   declarations at a 99.4% failure rate.
4. **Keep the `p2m`-free port as the parser test corpus.** It is a cleaner
   measure of grammar coverage: 92.0% of port files still emit errors, but almost
   none of those errors are FLT-specific commands — they are mathlib syntax that
   any Lean corpus would hit, and each grammar bump shows up directly in the
   statement-error rate.
5. Once (1)–(2) are in place, study 001's deferred next step — extracting
   identifiers from `body` and building the dependency index — is viable at
   ~98.8% declaration coverage.

## 9. Reproduction

The scan harness used a local, untracked scratch workspace (per-file JSON from
both paths, per-file `--errors` dumps, the comment/string-aware declaration
counter, and the comparison scripts). The parser is under `tools/parser`; its
grammar is symlinked from the `~/proj/tree-sitter-lean` clone at `916c44f`.
`moon test --target native` covers the new behaviour (statement/proof flags and
byte spans, resync coordinates, hidden missing tokens).

Commands used for the headline table (native build):

```bash
parser <file.lean> --json            # normal path
parser <file.lean> --json --resync   # chunked recovery
parser <file.lean> --errors          # ERROR + missing nodes, nested
```

Wall time for the 709-file port: 7.9 s for the normal path, 10.6 s for `--resync`
(one process per file, process startup included; the largest file, 192 KB, takes
0.10 s / 0.18 s).
