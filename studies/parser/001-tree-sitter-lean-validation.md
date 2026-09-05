# Study 001 — Validating the MoonBit + tree-sitter Lean 4 parser

Date: 2026-09-04 · Tool: `flt_for_human/tools/parser` · Status: **approach validated**
Toolchain field guide: `002-moonbit-lean4-toolchain-notes.md`

## Verdict

MoonBit + tree-sitter successfully parses FLT theorems and extracts structured
data (name, binders, statement, proof) with exact fidelity, Unicode included.
Throughput is ~4 ms/file (debug build), so a full FLT scan (60,478 `.lean`
files) takes ~4 minutes single-threaded.

## Setup (what it took)

- MoonBit binding: `tonyfettes/tree_sitter@0.4.6` (native target only).
- Grammar: vendored into `tools/parser/tree_sitter_lean/` as **symlinks** to
  `~/proj/tree-sitter-lean` (Julian/tree-sitter-lean @ f309609). `parser.c` is
  43 MB — symlinks avoid committing it.
- **Gotcha:** the mooncakes package of `tonyfettes/tree_sitter` ships without
  the tree-sitter C runtime. `tree-sitter.c` includes
  `tree-sitter#lib#src#lib.c`, a flattened file produced by the upstream
  `scripts/prepare.py`. We vendored the runtime
  (`third_party/tree-sitter/lib` @ submodule commit `8a15b881`) and re-ran the
  script. Re-setup steps are in `tools/parser/README.mbt.md`.
- `~/.moon` was read-only in this environment; no new mooncakes packages were
  needed beyond the already-cached ones.

## Extraction model (from the grammar's `node-types.json`)

```
source_file
└── declaration                 (command; also carries decl_modifiers/attributes)
    └── theorem | def | example | instance | abbrev | axiom | opaque | ...
        ├── name: identifier        (required except for example/anonymous instance)
        ├── (binders ...)           (named child, NOT a field; parameters + instance args)
        ├── type: <term>            (the statement after ':'; may span several nodes)
        └── body: <term>            (the proof/definition after ':='; optional)
```

Library slices raw UTF-8 bytes with tree-sitter byte offsets, decoding slices
to `String` only after slicing — immune to UTF-16/byte-offset mismatch on
Unicode-heavy sources (∀, ℤ, ×, ⟨⟩, …).

Query file: `tools/parser/queries/theorems.scm`:

```scm
(declaration
  (decl_modifiers)? @modifiers
  (theorem
    name: (identifier) @name
    (binders)? @binders
    type: (_) @statement
    body: (_) @proof))
```

Compiles cleanly against the grammar (verified by a test) and matches the
AST walker's output.

## First validation test (manual comparison)

Target: `Theorems/Thm_AddCommGroup_natCard_torsionBy_prod_eq_mul.lean` (12 lines, 1 theorem).

```lean
theorem AddCommGroup.natCard_torsionBy_prod_eq_mul
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] (N : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (A × B) (N : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) * Nat.card (Submodule.torsionBy ℤ B (N : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_natCard_torsionBy_prod_eq_mul.solution
```

| Field     | Manual read | Parser output | Match |
|-----------|-------------|---------------|-------|
| kind      | theorem     | `theorem`     | ✓ |
| name      | `AddCommGroup.natCard_torsionBy_prod_eq_mul` | same (single `identifier` node, dotted name intact) | ✓ |
| binders   | `(A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] (N : ℕ)` | byte-exact | ✓ |
| statement | `Nat.card … = Nat.card … * Nat.card …` | byte-exact, newline + indent preserved | ✓ |
| proof     | `by p2m_exact_reverting @…solution` | byte-exact | ✓ |
| location  | lines 9–12  | rows 8–11 (0-based) | ✓ |
| errors    | none        | `has_error: false` | ✓ |

No discrepancies. The custom tactic `p2m_exact_reverting` parses fine at term
level (treated as function application).

## Corpus sample (300 random FLT files)

- 617 declarations extracted: 548 theorem, 46 def, 12 abbrev, 8 instance, 3 structure.
- 1.15 s wall for 300 files (process startup included).
- Largest file (`P2M/Sol/S_LanglandsTunnell_…isHaarMeasure…lean`, 1.6 MB):
  403 declarations in 0.215 s.

## Parse errors: taxonomy and impact

234/300 sampled files contain ≥1 ERROR node, but **errors are localized**:
tree-sitter error recovery still yields complete `declaration` nodes, and the
affected commands are almost never the theorems themselves. Verified example:
a file with 4 ERROR nodes (all inside `attribute [-simp] …` commands) yields
its theorem with `has_error: false` and a complete 24-line statement.

Error causes, by frequency (first 60 sampled files):

| Cause | Count | Nature |
|-------|-------|--------|
| `attribute [-foo] …` (attribute erasure `-`) | 100 (+47 `]`) | **grammar gap** — fixable upstream |
| `⧸` (quotient notation `R ⧸ I`) | 38 | grammar gap |
| `‖…‖` (norm notation variants) | 31 | grammar gap |
| `↥` (coercion `↥U`) | 17 | grammar gap |
| `p2m_open "…"`, `p2m_export …` | ~18 | **custom FLT macro commands** — grammar can't know them |
| `set x : T := v with hx` | several | grammar gap (`with` clause) |
| misc (`:=`, `|`, `∞`, `ᵁ`, `[κ]`) | ~30 | grammar gap |

Impact by priority from `tasks.md`:

- **Parsing failures**: handled — tree-sitter never aborts; ERROR nodes are
  collected via `--errors` / `collect_errors()`, and `has_error` is recorded
  per declaration and per file. Statement extraction is unaffected in practice;
  proof text near an ERROR region may be partial.
- **Out-of-memory**: non-issue — 1.6 MB file parses in 0.2 s; peak RSS modest.
- **Timeout**: non-issue at these speeds (worst observed file: 0.2 s, debug build).
- **Unicode/UTF-8**: handled by byte-offset slicing (see above); round-trip
  test with `∀ ∃ ≤ ⟨⟩` passes.

## Known challenges going forward

1. The `attribute [-ident]` gap alone accounts for ~half of all error nodes —
  a one-rule fix in `~/proj/tree-sitter-lean/grammar.js` (then regenerate
  `parser.c` with the tree-sitter CLI). Worth upstreaming.
2. Custom FLT commands (`p2m_open`, `p2m_export`) are macros defined in
  `P2M/Util*`; the grammar will never parse them as commands. Acceptable:
  they sit between declarations and don't disturb theorem extraction.
3. No `lemma` node type exists — Lean 4 `lemma` is sugar for `theorem`; check
   how the grammar tokenizes it when it first appears in the corpus
   (the 300-file sample contained none).
4. Dependencies (tasks.md requirement) are not yet extracted. Cheap next step:
   collect `identifier` nodes under each decl's `body` field, filter against
   the corpus-wide declaration-name index.
5. `moon test --target native` — 5 tests, all passing.

## Next steps

- [ ] Batch mode: one process, many files → JSONL index of the whole corpus.
- [ ] Dependency extraction from `body` subtrees.
- [ ] Patch `attribute [-x]` + common Unicode notations in the grammar; measure
      error-node reduction on the same 300-file sample.
- [ ] Decide how to present `has_error` theorems to human readers
      (statement is still trustworthy; proof text may be partial).
