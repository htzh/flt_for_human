# Study 002 — MoonBit + Lean 4 toolchain notes (uncommon-tools field guide)

Date: 2026-09-04 · Companion to `001-tree-sitter-lean-validation.md`

Everything here was learned by building `tools/parser` from a fresh `moon new`
template to a working Lean 4 parser. Both toolchains are young, move fast, and
have thin documentation — these notes record the version of reality that
**actually worked** (moon `0.1.20260827`, feature flags `rr_moon_mod`,
`rr_moon_pkg`; `tonyfettes/tree_sitter@0.4.6`; tree-sitter runtime @ `8a15b881`;
Julian/tree-sitter-lean @ `f309609`).

---

## 1. MoonBit toolchain (`moon`)

### 1.1 Project layout and the module/package split

- A **module** = one directory with `moon.mod` at the root. A **package** =
  any directory with a `moon.pkg`. The root package *is* the module's default
  package; subdirectories like `cmd/main/` are separate packages.
- Both files exist in a legacy JSON form (`moon.mod.json`, `moon.pkg.json`)
  and a new "rr" TOML-ish form (`moon.mod`, `moon.pkg`). This project uses the
  new form. They differ in import syntax:
  - `moon.mod`: `import { "tonyfettes/tree_sitter@0.4.6", }` (versions pinned here)
  - `moon.pkg`: `import { "tonyfettes/tree_sitter" @tree_sitter, }` (no version;
    the alias after `@` is how you reference it in code as `@tree_sitter`)
- **Two-level import resolution (gotcha):** importing a package in `moon.pkg`
  fails with *"exists in global environment, but its containing module is not
  imported"* unless the *module* is also listed in `moon.mod`. Both levels are
  required.

### 1.2 Dependencies: mooncakes.io, the local registry, `.mooncakes/`

- `moon add user/pkg` resolves against `~/.moon/registry/index/user/pkg.index`
  (JSON-lines of every published version: deps, checksum, include-list) and
  downloads into `~/.moon/registry/cache/`. Vendored copies land in the
  project's `.mooncakes/` directory.
- **If `~/.moon` is read-only** (as in this sandbox), `moon update` and
  `moon add` fail — but builds work fine with already-cached packages, and you
  can add deps by hand-editing `moon.mod`'s `import` block (that's what we did
  for `tonyfettes/tree_sitter_language` and `tonyfettes/c`).
- Package docs/browse: `https://mooncakes.io/docs/<user>/<pkg>` (JS SPA; a 200
  response does **not** prove a package exists — check the registry index or
  `moon add`).

### 1.3 Build/test workflow

```bash
moon build --target native   # native|wasm|js; moon.mod preferred_target sets default
moon check --target native   # typecheck only, fast
moon test  --target native   # runs *_test.mbt (blackbox) + *_wbtest.mbt (whitebox)
moon run cmd/main --target native -- <args>   # args after --
moon info                    # regenerate pkg.generated.mbti interface files
moon fmt                     # formatter
```

- `moon build` only builds packages reachable from what it decides to build;
  an unreferenced new package may be silently skipped until something imports
  it (observed: our `tree_sitter_lean` package was ignored until `parser.mbt`
  imported it).
- Output: `_build/native/debug/build/...`; executables end in `.exe` even on
  Linux. Release: `--release`.
- **Warnings are build failures** in this configuration: a build can print
  `Failed with 6 warnings, 0 errors`. Fix every warning.
- The toolchain deprecates aggressively. Renames hit in one session:
  `derive(Show)` → `derive(Debug)`; `Option::or` → `unwrap_or`;
  `StringView::to_string` → `to_owned`; `BytesView::to_bytes` → `to_owned`;
  `Buffer::new()` → `Buffer()`; `@hashmap.new()` → `HashMap([], capacity=..)`;
  `options("supported-targets": ...)` → top-level `supported_targets = "..."`.
- `moon info && moon fmt` at the end, per `tools/parser/AGENTS.md`; watch the
  `.mbti` diff — no diff means no externally visible API change.

### 1.4 Language quirks that bit us

- **Block style:** top-level items are separated by `///|` comment fences;
  order is irrelevant.
- **Multiline strings** (`#|line` blocks) only in `let` bindings or
  parentheses — passing one directly as a call argument is deprecated. Wrap in
  `(...)`.
- **Escapes:** in `String`, `\x00` is deprecated → use `\u0000` (exactly 4 hex
  digits; `\u00` is an error). In `Bytes` literals (`b"..."`) `\x00` is fine.
- **`String` is UTF-16.** `StringView` offsets are UTF-16 code units. Any
  external system reporting **byte offsets** (tree-sitter!) must slice `Bytes`,
  not `StringView` — slice first, decode after. This is why the parser works
  on `Bytes` end to end.
- `let mut x = []` is *unused-mut* for arrays you only `.push()` into —
  mutability applies to the binding, not the contents.
- Optional labeled args: `old_tree? : Tree` defaults to `None` at call sites.
- Errors: `-> T raise` (any error) or `suberror Foo { ... } derive(Show)` +
  `raise Foo::Bar`; callers use `expr catch { err => ... }`. `main` can't
  raise — wrap a `run() -> Unit raise` and catch in `fn main`.
- Test blocks are `test "name" { ... }` and may raise; `abort(msg)` fails
  fast (there is no `fail` builtin).

### 1.5 The trimmed core library: no file IO

`~/.moon/lib/core` here has `env` (argv via `@env.args()`), `buffer`, `json`,
`encoding/utf8`, … but **no `fs`/`io` package**. File reading went through
`tonyfettes/c` (stdio): `fopen`/`fgets`/`fclose`.

### 1.6 C interop (native target)

- Declare: `extern "c" fn name(arg : T) -> R = "c_symbol_name"`; opaque C
  types as `#external pub type Foo` or `pub(all) struct Wrap(@ptr.Type)`.
- Compile C with the package: `options("native-stub": [ "parser.c", "scanner.c" ])`
  in `moon.pkg`; headers resolve relative to the package dir (symlinks work).
- `supported_targets = "+native"` in every package that (transitively) needs C,
  or you get warnings (which are errors, §1.3).
- `tonyfettes/c` gotchas:
  - Its `Borrow` trait passes **raw pointers without adding a NUL** —
    `fopen(path, mode)` needs explicit termination:
    `@stdio.fopen(@utf8.encode(path + "\u0000"), b"rb\x00")`.
  - No `fseek`/`ftell` — read files by looping `fgets` into a `@buffer.Buffer`
    (`write_bytes(BytesView)`, `to_bytes()`), sizing chunks with
    `@cstring.strlen`.
  - `#borrow(x)` annotations on externs keep MoonBit values alive across the
    FFI call.
- UTF-8 decode of slices: `@utf8.decode_lossy(bytes_view)` (lossy variant
  never raises — right for possibly-malformed source files).

---

## 2. Tree-sitter and the `tonyfettes/tree_sitter` binding

### 2.1 Two-layer design

- `tonyfettes/tree_sitter_language`: just `#external pub type Language` — the
  raw `TSLanguage*` a grammar's `tree_sitter_<lang>()` entry point returns.
- `tonyfettes/tree_sitter`: the real API — `pub(all) struct
  Language(@tree_sitter_language.Language)` plus `Parser`, `Tree`, `Node`,
  `Query`, `QueryCursor`, `Point`.
- Generated grammar packages (e.g. `tree_sitter_moonbit`) depend **only** on
  `tree_sitter_language` and are trivial:

  ```moonbit
  extern "c" fn tree_sitter_lean() -> @tree_sitter_language.Language = "tree_sitter_lean"
  pub fn language() -> @tree_sitter_language.Language { tree_sitter_lean() }
  ```

  plus `options("native-stub": ["parser.c", "scanner.c"])`. Consumers wrap:
  `@tree_sitter.Language(@tree_sitter_lean.language())`.

### 2.2 The big gotcha: the C runtime is not in the mooncakes package

- `tree_sitter/src/tree-sitter.c` starts with
  `#include "tree-sitter#lib#src#lib.c"`. That is a **literal filename**, not
  a path: upstream's `scripts/prepare.py` *flattens* the tree-sitter library
  (`lib/src/*.c`, `lib/include/...`) into the `src/` dir, mangling `/` → `#`
  and rewriting includes accordingly.
- The mooncakes tarball ships neither the runtime nor the script, so a naive
  `moon build --target native` dies with
  `fatal error: tree-sitter#lib#src#lib.c: No such file or directory`.
- Fix (now encoded in `tools/parser`): vendor the runtime
  (`third_party/tree-sitter/lib`, from the upstream submodule commit), symlink
  it to `.mooncakes/tonyfettes/tree_sitter/src/tree-sitter`, run
  `scripts/prepare.py` there. `.mooncakes/` is wiped by `moon clean` — the
  README has the re-setup recipe.
- ABI: binding's `LANGUAGE_VERSION = 15`; a grammar generated by an
  incompatible CLI raises `LanguageError::VersionMismatch` on `set_language`.

### 2.3 Parsing and the Node API

- `Parser::new()` → `set_language(lang)` (raises) →
  `parse_bytes(bytes, encoding=@tree_sitter.UTF8)` or `parse_string(view)`.
  Both keep the source so `Node::text()` works — but `text()` slices a
  `StringView`, so for Unicode-heavy sources slice `Bytes` yourself with
  `start_byte()`/`end_byte()` (§1.4).
- Navigation: `type_()`, `named_children()`, `named_child(i)`,
  `child_by_field_name("name")`, `field_name_for_named_child(i)`,
  `start_point().row()` (0-based), `parent()`.
- **Fields can be multi-node** (`type`/`body` in the Lean grammar). Walk
  `field_name_for_named_child` and take the span from the first match's start
  to the last match's end; `child_by_field_name` returns only the first.
- Errors never abort a parse: `root.has_error()`, `node.is_error()`. ERROR
  nodes are localized and the rest of the tree stays usable — extraction
  should record `has_error` per declaration instead of failing the file.
- Queries: `root.query("(declaration (theorem name: (identifier) @name ...))")`
  → `QueryCursor`; iterate `matches()` → `m.captures()` → `cap.name()`,
  `cap.node()`. Query compile errors (`QueryError`) point at the byte offset
  in the query string. Node/field names must match `node-types.json` exactly.

---

## 3. Lean 4 side: the grammar and the FLT corpus

### 3.1 tree-sitter-lean (Julian/tree-sitter-lean @ f309609)

- `grammar.js` (DSL) → tree-sitter CLI generates `src/parser.c` (**43 MB** —
  Lean's grammar is enormous; that's why we symlink instead of commit),
  `src/scanner.c` (external scanner), `src/node-types.json` (the schema:
  139 named node types), `grammar.json`.
- Externals (hand-written in `scanner.c`): `_scanned_ident`, `block_comment`,
  `doc_comment`, `raw_string`, `_indent`, `_dedent`, `_newline`,
  `error_sentinel` — Lean is layout-sensitive, so indentation is scanner
  state, like Python/Haskell grammars.
- Command structure (verified against `node-types.json` and real trees):

  ```
  source_file
  └── declaration                 (command; siblings: decl_modifiers, attributes)
      └── theorem | def | example | instance | abbrev | axiom | opaque
          | constant | inductive | structure
          ├── name: identifier        (required for theorem/def; absent on example)
          ├── level: ...              (universe levels, optional)
          ├── (binders ...)           (NAMED CHILD, not a field:
          │                          explicit_binder / instance_binder / ...)
          ├── type: <term>            (statement after ':'; multi-node field)
          └── body: <term>            (proof/definition after ':='; optional)
  ```

- Dotted names (`AddCommGroup.natCard_…`) are a **single** `identifier` node.
- There is **no `lemma` node type** — in Lean 4 `lemma` is sugar for
  `theorem`. None appeared in the 300-file FLT sample; if the grammar maps the
  keyword to `theorem` nodes nothing special is needed (unverified).
- `example` and anonymous `instance` have no `name` field → extractors must
  treat name as optional.

### 3.2 Grammar gaps found in the wild (FLT corpus)

Tree-sitter reports these as ERROR nodes; all counts from the study sample:

| Syntax | Example | Status |
|--------|---------|--------|
| `attribute [-foo] …` (erasure) | `attribute [-simp] bar` | biggest single gap (~50% of error nodes); one-rule fix in `grammar.js` |
| quotient notation | `R ⧸ I` | gap |
| norm notation variants | `‖x‖` | gap |
| coercion arrow | `↥U` | gap |
| `set … with hx` | tactic `with` clause | gap |
| custom macro commands | `p2m_open "…"`, `p2m_export …` | **unfixable in the grammar** — macros are Lean-side elaborations; accept ERROR nodes around them |
| misc notation | `∞`, `ᵁ`, `[κ]` | gap |

Mitigation that makes these tolerable: errors localize. A file with ERROR
nodes in `attribute` commands still yields its `theorem` with
`has_error: false` and a complete statement. Only proof text *near* an error
region can be partial.

### 3.3 FLT repository shape (`~/proj/fermats-last-theorem`)

- 60,478 `.lean` files. `Theorems/` — one theorem per file, small, cleanest
  parse rate. `Definitions/` — defs/structures. `P2M/Sol/` — generated proof
  solutions, up to 1.6 MB / 13k lines, heavy custom commands (`p2m_open`),
  hundreds of declarations per file.
- Mathlib is a lake dependency, **not vendored** (no `.lake/packages/` in a
  fresh clone) — validate on FLT's own files, not `mathlib/src/...`.
- Performance observed (debug build!): ~4 ms/file average, 1.6 MB file in
  0.215 s → full-corpus scan ≈ 4 min single-threaded. Parsing is not the
  bottleneck for this project.

---

## 4. The build recipe that worked (end to end)

```bash
# 1. Grammar binding package (one time, and after any grammar update)
mkdir tools/parser/tree_sitter_lean
ln -s ~/proj/tree-sitter-lean/src/{parser.c,scanner.c} tools/parser/tree_sitter_lean/
ln -s ~/proj/tree-sitter-lean/src/tree_sitter tools/parser/tree_sitter_lean/
#    + binding.mbt (extern fn) and moon.pkg (native-stub, supported_targets)

# 2. tree-sitter runtime (one time, and after every `moon clean`)
curl -L https://github.com/tree-sitter/tree-sitter/archive/8a15b881….tar.gz | tar xz
mkdir -p tools/parser/third_party/tree-sitter
mv tree-sitter-8a15b881*/lib tools/parser/third_party/tree-sitter/lib
cd tools/parser/.mooncakes/tonyfettes/tree_sitter
ln -sfn <abs path>/third_party/tree-sitter src/tree-sitter
python3 <abs path>/scripts/prepare.py        # creates src/tree-sitter#lib#src#*.c

# 3. Normal workflow
cd tools/parser
moon build --target native
moon test  --target native
moon info && moon fmt
```

Expected artifacts: `_build/native/debug/build/cmd/main/main.exe`
(~9.4 MB debug binary — the Lean parse tables dominate).

---

## 5. Pointers

- MoonBit docs: https://docs.moonbitlang.com · module/pkg config:
  `…/toolchain/moon/module.html`
- Binding: https://github.com/tonyfettes/moonbit-tree-sitter (README's
  Quickstart is accurate; the Development section is *required reading* —
  that's where `prepare.py` is documented)
- Tree-sitter C API: https://tree-sitter.github.io/tree-sitter/ (the binding
  is a thin wrapper; C docs apply)
- Grammar: https://github.com/Julian/tree-sitter-lean (`src/node-types.json`
  is the authoritative schema for extractors)
- Project-local: `tools/parser/README.mbt.md` (re-setup),
  `tools/parser/AGENTS.md` (MoonBit conventions)
