# Research workflow behind the math/ notes

How the `math/` notes (001 WLOG normalization, 002 Frey curve/discriminant,
003 `GaloisRepIsIrreducible`) were researched, so future sessions can extend
them without rediscovering the plumbing. Writing/citation conventions are in
[../AGENTS.md](../AGENTS.md) and are *not* repeated here except as pointers.

## 1. Sources of truth, in order of authority

1. **The local clone**: `~/proj/fermats-last-theorem`, pinned at
   `anthropics/fermats-last-theorem@aa2d8b3` (main, 2026-09-03) — check with
   `git -C ~/proj/fermats-last-theorem rev-parse HEAD` before citing line
   numbers. PROOF-PATH.md sets the rule: "Where this prose and the Lean
   differ, the Lean is right."
   **Pin every line-number citation to a git version, never `/main`** —
   `/main` moves, so a line number is only meaningful against a fixed sha.
   Cite the sha (full or short) in the URL, e.g.
   `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean`
   (raw) and
   `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/html/route/s1.html`
   (blob). To re-pin: `git -C ~/proj/fermats-last-theorem rev-parse HEAD`,
   then update the sha in the notes and in `AGENTS.md`.
2. **The pinned mathlib**: after the first `lake build`, sources live at
   `~/proj/fermats-last-theorem/.lake/packages/mathlib` (note: project
   `.lake/`, *not* `~/.lake`). Its HEAD `db584cd6…` **is** tag `v4.33.0` —
   verified via the refs API (§3), so v4.33.0 URLs cite exact local line
   numbers. Before the build existed, mathlib was read over the web (§3).
   **`.lake/` does not hold all FLT artifacts**: a complete build is too
   massive. All Definitions are being built. Check what
   exists with `ls ~/proj/fermats-last-theorem/.lake/build/lib/lean/Definitions/`
   before assuming a `.olean`/`.ilean` is present.
3. **The repo's own generated docs**: `html/def/*.html` (per-module English
   glosses, declaration lists, "adapted from …" lineage, import/imported-by
   graphs), `html/route/*.html` (narrative), root `PROOF-PATH.md` (the
   four-theorem skeleton of `no_frey_package`). Read them *locally*; cite
   them *publicly* via `tianyipeng.github.io/fermats-last-theorem/…`
   (GitHub's 1000-file directory cap breaks `html/def/` browsing).
4. **Upstream ICL FLT** (`github.com/ImperialCollegeLondon/FLT`) for lineage:
   file headers + def pages name the source module (e.g. `Def_FLTPrelim_GaloisRep.lean`
   ← `FLT/EllipticCurve/Torsion.lean`); diffing against upstream shows what
   the port generalized (field `k` → tower `R → S → K`) and completed
   (`sorry` fields proved).

## 2. The question → note loop (worked example: math/003)

Question: "`GaloisRepIsIrreducible` takes a very general `Affine R` — why
does the application to the Frey curve even typecheck?"

1. **Grep the identifier in the local clone**, definition first, then all use
   sites. Whole-repo grep can time out — narrow to `Definitions/`,
   `Theorems/`, `P2M/Sol/`.
2. **Read the definition file whole.** A def inside `namespace` + section
   `variable`s is meaningless alone: the puzzling binder `(W' : Affine R)`
   only made sense with lines 21–23 (the `R S K` tower + instances), and the
   full name needs the namespace prefixes
   (`WeierstrassCurve.Affine.Point.GaloisRepIsIrreducible`).
3. **Classify every binder**: implicit (`{R}`, `{K}`) vs explicit — watch
   `variable (S) in`, which makes `S` the first positional argument — vs
   instance-implicit. At the use site, determine what pins each: unification
   from an explicit argument's type (`P.freyCurve : WeierstrassCurve ℚ` pins
   `R := ℚ` *because `Affine` is an `abbrev`*), a named argument
   (`(K := AlgebraicClosure ℚ)`), or typeclass synthesis (the whole
   `[CommRing]/[Field]/[Algebra]/[IsScalarTower]` tail).
4. **Find the non-synthesizable instance.** TC failed exactly once:
   `DecidableEq (AlgebraicClosure ℚ)` — required because mathlib's
   `AddCommGroup W.Point` sits under `variable [DecidableEq …]`
   (`Affine/Point.lean:656,782`), and an algebraic closure has no computable
   equality. The definition file itself appends a classical instance
   (`instDecEqAlgebraicClosureRat`, lines 81–83) — inherited from ICL.
5. **Cross-check the generated def page** (`html/def/FLTPrelim_GaloisRep.html`)
   — its English gloss independently confirmed the reading ("basis-free …
   A final instance supplies classical decidable equality").
6. **Write the note**, citing line numbers re-grepped from source at write
   time — never from memory.

Follow-up questions get the same loop (the "map into GL₂" aside: grep
`galoisRep`/`residualGaloisRepOf` → `DistribMulAction.toModuleAut` in
`Def_FreyPackage_GaloisRep.lean` → `ResidualGaloisRep` in
`Def_GaloisRep_Residual.lean`, whose `hcard : Nat.card E[p] = p²` hypothesis
is the formal content of `E[p] ≅ 𝔽_p²`; actual matrices never appear on the
Galois side — `GL (Fin 2)` is automorphic-side only).

## 3. Web recipes (when local artifacts are missing)

- **Repo tree**: `https://api.github.com/repos/anthropics/fermats-last-theorem/git/trees/main?recursive=1`
  — complete but ~1 MB and truncates in transit; prefer local `ls`/`grep`.
- **Single file at a rev/tag**:
  `https://raw.githubusercontent.com/<org>/<repo>/<rev-or-tag>/<path>`.
  404 = wrong path *or* moved file — e.g. mathlib's elliptic-curve files now
  live in `Affine/`/`Jacobian/`/`Projective/` subdirs; list a directory with
  `https://api.github.com/repos/<org>/<repo>/contents/<dir>?ref=<tag>`.
- **Tag ↔ commit**: `https://api.github.com/repos/leanprover-community/mathlib4/git/ref/tags/v4.33.0`
  returns the commit sha; compare with `git -C …/mathlib rev-parse HEAD`.
- **Line numbers in a big remote file without loading it whole**:
  `curl -s <raw-url> | grep -n <pattern>`.
- **Version pins**: `lake-manifest.json` (`inputRev`), `lean-toolchain`
  (Lean v4.33.1).

## 4. Gotchas that cost time (don't relearn)

- `WeierstrassCurve.Affine R` is an **`abbrev`** for `WeierstrassCurve R`
  (mathlib `Affine/Basic.lean:73–75`), not a new type — so no coercion is
  ever needed, and unification sees through it.
- Section `variable`s are part of a definition's type; export order after
  inclusion puts the `variable (S) in` argument first among explicit ones.
- The acting group is literally `K ≃ₐ[S] K` and the action is `Point.map` —
  no matrices anywhere in the irreducibility predicate.
- The four-theorem contradiction skeleton is in PROOF-PATH.md; the route
  pages (`html/route/s1…s5.html`) narrate the same with theorem links.
- `flt_for_human/AGENTS.md` is **not auto-loaded** when the agent session
  opens at the sandbox root — read it explicitly before writing notes.
  (Also saved in agent memory as `flt-math-note-conventions`, alongside
  `flt-moonbit-parser-toolchain` for the sibling parser project.)
- **The FLT clone may be mounted read-only.** `lake build` then fails with
  `failed to remove output artifacts: read-only file system` even for a
  module that otherwise compiles. Check with `findmnt -T ~/proj/fermats-last-theorem`;
  remount writable (or clone elsewhere) before building.
- **Building all of `Definitions/`**: a complete build is too massive, so
  build incrementally — walk `Definitions/*.lean` and `lake build` each
  module whose `.olean` is missing, skipping the rest. A helper script does
  exactly this (in `tools/`, which is gitignored and not published); the
  core loop is:

  ```bash
  for m in $(ls Definitions/*.lean | sed 's#.*/##; s/\.lean$//'); do
    [ -f ".lake/build/lib/lean/Definitions/$m.olean" ] || lake build "Definitions/$m.lean"
  done
  ```

  `lake build Definitions/<Module>.lean` builds a single module (and its
  deps); `lake build --help` lists the module/facet target syntax.

## 5. Writing checklist for a new math/ note

1. Header: companion links, one-paragraph scope, the `@aa2d8b3` pin (and the
   mathlib tag if mathlib lines are cited).
2. Numbered sections; quote Lean verbatim (≤ a screenful) with
   `[File.lean, lines a–b](raw-url)` links on first mention. Every
   line-number citation is pinned to the sha (`…/aa2d8b3/…`), never `/main`.
3. Key-point → code map table; Links section (raw Lean sources at the pinned
   sha, tianyipeng def/route pages, mathlib at the pinned tag, upstream
   background).
4. Math hygiene per AGENTS.md: `$`…`$` inline whenever in doubt (always for
   `E_P[p](K)`-shaped terms), `\\,` for thin space.
5. Do not commit — the user commits and pushes.
