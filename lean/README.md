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
lake build
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

## Layout

| module | topic | notes |
|---|---|---|
| `FLTForHuman/Basic.lean` | smoke test | toolchain and mathlib wiring only; no mathematics |
| `FLTForHuman/CountableModule.lean` | cardinality | a finite module over a countable ring is countable; number fields are countable. From [`Def_Mathlib_LinearAlgebra_Countable.lean`][src-countable] |
| `FLTForHuman/Elliptic/Basic.lean` | shared setup | base change preserves `IsElliptic`; the `W⟮S⟯` point-group notation |
| `FLTForHuman/Elliptic/Universal.lean` | universal curve | coefficients as indeterminates, `polyToField`, `ringEval`, `specialize`. Ported from `Def_WeierstrassCurve_EDSEngine.lean` |
| `FLTForHuman/Elliptic/DivisionPolynomial.lean` | `ω` extras | `invar`, `ψc` + `ψc_spec`, `invarNum`/`invarDenom`, `complEDSAux`, `redInvarNum`; the rest of the multiplication-formula bridge follows |
| `FLTForHuman/Elliptic/EDS.lean` | EDS plumbing | `map_invar*`, universal `Param` indices, `universalNormEDS`, `normEDS_eq_aeval` |
| `FLTForHuman/Elliptic/EllSequence.lean` | EDS relators | `addMulSub`/`rel₄`/`net` aliases to mathlib `atom`/`atomRel`/`rel`; `HaveSameParity₄`/`StrictAnti₄`/`avg₄` and the `transf` transfer lemmas; `IsEllipticSequence (normEDS b c d)` |
| `FLTForHuman/Elliptic/Complement.lean` | complement EDS | `normEDS_mul_complEDS` and `normEDS_mul_complEDS_div`: the complement witnesses `normEDS m ∣ normEDS (n*m)` |
| `FLTForHuman/Elliptic/RedInvar.lean` | `ω` denominator | `normEDS_six_eq_mul`, `redInvarDenom`, `invarDenom_eq_redInvarDenom_mul` |
| `FLTForHuman/Elliptic/Net.lean` | EDS net | `net_normEDS` (full `IsEllipticNet`), `invar_normEDS`, `invar₂_normEDS`, `redInvar_normEDS` |
| `FLTForHuman/Elliptic/Omega.lean` | `y`-numerator | `preΨ₄_add_Ψ₂Sq_sq`, `φ_mul_ψ`, `ωe` + `ωe_spec` + `two_mul_ωe` |
| `FLTForHuman/Elliptic/MulFormula.lean` | multiplication formula | evaluation at the universal point, `ψᵤ`, `smulX`/`smulY`, `zsmul_point_eq_smulX_smulY` |
| `FLTForHuman/Elliptic/JacobianMulFormula.lean` | projective form | `smulPoly`/`smulField`, `dblXYZ`/`addXYZ`, `zsmul_eq_smulEval` |
| `FLTForHuman/Elliptic/Bridge.lean` | torsion bridge | `evalEval_ψ_sq`, `evalEval_φ`, `smul_eq_zero_iff_evalEval_ψ` |
| `FLTForHuman/Elliptic/Fiber.lean` | counting | the Wronskian coprimality, the double-fiber engine, and **`card_torsion_of_isAlgClosed`** (`#E[n] = n²`) |

The port of `#E[n](K) = n²` (math/005) has its own working record:
[logs/card-torsion-port.md](logs/card-torsion-port.md) — dependency trace,
dropped clutter, and port order — with the reusable lessons (method, gotchas,
v4.34.0 API drift, and a checklist) in [porting-playbook.md](porting-playbook.md).

The next effort is scoped to definitions: [PORTING-FFG.md](PORTING-FFG.md) plans
the `ModularCurveX0/` library (the `jq` / `qExpand` / `qTwist` objects of
math/010) and records why the theorem itself is deferred.

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
[src-countable]: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Mathlib_LinearAlgebra_Countable.lean
