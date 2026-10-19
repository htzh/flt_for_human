# The centre-cut vanishing leaf — `AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre`

**Status: landed 2026-10-18.** One module,
`FLTForHuman/AutomorphicForm/Adelic/Cusp/CentreCutVanishing.lean` (939 lines,
one public headline + 48 `private` helpers), green with 0 errors and 0 warnings;
no `sorry`, no axiom beyond `[propext, Classical.choice, Quot.sound]`. The
module is listed (tier 1): its wire is exactly the one headline, checker
**10,238 identical**, 0 mismatched / 0 missing.

| | |
|---|---|
| statement | `AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre` |
| pin proof | `P2M/Sol/S_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean` (902 lines) |
| statement authority | `Theorems/Thm_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean` |
| scope | 902 raw lines → **884 net new math lines**, 51 declaration groups, 0 substitutions, 0 shared blocks |
| public surface | **one theorem**, statement copied binder for binder from the wrapper; the 48 helpers are `private` |
| FLT premises | only `Definitions/Def_AutomorphicForm_CuspidalConstituent.lean` (ported at `Cusp/Constituent.lean`), plus its transitive ported closure |
| build | edit loop 0 errors / 0 warnings; `lake build` 11 s (3,622 jobs) |
| register | current (`unwired_register.py --check`) — no tier-3 surface |

## 1. What the theorem says

Let `F` be a number field, `c u d₁ d₂ : ℝ` with `c ≤ 0 < d₁ < d₂`, and `T` a
finite set of adelic points. Let

```
W = ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂.
```

If `W` covers the centre of `GL₂(𝔸_F)` (`CoversModCentre F W`), then every
continuous automorphic function `φ` at the production pins of `W` is zero:

```
φ = 0.
```

This is the vanishing half of the centre-cut alternative. The non-vanishing
alternative is carried by the cuspidal-constituent machinery; this leaf is the
input that rules out a continuous automorphic function living entirely on a
centre-cut cover.

## 2. The proof

The pin's proof is the classical disjoint-translates argument, in three blocks.

* **`Generic` / `Completion` / `Unipotent` / `Window`.** The measure-theoretic
  kernel: if `f : G → ℝ≥0∞` is invariant under left translation by a sequence
  `γ`, then the integral of `f` over a set containing infinitely many disjoint
  translates of a positive-measure set `O` is `⊤`; the archimedean entries of
  `w.Completion` are compared through `extensionEmbedding`; the lower unipotent
  `lowerUnip n` and the window functions `xWindowSq`, `topNormSq`, `rowNormSq`
  supply the estimates.
* **`Adelic`.** The adelic bookkeeping: `aC w g` is the archimedean component of
  `g` at `w`; `unipT n` is the global lower unipotent; central rescaling
  `archRescale` moves an element into the determinant window `(d₁, d₂)` while
  keeping the finite component trivial; `xWindowSq_lowerUnip_mul_le` makes a
  sufficiently large lower-unipotent translate land in the centre-cut set.
* **`NullX` / `Core`.** `not_coversModCentre_of_u_eq_zero` rules out `u = 0`
  by a countable-avoidance argument on the lower-unipotent parameter, not by a
  measure statement. For `u ≠ 0`, assume `φ g₀ ≠ 0`; after a central rescaling
  and a small open neighbourhood `O` on which `φ` stays nonzero, the translates
  `γ k * O` are pairwise disjoint and contained in `W`; left invariance of `φ`
  makes `‖φ‖²` integrate to `⊤` over `W`, contradicting the `MemLp` half of
  `IsAutomorphicFnAt` (`lsXiMemberAt_iff`).

## 3. The port

`port_advise` reports **0 substitutions**, **0 shared blocks** and **0 helpers
already in the port**: the whole 902-line file is a single self-contained
development. It is transcribed whole, with two unused pin helpers dropped
(`toFun_unipT_mul`, `topNormSq_le_of_entries`) and the pin's `p2m_exact_reverting`
glue inlined. Everything except the headline is `private`, so the checker sees
exactly one declaration.

The import is only

```lean
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
```

— the port's home of the pin definition module. Its transitive closure already
contains every other premise (`CoversModCentre`, `centreCutSiegelSet`,
`productionPinsOf`, `IsAutomorphicFnAt`, `adelicGLHaar`, `glFin`,
`archDetNorm`, the window functions). No promotion was needed: the pin's helpers
are `private` and no other target file shares them.

## 4. Mathlib `v4.34.0` drift

Two proofs needed adaptation; both are statement-preserving.

* `coe_mapGL_lowerUnip`: the pin's `ext i j; simp [mapGL, lowerUnip]` no longer
  normalizes the `SpecialLinearGroup.mapGL` composite. The port uses
  `apply Matrix.ext; intro i j`, a `change` to the `SpecialLinearGroup.map`
  coercion, `rw [Matrix.SpecialLinearGroup.map_apply_coe]`, then the four
  `fin_cases` entries.
* `aC_unipAdelic`: `InfinitePlace.Completion` is now a structure wrapping
  `v.1.Completion`, so `ext` descends into `toCompletion` and the pin's final
  `rfl` no longer sees the adelic entry. The port first applies
  `Matrix.ext` (not `ext`), then closes the four entries with `rfl` or with the
  `ArchSlab.lean` device: ascribe the unfolded `Pi` type,
  `rw [show Function.update (0 : InfiniteAdeleRing K) w t = Function.update (0 : (a : InfinitePlace K) → a.Completion) w t from rfl]`,
  then `Function.update_self`.

The remaining renames are the recorded deprecations: `if_pos`/`if_neg` →
`ite_eq_left`/`ite_eq_right`, `Polynomial.finite_setOf_isRoot` →
`Polynomial.finite_setOfPred_isRoot`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`.
Four `set_option linter.style.haveILetI false in` suppressions are local to the
declarations that genuinely introduce instances (`Countable C`, `Countable K`,
`Countable (GL …)`, the measure/Borel instances of `no_function_of_ne_zero`);
they are the house-style narrow form recorded in `CARRY-FORWARD.md`.

## 5. What it buys

The node leaves the D-S `--include-leaves` demand. Its sibling
`AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre`
(892 lines) remains on the shelf and is the natural next cut; the rest of the
centre-cut family is unchanged. The module is listed in `PORT_FILES`, and its
wrapper and `S_` file are appended to `SOURCES`, so the headline stays
statement-diffed against the pin wrapper.
