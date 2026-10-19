# The centre-cut vanishing leaf — `AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre`

**Status: landed 2026-10-18, refactored the same day when the sibling was cut.** The leaf first
landed as a self-contained 939-line module. The next leaf
([centre-cut-sibling.md](centre-cut-sibling.md)) shares the whole 645-line development, so the
shared block was extracted to `Cusp/CentreCutEngine.lean` (964 lines, 49 public declarations,
tier 3) and this leaf became a 64-line façade holding only its headline. Green with 0 errors and
0 warnings; no `sorry`, no axiom beyond `[propext, Classical.choice, Quot.sound]`. Checker after
the pair: **10,239 identical**, 0 mismatched / 0 missing.

| | |
|---|---|
| statement | `AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre` |
| pin proof | `P2M/Sol/S_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean` (902 lines) |
| statement authority | `Theorems/Thm_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean` |
| scope (first pass) | 902 raw lines → **884 net new math lines**, 51 declaration groups, 0 substitutions, 0 shared blocks within the target |
| final structure | 64-line façade + `Cusp/CentreCutEngine.lean` (49 declarations shared with the sibling) |
| public surface | **one theorem** here; the engine's 49 declarations are public tier 3 and registered |
| FLT premises | only `Definitions/Def_AutomorphicForm_CuspidalConstituent.lean` (ported at `Cusp/Constituent.lean`), plus its transitive ported closure |
| build | engine 9.7 s, façades 3 s; 0 warnings |
| register | 49 engine declarations with `-- pin:` provenance, current |

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
  `IsAutomorphicFnAt` (`lsXiMemberAt_iff`). This final contradiction is the
  engine's general lemma `no_function_of_ne_zero`, which takes `ξ`, `φ`, the
  automorphy hypothesis, continuity, and one point with `φ g₀ ≠ 0`.

## 3. The port, and the engine extraction

`port_advise` on the first target reported **0 substitutions**, **0 shared
blocks** and **0 helpers already in the port**: the 902-line file is a single
self-contained development. It was transcribed whole, with the unused pin
helper `topNormSq_le_of_entries` dropped and the pin's `p2m_exact_reverting`
glue inlined. Everything except the headline was `private`, so the checker saw
exactly one declaration.

When the sibling target was scoped, `port_advise` reported **46 of its
declarations already identical in the port — as `private` in this module**. The
two pin files share the whole 645-line block byte-for-byte; only the tail
differs. Rather than copy 636 lines or promote 46 declarations in place, the
block was extracted to

```lean
FLTForHuman/AutomorphicForm/Adelic/Cusp/CentreCutEngine.lean
```

(964 lines, 49 public declarations, `namespace AutomorphicForm.CentreCutEngine`,
each with a `-- pin:` marker). The module is unlisted (tier 3) and registered in
`spec/UNWIRED-PUBLIC.md`; the checker wires only the two façades. The general
`no_function_of_ne_zero` is in the engine and serves both headlines; the
sibling's pin-specific `no_realization_of_ne_zero` is not ported separately.

The engine imports

```lean
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
```

— the port's home of the pin definition module. Its transitive closure contains
every premise (`CoversModCentre`, `centreCutSiegelSet`, `productionPinsOf`,
`IsAutomorphicFnAt`, `lsXiMemberAt_iff`, `adelicGLHaar`, `glFin`,
`archDetNorm`, the window functions, and `SmoothCuspRealizationAt`).

## 4. Mathlib `v4.34.0` drift

Two proofs needed adaptation; both are statement-preserving and live in the
engine.

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
engine declarations that genuinely introduce instances (`Countable C`,
`Countable K`, `Countable (GL …)`, the measure/Borel instances of
`no_function_of_ne_zero`); they are the house-style narrow form recorded in
`CARRY-FORWARD.md`.

## 5. What it buys

Both centre-cut leaves leave the D-S `--include-leaves` demand:
this one and
`AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre`
(892 lines), which now shares the engine
([centre-cut-sibling.md](centre-cut-sibling.md)). The larger
`coversModCentre` silo
(`exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre`,
3,038 lines) is still behind the unit-factorizable chain recorded in
`CARRY-FORWARD.md`. The façades are listed in `PORT_FILES`, their wrappers and
`S_` files are appended to `SOURCES`, and the engine is registered tier 3.
