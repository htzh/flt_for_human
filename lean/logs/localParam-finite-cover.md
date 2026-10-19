# The local-parameter finite cover — landing record

The D-S cone's next leaf silo after the `normsq-lt` set:
`AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex`, the
857-line `S_` file `P2M/Sol/S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean`
(pin `anthropics/fermats-last-theorem@aa2d8b3`), ported to mathlib `v4.34.0` as
**two new modules, 30 statement-checked declarations, one public headline**. The
planning record is
[topics/algebraicCurve/TOPIC-localParam-finite-cover.md](../topics/algebraicCurve/TOPIC-localParam-finite-cover.md);
the order is
[topics/algebraicCurve/WORKORDER-LP1-localParam-finite-cover.md](../topics/algebraicCurve/WORKORDER-LP1-localParam-finite-cover.md).

This landing is the first in the column that uses the **new per-module statement
protocol** end to end (playbook §4, `spec/check_port.py`): neither module carries a
`PORT_FILES`/`SOURCES` entry, both carry `spec-pin:` lines in their header, and the
frozen `old_check_stmts.py` count is **unchanged**. It is also the first landing
where a whole module's internal engine — not only its headline — is
statement-checked: 30 declarations verified against the pin, for zero registry
maintenance.

## 1. What landed

| module | lines | public decls | wire (`spec-pin:`) | verdict |
|---|---:|---:|---|---|
| `FLTForHuman/AlgebraicCurve/Place/OrdCalculus.lean` | 218 | 13 | the pin `S_` file | 13 ok / 0 / 0 |
| `FLTForHuman/AlgebraicCurve/Place/FiniteCover.lean` | 654 | 17 | the `Theorems/` wrapper + the pin `S_` file | 17 ok / 0 / 0 |

`OrdCalculus.lean` is the **manager's pre-round**, not the silo: the thirteen
generic `Place` lemmas that the pin writes into the prelim section of all three
`localParam` `S_` files (five verbatim in both siblings, two more in one). Eleven of
the thirteen are re-proved in 3–40 pin files each (`ord_pos_of_mem_maximalIdeal` 32, `residue_algebraMap` 29,
`isRational_of_isCurveOver` 21, `evalAt_sub_algebraMap` 23,
`evalAt_eq_zero_of_ord_pos` 40, `ord_pos_of_evalAt_eq_zero` 40, …), so the module is
a dedup home as well as a prerequisite. The nine further prelim lemmas the port
already had are imported, not restated:
`Place.adicValuation_le_one_of_mem`, `Place.adicValuation_eq_exp_neg_ord`
(`Defs/Repartitions.lean`), `Place.mem_of_ord_nonneg`, `Place.ord_nonneg_of_mem`
(`Defs/PushPull.lean`), `Place.evalAt_algebraMap`, `Place.evalAt_mul`
(`Defs/PlaceEvaluation.lean`), `Place.evalAt_zero`, `Place.ord_sub_evalAt_pos`
(`Defs/PlaceCalculus.lean`), `Place.ord_algebraMap` (`Defs/Place.lean`).

`FiniteCover.lean` is the silo: `sum_support_eq_zero`, the two analytic lemmas
(`exists_analyticAt_pow_eq`, `exists_finset_preimages_of_meromorphicOrderAt_eq`),
the `structure Fam` and its eleven lemmas, `Fam.exists_finset_cover`, and the
headline at the wrapper's name and text.

## 2. Measured

Every number below is the tree this landing leaves.

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Place/OrdCalculus.lean \
                                   FLTForHuman/AlgebraicCurve/Place/FiniteCover.lean
# 30 ok, 0 mismatch, 0 missing, 0 own — 2 module(s), 2 checked, corpus aa2d8b3
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.FiniteCover
# Build completed successfully (3295 jobs)
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/AlgebraicCurve/Place/FiniteCover.lean     # no output: 0 warnings
timeout 280 python3 spec/old_check_stmts.py
# 10473 identical (774 promoted, 83 renamed), 0 mismatched, 0 missing,
# 42 own-proof exempted, 294 registered-unwired exempted (10809 checked)
python3 spec/unwired_register.py --check          # register is current
```

* **The frozen checker is unchanged**: 10473 before the landing and 10473 after.
  That is the check that nothing was wired the old way. (The note's 10476 figure
  predates the `CommTriplet` handoff of commit `610b73d`, which moved that module's
  three headlines to the new checker: 10476 − 3 = 10473.)
* **`#print axioms`** on the headline, on `Fam.exists_finset_cover`, on `Fam.fibre`
  and on `exists_finset_preimages_of_meromorphicOrderAt_eq`:
  `[propext, Classical.choice, Quot.sound]` each.
* **Grep sweep** of both modules for `sorry` / `admit` / `axiom` /
  `native_decide` / `import Mathlib` / `maxHeartbeats`: zero. Two `set_option`s only:
  `autoImplicit false` and the narrow `linter.unusedVariables` on the headline
  (`hfg` is in the statement and unused in the proof — the pin suppresses the same
  linter for the same reason) plus one narrow `linter.style.haveILetI` on
  `isRational_of_isCurveOver` (its two `haveI`s are load-bearing: `Module.Finite`
  and `Algebra.IsIntegral` feed `IsAlgClosed.algebraMap_bijective_of_isIntegral`).
* **`git status --short`**: the two new modules and the two new notes; no tracked
  file edited.

## 3. Friction and deviations

1. **`port_advise`'s "already in the port" reading was a binder-text artefact — and
   the instrument is now shape-based (2026-10-19).** As it stood, the tool reported
   **0** substitutions and `port_plan` **832** net new lines, because it asked for
   byte-identical *text* while the port's `Defs/` copies of the nine prelim lemmas
   were homed from the pin's `Theorems/` wrappers (`{K F : Type*} [Field K] … (v :
   Place K F)`) and the pin's `S_` rows are the section-variable spelling
   (`(v : Place K F) {f : F} …`). Verified on three of them: the port's
   `Place.mem_of_ord_nonneg`, `Place.evalAt_mul`, `Place.ord_algebraMap` are
   statement-hash identical to the pin's `Thm_AlgebraicCurve_Place_*` rows and
   different from this file's `S_` rows. The pin is not textually self-consistent —
   `mem_of_ord_nonneg` occurs 263 times in **33** distinct texts, `ord_nonneg_of_mem`
   315 / 38 — so "byte-identical" was never the right test for a reuse decision.

   The instrument now answers the question it is asked (`tools/deps/port_advise.py`):
   a **shape tier** beside the byte tier — same conclusion and same *hypothesis
   multiset* after dropping the section/instance plumbing (`{X Y : Type*}`, `[…]`),
   normalising the binder mode (`{n : ℕ}` against `(n : ℕ)`) and alpha-renaming the
   bound names — plus a **residue** list for the pairs whose binder skeletons do not
   line up at all (one side leaves the variable in a file-level `variable`), printed
   as a pointer, not a verdict. `--selftest` covers all three normalisations and
   checks that the hypothesis list is *not* normalised away (a weaker statement must
   not match a stronger one). Re-run on this file with the two new modules removed
   from the port corpus (a shadow root): **6 shape matches + 1 port-`private` +
   4 residue pointers**, i.e. all nine reuse cases surface, where the byte tier alone
   said *none*. `port_tier` is also read from the module's own `spec-pin:` line now,
   so a wired module is no longer labelled "tier 3, registered".

   The lesson that outlives the fix: **the reuse decision is a shape question and the
   checker's question is a text question.** You import the shape match and you never
   restate it; if a module must restate one, it must use the pin's text shape, which
   is what `spec/check_port.py` hashes.
2. **Section-variable shape is now a checking constraint, not a style choice.**
   Because `spec/check_port.py` hashes the statement *text*, a new module must
   transcribe the pin's `variable {K F …}` shape; a restated lemma with explicit
   binders would be a `MISMATCH`. This is the one house-style rule the new
   protocol adds. It is recorded in the topic note and the module headers.
3. **New modules need no registry entry, and must not get one.** Both modules are
   wired by their `spec-pin:` lines. The frozen checker's `PORT_FILES`/`SOURCES`
   were not touched, its count is unchanged, and `spec/UNWIRED-PUBLIC.md` is not
   involved (neither module is tier 3).
4. **The mathlib drift was small.** `exists_analyticAt_pow_eq` and the analytic core
   of `exists_finset_preimages_of_meromorphicOrderAt_eq` accepted the pin's proofs
   unchanged on `v4.34.0` (`meromorphicOrderAt_eq_int_iff`,
   `HasStrictDerivAt.localInverse`, `map_nhds_eq`, `nthRoots`, `card_nthRoots`,
   `nthRoots_nodup`, `Complex.isPrimitiveRoot_exp`, `Complex.slitPlane`). The only
   proof-side edits were seven deprecated `if_pos`/`if_neg`/`dif_pos`/`dif_neg`
   → `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right` renames, taken to
   reach 0 warnings. The port's `Defs/` closure carries no analysis at all
   (`AnalyticAt`, `MeromorphicAt`, `Complex.log`, `localInverse` are unknown there),
   so the module adds five specific mathlib imports; no `import Mathlib`.
5. **`hfg` is dead in the proof.** It is in the statement (the pin's, and the
   wrapper's) and used by no step; the port keeps it. The suppression is narrow.

## 4. What is on the shelf now

The landing leaves the two sibling `localParam` rows — both now shorn of the
prelim block (they can import `Place/OrdCalculus.lean` and, for the branch
uniqueness, `Fam`/`exists_finset_cover`):

* `AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex` (500 pin
  lines) — uniqueness of the analytic branch through a complex place;
* `AlgebraicCurve.Place.exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex`
  (1,142) — the chart's order/`meromorphicOrderAt` compatibility.

Their common capstone is
`AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex`
("the places of a complex function field form a compact Riemann surface"), which
also needs `exists_forall_ord_eq`, `exists_ord_eq_one`,
`connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex` (28 nodes
below it) and `exists_strictMono_forall_tendsto_evalAt_complex`. None is ready.

## 5. Reproduce the scope

```bash
cd tools/deps
python3 frontier.py --ds --include-leaves --rank-by silo --top 0   # the leaf's row and its siblings
python3 frontier.py --ds --rank-by silo --ready --top 0            # 85 candidates today
python3 port_advise.py --target AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex
python3 port_plan.py --json build/localParam_advise.json
```

With the corpus: `rg -n 'exists_finset_forall_exists_localParam_eq_complex' tmp/flt-statements/statements.tsv`
gives the file's 39 rows, and `python3 spec/statement_db.py show <name>` a single
signature. `tmp/port_index.py` (git-ignored) is the ad-hoc port-side statement
index this round used to find the nine existing copies: `python3 tmp/port_index.py <pin-file>`.
