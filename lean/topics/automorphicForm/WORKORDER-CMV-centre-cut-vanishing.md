# WORKORDER-CMV — the centre-cut vanishing leaf

One set, one module, one headline. The mathematics and the landing record are in
[../../logs/centre-cut-vanishing.md](../../logs/centre-cut-vanishing.md); the column is
[../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3.

**Status: landed 2026-10-18.**

## 1. Scope

Port one pin proof file, whole:

| | |
|---|---|
| pin statement authority | `Theorems/Thm_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean` (26 lines) |
| pin proof | `P2M/Sol/S_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean` (902 lines) |
| net new math | **884 lines**, 51 declaration groups, 0 substitutions, 0 shared blocks |
| public surface | **one theorem**, at the wrapper's exact name and statement |
| expected checker delta | **+1** |

**Not this set:** the sibling `AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre`
(892 lines, the next cut); the rest of the centre-cut family
(`eq_of_isCuspConstituent_…`, `exists_setLIntegral_…`, the local-height rows); the
definition layer (`Cusp/Constituent.lean` and its transitive closure), which is frozen; any
consumer-side edit.

## 2. Deliverable

`FLTForHuman/AutomorphicForm/Adelic/Cusp/CentreCutVanishing.lean`:

* a docstring stating the mathematics — a continuous automorphic function at the production pins
  of a centre-cut Siegel cover is zero, and the disjoint-translates proof — and "transcribed from
  `P2M/Sol/S_…` (pinned `aa2d8b3`, 902 lines)";
* imports: only `FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent`, whose transitive closure
  contains every premise; no `import Mathlib`;
* `namespace AutomorphicForm`, with the helpers in `namespace CentreCutVanishing`;
* **one public theorem** at the wrapper's exact name
  `AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre`,
  statement copied binder for binder from the wrapper; **everything else `private`**;
* the pin's `p2m_exact_reverting` glue inlined; the pin's unused `toFun_unipT_mul` and
  `topNormSq_le_of_entries` dropped.

## 3. Reuse, do not re-prove

`port_advise` reports **0 substitutions / 0 shared blocks / 0 helpers already in the port**; the
whole file is one self-contained development. The premise module is already ported:

| pin module | port home |
|---|---|
| `Definitions/Def_AutomorphicForm_CuspidalConstituent.lean` | `FLTForHuman/AutomorphicForm/Adelic/Cusp/Constituent.lean` (183 lines, 21 declarations) |

Its transitive closure supplies `CoversModCentre`, `centreCutSiegelSet`,
`productionPinsOf`, `IsAutomorphicFnAt`, `lsXiMemberAt_iff`, `adelicGLHaar`, `glFin`,
`archDetNorm`, `xWindowSq`/`topNormSq`/`rowNormSq` and the rest; no promotion is owed
(the pin's helpers are `private` and no other target shares them).

## 4. Known drift (mathlib `v4.34.0`)

* `coe_mapGL_lowerUnip`: use `Matrix.ext`, a `change` to the `SpecialLinearGroup.map`
  coercion, `Matrix.SpecialLinearGroup.map_apply_coe`, then the four entries.
* `aC_unipAdelic`: `InfinitePlace.Completion` is a structure wrapping `v.1.Completion`; use
  `Matrix.ext` rather than `ext`, then for the `Function.update` entry ascribe the unfolded
  `Pi` type before `Function.update_self` (the `ArchSlab` device).
* deprecated renames: `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`,
  `Polynomial.finite_setOf_isRoot` → `Polynomial.finite_setOfPred_isRoot`,
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`.
* four narrow `set_option linter.style.haveILetI false in` suppressions on the declarations that
  introduce instances; the house-style narrow form, not a file-wide suppression.

## 5. Build discipline

* edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`;
* `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.Cusp.CentreCutVanishing`;
* no whole-tree build; no `sorry`/`admit`; no heartbeat override; no `import Mathlib`.

## 6. Wiring (manager)

Append to `spec/check_flt_statements.py`:

* `SOURCES`: the `Theorems/` wrapper and the `P2M/Sol/S_` file, last;
* `PORT_FILES`: `FLTForHuman/AutomorphicForm/Adelic/Cusp/CentreCutVanishing.lean`, last.

## 7. Results

* edit loop: **0 errors / 0 warnings**;
* `lake build`: **11 s**, 3,622 jobs;
* checker: **10,238 identical**, 0 mismatched / 0 missing; the module's wire is exactly +1;
* `#print axioms` on the headline: `[propext, Classical.choice, Quot.sound]`;
* `unwired_register.py --check`: current (no tier-3 surface);
* `git status`: the new module and the checker wiring only.

## 8. Successor

`AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre` (892 pin
lines) is now the natural next leaf of the family; it was already on the `--include-leaves` shelf
and is not part of this set.
