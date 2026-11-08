# SET-AF24 — the `𝔰𝔩₂`-string decomposition at a complex place

**Status: DISPATCHED 2026-11-07** — two orders on two new modules, run in parallel; §7 is the
forecast and §8 records the landing at review. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF23 left. It is the **twenty-fourth** `AutomorphicForm`-serving set, and the one SET-AF23 §5
named by hand ("the `su(2)`/circle-weight string, the largest single leaf left on the shelf").

**4 rows / 2,016 silo / 1,314 net new math lines (`port_plan`) / 88 declaration groups**, of which
**575 lines are one prelude the pin copies into two files** and 34 lines are already in the port.

| row (`AutomorphicForm.` dropped) | silo | prem | lev | block | what it says |
|---|---|---:|---|---|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 0 | 3/4 | leaf | the three complex derivatives preserve `Y`; the flows `iH`, `rotR`, `rotS` differentiate `y (g * ·)`; a `D`-invariant submodule is flow-invariant; `Y` splits into circle-weight `iH`-eigenvectors |
| `exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex` | 908 | 1 | 1/1 | *off-shelf* | `Y` has a basis of `𝔰𝔩₂` strings: independent `x s p`, highest weights `n s`, `D₀ x = i(n−2p)·x`, raising/lowering with the `p(n+1−p)` coefficient, and circle weights |
| `hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero` | 169 | 1 | 1/1 | *off-shelf* | a vector killed by all three derivatives has trivial archimedean character (`HasArchCharacterAt₀ F w 1 x`) |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 0 | 1/1 | leaf | a flow that preserves a finite span with prescribed derivative data has a coordinate matrix `E`, `E 0 = 1`, `E'(0) = M`, `x p (g • k s) = ∑ E s p' p · x p' g` — the rotation flow's matrix form |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af24.json
python3 build/af-return.py build/shelf-af24.json AutomorphicForm. 300      # per-row readiness return
python3 frontier.py --ds --selfcheck
```

SET-AF23's post-landing read, reproduced exactly on this tree:

| figure | value |
|---|---|
| `needed [F terminal]` | **795 nodes / 335,379 lines** |
| `needed [literal]` | 807 / 338,844 |
| frontier F | 1,621 / 791,997 |
| ready block | **72 rows / 24,200** — 44 `AutomorphicForm` rows / 18,061 |
| leaves block | **212 rows / 55,301** — 47 `AutomorphicForm` rows / 10,181 |
| `AutomorphicForm` demand | 304 / 135,084 |
| `--selfcheck` | PASS (1,440 sources / 1,621 names) |
| `--unport` corrections | **none** (the FR-0095 shadow was retired by SET-AF5) |

**The withheld block is non-empty, and it is not this column's work:** 4 rows, the two `ModularCurve`
Tate-module rows (327 + 283) whose direct premise is `AlgebraicCurve.Pic0.abelJacobiCard_genus`, and
the two `AlgebraicCurve` rows (126 + 95) whose premises are the path-period lattice. They are the
prunable complex-analytic subject (recipe §0); named here, deferred, not cut.

**Both blocks are quoted — and the correction is part of the record.** The four rows are **two
leaves** (755, 184 = 939 silo) and **two rows that are on neither block**: 908 and 169 are one edge
behind the leaf 755 (each `needed = 2`), so the shelf omits them and `af-return.py` is what prices
them (755 readies exactly 1,077 = 908 + 169). The first draft of this brief called that pair "ready
rows" — it had taken the pairing from SET-AF23 §5's prose instead of from the JSON's block
membership. The set therefore **touches the ready block not at all** (it leaves it at 72 / 24,200)
and takes 2 leaves + 2 off-shelf rows; a brief that read only the ready block would have priced the
set at 0 silo.

## 1. The price

```bash
python3 port_advise.py --nodes AutomorphicForm.su2Derivs_… --nodes AutomorphicForm.exists_su2Strings_… \
  --nodes AutomorphicForm.hasArchCharacterAtZero_one_… --nodes AutomorphicForm.exists_coordMatrix_… \
  --json build/af24-advise.json
python3 port_plan.py --json build/af24-advise.json
```

| figure | value |
|---|---|
| raw `S_` lines | 2,016 |
| declaration lines | 1,923 |
| — duplicate copies | 575 |
| — boilerplate | 93 |
| distinct declaration groups | 88 |
| already in the port (vetted) | 34 |
| **net new math lines** | **1,314** |

**The duplication is the story** (`port_advise` §2): 55 names / 576 lines are proved in **both** big
pin files — `hasCircleWeightAt_of_eigen` (31), `maxGenEigenspace_le_eigenspace` (30), `ker_sq_le`
(29), `eigen_sum` (23), `scalar_ode_forced` (23), `D_mem` (22), and 49 more. This is the recipe's
§2 first signal: one engine and two statements, written once. Both files are 755 / 908 lines and 576
of them are the shared block, so the two headlines themselves are ~180 and ~330 lines. Measured
directly: the two blocks (`:22-274` of the 755 file, `:27-279` of the 908 file, 253 lines each) are
**byte-identical apart from the block label** — `diff` reports 2 differing lines, `KStabAux` vs
`RepCoreKS` — so this is a literal copy, not a near-duplicate, and the saving is the whole block.

**Substitutions** (6 rows, all read): `rotGL → AutomorphicForm.IwasawaChartComplex.rotR`
(binder-spelling; the port's is a `GL` element and the pin's `rotGL` is one too — use it, do not
restate) and the four `D0`/`D1`/`D2 → AutomorphicForm.OsAlg.Dk` rows, which are the parser's
type-only `def` false positives (a `def … : (G → ℂ) → (G → ℂ)` has type `→` whatever its body), i.e.
**ignore them**.

**No definition gate.** `gate_scan` over the four wrappers' `Def_` closure —
`Def_AutomorphicForm_IsotypicCuspSpace` (2–9 used), `Def_AutomorphicForm_ArchDerivCasimirComplex`
(2–9), `Def_AutomorphicForm_ArchDerivCasimirComplexAPI` (0–13), `Def_AutomorphicForm_ArchWeightCharTransport`
(0), `Def_AutomorphicForm_CuspidalConstituent` (0) — reads **0 missing on every row**. The `𝔰𝔩₂`,
circle and character vocabulary all landed in the AF6–AF13 waves. `twin_scan --node`: **`new`** four
times.

## 2. Why these four — the return, honestly

`build/af-return.py` (per-row readiness return) says the top three AF rows by return are

| row | silo | readies | 1-hop |
|---|---:|---:|---:|
| `su2Derivs_…` | 755 | **1,077** (its own two successors) | 0 |
| `CuspidalSpectrum.exists_isLift_rightConv` | 199 | 1,055 | 702 |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 552 | 0 |

So `su2Derivs` is the shelf's best single buy, and it readies exactly the two off-shelf rows this set
takes with it. **After the set, zero rows become ready** (measured by `build/af24-return.py`: the four rows are
each other's only missing premises). That is not a defect of the cut but its shape: this is the head
of a chain, and the honest statement is *what it leaves one or two premises short*:

- `CuspidalConstituent.exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex` (458) goes from
  **6 premises to 2**: `CuspidalConstituent.isArchSmoothAtComplex_and_continuous_foldr_archDerivAtComplex_of_mem_cut`
  (87) and `CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent`
  (123) — i.e. the `isCuspConstituent` cluster, which is the natural AF25 (§9).
- The four rows are one subject, and `port_plan`'s topological order puts them in two layers: 755 and
  184 at layer 0, 908 and 169 at layer 1 — the pin proves them in that order (the other three `S_`
  files import `Thm_…su2Derivs`).

The second candidate by return, `CuspidalSpectrum.exists_isLift_rightConv` (199, return 1,055 + 702
one hop), is the carrier-operator story deferred by name from SET-AF22/AF23 — a *different* subject
(the cuspidal lift of `rightConv`), so it is named and deferred (§9). The third,
`exists_sum_prod_mul_of_rightTranslatesSpanFinite` (576), is the span-of-right-translates block.

## 3. Homes

Two new modules, no insertion, no cascade, no legacy module touched:

| module | holds | why there |
|---|---|---|
| `Adelic/Su2Strings.lean` | the 55-declaration shared prelude, `D0/D1/D2` and the ten linearity lemmas, the three `𝔰𝔩₂` commutators, and the three headlines | above `ArchDerivCasimirComplexAPI` (the vocabulary), `ArchCasimirComplex` (the commute table) and `LinearAlgebra/Eigenspace/Sl2Strings` (the abstract string basis); it is a *consumer* of all three |
| `Adelic/ArchRotCoordinate.lean` | `exists_finsupp_dual`, `engine` and the coordinate-matrix headline | the rotation flow's matrix form is a subject of its own; the engine is generic (`[Monoid G]`, arbitrary `Fin`-indexed family) and the headline is its instantiation at the two rotations |

`ArchRotCoordinate` is deliberately **not** folded into `Su2Strings`: it is layer 0, independent of
the prelude, and folding it in would make two subjects share one file and one worker. It is
deliberately **not** inserted into `ArchCasimirComplex.lean` (the complex-place `𝔰𝔩₂` calculus, 2,124
lines, three in-tree importers) because the row is a leaf with no consumer in the port yet, and a new
module is cascade-free (recipe §5: a new module is a price, not a preference).

## 4. The manager's layer

1. **Scaffolding, checker-green before dispatch.** `Su2Strings.lean` carries the three headlines
   verbatim from their wrappers and `sorry` bodies: `check_port --force` reads
   **3 ok / 0 mismatch / 0 missing**. `ArchRotCoordinate.lean` carries its headline the same way:
   **1 ok / 0 / 0**. The statements are frozen; a worker may not touch them.
2. **One promotion.** `apply_mul_archFlowAtComplex_eq` (28 lines, the "a vector killed by `d`'s
   derivative is constant along `d`'s flow" engine) was `private` in `ArchCasimirComplex.lean` while
   the pin states it **publicly** in two files (`…_hasArchCharacterAtZero_one_…:27`,
   `…_apply_mul_archComplexGLAt_eq_…`). Promoted to public at the pin's name
   (`AutomorphicForm.InvZeroC.apply_mul_archFlowAtComplex_eq`) and the 169 row's `S_` file added to
   that module's wire. Measured: 106 → **107 ok / 0 mismatch / 0 missing**, module rebuild **12 s**,
   dependent cascade 3 modules / 1,016 lines (`build_ladder --edit`, ≈38 s). The 169 row imports it
   instead of restating it.
3. **Wires.** Both new modules carry their `spec-pin:` lines (`Theorems/` wrapper + `S_` file per
   row) — the checker, not per-declaration markers (playbook §5).

## 5. The cut, and the gates

Two orders, dispatched together on **disjoint files** (no hub is edited by either; the only shared
thing is the build lock):

- `lean/tmp/WORKORDER-AF24A-su2-strings.md` — `Adelic/Su2Strings.lean`: the prelude first, then
  `su2Derivs` → `exists_su2Strings` → `hasArchCharacterAtZero_one` (§5 of the recipe's gates);
- `lean/tmp/WORKORDER-AF24B-rot-coordinate.md` — `Adelic/ArchRotCoordinate.lean`: the two generic
  lemmas then the headline.

Each order carries the build ladder (low-cap edit loop, `flock` + `timeout` per module build, never a
tree build), the axiom gate, the silence gate, `dedup`/`move_dead`, and its own consumer zone
(`spec/AutomorphicFormSetAF24{A,B}Consumer.lean`) with a real cross-module composition and no
`#check`s.

## 6. Verification of the dispatch

| gate | A | B |
|---|---|---|
| scaffold `check_port --force` | 3 ok / 0 / 0 | 1 ok / 0 / 0 |
| scaffold elaboration | 1 s (`lake env lean`) | 1 s |
| definition gate (`gate_scan`) | 0 missing (5 `Def_` modules) | 0 missing (2 used) |
| twin (`twin_scan --node`) | `new` | `new` |
| axioms / silence / dedup / consumer | the order's §6 | the order's §6 |

## 7. Forecast

| figure | before | forecast | **actual (re-read)** |
|---|---|---|---|
| `needed [F terminal]` | 795 / 335,379 | 793 / 333,363 | **791 / 333,363** |
| `needed [literal]` | 807 / 338,844 | 805 / 336,828 | **803 / 336,828** |
| frontier F | 1,621 / 791,997 | 1,625 / 794,013 | **1,625 / 794,013** ✓ |
| ready block | 72 / 24,200 | 70 / 23,123 | **72 / 24,200** (untouched: the set took nothing from it) |
| leaves block | 212 / 55,301 | 210 / 54,362 | **210 / 54,362** ✓ (−2 / −939) |
| `AutomorphicForm` demand | 304 / 135,084 | 302 / 133,068 | **300 / 133,068** |
| rows readied | — | 0 | **0** ✓ |

Two forecast errors, both worth carrying. The **line** column was exact on every row. The **node**
column was wrong on two rows because it was computed as if a set removed half its rows from the
demand: `needed`/demand lose **one node per landed row** (795 − 4 = 791, 304 − 4 = 300). And the
**ready-block** row was wrong because two of the four rows were never *on* the ready block (§0): the
forecast subtracted 1,077 silo that the block never held.

The per-row return column is the column's standard underestimate (FR-0106), so the re-read must be
reported as it is, not as forecast: what the set should deliver is the **458 row's move to 2
premises**, not a new shelf row.

## 8. The landing

| order | module | result |
|---|---|---|
| **A** (landed 2026-11-07) | `Adelic/Su2Strings.lean` | **1,207 lines / 81 declarations** (57-declaration prelude + `D0/D1/D2`, the ten linearity lemmas, `comm01/02/12`, the 169-file helpers, three headlines); **81 ok / 0 mismatch / 0 missing**; silent, zero warnings; axioms `[propext, Classical.choice, Quot.sound]` on all three; `dedup --within` **0 clusters / 0 removable**; `move_dead` 0; consumer `spec/AutomorphicFormSetAF24AConsumer.lean` **0 errors** |
| **B** (landed 2026-11-07) | `Adelic/ArchRotCoordinate.lean` | 223 lines / 3 declarations; **3 ok / 0 mismatch / 0 missing**; silent, zero warnings; axioms `[propext, Classical.choice, Quot.sound]`; `dedup --within` 0 clusters; `move_dead` 0; consumer `spec/AutomorphicFormSetAF24BConsumer.lean` **0 errors** |

**A's measured shape.** 1,062 declaration lines over 81 declarations, against a 1,314-line budget:
the prelude came in at **549 lines / 57 declarations** (the order said 576 / 55 — the count is the
`port_advise` name count, the line count the block's own), written once and checker-`ok` at every pin
last name. The pin's two copies are byte-identical (engine block 248 lines, complex-place block 301),
which is what made the dedup saving real: 575 lines not written. Headline sizes: 126 / 206 / 66.

**A's deviations** (bodies only; every statement byte-identical, checker-confirmed; recorded in the
module header): `rotR/rotS/rotR'/rotS'` literals written `![![…], ![…]]` because v4.34's `!![…]` at a
function type goes through `Matrix.of`'s coercion (the same drift FR-0149 records from the other
side); four simp lists lose one v4.34-unused argument; `rot_det` by `exact det_rotR b`; `haveI` →
`have` for a Prop-valued `FiniteDimensional`; and the 169 headline's unused `h2` referenced once
(`linter.unusedVariables`, not silenced).

**A's one known twin.** `archDerivAtComplex_sub'` is re-stated locally (pin `S_…su2Strings…:615`)
because the checker needs a public declaration at the pin's name in *this* module's wire; the public
`AutomorphicForm.ArchCxGL.archDerivAtComplex_sub'` exists in `ArchCasimirComplex.lean`. It is the
pin's own duplication, and `dedup --within` correctly does not count it — a `dedup --cross` cluster
to keep with that reason.

**B's measured shape.** Net new math **175 lines** over 3 declarations (pin 184 → port 223 with
header/namespace scaffolding). The two *generic* lemmas needed no adaptation at v4.34 bar two
deprecation tokens (`if_true` → `ite_true`, pin `:87`/`:103`); whitespace-normalised, the whole pin
block is character-identical. The only genuine drift is in the headline's proof: v4.34's `!![…]`
elaborates through `Matrix.of ![![…]]` and is wrapped again by `archComplexLiftAt`'s `Matrix.of`, so
the pin's entry-level `simp` cannot fire — fixed by feeding the literal through `fun i j => … i j`
(definitionally the frozen term, +3 lines, statement untouched): FR-0149.

`engine` is **not** a `Classical.choose`: it is `(Module.Basis.span hli).repr` applied to
`⟨fun g => x p (g * k s), hspan p s⟩`, so the expansion conjunct is `b.sum_repr` and the choice lives
only in `exists_finsupp_dual`'s surjectivity argument (`Submodule.exists_le_ker_of_lt_top`).

## 9. What this set does not do, and what is named next

Deferred by subject, each named with its silo in Appendix A (all 91 `AutomorphicForm` rows of the two
blocks are listed there):

- **The `isCuspConstituent` cluster** — the 458 row's remaining premises and their own premises:
  `continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` (154, a
  **ready leaf**, lev 8/19), `rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite`
  (52), `exists_rightConv_injOn_of_finiteDimensional_of_le` (77),
  `finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent` (240),
  `exists_eq_rightConv_of_mem_cut` (204), `exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent`
  (148), `exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc` (105). That is **AF25** by
  measurement, not by taste: it is the whole of the 458 row's requirement, and 154 is its shelf leaf.
- **The Weyl intertwining integrand** — `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half`
  (1,349) + `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`
  (1,291) + `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043) + the two
  `apply_weylInv_unipotent_…` rows (360, 217) + `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral`
  (156) + `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd`
  (66) — ≈4,482 silo, the largest single subject left on the AF shelf.
- **The LsXi/Petersson bound pair** — `exists_forall_setLIntegral_nnnorm_sq_le_…_of_coversModCentre`
  (1,361) and its `…_of_isFundamentalDomain` sibling (447): 1,808 silo, a third subject.
- **The carrier operator** — `CuspidalSpectrum.exists_isLift_rightConv` (199, lev 11/13) and the five
  `CuspidalSpectrum` rows behind it (665, 435, 363, 295, …): deferred by name from SET-AF22/AF23.
- **The left-Casimir test-factor rows** — `isFactorizableTestFn_leftCasimir{,Complex}_and_rightConv_mem_of_isArchBiFinite`
  (472, 651) and their `exists_isFactorizableTestFn_isArchBiFinite_…` companion (412): the archimedean
  Casimir ↔ right-convolution bridge, a fourth subject.
- **The Siegel/height rows** — `exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat`
  (905, lev 4/7), `coversModCentre_*`/`centreCutSiegelSet` leaves (520, 432, 346, 282, 150, 136, 25).
- **The Whittaker diagonal rows** — `exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt`
  (913) and the two `CuspidalConstituent.exists_forall_whittakerCoefficient_…_diagOne` rows (716, 714):
  they want the Whittaker API SET-AF11 built, and now also this set's circle weights.

## Appendix A — the shelf as read (both blocks, `AutomorphicForm` only)

Ready **44 / 18,061**, leaves **47 / 10,181**; every row is marked with its disposition and every
row not cut is deferred to the subject named in §9.

**Two of the set's four rows are not in this table**, because they are on neither block (§0):

| row (`AutomorphicForm.` dropped) | silo | prem | why off-shelf |
|---|---:|---:|---|
| `exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex` | 908 | 1 | one edge behind the leaf 755 (`needed = 2`); taken as **AF24A** |
| `hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero` | 169 | 1 | same (one edge behind 755); taken as **AF24A** |

The table below is generated from `build/shelf-af24.json` (columns: silo, direct pin premises,
leverage inside the cone / across the project, block).

| row (AutomorphicForm. dropped) | silo | prem | lev | block | disposition |
|---|---:|---:|---|---|---|
| `exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre` | 1361 | 2 | 1/4 | ready | deferred |
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | ready | deferred |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | ready | deferred |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | ready | deferred |
| `exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt` | 913 | 1 | 1/1 | ready | deferred |
| `exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat` | 905 | 1 | 4/7 | ready | deferred |
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 0 | 3/4 | leaf | AF24A |
| `CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent` | 716 | 2 | 2/2 | ready | deferred |
| `CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent` | 714 | 2 | 1/2 | ready | deferred |
| `isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite` | 651 | 9 | 1/1 | ready | deferred |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 0 | 2/4 | leaf | deferred |
| `integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn` | 635 | 1 | 1/1 | ready | deferred |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 0 | 1/1 | leaf | deferred |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 0 | 2/2 | leaf | deferred |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | ready | deferred |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 0 | 1/3 | leaf | deferred |
| `exists_integral_rightConv_eq_rightConv` | 514 | 3 | 2/3 | ready | deferred |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | ready | deferred |
| `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite` | 472 | 9 | 1/1 | ready | deferred |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | ready | deferred |
| `exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain` | 447 | 5 | 3/4 | ready | deferred |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 0 | 1/2 | leaf | deferred |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 0 | 2/7 | leaf | deferred |
| `exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` | 429 | 3 | 1/1 | ready | deferred |
| `exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul` | 412 | 6 | 1/4 | ready | deferred |
| `exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates` | 390 | 2 | 1/5 | ready | deferred |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 0 | 3/4 | leaf | deferred |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 0 | 1/2 | leaf | deferred |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 0 | 1/1 | leaf | deferred |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | ready | deferred |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | ready | deferred |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 0 | 1/2 | leaf | deferred |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | ready | deferred |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 0 | 3/4 | leaf | deferred |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 0 | 1/1 | leaf | deferred |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 0 | 1/1 | leaf | deferred |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | ready | deferred |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 0 | 5/10 | leaf | deferred |
| `CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant` | 260 | 6 | 1/1 | ready | deferred |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 0 | 1/1 | leaf | deferred |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | ready | deferred |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | ready | deferred |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | ready | deferred |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | ready | deferred |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | ready | deferred |
| `CuspidalSpectrum.exists_isLift_rightConv` | 199 | 4 | 11/13 | ready | deferred |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 0 | 7/20 | leaf | deferred |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 0 | 4/5 | leaf | deferred |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | ready | deferred |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 0 | 1/1 | leaf | deferred |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 0 | 1/4 | leaf | deferred |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 0 | 1/1 | leaf | AF24B |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | ready | deferred |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 0 | 1/1 | leaf | deferred |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | ready | deferred |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | ready | deferred |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 0 | 1/5 | leaf | deferred |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 0 | 1/1 | leaf | deferred |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 0 | 8/19 | leaf | deferred |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 0 | 1/2 | leaf | deferred |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 0 | 4/8 | leaf | deferred |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 0 | 2/2 | leaf | deferred |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 0 | 1/14 | leaf | deferred |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | ready | deferred |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 0 | 1/3 | leaf | deferred |
| `isFactorizableTestFn_comp_inv_mul` | 133 | 1 | 2/3 | ready | deferred |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 0 | 1/1 | leaf | deferred |
| `IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq` | 108 | 1 | 1/1 | ready | deferred |
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 0 | 2/2 | leaf | deferred |
| `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 0 | 1/1 | leaf | deferred |
| `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 0 | 2/4 | leaf | deferred |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 0 | 1/1 | leaf | deferred |
| `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 0 | 1/1 | leaf | deferred |
| `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 0 | 2/3 | leaf | deferred |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 0 | 2/2 | leaf | deferred |
| `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 0 | 1/2 | leaf | deferred |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | ready | deferred |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | ready | deferred |
| `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 0 | 1/1 | leaf | deferred |
| `CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite` | 52 | 1 | 3/5 | ready | deferred |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | ready | deferred |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 0 | 2/2 | leaf | deferred |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | ready | deferred |
| `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 0 | 1/2 | leaf | deferred |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | ready | deferred |
| `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 0 | 2/10 | leaf | deferred |
| `exists_linearMap_archCutProjector` | 29 | 2 | 2/3 | ready | deferred |
| `exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 0 | 1/1 | leaf | deferred |
| `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 0 | 1/1 | leaf | deferred |
| `constantTerm_add` | 13 | 0 | 1/2 | leaf | deferred |
| `constantTerm_smul` | 11 | 0 | 1/1 | leaf | deferred |
