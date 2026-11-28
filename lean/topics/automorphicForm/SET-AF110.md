# SET-AF110 — the consumer shelf of SET-AF109, plus its second def layer

**Status: PLANNED and scaffolded (2026-11-27).** The next set of the AF column in the D–S cone, scoped
per [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. SET-AF109 left a shelf of twelve ready rows, **2,342 silo**; this set cuts **ten of
them, 2,282 silo**, in five orders: five new modules, three insertion sites and one def-layer module.

| # | order | rows | silo | module(s) |
|---|---|---:|---:|---|
| A | the Whittaker coefficient's norm bound | 1 | 645 | `AutomorphicForm/Adelic/WhittakerNormBound.lean` (new) |
| B | the trace character and Poisson summation on pure tensors | 2 | 602 | `NumberTheory/AdelicFourier/{PureTensorPoisson,NonzeroTrace}.lean` (new) |
| C | the Tate defect as a `q`-series | 2 | 381 | `TateCurve/SeriesIdentities.lean` (insert) + `TateCurve/Defect.lean` (new, def layer) |
| D | the genus bound, and the base-changed lift's descent | 2 | 386 | `AlgebraicCurve/Genus/GenusFFKrullDim.lean` (new), `AlgebraicCurve/Pic0/BaseChangeDescent.lean` (new) |
| E | the trace dual's coset forms, and the full-level equality | 3 | 268 | `NumberTheory/AdelicFourier/TraceDual.lean` (insert ×2), `ModularCurve/FullLevelFunctionField.lean` (insert) |
| **total** | | **10** | **2,282** | 5 new + 3 insertions (+1 def-layer module) |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af108/unport_final.txt)) > build/shelf_af110_read.json
```

The correction list is still SET-AF109's `unport_final.txt`, **20 names**, and `--selfcheck` still reports
the same twenty "source node not covered by the name scan" lines (this set's rows are new declarations in
new modules, so the set did not change it).

| figure | value |
|---|---:|
| `needed [F terminal]` | **236 / 144,835** |
| ready rows | 12 / 2,342 |
| leaves | 5 / 13,761 |
| withheld (FR-0044 guard) | 5 / 1,648 |

The shelf is **SET-AF109's payoff**: nine of the twelve ready rows are consumers of rows that set landed,
and the twelfth (`TateCurve.defectCoeff_zero`) becomes statable once this set ports its def layer. Three
are not cut (§5): the false ready (`exists_sum_smul_eq_of_isIntegralQExp_gamma1`) and the two
definition-gated rows (`rep_tateModule_jOne_comm`, and — as it turns out — nothing else, once
`Def_TateCurve_Defect` is ported).

The def-layer read is again the deciding instrument: **`TateCurve.defect_qExpansion` (368, the shelf's
second largest) reads `needed = 1` but is not statable** — its statement's `defectCoeff`/`a₄Coeff`/
`a₆Coeff` come from `Definitions/Def_TateCurve_Defect.lean` (**0 public / 29 absent**, the only `GATE`
line of the ten). Everything else is a structure field. So the set opens, like SET-AF109, with the
manager's def-layer port (`TateCurve/Defect.lean`, 182 pin lines, **28 checked declarations**).

## 1. The stories

### A — the Whittaker coefficient's norm bound (645)

`AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le`:
a bound on the right translates plus a bound on the derivative at the unipotent give
`‖W(α)‖ ≤ C * D * ‖α‖⁻¹` — the norm estimate the entire-Euler-product identity of SET-AF109A exists to
feed. It is the set's largest row and its only `AutomorphicForm` one; the three premise modules (the box
Fourier factorisation, the fundamental-domain integration, the archimedean trace character) have no common
home, so the module is new.

### B — the trace character and Poisson summation on pure tensors (602)

* `tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace` (360, **16 premises**
  — the largest premise count on the shelf): Poisson summation over the principal adèles for a pure-tensor
  test function, for a global character whose archimedean part is `fourierChar ∘ trace`;
* `exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar` (242): some non-zero `a` makes *any*
  global character's archimedean part the trace character — the existence half of the `hψ_inf` hypothesis
  that the whole trace-dual family assumes.

The pin does not make the second a consumer of the first, so neither do the port's modules.

### C — the Tate defect as a `q`-series (381 = 368 + 13)

`defect_qExpansion`: the Weierstrass defect of `(pointX q u, pointY q u)` is `∑' N, defectCoeff u N q^N`,
and `defectCoeff_zero`: its constant term vanishes for `u ≠ 1`. Both are **insertions into
`TateCurve/SeriesIdentities.lean`**, the module that holds SET-AF109F's two `q`-expansions, and both are
statable only because the def layer landed first. The def module is
`TateCurve/Defect.lean` (**28 ok / 0 mismatch**, 15/15 by hash in the pin's `Def_` file): the Cauchy
product of `q`-series, the full coefficient sequences, the Weierstrass coefficients as divisor sums, and
`defectCoeff` itself. Ten of `defect_qExpansion`'s prelude rows are already `private` in
`SeriesIdentities.lean` (the `pairTerm`/`summable_*` block AF109F wrote once), so the insertion is **153
lines of reuse** in the same module.

### D — the genus bound, and the base-changed lift's descent (386)

* `sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one` (216): `∑ genusFF (residue field) ≤ genusFF L F` in
  the `krullDimLE`-one residue-span setup — the **consumer of SET-AF109B/C**, whose two rows are among its
  ten premises;
* `freeAlgebra_lift_baseChange_correspondence_eq_zero` (170): the **descent** direction of
  `Pic0/BaseChange.lean`'s row (that module lifts a vanishing correspondence *to* the base change), whose
  premise set includes SET-AF109D's place-reduction row.

Homes: the first is new (`AlgebraicCurve/Genus/GenusFFKrullDim.lean`, ten premise modules with no common
home); the second is a **new `Pic0/` module** (`Pic0/BaseChangeDescent.lean`), not an insertion into the
`Genus/` module that happens to be in its premise set — the subject is `Pic0` + base change, and the
`Pic0/BaseChange.lean` module cannot host it (it is below the premise).

### E — the trace dual's coset forms, and the full-level equality (268)

* `forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles` (144) and
  `…iff_exists_mem_traceDual` (99): the two *forms* of SET-AF109G's trace-dual criterion (the
  integral-ideal module form, and the `w`-coset form) — **insertions into `AdelicFourier/TraceDual.lean`**,
  the module that states the criterion;
* `modularFunctionFieldC_eq_modularFunctionFieldFullC` (25): the full-level function-field equality
  **without** SET-AF109E's `[NeZero ℓ]` — a *generalisation* of that row, whose pin proof is a two-case
  wrapper (`ℓ = 0` → `X1/FunctionFieldInclusion.lean`'s `charZero` row, already ported at `:80`; `ℓ ≠ 0` →
  AF109E's row). **Insertion into `ModularCurve/FullLevelFunctionField.lean`.**

## 2. The scaffolds

Nine files are touched before any order starts: **six new** (five row modules plus the def-layer
`TateCurve/Defect.lean`) and **three insertions**. All elaborate at the 200 k edit-loop cap, silent but for
their `sorry`s.

| order | module | new | scaffold `check_port` |
|---|---|---|---:|
| – | `TateCurve/Defect.lean` (def layer, new) | 28 | **28 ok** |
| A | `AutomorphicForm/Adelic/WhittakerNormBound.lean` (new) | 1 | **1 ok** |
| B | `NumberTheory/AdelicFourier/PureTensorPoisson.lean` (new) | 1 | **1 ok** |
| B | `NumberTheory/AdelicFourier/NonzeroTrace.lean` (new) | 1 | **1 ok** |
| C | `TateCurve/SeriesIdentities.lean` (insert) | 2 | **16 ok** (14 before) |
| D | `AlgebraicCurve/Genus/GenusFFKrullDim.lean` (new) | 1 | **1 ok** |
| D | `AlgebraicCurve/Pic0/BaseChangeDescent.lean` (new) | 1 | **1 ok** |
| E | `NumberTheory/AdelicFourier/TraceDual.lean` (insert) | 2 | **3 ok** (1 before) |
| E | `ModularCurve/FullLevelFunctionField.lean` (insert) | 1 | **6 ok** (5 before) |
| **total** | **9 files** | **10 rows** | **58 ok / 0 / 0 / 0 / 0** |

### 2.1 What the scaffold pass cost, and what it caught

* **the def layer first, again** (FR-0325): `Def_TateCurve_Defect` is the one gate of the ten, and porting
  it first is what makes order C's two statements writable. It came out at **28 checked declarations**, 15/15
  by hash against the pin's `Def_` file, and it is a *verbatim* transcription (three section-variable
  moves, no statement change); the only pin declaration not carried is the `private`
  `antidiagonal_sum_mul_pow`, which the pin keeps private and which the port keeps private.
* **a read the shelf got wrong, caught by the scaffold**: the 25-row of order E looked like a *chain*
  (its pin proof cites `modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero`, which I could not
  find in the port). The scaffold pass proved it is **already ported**
  (`X1/FunctionFieldInclusion.lean:80`, with its own wire) — the first grep missed it, and a scaffold for
  the "missing" row collided with the ported one. The row is therefore a generalisation already provable
  from two port rows, not a new engine.
* **the home direction, measured**: `tmp/af110/homes_audit.py` reads **44 premise edges over the 10 rows,
  `problems 0`** on the scaffolded tree — every premise module is reachable from its row's home. The
  first-cut table (`tmp/af110/homes.py`) is what chose the five new modules: it prints
  `candidates: NONE` for A, both of B's rows and D's 216-row, and for D's 170-row it prints only the two
  `Genus` modules that *happen* to be in the closure — which is why the row got a new `Pic0/` home instead
  (the subject decides, then the price).
* **three imports the scaffold had to add**, all found by the edit loop: `NumberTheory/AdelicLevel`,
  `NumberTheory/NumberField/TateGlobal/Defs` and `NumberField/MixedEmbedding` for order A's statement
  (its wrapper opens `NumberField.TateGlobal` and `NumberField.AdelicLevel`, namespaces whose modules the
  scaffold's premise list did not reach); `FLTForHuman.TateCurve.Defect` for order C.

## 3. The pricing

| figure | value |
|---|---:|
| raw `S_` lines (the 12-row shelf) | 2,342 |
| declaration lines | 2,067 |
| of which duplicate copies | 21 |
| boilerplate (imports/attrs/`p2m`) | 275 |
| distinct declaration groups | 115 |
| **already in the port (vetted)** | **275** |
| **net new math lines** | **1,771** |
| substitutions | 22 trusted / 0 suspect |

Two things to read carefully:

* **the figures are the 12-row shelf's**, taken *before* the scaffolds were written. A post-scaffold
  re-run is unusable: `port_advise` scans the whole port tree, so it reports the scaffolds' own headlines
  as substitutions (CARRY-FORWARD's tool hazard — the 10-row re-run reads 1,124 "in the port", of which
  ~850 is the scaffolds themselves). This set is nonetheless the **most reuse-heavy of the column**: 275
  of 2,067 declaration lines were already public *before* its own scaffolds, and two of its rows are pure
  assembly over the previous set's work:
* **order D's 170-row**: seven of its declarations are already public in `Pic0/BaseChange.lean`
  (`lift_equivariant` 15, `degree_eq_sum` 11, `degree_mapDomain` 10, `mkHom_apply` 9, `mk_eq_zero_iff` 4,
  `mkHom` 3), i.e. **~52 reusable lines**; and **order C** reuses **153 lines** of the module it inserts
  into (the ten `private` prelude rows).

**Correction, measured by order B (FR-0335).** The advise's substitution for the 242-row,
`continuous_ringEquiv_mixedSpace_symm` (32 lines), is **unusable**: the named `private` copy does not exist
in `RightConvRegularity.lean`, and the two public copies are declared under `variable (F : Type)`
(**universe 0**) while the pin's row is `(K : Type*)` — application at `Type u` is rejected. The row's
statement text hashes identically, so neither the checker nor the advise can see the difference; the pin's
proof was transcribed at the pin's name (`NumberField.InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm`,
now importable from `AdelicFourier/NonzeroTrace.lean`). The set's effective reuse is therefore **~240 lines
lower** than the table above, and the lesson is FR-0335: a `Type*`-valued binder in a substitution must be
checked at its declaration site.

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6: `check_port` **0 mismatch / 0 missing / 0 own**; the engine diff by hash; `#print axioms`; the silent
edit loop and one locked `lake build`; `dedup --within`; `move_dead --dry-run`; a heartbeat probe pair
recorded and not installed. The house policies carry unchanged (low-cap probe ladder, surface gate at
review, **no `import Mathlib`**, declaration-scoped linter options only).

## 5. Not cut — named and deferred (FR-0040)

* **`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36)** — the false ready SET-AF107H found:
  its premise `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (261) is unported and the chain
  behind it is ~3,040 silo of `ModularForm`-level rational structure ("a set of its own", CARRY-FORWARD).
* **`ModularCurve.rep_tateModule_jOne_comm` (24)** — held for `Def_EllipticCurve_TateModule` (883 pin
  lines / 69 declarations) and `Def_ModularCurve_X1HeckeModule` (28 public / 14 absent), i.e. the
  padic-Tate-module programme, not this set.
* **The five leaves (13,761 silo)** — unchanged: `M4aTorus.completedRayL_fe` (12,126, on three
  `Def_NumberField_*` modules + `NarrowRayClassGroup`), `NumberField.exists_continuousOn_exp_eq_rayClassLSeries`
  (684, the same pair), `NumberField.ncard_primesOver_…` (233, `Def_LanglandsTunnell_NormClass`), and the
  two Tate points-law rows (471 + 247, on `Def_TateCurve_TorsionParametrization`, 1,088 pin lines / 43
  declarations — a definition-layer wave of its own, and the natural *next* set after this one).
* **Withheld by the FR-0044 guard (5 rows / 1,648):** the prunable subject's work, unchanged.

## 6. The landing

**LANDED (2026-11-27).** Nine files (five new row modules, three insertions, one def-layer module),
**10 rows / 2,282 silo**, **129 checked declarations** (10 of them the rows), ~2,600 written lines, no
`sorry`, no `sorryAx`, every module silent at the 200 k edit loop.

| order | module(s) | lines | checker | engine diff | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---|---|---|---:|---|---|---|
| A | `AutomorphicForm/Adelic/WhittakerNormBound.lean` (new) | **725** | **52 ok / 0 / 0** (no `private` in the pin, so no surface gate) | 60 pin decls → 56 by name **and** hash + 1 by hash (`solution` → headline); 3 reused (FR-0274 collisions); 0 outside the pin's list | 52 clean | 0 | 0 / 0 | 40,000 / 20,000 (floor 5,000 / 1,000) |
| B | `NumberTheory/AdelicFourier/PureTensorPoisson.lean` (new) | **423** | **1 ok / 0 / 0** | 1 pin decl → 1, **1 hash** | 1 clean | 0 | 0 / 0 | **50,000 / 45,000** (the set's floor; the pin installs 6.4 M) |
| B | `NumberTheory/AdelicFourier/NonzeroTrace.lean` (new) | **338** | **5 ok / 0 / 0** | 5 → 5, **5 hash** | 5 clean | 0 | 0 / 0 | 40,000 / 20,000 (the headline *statement*; the pin installs 3.2 M) |
| C | `TateCurve/SeriesIdentities.lean` (insert) | **1,371** (+203) | **16 ok / 0 / 0** (16 before) | 116 pin decls (25 sources) → 61; **54 hash**, 1 name (pre-existing), 6 `solution`s; 0 pin row unmatched (23/23) | 16 clean | 0 | 0 / 0 | **3,000 / 2,500** (`defect_qExpansion_loc`; module floor moves AF109F's 2,500/2,400) |
| – | `TateCurve/Defect.lean` (def layer, new) | **216** | **28 ok / 0 / 0** | 29 pin decls → 29, **29 by hash** | 28 clean | 0 | 0 / 0 | — |
| D | `AlgebraicCurve/Genus/GenusFFKrullDim.lean` (new) | **274** | **3 ok / 0 / 0** | 4 pin decls (2 sources) → 3, **3 hash** | 3 clean | 1 (the pin's own `main` ↔ headline pair) | 0 / 0 | 40,000 / 20,000 (floor 10,000) |
| D | `AlgebraicCurve/Pic0/BaseChangeDescent.lean` (new) | **184** | **1 ok / 0 / 0** | 8 pin decls → 1 new + **6 imported**, **1 hash**; 7/7 with the imports | 1 clean | 0 | 0 / 0 | 40,000 / 20,000 (floor 20,000) |
| E | `NumberTheory/AdelicFourier/TraceDual.lean` (insert) | **401** (+212) | **17 ok / 0 / 0** (3 before) | 24 pin decls (6 sources) → 17, **17 hash**, 0 unaccounted; **2 merges** (two wires declare the same row) | 17 clean | 2 (the pin's own headline↔engine pairs) | 0 / 0 | 40,000 / 5,000 (above the new rows) |
| E | `ModularCurve/FullLevelFunctionField.lean` (insert) | **361** (+30) | **6 ok / 0 / 0** (6 before) | 10 pin decls (4 sources) → 6, **6 hash** | 6 clean | 0 | 0 / 0 | 50,000 / 40,000 (AF109E's headline, unchanged) |
| **set** | **9 files** | **4,293** (180 declarations) | **129 ok / 0 / 0 / 0 / 0** | **129 by hash**; one row's substitution unusable (§3 correction) | **129 clean, no `sorryAx`** | 3 clusters, all the pin's own pairs | **0 / 0 everywhere** | **set floor 50,000** (B1); no `set_option` installed anywhere |

The set-level gates, run on the landed tree:

* **wave build** — the nine modules built in the orders' locked runs (3,117–4,194 jobs apiece), 0 warning
  lines from any of them;
* **collision probe** — `lean/tmp/af110/collision-probe.lean` over all nine: **silent, exit 0**;
* **home audit** — **44 premise edges over the 10 rows, `problems 0`**;
* **cross-module `dedup`** over the nine (182 declarations, `--cross --min-cost 8`): **0 clusters,
  0 removable lines**;
* **per-module gates** — nine `review.py` runs: every edit loop silent, every `check_port` `0 mismatch /
  0 missing / 0 own`, every axioms probe clean, `move_dead` **0 / 0 in all nine** (the set has no dead code
  at all, unlike SET-AF109's 3 / 37);
* **consumer zone** — `spec/SetAF110Consumer.lean`, two zones, **exit 0** (below).

### 6.1 What the orders decided, and the three corrections to this brief

* **The advise's substitution for B's 242-row is unusable** (FR-0335): the two public
  `continuous_ringEquiv_mixedSpace_symm` copies are at **universe 0** while the pin's row is `(K : Type*)`,
  so application at `Type u` is rejected and the pin's 32-line proof had to be transcribed under the pin's
  name. The effective reuse is ~240 lines lower than §3's table says.
* **`check_port` counts a scaffolded headline** (order C measured 16/16 where its order predicted 18; order
  E measured 6/6 where the brief predicted 7): an order's post-landing count adds only its *new public*
  rows. Corrected in §6's table.
* **Two declarations of order E are merged, not omitted**: `mul_mem_integralFiniteAdeles` is declared by
  both wires, and the pin's `addChar_zero_add`/`apply_zero_add` share one `S_` statement hash, so 17 module
  declarations cover 20 pin rows. That is the `port once` rule operating inside one set.
* **Three rows were reused rather than re-declared** (order A, all FR-0274 collisions with public port
  declarations, all `ok` by hash): `continuous_eA_symm` (imported, hash-identical), `continuous_unipotentGL2`
  (the port's general form, instantiated), `μA` (the same `abbrev` with `F` for `K`).
* **No linter is silenced anywhere in the set** and **no `set_option maxHeartbeats` is installed**: order A's
  7 `haveI`→`have` conversions, order D's 7, order E's one and order C's two `omit` corrections all met the
  200 k cap without a budget. The two pin budgets the orders did *not* install are recorded: 6.4 M (B1) and
  3.2 M (B2).
* **The `private` question never arose**: seven of the nine files have no `private` declaration at all (the
  pins do not), and the two that do (SeriesIdentities, Defect) are pin-faithful — the surface probes read
  37 ok and 29 ok respectively, and neither was promoted.

### 6.2 The consumer zone

`spec/SetAF110Consumer.lean`, two zones, elaborates at **exit 0**:

* **Zone 1 — order C's two rows composed**: `defect_qExpansion` (the defect is `∑' N, defectCoeff u N * q^N`)
  with `defectCoeff_zero` gives `defect_qExpansion_eq_tsum_succ`: for `u ≠ 1` the defect series starts at
  `q ^ 1`, i.e. the defect vanishes to first order at the cusp — the form the point-arithmetic layer works
  in (summability is the pin's `summable_norm_*` block, carried as a hypothesis).
* **Zone 2 — order E's coset row with the previous set's membership row**:
  `mem_traceDual_iff_exists_sub_mem_integralFiniteAdeles` states that `ξ` is trace-dual **iff**
  `algebraMap ξ` is an integral translate of a trace-dual element, by rewriting AF109G's criterion into
  order E's coset form. It is the set's cross-order composition and the bridge between the two forms of the
  trace-dual criterion.

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af108/unport_final.txt)) > build/shelf_af110_final.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 236 / 144,835 | **226 / 142,553** |
| ready rows | 12 / 2,342 | **15 / 6,727** |
| leaves | 5 / 13,761 | 5 / 13,761 |
| withheld (FR-0044 guard) | 5 / 1,648 | **6 / 1,970** |

The delta is **−10 nodes / −2,282 lines**, exactly the cut. The correction list is unchanged (the same 20
names).

**Thirteen rows became ready (6,727 silo)**, and the head of the new shelf is an order of magnitude above
anything this column has opened before:

* **`AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary` (3,747)** — order A's
  consumer, and the largest ready row of the column: the **polynomial decay** of the Weyl-unipotent
  `addChar` integral for a unitary section. That is the analytic heart of the Eisenstein bound, and it needs
  order A's norm bound as an input;
* **`ModularCurve.exists_slot_algHom_modularFunctionFieldFullC_of_ord_neg` (906)** and
  `…exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental` (309) — order E's consumers (the
  full-level function field's slot/root dictionary);
* **`AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero` (286)** — order D's
  descent row feeding the geometric-cycle form;
* **`NumberField.AdelicFourier.measure_setOf_forall_addChar_finitePart_mul_eq_one` (263)**,
  `…isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one` (117) and
  `…tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one` (64) — order B's and
  order E's consumers (the vanishing set's measure and compactness, and the normalized-measure form of
  Poisson summation);
* **`LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal` (252)** — order B's consumer
  in the Tate-local layer;
* **`AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one`
  (249)** — order D's genus-bound consumer;
* **`TateCurve.lineCoeff_eq_zero` (142)** and **`TateCurve.equation_of_defectCoeff_eq_zero` (25)** — order
  C's defect consumers, the first step of the point-arithmetic layer;
* **`AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar` (118)** — order B's;
* **`ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero` (189)** — a consumer
  unlocked by order E's full-level equality.

**The withheld block grew by one row (322 silo)**, and it is the FR-0044 guard doing its job:
`AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero` cites the complex-
analytic `…_of_lift_differential_eq_zero_complex`, which lies in the prunable set R — the prunable subject's
work, not this column's.

The three rows that stayed are unchanged from SET-AF108/109 §7: the false ready
(`exists_sum_smul_eq_of_isIntegralQExp_gamma1` 36), and the two definition-gated ones
(`rep_tateModule_jOne_comm` 24, and `defectCoeff_zero`'s sibling — which this set landed, so the pair is
gone).

## 8. What the set leaves behind

**The shelf more than doubled its silo while losing its consumers**: 12 rows / 2,342 → 15 rows / 6,727,
headed by a **3,747-line** row. Two consequences for the next scoping:

* the next set is no longer a consumer tail — it is a **single-row story** (the 3,747-line polynomial-decay
  theorem needs its own order and its own wall time) plus a 906-line ModularCurve row, exactly the shape
  SET-AF108 found with its 2,468-line Eisenstein row;
* the definition-layer option is now cheaper than it was: `Def_TateCurve_TorsionParametrization`
  (1,088 lines / 43 declarations) would open the two Tate points-law leaves (718), and this set's def-layer
  module (`TateCurve/Defect.lean`, 216 lines, 29 declarations, 29/29 by hash) is the measured evidence that
  a `Def_` port of that size is a manager-scale job, not a wave.

Six things carried beyond the files:

* **five new frictions**, and three of them are about *instruments disagreeing with Lean*: **FR-0331** (a
  `@[reducible]` alias makes a term ambiguous under two opened namespaces — drop the `open`, never change
  the spelling), **FR-0332** (`AddChar.compAddMonoidHom_apply` under the `AdeleRing` product `defeq`;
  `show`-based remedy, twice-seen), **FR-0333** (a declaration can read `ok` while matching the *wrong* pin
  row — read the `-> file:line` column, and never move a pin's `variable (F : Type)` into a binder),
  **FR-0334** (`lean_parser.ENCLOSE_RE` reads a bare `end`'s name from the next `end Foo`, which now also
  breaks the harness's generated axioms probe), and **FR-0335** (a public "identical" port copy can be
  unusable because it was declared at **universe 0** — the checker cannot see universes).
* **the def-layer-first rule is now three-for-three** (Tails 90 lines, Defect 182, and this set's 216-line
  module) and it is the only gate that sees a row whose statement needs an unported `Def_` module.
* **the `port once` rule fired inside one set** for the first time (order E's two merges: 17 declarations
  for 20 pin rows).
* **three CARRY-FORWARD items**: `mem_compositeRing_iff` (still deferred), the parser `ENCLOSE_RE` fix (now
  with a second measured consequence), and the `ArchKType.majorant_integrable` dedup decision.
* **the column's cheapest set per silo**: 275 of 2,067 declaration lines were already public *before* its own
  scaffolds (13 %), and two orders were pure assembly (C reused 153 lines of the module it inserted into;
  D's 170-row imported six declarations).
