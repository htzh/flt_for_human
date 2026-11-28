# SET-AF109 — the consumer shelf, one giant row

**Status: PLANNED and scaffolded (2026-11-27).** The next set of the AF column in the D–S cone, scoped
per [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. SET-AF108 left a shelf of fourteen ready rows, **5,576 silo**, a third of it one
Eisenstein row; this set cuts **eleven of them, 5,503 silo**, in seven orders, five new modules, five
insertions and one def-layer module.

| # | order | rows | silo | module(s) |
|---|---|---:|---:|---|
| A | the entire partial Euler product | 1 | 2,468 | `EisensteinGeneral/PiecePartialEulerProduct.lean` (new) |
| B | the residue span at Krull dimension one | 1 | 783 | `AlgebraicCurve/RegularProlongationResidueKrullDim.lean` (new) |
| C | the residue span's finrank bound | 1 | 638 | `AlgebraicCurve/RegularProlongationResidueFinrank.lean` (new) |
| D | principal divisors under the place reduction | 1 | 485 | `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (insert) |
| E | the full-level function field | 2 | 413 | `ModularCurve/FullLevelFunctionField.lean` (new), `ModularCurve/Degree/FinrankDedekindPsi.lean` (insert) |
| F | the point coordinates as `q`-expansions | 2 | 568 | `TateCurve/SeriesIdentities.lean` (insert) + `TateCurve/Tails.lean` (new, def layer) |
| G | the trace dual and its companions | 3 | 148 | `NumberTheory/AdelicFourier/TraceDual.lean` (new), `NumberTheory/NumberField/{MixedEmbedding,StandardAddCharTrace}.lean` (insert) |
| **total** | | **11** | **5,503** | 5 new + 5 insertions (+1 def-layer module) |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af108/unport_final.txt)) > build/shelf_af109_read.json
```

The correction list is SET-AF108's `unport_final.txt`, **20 names**, and it is still the `--selfcheck`
output of the landed tree (byte-identical: this set's rows are new declarations, so the set did not change
it; `python3 frontier.py --ds --selfcheck` still reports the same twenty "source node not covered by the
name scan" lines).

| figure | value |
|---|---:|
| `needed [F terminal]` | **247 / 150,338** |
| ready rows | 14 / 5,576 |
| leaves | 5 / 13,761 |
| withheld (FR-0044 guard) | 5 / 1,648 |

The cut is **eleven of the fourteen ready rows**, and the three left out are exactly SET-AF108 §7's
"three that stayed" (§5). The leaves block is unchanged and entirely definition-gated; it is not touched.

The head of the shelf is one row — `EisensteinGeneral.Piece.exists_entire_partialEulerProduct_mul_eq_
whittakerCoefficient_and_summable_majorant`, 2,468 silo over 17 premises — and it is 45 % of the set. The
rest is the consumer tail the previous set's landings made ready: two rows of the residue-span family
(orders B, C), the `mapDomain` descent (D), the two full-level function-field rows (E), the two point
`q`-expansions (F) and three adelic-Fourier leaves (G).

## 1. The stories

### A — the entire partial Euler product is the Whittaker coefficient (2,468)

The pin's single largest row in the column: for a global additive character with local factors, a Hecke
character `χ`, a finite place set `S` and a factorization datum `D`, the Whittaker coefficient of the
unfolded section is `∏'_{v ∉ S} (1 - χ_v(ϖ_v) |N v|^{-(2s+1)})` times an entire `Q ξ` with a locally
summable majorant. Its 104 declarations are the adelic unfolding computation in four layers
(archimedean weight integrals; local/finite Haar and Euler factors; the tensor and finite-product
integrability; the shell estimates and `pc_finite_half`).

Six of its premises are the last three sets' Eisenstein landings; the seventh,
`Piece.integrable_weyl_unipotent_mul_of_factorization`, is SET-AF108F's. The row is why this set is
called "one giant row": nothing else in the column is close (the largest single row of SET-AF108 was 729).

**The promotion that made it cheap.** Fourteen of its declarations of its own prelude are the *same
declarations* SET-AF108F landed `private` in `EisensteinGeneral/PieceWeylIntegrability.lean` (the two pin
`S_` files share the block verbatim: 12 statement-hash-identical and 2 by name). The manager promoted all
fourteen (`private` dropped; `check_port` then reads **15 ok / 0 mismatch** on that module, from 1 ok +
21 `private`), so order A imports ~300 lines rather than re-proving them — the recipe's *promote instead
of copy* rule, and the CARRY-FORWARD item `ArchKType.majorant_integrable` is the same shape one layer
down (deferred: the pin keeps that one `private` in a module A does not own).

### B — the residue span is constant, at Krull dimension one (783)

`exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one`: a vector in both the
`f`- and the `f⁻¹`-residue span is a constant. It closes the `Fin (finrank)`-family SET-AF108B opened
(the multiplicative normal form and the monic-polynomial rows), and it is the residue-span story's
*Krull-dimension-one* form.

The module is new because its premises include the two AF108 residues modules; the pin's 59 declarations
are all public (the `IsGoodAt`/`InT` predicate calculus, the adapted subalgebras `Sg`/`Pg`/`Ppp`, the
residue submodule `rho`, the indicator, the torsion killer, the idempotent-equality argument).

### C — the residue span's finrank bound (638)

`exists_forall_finrank_residueSpan_inf_add_card_le`: the `M`-window calculus (`mulEquiv`, `ordSub`,
`Bsub`, `piEquiv`, `ST`) and the bound `finrank + card ι ≤ ∑ i, ell (M • Db i) + finrank (untwisted)`.
Order B's **sibling**, not its consumer: their premise sets intersect only in the ord layer and the two
rows do not cite each other, so the two modules are dispatched in parallel and neither imports the other.

### D — a divisor is principal if all its place reductions are (485)

The descent direction of the `mapDomain` dictionary — the third direction, after SET-AF107B/C's converse
and AF108A's divisibility theorem. The home is an **insertion** into `Genus/PlaceReductionRiemannRoch.lean`
because one of its three premises is that module's own equality row, and because the module is the
dictionary's home.

This is the set's cheapest order per silo: **twenty-two of the pin's 29 declarations are already public in
the port** — fifteen of them are the `BaseChangeDescentAux` block that `AlgebraicCurve/Pic0/BaseChange.lean`
imported for the *same* pin helper family, and the rest are the ord calculus of
`Defs/PushPull`/`ConstantReduction` plus `degree_eq_sum`/`mem_range_of_forall_ord_nonneg`. Only six
declarations are new (~120 lines).

### E — the full-level function field, two ways (413)

* `coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq` (299): a `ρ`-fixed element
  of the Γ_H `q`-expansion field lies in `modularFunctionFieldFullC K M` — the *membership* half of the
  full-level dictionary whose finrank half SET-AF108D landed. New module (six premise modules, no existing
  module above them).
* `modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos` (114): in characteristic `p`, the two
  function fields coincide. **Insertion** into `Degree/FinrankDedekindPsi.lean`, the module that states the
  `ψ(N)` finrank the proof sandwiches with.

Two declarations of the two pins are already public in the port (`finrank_adjoin_eq_relfinrank`,
`mem_or_neg_mem_of_mem_sup_zpowers_neg_one`, `dedekindPsi_pos`), so the order is ~180 new lines.

### F — the point coordinates as `q`-expansions (568)

`pointX_qExpansion` and `pointY_qExpansion`: `pointX q u = xfun u + ∑' N, xCoeff u (N+1) q^(N+1)` and its
`y`-twin. The two pin files are **the same proof** with `x` interchanged for `y`, and `port_advise`'s
`port once` block prices the duplication at **241 removable lines**; moreover six of their fifteen shared
prelude rows already sit `private` in `TateCurve/SeriesIdentities.lean` (the same shapes the
`sOne_eq_tsum_xfun` pin file carries), so the order writes that prelude **once**, in the module it
inserts into.

The definition gate is real and belongs to the manager: `Definitions/Def_TateCurve_Tails.lean` (90 lines,
15 declarations — `xDivTerm`, `yDivTerm`, `xCoeff`, `yCoeff`, `growthBound` and ten bounds) was
**unported** (0 public / 15 absent). It is now `TateCurve/Tails.lean`, **13 checked declarations, 0
mismatch**, and it is the module that makes the two rows *statable*. Landing it also makes the pin's
torsion-parametrisation deferral dossier (CARRY-FORWARD) one step cheaper.

### G — the trace dual and its companions (148)

Three small rows of one subject, in three files: the finite-part vanishing set is the trace dual (85, new
module above the box measure — the same cycle SET-AF108 hit for the Fourier rows), the lattice-level dual
(50, insertion into `MixedEmbedding.lean`, whose `traceForm_mixedSpace_nondegenerate` is a premise) and
`stdAddChar`'s archimedean value (13, insertion into `StandardAddCharTrace.lean`). None needed a def-layer
port — `stdAddChar` is the port's `AdelicTraceFin.lean` `abbrev`, and the trace data is `StandardGlobalAddChar`'s.

## 2. The scaffolds

Eleven files are touched before any order starts: **six new** (five row modules plus the def-layer
`TateCurve/Tails.lean`) and **five insertions** (one or two headlines appended to a wired module, with
their wires). All elaborate at the 200 k edit-loop cap, silent but for their `sorry`s, and are built:

```bash
cd lean && flock -w 900 /tmp/flt-build.lock timeout 1700 lake build <the ten row modules>
# Build completed successfully (4991 jobs) — no non-`sorry` warning from any of them
```

| order | module | new | scaffold `check_port` |
|---|---|---|---:|
| — | `TateCurve/Tails.lean` (def layer, new) | 13 | **13 ok** |
| A | `EisensteinGeneral/PiecePartialEulerProduct.lean` (new) | 1 | **1 ok** |
| B | `AlgebraicCurve/RegularProlongationResidueKrullDim.lean` (new) | 1 | **1 ok** |
| C | `AlgebraicCurve/RegularProlongationResidueFinrank.lean` (new) | 1 | **1 ok** |
| D | `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (insert) | 1 | **26 ok** (25 before) |
| E | `ModularCurve/FullLevelFunctionField.lean` (new) | 1 | **1 ok** |
| E | `ModularCurve/Degree/FinrankDedekindPsi.lean` (insert) | 1 | **16 ok** (15 before) |
| F | `TateCurve/SeriesIdentities.lean` (insert) | 2 | **14 ok** (12 before) |
| G | `NumberTheory/AdelicFourier/TraceDual.lean` (new) | 1 | **1 ok** |
| G | `NumberTheory/NumberField/MixedEmbedding.lean` (insert) | 1 | **14 ok** (13 before) |
| G | `NumberTheory/NumberField/StandardAddCharTrace.lean` (insert) | 1 | **3 ok** (2 before) |
| **total** | **11 files** | **11 rows** | **91 ok / 0 / 0 / 0 / 0** |

### 2.1 What the scaffold pass cost, and what it caught

* **the def-layer module first**: `Def_TateCurve_Tails` is the only row of the eleven whose *statement*
  needed a definition the port did not carry (the scoping read's def-layer check flagged it
  `0 public / 15 absent`; every other absence is a structure field, which the checker does not index).
  Porting it first is what lets order F's scaffold state its two theorems at all — a `needed = 1` row
  whose statement vocabulary is missing reads ready and cannot be written (the recipe's §0 warning).
* **two section-variable restructurings, no statement changes**: `TateCurve/Tails.lean` moves
  `[IsUltrametricDist K]` into two nested sections so the five instance-free `growthBound` rows are
  silent, and the port's `PieceWeylIntegrability` promotion needed no statement change at all
  (`check_port` reads the same 15 `ok`). The checker hashes *source* statements, so a section-variable
  rearrangement is free (the AF108 lesson, measured again).
* **three imports the scaffold had to add**: `Mathlib.RingTheory.DedekindDomain.Different` (for
  `FractionalIdeal.dual`, order G's 50-row), `FLTForHuman.TateCurve.Tails` (order F),
  and `FLTForHuman.NumberTheory.NumberField.AdelicTraceFin` (order G's 13-row, for the `stdAddChar`
  `abbrev`) — each found by the edit loop, none by reading.
* **one `open scoped Classical in` on a headline**: order A's statement has `Fintype {w // w.IsReal}`
  subterms, which the pin's wrapper supplies with `open scoped Classical in`; without it the statement
  does not elaborate (`synthInstanceFailed`). It is attached to the declaration, not the module.
* **the home direction, measured on the scaffolded tree**: `tmp/af109/homes_audit.py` reads **61 premise
  edges over the 11 rows, `problems 0`** — every premise module is reachable from its row's home, so no
  order starts in the import-direction cycle that re-homed rows of SET-AF107/108. The audit's own
  first-cut table (`tmp/af109/homes.py`) is what chose the five new modules: for **five** of the eleven rows
  it prints `candidates: NONE` (A, B, C, E's 299-row, G's 85-row), and for the other six its top candidate
  is the insertion site (D → `PlaceReductionRiemannRoch`, E's 114-row → `FinrankDedekindPsi`, F's two →
  `SeriesIdentities`, G's two → `MixedEmbedding` / `StandardAddCharTrace`).
* **the namespace trap**: the extracted wrapper statements already carry their full names
  (`theorem TateCurve.pointX_qExpansion`, `theorem EisensteinGeneral.Piece.…`), so wrapping a scaffold in
  `namespace` duplicates the namespace. The generator emits the statements at root and the `dupNamespace`
  linter stays quiet.

## 3. The pricing

`port_advise` on the eleven rows, then `port_plan`:

| figure | value |
|---|---:|
| raw `S_` lines (22 `S_` files) | 5,503 |
| declaration lines | 5,234 |
| of which duplicate copies | 241 |
| boilerplate (imports/attrs/`p2m`) | 269 |
| distinct declaration groups | 265 |
| **already in the port (vetted)** | **768** |
| **net new math lines** | **4,225** |
| substitutions | 69 trusted / 3 suspect |

768 of 5,234 declaration lines are already public in the port (15 %), the highest of the column — of which
**37 lines are not in fact reusable** (see the correction below), so the effective figure is **~731**. The
two blocks that carry it are the ones the previous sets built:

* **order D** — the 15-row `BaseChangeDescentAux` block of `Pic0/BaseChange.lean` plus the ord calculus
  (`mem_of_ord_nonneg` 62, `ord_algebraMap` 61, `ord_nonneg_of_mem` 18): 147 lines already paid for;
* **order F** — six of the fifteen shared prelude rows are `private` in `SeriesIdentities.lean`, and
  `port_advise` prices the whole shared block at **241 removable lines** (`summable_sigmaTerm'` 35,
  `hasSum_yfun_succ` 31, `hasSum_yRow` 28, `tsum_pairTerm_eq_tsum_divisors` 28, `hasSum_xRow` 19, …).

**Correction, measured by order D (FR-0330).** Two rows this brief counted as "already paid for" are not:
`mem_range_of_forall_ord_nonneg` (pin 31 lines) has only a *weaker* namesake in
`Genus/ConstantFieldExtensionDivisor.lean`, and that module imports the row's home (a cycle, so the stronger
row had to be transcribed), and `degree_eq_sum` (6 lines) names the pin's *other* `degree_eq_sum` in
`Defs/Divisor.lean`. A third row of the same pin (`mem_compositeRing_iff`, 3 lines, `Iff.rfl`) has no port
copy at all and is deferred (CARRY-FORWARD). The table above is the advise's, not a name-matching result —
the difference between the two is exactly what this correction measures, and it costs the set **+38
transcribed lines and one deferred row**.

The **three suspects** (type-only `def` matches) are assigned to their orders: `InT → ZfSol.IsW` (B: the
pin's `InT` is a two-place predicate, not a one-place `IsW` shape), `pc_finBorel → M4aS4.finBorel` and
`pc_locBorel → AutomorphicForm.kvBorel` (A: the body may be the measurable structure or only its carrier).

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6, unchanged from SET-AF108 (§4 of that brief): `check_port` **0 mismatch / 0 missing / 0 own**, the
engine diff by hash, `#print axioms`, the silent edit loop and one locked `lake build`, `dedup --within`,
`move_dead --dry-run`, a heartbeat probe pair recorded and not installed. The four house policies carry
unchanged: the low-cap probe ladder (no `set_option maxHeartbeats` is ever installed), the surface gate at
review (drop `private`, re-read the three numbers), **no `import Mathlib`**, declaration-scoped linter
options only.

New in this set: **FR-0325** (the def-layer module that a ready row's *statement* needs must be ported
before its scaffold — the scoping read's `0 public / n absent` line is the gate, and the `TateCurve/Tails`
case is the worked one), and the reuse of the recipe's promotion rule as a **cost instrument**, not only a
dedup one: promoting fourteen `private` rows in a neighbour module saved order A ~300 lines and removed a
future dedup obligation (the same argument as the CARRY-FORWARD `ArchKType.majorant_integrable` item).

## 5. Not cut — named and deferred (FR-0040)

* **The three ready rows that are not ready:** `ModularCurve.rep_tateModule_jOne_comm` (24) and
  `TateCurve.defectCoeff_zero` (13) stay held for their definition modules
  (`Def_EllipticCurve_TateModule` 8/100 — 883 pin lines / 69 declarations — and `Def_TateCurve_Defect`
  0/29); and `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36) is the **false ready** SET-AF107H
  found: its premise `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (261) is unported and the
  chain behind it is ~3,040 silo of `ModularForm`-level rational structure, "a set of its own, not a row
  on a `ModularCurve` shelf" (CARRY-FORWARD). Still registered there.
* **The five leaves, all definition-gated (13,761 silo):** `M4aTorus.completedRayL_fe` (12,126, on
  `Def_NumberField_{CompletedRayL,RayCharacterData,FrobeniusDensity_ClassGroupLSeries}` +
  `NarrowRayClassGroup`), `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` (684, the same pair),
  `NumberField.ncard_primesOver_…` (233, `Def_LanglandsTunnell_NormClass`) and the two Tate-curve
  points-law rows (471 + 247, `Def_TateCurve_TorsionParametrization` 1/43). A definition-layer wave, not
  this set.
* **Withheld by the FR-0044 guard (5 rows / 1,648):** the prunable subject's work, unchanged.
* **CARRY-FORWARD items not this set's business:** `ArchKType.majorant_integrable`'s promotion, the nine
  `W7XL2`/`TorsionDescentDeriv` promotions, the `CoeffMap.linearIndependent_coeffMap_comp_of_linearIndependent`
  instance fix, and `hasCanonicalDivisor_of_fg`'s hub edit. None of them blocks a row here.

## 6. The landing

**LANDED (2026-11-27).** Eleven modules (five new row modules, five insertions, one def-layer module),
**11 rows / 5,503 silo**, **198 checked declarations** (11 of them the rows), ~5,000 written lines, no
`sorry`, no `sorryAx`, and every module silent at the 200 k edit loop.

| order | module(s) | lines | checker | engine diff | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---|---|---|---:|---|---|---|
| A | `EisensteinGeneral/PiecePartialEulerProduct.lean` (new) | **2,382** | **1 ok / 0 / 0** (surface gate: **90 ok** with `private` dropped) | 104 pin decls → 90 module; **87 by name *and* hash**; 17 accounted (11 promoted + 1 promotion by binder + 2 substituted + 2 renamed + 1 headline) | 1 clean | 0 | **3 / 37** (the pin's own dead rows, below) | 45,000 / 40,000 (`pc_finite_half`); floor 5,000 / 1,000 |
| B | `AlgebraicCurve/RegularProlongationResidueKrullDim.lean` (new) | **886** | **57 ok / 0 / 0** (2 `private`) | 59 pin → 59 declared, **59/59 matched** (55 by hash; 2 renamed, 1 `private`) | 57 clean | 0 within; **5 clusters / 22 lines** against `RegularProlongationResidueOrd` (the pin's own duplication, §6.2) | 0 / 0 | 40,000 / 20,000 (`exists_torsion_killer`) |
| C | `AlgebraicCurve/RegularProlongationResidueFinrank.lean` (new) | **703** | **40 ok / 0 / 0** | 43 pin → 40 + 3 substituted, **40 hash** | 40 clean | 0 | 0 / 0 | **40,000 / 20,000** (`core`; the pin installs 3,200,000) |
| D | `AlgebraicCurve/Genus/PlaceReductionRiemannRoch.lean` (insert) | **1,435** (+239) | **33 ok / 0 / 0** (26 before) | 86 pin decls (8 sources) → 33; **32 hash**, 0 unaccounted; this pin 29 = 20 imported + 7 transcribed + 1 headline + 1 deferred | 33 clean | 1 (pre-existing pair) | 0 / 0 | 40,000 / 20,000 (`:867`, `:1000`, `:1173`) |
| E | `ModularCurve/FullLevelFunctionField.lean` (new) | **312** | **5 ok / 0 / 0** | 8 pin → 5, **5 hash**, rows 7/7 credited | 5 clean | 0 | 0 / 0 | **50,000 / 40,000** (the set's floor) |
| E | `ModularCurve/Degree/FinrankDedekindPsi.lean` (insert) | **389** (+107) | **17 ok / 0 / 0** (16 before) | 21 → 17, **17 hash** | 17 clean | 0 | 0 / 0 | floor unmoved (AF108D's `mem_adjoin_of_degree_count`) |
| F | `TateCurve/SeriesIdentities.lean` (insert) | **1,078** (+207) | **14 ok / 0 / 0** (14 before) | 91 pin decls (21 sources) → 48; **41 hash**, 1 name (pre-existing), 6 `solution`s; 0 pin decl unmatched (32 pin rows → 17 port rows) | 14 clean | 0 | 0 / 0 (was 2 / 22) | 2,500 / 2,400 (`yTerm_neg_add_one`, pre-existing) |
| – | `TateCurve/Tails.lean` (def layer, new) | **120** | **13 ok / 0 / 0** | **15/15 by hash**, 0 unaccounted | 13 clean | 0 | 0 / 0 | — |
| G | `NumberTheory/AdelicFourier/TraceDual.lean` (new) | **140** | **1 ok / 0 / 0** | 2 pin → 1, **1 hash** | 1 clean | 0 | 0 / 0 | 10,000 / 5,000 |
| G | `NumberTheory/NumberField/MixedEmbedding.lean` (insert) | **580** (+58) | **14 ok / 0 / 0** (13 before) | 2 → 14, **1 hash** | 14 clean | 1 (pin's own pair) | 0 / 0 | unchanged (100,000 passes) |
| G | `NumberTheory/NumberField/StandardAddCharTrace.lean` (insert) | **206** (+22) | **3 ok / 0 / 0** (2 before) | 2 → 3, **1 hash** | 3 clean | 0 | 0 / 0 | unchanged (10,000 / 5,000) |
| **set** | **11 files** | **8,231** (325 declarations; ~5,000 written) | **198 ok / 0 / 0 / 0 / 0** | **198 by hash** in the 11 files; 2 renamed rows + 3 unaccounted by name (two renames, one pre-existing fold) | **198 clean, no `sorryAx`** | 1 pre-existing (D), 1 pin-internal (G), 5 the pin's own prelude (B) | 1 site: A's 3 / 37 (pin's dead code) | **set floor 50,000** (E); no probe gap; no `set_option` installed anywhere |

The set-level gates, run on the landed tree:

* **wave build** — each module built in its order's locked run (`lake build` of 3,116–4,270 jobs apiece,
  under `flock`), every one reporting `0 warning lines` from the set's files; the two modules the manager
  touched (`PieceWeylIntegrability`, `Tails`) were built first so the orders' edit loops had their oleans;
* **collision probe** — `lean/tmp/af109/collision-probe.lean` over all eleven: **silent, exit 0**;
* **home audit** — `lean/tmp/af109/homes_audit.py`: **61 premise edges over 11 rows, `problems 0`**;
* **cross-module `dedup`** over the eleven (325 declarations, `--cross --min-cost 8`): **0 clusters,
  0 removable lines**; widened to the two modules where the pin duplicates its own prelude, the only
  clusters are the pin's own (B vs AF108B: 5 clusters / 22 lines, all `shape`/`name`/`body` tier on
  `IsGoodAt` and its four lemmas — §6.2);
* **surface gate** — order A's module drops `private` cleanly: **90 ok / 0 mismatch / 0 missing** (the
  independent re-run reads 88 ok with only the three `private` spellings my `sed` knows stripped), so the
  2,468-line row's 89 private rows are all pin-faithful;
* **consumer zone** — `spec/SetAF109Consumer.lean`, two zones, exit 0 (§6.3).

### 6.1 What the orders decided, and the two corrections to this brief

* **The "fourteen promotions" count was wrong** (my error, corrected here): of the fourteen rows promoted
  in `PieceWeylIntegrability.lean`, **eleven are statement-hash-identical** to this pin's prelude, **one**
  (`pc_isCompact_integers`) differs only in binder explicitness and is used as promoted, and **two**
  (`pc_norm_mul_cpow_lt_one`, `pc_excess_bounds`) are *different lemmas* that happen to share a last name
  with the sibling pin's rows — the pin's two files reuse both names for different statements, invisible in
  the pin because both copies are `private`. Lean refuses a `private` shadow of an imported public name
  (FR-0328), so order A transcribed them privately as `pc_norm_mul_cpow_lt_one_nat` (3 call sites) and
  `pc_excess_bounds_local` (2), both `ok` under the checker's content-hash tier. Renaming the promoted
  copies instead would churn a landed module with no gain; the distinction is recorded in both headers.
* **The substitution table was rebuilt from the name index and was wrong twice** (FR-0330): order D found
  `mem_range_of_forall_ord_nonneg`'s only namesake is a *weaker* row in a module that imports the home
  (a cycle), and `degree_eq_sum` names the pin's *other* `degree_eq_sum`; the "already in the port" figure
  is therefore **~731**, not 768, and the pin's 29th row (`mem_compositeRing_iff`, 3 lines) is deferred
  (CARRY-FORWARD).
* **Three rows were renamed for real collisions** (all `ok` by hash, all recorded): B's
  `inv_mem_integers_of_transcendental` (order C's module has the bare name with a different statement,
  set-internally), B's `private residue_eq_zero_iff_of_mem` (a public same-name row exists in another module — the
  toolchain refuses the shadow, FR-0328), and A's two name-sharing lemmas above.
* **Linters**: order A silenced **nothing** (43 `haveI`/`letI` rewritten as `have`/`let`, FR-0323), B nothing,
  D nothing, E nothing, F nothing, G nothing; only C carries one declaration-scoped
  `linter.style.haveILetI` on `core` (six genuine instance binders, the `FinrankStableInequality`
  precedent). No module-wide silencing anywhere.
* **No `set_option maxHeartbeats` is installed anywhere**, and the four pin budgets the orders met are
  recorded rather than carried: the pin's `synthInstance.maxHeartbeats 1600000` (E), its
  `maxHeartbeats 3200000` on C's `core` (port silent at 40,000, ~80× cheaper), and A's `pc_finite_half`
  (port 45,000). The port is cheaper than the pin on all four measured sites.
* **`move_dead` on order A reads 3 / 37**, and it is the pin's own dead code, not a transcription defect:
  `pc_ram_norm_le` (28 lines), `pc_tprod_mul_finprod` (4) and `pc_fin_one_apply` (2) occur exactly once in
  the pin's `S_` file (the pin uses the primed `pc_ram_norm_le'`). They stay: shelving them needs
  `move_dead --expose` of two live private helpers, and the pin's block is transcribed whole (playbook
  §2.3), which is what makes the engine diff 104/104 accounted.

### 6.2 The pin's own duplications the port keeps, with the reason

* **B vs AF108B (`RegularProlongationResidueOrd`)**: 5 clusters / 22 removable lines — `IsGoodAt` (3–7
  lines), `valuation_le`, `ne_zero`, `coeff_mem`, `aeval_ne_zero_of_isGoodAt`. The pin states this prelude
  in *both* `S_` files; the port's two copies differ in binder explicitness (AF108B leaves `A` explicit,
  B's is the pin's `variable {A}` text), so merging either direction makes one of the two modules
  `MISMATCH`. Kept, with this reason.
* **D and G2** each carry one pre-existing cluster that the insertion does not add to (D: the pin
  headline↔engine pair, 21 lines; G2: the pin's `…_sub_le_impl ↔ …_sub_le`, 7).
* **F**'s module now has **0 dead declarations** (the AF108E `move_dead` escape clause for
  `summable_pairTerm`/`summable_succ_prod` is moot: both new headlines call `summable_succ_prod`).

### 6.3 The consumer zone

`spec/SetAF109Consumer.lean` composes across orders rather than instantiating, and it elaborates at
**exit 0** (three theorems, two zones):

* **Zone 1 — the `q`-expansion at every representative of the `u`-coset.** Order F's two rows give the
  expansion at `u`; the module's own `pointX_zpow_mul` / `pointY_zpow_mul` say the coordinates are
  `q`-periodic in `u`. Composed: `pointX_qExpansion_zpow_mul` / `pointY_qExpansion_zpow_mul`, i.e. the
  expansion stated at `q ^ n * u` — the form a call site holds, since the point-arithmetic layer works with
  representatives of the coset, and the form in which `TateCurve/Tails`' coefficient bounds apply.
* **Zone 2 — the trace-dual vanishing set as a *lattice* condition.** Order G's Fourier row (the finite-part
  vanishing set is the trace dual of the unit ideal) composed with order G's lattice row
  (`dualSubmodule (traceForm.flip) (idealLattice K I)` is the `mixedEmbedding` of the dual ideal) at
  `I = 1`, closed with `mixedEmbedding_injective`: `forall_addChar_finitePart_mul_eq_one_iff_mem_dualSubmodule`
  states the vanishing set as `mixedEmbedding F ξ ∈ Λ^*`, which is the form Poisson summation consumes.

The two zones are the set's real composition test: zone 1 needs F's row *and* a row of the module it was
inserted into, zone 2 needs the two rows of one order *and* the injectivity of `mixedEmbedding` from the
module it was inserted into — neither is an instantiation.

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af108/unport_final.txt)) > build/shelf_af109_final.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 247 / 150,338 | **236 / 144,835** |
| ready rows | 14 / 5,576 | **12 / 2,342** |
| leaves | 5 / 13,761 | 5 / 13,761 |
| withheld (FR-0044 guard) | 5 / 1,648 | 5 / 1,648 |

The delta is **−11 nodes / −5,503 lines**, exactly the cut, and the correction list is unchanged (the same
20 names: this set's rows are new declarations and new modules, and `--selfcheck` still reports the same
twenty lines).

**Nine rows became ready (2,269 silo)** — the shape of the new head is this set's payoff:

* **`AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le`
  (645)** — order A's consumer: the *norm bound* on the Whittaker coefficient that the entire-Euler-product
  identity was the last input for. It is the largest row on the new shelf;
* **`TateCurve.defect_qExpansion` (368)** — order F's consumer (the defect coefficient's `q`-expansion, the
  next step of the torsion-parametrisation layer the def-layer module opened);
* **`NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace`
  (360)**, `…exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar` (242),
  `…forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles` (144) and
  `…iff_exists_mem_traceDual` (99) — four consumers of order G's trace-dual row;
* **`AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one` (216)** —
  orders B/C's consumer (the genus-degree bound in the `krullDimLE`-one form);
* **`AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero` (170)** — order D's;
* **`ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC` (25)** — order E's non-`charP` form,
  now derivable from the `charP` equality.

The three rows that stayed are unchanged from SET-AF108 §7: the two definition-gated ones
(`rep_tateModule_jOne_comm` 24, `defectCoeff_zero` 13) and the false ready
(`exists_sum_smul_eq_of_isIntegralQExp_gamma1` 36).

## 8. What the set leaves behind

**The shelf halved**: 5,576 ready silo → 2,342, and the two largest rows the set left are a 645-line
AutomorphicForm bound and a 368-line Tate-curve row — a shelf of *consumers of this set*, not a new pile of
engines. The next set is therefore another consumer set of ~2,300 silo, or a definition-layer wave (the
five leaves, 13,761, all def-gated) if the column prefers to open the `TateCurve` torsion layer first
(order F's `q`-expansions and the def module were its first step).

Five things carried beyond the files:

* **five new frictions**, three of them about **name resolution and the checker's text hashing**:
  **FR-0325** (a ready row whose *statement* needs an unported `Def_` module is not statable — the def-layer
  read is the only gate that sees it, and `TateCurve/Tails.lean` is the worked cure), **FR-0326** (promoting
  a neighbour module's `private` block is a *cost* instrument, with the correction that two of the fourteen
  were different lemmas, not the same one), **FR-0327** (`open` order fixes name collisions; a collision that
  reaches a term the statement spells bare is fixed on the proof side only), **FR-0328** (`private` gives no
  shadowing exemption), **FR-0329** (a projection in the same namespace beats every `open`; `local notation`
  is the hash-preserving cure) and **FR-0330** (a substitution table built from the name index is not a
  substitution table).
* **the promotion precedent is now measured twice**: SET-AF108F's fourteen rows (11 + 1 + 2, §6.1) and the
  def-layer module — both are the recipe's "promote instead of copy" applied *before* dispatch, which is when
  it is cheap.
* **the def-layer read is now a first-class scoping step** (§0's `0 public / n absent` classification:
  structure field vs. def), and it is the gate that `--selfcheck` and the readiness test both miss.
* **three CARRY-FORWARD items**: `mem_compositeRing_iff` (3 lines, deferred with its cost), the doubled
  `mem_range_of_forall_ord_nonneg` (strong row now in `PlaceReductionRiemannRoch`, weak namesake in
  `ConstantFieldExtensionDivisor`; no gate sees the pair), and `ArchKType.majorant_integrable`'s promotion
  (now a `dedup` decision, since its sibling copy is public).
* **the consumer-zone practice**: `spec/SetAF109Consumer.lean` is the set's only artifact that *uses* the
  rows together; the two zones are recorded in its header and its exit code is the metric.
