# Ready shelf 3 — the `ModularCurve` residue after shelf 2 (2026-11-01)

**Status: landed (2026-11-01); all five rows green, §11 is the measured record.** Two agents, one at a
time: orders A + C, then order B. This is the "one new shelf pass, not a continuation" that
[TOPIC-ready-shelf-2.md](TOPIC-ready-shelf-2.md) §12 called for. It reads the `ModularCurve` ready
block on the tree shelf 2 left (`2ccb5e5`; the Lean tree unchanged since `0f5039f`), and the
instrument reproduces shelf 2 §12's baseline **figure for figure** — that is this pass's stability
check, so the only deltas it reports are corrections of the read, never movement of the tree. The
recipe is [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md).

The corrected ready block is **6 rows / 2,450 silo**; the cut is **5 rows / 2,426 silo**, priced at
**2,046 net new math lines** (≈2,066 by hand), in **three orders** over **three disjoint files**.
One further row (24 silo) is named and deferred as unstatable. The set's one structural finding is on
the 1,123 row: the pin proves its whole prelude **twice**, and the port already holds that prelude
privately in `LevelN/GenusFF.lean`, which decides the home and removes the set's only potential
promotion lane (§4). Its second finding is on the 128 row: 97 net lines gate a 23-consumer project
block, but **nothing on the D–S shelf becomes ready** when it lands (§8).

**The dispatch brief is [WORKORDER-RS3-ready-shelf3.md](WORKORDER-RS3-ready-shelf3.md).** Its §0
records the manager's prep as measured-empty: no `Def_` node, no promotion, no migration, no bridge;
the `spec-pin:` lines are declaration-coupled and go in with each landing (a wire ahead of its
declaration is MD-001's false marker). The checker baselines it carries were taken on this tree
(`GenusFF` 2 ok, `ModularPolynomialCoset` 34 ok, `SiegelUnit/Integrality` 116 ok,
`LevelN/SpecialRamification` 18 ok; all 0 / 0).

| figure | instrument | corrected (§0.1) | this cut (§0.3) |
|---|---:|---:|---:|
| `needed [F terminal]` | 931 / 378,258 | 932 / 378,519 | — |
| ready, all namespaces | 66 / 13,860 | 66 / 14,085 | — |
| leaves, all namespaces | 262 / 64,874 | 262 / 64,874 | — |
| `ModularCurve` ready | 7 / 2,486 | **6 / 2,450** | **5 / 2,426** |
| `ModularCurve` leaves | 0 / 0 | 0 / 0 | 0 / 0 |
| `ModularCurve` demand | 102 / 56,185 | 102 / 56,185 | — |
| withheld (FR-0044) | 4 / 831 (2 MC / 610) | 4 / 831 | 4 / 831 |
| cone (target closure) | 2,103 / 982,173 | 2,103 / 982,173 | — |
| avoided R (prunable) | 140 / 74,620 | 140 / 74,620 | — |
| frontier F | 1,484 / 749,108 | 1,483 / 748,847 | — |

No Lean was run while scoping: the read is `frontier.py`'s cached graph, the pricing is
`port_advise`/`port_plan`, and the definition audit is `spec/gate_scan.py`, `twin_scan.py` and a
hand read of the pin statements.

## 0. The read

Canonical, with `--selfcheck` and the corrected pass as the recipe requires:

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc3shelf.json
python3 frontier.py --selfcheck
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast > build/mc3shelf-corr.json
```

- **`--selfcheck` PASSes** (1,319 `Thm_` sources, 1,484 union nodes / 749,108 raw): the
  false-marker inventory is empty, MD-001–003 stay resolved. The one correction below is not a
  `spec-pin` artifact; it is the FR-0047 name shadow, which the check cannot see.
- **The read is stable.** `needed` 931 / 378,258, frontier 1,484 / 749,108, ready 66 / 13,860, MC
  ready 7 / 2,486 — exactly shelf 2 §12's "after the wave" column. The tree has not moved, so this
  pass's numbers are the residue shelf 2 predicted, re-measured.
- **`--ds` is the subtraction, and the report's cone line is not the work line.** `needed [F
  terminal]` is 931 / 378,258 against a literal cone of 2,103 / 982,173; the avoided set is 140 /
  74,620. The `ModularCurve` demand is 102 / 56,185, of which this shelf is 2,450.
- **The leaves block is not this column's.** `ModularCurve` leaves are **0 / 0**; the 262 rows /
  64,874 lines of other namespaces are named and deferred (FR-0040), and `--include-leaves` is part
  of the read only for the column's sake.
- **The withheld block is unchanged and is not this shelf's**: four rows / 831 silo, the two
  `ModularCurve` Tate-module rows (`moduleFinite_and_free_padicInt_tateModule_jH` 327,
  `moduleFinite_padicInt_tateModule_jOne` 283) on `AlgebraicCurve.Pic0.abelJacobiCard_genus`, and two
  `AlgebraicCurve` rows (126, 95) on the prunable Abel–Jacobi subject. The `ModularCurve` part is
  610 silo. Quote and defer; they wait on the Abel–Jacobi programme plus
  `Def_EllipticCurve_TateModule`.
- **The read is taken twice.** The corrected pass unports the 261-line
  `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, which the port holds only as a
  `CuspForm` last-name shadow: `needed` moves 931 / 378,258 → **932 / 378,519** (+1 node, +261
  lines), the shelf loses the 36 row, and the ready total moves 13,860 → 14,085 because the 261
  enters as a `ModularForm` ready row. **The corrected figure is the one to quote**, and it was
  produced by unporting the 261 only — the same single-marker correction shelf 2 used; the
  `weilReciprocity` shadow is unchanged from shelf 1/2 and is not a row of this shelf.

### 0.1 The correction, and the two rows it names

| node | silo | why it is not a row of this shelf |
|---|---:|---|
| `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` | 261 | in the **demand**, not on the MC shelf: the `CuspForm` twin's last name shadows it (FR-0047), which is why the MC row below reads ready. A `ModularForm` row; the chain is 261 → 36 and [TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §8 has deferred it since shelf 0. |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | its only substantive premise is the 261 above, so it is a false ready; the corrected read drops it (2,486 → 2,450). Same chain, same deferral. |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | its *premises* are ported (`JOne.galois_smul_heckeAlgOne_smul`) but its *statement* is `TateModule.rep …`: `Definitions/Def_EllipticCurve_TateModule.lean` (883 pin lines / 69 declarations) is unported and the port has no `TateModule.rep` at all. Not statable. The padic-Tate-module programme's row ([TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md)). |

So the shelf is **6 rows / 2,450 corrected**, of which 5 / 2,426 are cut and 1 / 24 is deferred.

### 0.2 The definition audit — no gate

`port_advise --with-defs` puts six pin `Def_` modules in the five cut rows' closure (16 target
files, 372 declarations). `spec/gate_scan.py` was run per module over the rows that use it, at
the **declaration** level the work is written in:

| pin `Def_` module | public decls | rows using it | used | **missing** | lines |
|---|---:|---:|---:|---:|---:|
| `ModularCurve_SiegelFunction` | 2 | 249, 469, 457 | 1 | 0 | 0 |
| `ModularCurve_X0` | 61 | 1123, 128 | 8 / 16 | 0 | 0 |
| `ModularCurve_JqCoeff` | 11 | 1123, 128 | 1 / 1 | 0 | 0 |
| `ModularCurve_PrimCosetReps` | 5 | 128 | 3 | 0 | 0 |
| `ModularCurve_X1` | 35 | 457, 1123 | 1 / 4 | 0 | 0 |
| `AlgebraicCurve_DivisorClassGroup` | 63 | 1123, 128 | 8 / 2 | 0 | 0 |

**0 missing on all six**, so the five rows are statable against the landed layer: **no definition
lane, no new definition, no promotion for a missing structure**. The three same-last-name neighbours
the instrument flags are specialisations the rows do not consume (`coeff_jqModC_of_lt` at `K` vs the
pin's `R`, `isIntegral_intCast`/`isIntegral_natCast` private in the Siegel modules) — read, not
imported.

### 0.3 The shelf, quoted whole

| row (`ModularCurve.` dropped) | silo | prem | prem unported | prem pruned | lev cone / proj | status |
|---|---:|---:|---:|---:|---:|---|
| `natCard_doubleCoset_le_card_fibres_of_finrank_eq_index` | 1,123 | 10 | 0 | 0 | 1 / 3 | **cut, order B** |
| `SiegelUnit.isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` | 469 | 5 | 0 | 0 | 1 / 1 | **cut, order A** |
| `SiegelUnit.qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` | 457 | 2 | 0 | 0 | 1 / 1 | **cut, order A** |
| `SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` | 249 | 3 | 0 | 0 | 1 / 2 | **cut, order A** |
| `ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero` | 128 | 6 | 0 | 0 | 2 / 23 | **cut, order C** |
| `rep_tateModule_jOne_comm` | 24 | 1 | 0 | 0 | 1 / 6 | unstatable; deferred §0.1 |
| | **2,450** | | | | | 2,426 cut · 24 deferred |

The instrument's eighth row (`exists_sum_smul_eq_of_isIntegralQExp_gamma1`, 36) is the 261 shadow
and leaves on the corrected read. `premises_pruned` is 0 on all six, so the FR-0044 guard does not
bite; the withheld pairs are elsewhere (§0).

## 1. The cut

**5 rows / 2,426 silo / 2,046 net**, three orders, three files, all disjoint:

| order | story | rows | silo | net | home |
|---|---|---|---:|---:|---|
| **A — the Siegel product form and its q-expansion** | one product, one modularity, two q-expansion conclusions | 249 + 469 + 457 | 1,175 | 1,075 | **new** `ModularCurve/SiegelUnit/ProductForm.lean` |
| **B — the special-fibre bounds for `j` on `X(N)`** | the double-coset ↔ place count over `0`, `1728`, `i∞` | 1,123 | 1,123 | 878 | insert `ModularCurve/LevelN/GenusFF.lean` |
| **C — separability of `Φ_N` over `K(X)`** | the transcendental transfer of the coset-root separability | 128 | 128 | 97 | insert `ModularCurve/ModularPolynomialCoset.lean` |
| | | **5** | **2,426** | **2,046** | 1 new, 2 inserts |

What is deliberately not one order:

- **A's three rows are one story.** The 249 row builds the form `u_μ Δ^t`; the 469 and 457 rows are
  its two q-expansion conclusions (width `N` and width 1), and both take the 249 statement as a
  *hypothesis* (`hϑ`), so they are its consumers, not siblings. The pin itself puts them in three
  files because each is a self-contained `solution`; the port should not. The instrument's *port
  once* block finds **no shared prelude** (only `T_pow_mem_Gamma` is proved twice, 5 lines), so the
  module is three developments side by side, not one engine.
- **B is alone** although it is 1,123 silo: its ten graph premises are the D–S set's heaviest wall
  (the recipe's "a 15-premise node is where a set stalls" at 10), and its pin carries the set's only
  heartbeat cap (§5.1). It gets its own order and its own wall time. It is *not* merged with C:
  the subjects share `transcendental_jqModC` and nothing else.
- **C is alone** although 128 silo prices at 97: its subject is the separability of `Φ_N` over
  `K(X)`, a different theorem from B's counting bound, and its value is the block it gates
  (§8), not its size.

The recipe's dispatch guide (1,300–1,600 silo per order) leaves A and B each a little under it and C
well under; there is no fourth subject on the shelf to merge into C without mixing stories, and a
2,426-silo wave over three disjoint files is one dispatch, not two.

## 2. The rows

Each pin `S_` file is a **flat public surface** (`port_advise` drags: 0 helpers in all five), so the
transcription is the file, not a headline plus a private prelude. Figures are the `S_` file's lines.

1. **A — `SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow`
   (249).** The pin's `FORM` block: `uFun = ∏_{r,s} siegelFun^{12Nm(r,s)}`, the weight `Ord`, the
   row action `rowMul` on `ZMod N × ZMod N`, the multiplier transport `uFun_smul`, the cusp decay
   `thetaFun_slash_isBigO` (via `discr_isBigO` and the exp bound), then `theta` as a `ModularForm
   Γ₁(N) (12t)` with `theta_apply` and the existential `solution`: some `ϑ` equals the product and
   every `S`-slash is `O(exp(-2π((Ord β)/N + t)·im))`. 24 declarations; the port's only near-match
   is the type-only `uFun → LevelN.jAnalytic`, which is not an import (§3).
2. **A — `…isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow`
   (469).** The pin's `GammaS`/`restrictMF`/`Thetaform` block (the `S`-conjugate group, the
   restriction of scalars, the slash as a form on `GammaS`), the `hasSum_shift`/`hasSum_spread`/
   `qExpansion_coeff_eq_of_hasSum_div_qParam_zpow` engine, then `uProd`, `uProd_S_smul`,
   `slash_S_apply`, `hasSum_discriminant_pow`, and `main`: for a form `ϑ` equal to the product, there
   is `a` with every coefficient of `qExpansion N (ϑ ∣[12t] S)` integral after multiplying by `N^a`.
   31 declarations.
3. **A — `…qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` (457).** The pin's
   `INTINF` block: `sigmaSeries`, `E4Z`/`E6Z`, `P144`/`P1728`, `deltaZ`, the discriminant q-expansion
   arithmetic, the `EvA`/`deltaN`/`CoeffMem` coefficient calculus, then `solution`: with
   `m₀` pinned by `N m₀ = Ord + N t`, the width-1 q-expansion of `ϑ` vanishes below `m₀`, is
   non-zero at `m₀`, and `N^a` times every coefficient (and the inverse of the `m₀` coefficient) is
   integral. 45 declarations.
4. **B — `natCard_doubleCoset_le_card_fibres_of_finrank_eq_index` (1,123).** The pin's
   `SpecialFibresLB` development: the three special points (`E₄_ρ`, `E₆_I`, `jAnalytic_ρ`,
   `jAnalytic_I`), the subgroup `Gpm`, the order-of-`σ'` block (`orderOf_σ'_S/ST/T`,
   `subsingleton_gal_of_lt_two`), the three place-existence lemmas (`exists_place_1728/zero/infty`),
   the `K`-model (`σK`, `jK`, `finrank_fixedField_map`, `isGalois_jK`), the Galois package, then
   `main_K` (≈170 lines) and `main`: three inequalities bounding the double-coset count of
   `Γ` by the number of places where `j` is `0`, `1728`, or has a pole. 83 declarations.
5. **C — `ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero` (128).** The pin's
   `IgusaSepAux` block: the general transfer `separable_map_ratFunc_of_transcendental` (separability
   descends along a transcendental generator), `map_aeval_comp_mapRingHom_intCast`, the
   `jqModC` coefficient facts, `qExpandAlg`, `transcendental_qExpand_jqModC`, then `solution`: for a
   field `K` with `(N : K) ≠ 0`, `Φ_N` with its coefficients cast to `K`, then mapped into `(K(X))[Y]`, is separable. 7
   declarations.

### 2.1 The pin's own duplication is the 1,123 row's story

The 1,123 `S_` file and the ported genus row's `S_` file
(`S_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF`) share **21 declaration names**,
including `E₆_I`, `Gpm`, `dvd_of_ST_pow_mem`, `apply_eq_self_of_mem_adjoin`,
`isIntegral_of_apply_eq`, `liftE`/`liftHom`, `isDomain_ring`, and both carry a `main` and a
`solution` under different namespaces (`GenusBound` vs `SpecialFibresLB`). The port already wrote
**15 of those declarations once, privately, in `LevelN/GenusFF.lean`**, and the pin's namespaces
split cleanly: the private `ModularCurve.LevelN.GenusBound.main` is the genus inequality, the new
`ModularCurve.SpecialFibresLB.main` is the fibre bound. That is recipe §4's promotion-or-copy rule
in its cheapest form — the copy is already in the home, so nothing is promoted and nothing is
copied (§4).

One further false premise to record: the 1,123 file imports `Thm_WLight_levelN_structure_package`,
but uses it **only** for its no-zero-divisors clause (`isDomain_ring`, line 846). The port holds
that conclusion publicly, at a more general binder spelling, as
`ModularCurve.LevelN.isDomain_ring (M) [NeZero M]` (`LevelN/FieldGalois.lean:61`, already imported
by GenusFF and used at its line 750). So the row needs no `WeightOne` import and no new hypothesis
from that package; the transcription's `isDomain_ring` step is the pin's twelve-line proof replaced
by one application.

### 2.2 The premise audit, by hand (the SET 9–10 lesson)

All 26 premise links (22 distinct nodes) are public in the port, read this pass rather than
last-name matched:

| premise | port home | statement read |
|---|---|---|
| `SiegelUnit.differentiableOn_siegelFun` | `SiegelUnit/Basic.lean:605` | the conjunction `DifferentiableOn ∧ MDifferentiable`, verbatim |
| `SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow` | `SiegelUnit/Integrality.lean:1468` | shelf 2's A row, arbitrary `N`, `e`, `e 0 0 = 0` — verbatim |
| `SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul` | `SiegelUnit/Basic.lean:733` | SET MS-4's row, every exponent function — verbatim |
| `qParam_coeff_unique` | `Analytic/QParamUnique.lean:183` | width `h`, power series — verbatim |
| `hasSum_qParam_mul` | `ModularForms/Hauptmodul.lean:119` | width `h`, `PowerSeries` — verbatim |
| `hasSum_coeff_etaProd_pow` | `ModularCurve/JqCoefficients.lean:690` | `‖q‖ < 1`, verbatim |
| `qExpansion_coeff_mul_width` | `NumberTheory/ModularForms/QExpansionCoeff.lean:406` | the port's mathlib supplement, verbatim |
| `LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin` | `LevelN/FieldGalois.lean:620` | the Galois package over a fraction field of `ring N`, verbatim |
| `LevelN.exists_place_ord_sub_pos_forall_smul_eq` | `LevelN/Places.lean:1144` | any `τ₀`, a place with positive order at `j − j(τ₀)`, stabilised — verbatim |
| `LevelN.exists_place_ord_neg_forall_smul_eq` | `LevelN/Places.lean:637` | the cusp place, negative order — verbatim |
| `LevelN.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN` | `LevelN/QExpBridge.lean:604` | the ring hom `Φ` from `qExpFunctionFieldC ℚ Γ`, verbatim |
| `LevelN.exists_place_ord_jGen_le_two_three_level` | `LevelN/SpecialRamification.lean:291` | shelf 2's D row, verbatim |
| `Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois` | `AlgebraicCurve/Place/OrbitCardinality.lean:768` | the orbit/stabiliser dictionary, verbatim |
| `isCurveOver_of_transcendental_of_perfectField` | `IsCurveOver/Transcendental.lean:119` | verbatim |
| `finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin` | `IsCurveOver/ConstantFieldExtensionSpan.lean:1657` | characteristic 0, alg closed `k` — the general form the row instantiates at `ℚ̄` |
| `transcendental_jqModC` | `Degree/PhiDegree.lean:74` | `[CommRing K]` — more general than both pins |
| `WLight.levelN_structure_package` | `ModularForms/WeightOne/LevelN.lean:93` | ported in full; the row uses only its no-zero-divisors clause, which the port also has as `LevelN.isDomain_ring` (§2.1) |
| `card_primCosetReps_eq_dedekindPsi` | `ModularCurve/Gamma0Index.lean:725` | verbatim |
| `eq_cosetTwoVarPoly_of_forall_isRoot` | `ModularPolynomialCoset.lean:320` | verbatim |
| `separable_cosetTwoVarPoly` | `ModularPolynomialCoset.lean:344` | verbatim |
| `ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex` | `ModularPolynomialCoset.lean:150` | shelf 2's B1 row, verbatim |
| `ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex` | `ModularPolynomialCoset.lean:694` | shelf 2's B1 row, verbatim |

No shadow: each is a single declaration at the pin's statement or more general. `twin_scan --node`
returns `new` on all five rows and the 24 (`new=6`), so the statements are not in the port under
another name.

## 3. The pricing

`port_advise` per order, `port_plan` on each JSON:

| order | raw `S_` | declaration lines | boilerplate | duplicate copies | already in port | **net** |
|---|---:|---:|---:|---:|---:|---:|
| A (249 + 469 + 457) | 1,175 | 1,112 | 63 | 0 | 37 | **1,075** |
| B (1,123) | 1,123 | 1,084 | 39 | 0 | 206 | **878** |
| C (128) | 128 | 103 | 25 | 0 | 6 | **97** |
| **set** | **2,426** | **2,299** | **127** | **4** | **249** | **2,046** |

The set's 4 duplicate lines are `T_pow_mem_Gamma`, proved in the 469 and the 1,123 files (the tool's
*port once* block: 4 names in ≥2 target files, and this is the only one whose copies sit in two
target files); write it once, publicly, at the pin's name, in whichever home is above both
(`LevelN/Prelude.lean` already holds the port's copy).

`port_plan`'s sections, and the hand corrections:

- **substitute** — 37 declarations (≈278 lines) already have their statement in the port, 19
  importable and **18 only as a port-private declaration**: 15 in `LevelN/GenusFF.lean` (the
  1,123 prelude, 165 lines), `restrictMF` (private in `WLightS10`; the port's other copies,
  `ModularForms/Level/Degeneracy.lean:44` and `DeligneSerre/Lifting.lean:70`, are private too —
  errata at dispatch, so it is re-spelled in the new module, not imported), `isIntegral_intCast` (4 lines, private in
  `SiegelUnit/Integrality.lean`) and `isIntegral_natCast` (7 lines, private in
  `SiegelUnit/Eisenstein.lean`). The instrument's 2,046 counts all of them as in-port; that is true
  for the 1,123 prelude **only from inside `GenusFF`** (§4), and true for the two `IsIntegral`
  helpers by re-spelling them in four and seven lines. **Do not promote** the helpers: they are
  generic `IsIntegral ℤ (z : ℂ)` facts with no consumer, and a promotion buys public surface for
  nothing.
- **generalise** — 8 names in the target set share a conclusion with different binders and 5 share
  a name with a different statement; take **the wrapper's binders**. The two that matter: the pin's
  `isDomain_ring : IsDomain (LevelN.ring M)` (a section variable) vs the port's explicit
  `(M) [NeZero M]`, and the pin's `main`/`solution` pair, which is a **namespace split** (the pin
  proves `main` twice, `GenusBound` and `SpecialFibresLB`; both have consumers, so both are written).
  Binder-only variants to take from the wrapper: `qParam_one_eq_pow` (9 statements over 37 files),
  `Gamma_le_Gamma1` (7), `T_mem_Gamma1` (8), `T_pow_mem_Gamma` (3), `natCast_pos`, `conj_mem_Gamma`,
  `coeGL_mul`, `GammaS`.
- **drags** — **0 helpers on all five files**: every pin file is a flat public surface, so no
  private prelude is hiding in a headline's closure.
- **false negatives (FR-0069).** The 37 substitutions include **seven type-only `def` matches**:
  `uFun → LevelN.jAnalytic` (3), `thetaFun → EIS2K1.qN` (2), `P1728 → e1Chi3` (3),
  `P144 → e1Chi3` (2), `deltaZ → e1Chi3` (3), `sigmaSeries → EtaQSeries.f` (3), and
  `GammaS → CohCarrier.Gamma0Upper` (4). They share a type, not a value (`P1728` is a period, not an
  Eisenstein coefficient; `GammaS` is an `S`-conjugate, not the upper-triangular group). The brief's
  hand figure is therefore **≈2,066**, not 2,046; the 20 lines are all in order A. The instrument
  cannot see the converse either: a port theorem with *weaker* hypotheses reads as new (FR-0078),
  which is why the 128 row's `separable_map_ratFunc_of_transcendental` is priced new and written.

## 4. The homes, and the import direction

Subject first, then the import direction (recipe §4): every premise's port module must sit at or
below the home. Checked against the port's import graph (reachability on `import
FLTForHuman.…`); no cycle in any of the three.

| order | home | why | host now / after | dependents |
|---|---|---|---|---|
| A | **new** `ModularCurve/SiegelUnit/ProductForm.lean` | "the Siegel product `u_μ Δ^t`: modularity and its integral q-expansion" is one subject with three conclusions; a new module is cascade-free and the name says the mathematics. Imports `SiegelUnit.Integrality`, `ModularForms.Hauptmodul`, `ModularCurve.JqCoefficients`, `ModularCurve.Analytic.QParamUnique`, `NumberTheory.ModularForms.QExpansionCoeff` (all new imports, all acyclic) | — / ≈1,100 | new |
| B | **insert** `ModularCurve/LevelN/GenusFF.lean` | the pin's prelude **is** this module's private prelude (21 shared names, 15 already written, §2.1); the row is the second headline of the dimension-tower development, and its `SpecialFibresLB` namespace is disjoint from the private `GenusBound.main`. New imports: `LevelN.QExpBridge`, `LevelN.SpecialRamification`, `IsCurveOver.ConstantFieldExtensionSpan`, `Degree.PhiDegree` — `OrbitCardinality`, `IsCurveOver.Transcendental` and `WeightOne.LevelN` are already in the closure | 784 / ≈1,650 | `Period/ParabolicHomsBasis` (re-elaborates; a price, not a veto) |
| C | **insert** `ModularCurve/ModularPolynomialCoset.lean` | the row is the separability conclusion of the module's own coset-root engine (`separable_cosetTwoVarPoly`, `eq_cosetTwoVarPoly_of_forall_isRoot`); `Gamma0Index` is already in the closure, `Degree.PhiDegree` is one new acyclic import | 871 / ≈970 | **0** |

**Why B is not a new module.** A new `LevelN/SpecialFibres.lean` would be the cleaner name, but
`GenusFF`'s 15 private declarations are not importable (private declarations are invisible even to
the checker), so the new module would have to re-prove or promote **165 lines** — a 15-declaration
promotion lane with its own surface gate — for a naming preference. The subject argument does not
demand it: both pin files are the same dimension-tower development, and the port already wrote the
shared half once. The recipe's rule is explicit: promote or move the mathematics to where it is
needed, rather than let the next node copy 150 lines. Here the mathematics is already where it is
needed; only the *headline* is missing. The alternative is recorded for the reviewer: if the
namespace should instead be `LevelN/SpecialFibres.lean`, the lane is 15 promotions (§4 above) and
the price rises to ≈1,043.

**Why A is not an insertion.** `SiegelUnit/Basic.lean` is the multiplier/differentiability module
and `SiegelUnit/Integrality.lean` the single unit's integral q-expansion; the product form is a
third layer that consumes both, and inserting into either would edit a module the other imports
(`Integrality` imports `Basic`) for no homing gain. A new module above both is cascade-free.

**No legacy home.** None of the three homes is in `spec/old_check_stmts.py`'s `PORT_FILES`; the new
module is fresh and the two insertion hosts are already wired. The set has **no migration**.

**The manager lane is wiring only.** For A, the new module's `spec-pin:` header carries six lines
(the wrapper and the `S_` file of each of the three rows) plus the prose. For B and C, two `spec-pin:`
lines and the prose are added to each host. **No promotions, no migrations, no definitions.** The
one thing to check when B's second source is wired: `GenusFF`'s public surface is exactly its two
headlines, neither of which appears in the 1,123 source, so the checker reads clean `ok` rows and no
`MISMATCH` from the doubled wire.

## 5. The traps

1. **B carries the set's only heartbeat cap, and it is the wall.** The pin sets
   `synthInstance.maxHeartbeats 1600000` at module level and `maxHeartbeats 6400000 in` on `main_K`
   (lines 26 and 895). The port's build cap is 4M (`lakefile.lean`) and the edit loop is 200k. Plan:
   state the public headline and probe the `main_K` block in `tmp/` with its own `sorry`-cut lemmas;
   split along the pin's own factoring (`finrank_fixedField_map`, `galoisPackage`, the three
   `exists_place_*`, `main_K`, `main`); replace the module-level synthInstance cap by an explicit
   instance, as shelf 2's order C did with `Module.Free`/`finrank_pos_iff_of_free`. **Never bump the
   cap.** If a declaration cannot meet the 200k loop, report it as a localised overrun in the FR-0074
   form, with the module still building, instead of raising the cap or dropping a gate.
2. **The pin's attribute walls are artifacts.** The 1,123 wrapper carries two long
   `attribute [-instance]`/`[-simp]` walls and the 469 wrapper a 13-lemma `[-simp]` wall; the port
   does not transcribe them (its modules build silent without them — the `GenusFF` header already
   records that for its own wall). If a transcription *needs* one, add a local `simp only` at the
   call site, never a module-level wall.
3. **`include K hΓ in` and the `variable (Γ) (hΓ)` block.** The pin's `main_K` is stated under
   `variable (Γ : Subgroup SL(2,ℤ)) (hΓ : Gamma1 M ≤ Γ)` with a `local notation ℚ̄`/`FF` and
   `include K hΓ in`. The port's convention is to make the variables explicit or split the section
   (shelf 2's D deviation: `omit … in theorem` did not parse, so the pin's `variable (M) (K)` block
   was split into three, declaration text unchanged). Do the same: the wrapper's statement spells
   `AlgebraicClosure ℚ` and `laurentBaseChange …` in full, and that is what the checker diffs.
4. **The same-last-name pair is a namespace split, never a rename.** `GenusBound.main` (private,
   the genus inequality) and `SpecialFibresLB.main` (new, the fibre bounds) are two statements with
   one last name; the pin itself writes both. Keep both, in their pin namespaces. The new
   development's references to the prelude are by qualified name from `namespace ModularCurve`
   (`LevelN.GenusBound.dvd_of_ST_pow_mem`, or `open ModularCurve.LevelN.GenusBound in …` at a
   section head); the checker hashes statements,
   not qualified names, so the 15 private copies still match the 1,123 pin's `SpecialFibresLB`
   spellings if the surface gate ever promotes them.
5. **The two `IsIntegral` helpers and `restrictMF`.** `isIntegral_intCast` (4 lines) and
   `isIntegral_natCast` (7 lines) are private copies; re-spell them in the new module from
   `isIntegral_algebraMap` (an `own:` row if the checker objects — the manager's call). `restrictMF`
   has **no public copy** in the port (`ModularForms/Level/Degeneracy.lean:44` is `private` inside
   `ModularForm.DegeneracyPort`; `DeligneSerre/Lifting.lean:70` another private copy), so it is
   re-spelled privately in the new module too — promotion would be a hub edit with a cascade for
   four lines, and the checker reads only public declarations.
6. **A's seven type-only `def` matches must not be imported** (§3): write `uFun`, `thetaFun`, `Ord`,
   `P144`, `P1728`, `deltaZ`, `sigmaSeries` and `GammaS` from the pin. Importing `P1728 = e1Chi3`
   would be a silent mathematical error, not a compile error.
7. **C's engine is new and its helpers are not.** `separable_map_ratFunc_of_transcendental` (10
   lines) and `map_aeval_comp_mapRingHom_intCast` (5) are the row's own; `coeff_jqModC_neg_one`,
   `coeff_jqModC_of_lt` and `qExpandAlg` are already public (`Defs/JqCoeff.lean`,
   `Defs/Laurent.lean`) with only binder spelling to adjust. Take the port's binders.
8. **The 24 row is not statable and does not belong in this wave.** It is `TateModule.rep …` with
   `Def_EllipticCurve_TateModule` (883 lines / 69 declarations) absent, plus D2's deferred
   `rationalHeckeRepOne`. Defer to the padic-Tate-module programme; the wave's B row removes one of
   its hypotheses (`hcomm : HeckeDiamondCommuteBar`) without making it statable.

## 6. The gates, per order

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, every added
   declaration `ok` (or an `own:`/`pin:` row in `spec/decl_markers.tsv`, which the manager writes).
   For the two insertions the module's `spec-pin:` header carries both the old and the new sources.
2. `#print axioms` on the five headlines → `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`/`native_decide`.
3. The module's own `lake build` under `flock`/`timeout`, and **the module silent**; a `Replayed`
   line is not evidence that its `.olean` exists — build the defining module explicitly (FR-0033).
   No tree build.
4. `dedup.py` / `move_dead.py` on the module; wrapper-over-engine `shape` clusters stay where they
   are the pin's own pattern (`main`/`solution`, `theta`/`theta_apply`), with the reason recorded.
5. One `spec/` consumer zone for the wave, proposed `spec/ModularCurveReady3Consumer.lean`, one zone
   per order, with a real cross-module composition and no `#check`s:
   A applies 249 to get `ϑ`, then 469 and 457 to get `a`, the order `m₀` and coefficient
   integrality, and composes the product with `SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul`;
   B instantiates the three inequalities at a concrete `K` (the port's `LevelN/FunctionField` model)
   and composes them with `LevelN.exists_place_ord_jGen_le_two_three_level` and the genus inequality;
   C composes the new separability row with `ModularPolynomialFibreTwo`'s `Φ₂` data and
   `separable_cosetTwoVarPoly`. **The error count is the deliverable metric.**
6. No `set_option maxHeartbeats`, no `set_option synthInstance.maxHeartbeats`, no warnings, no
   `sorry`, no marker rows written by a worker. Files are disjoint across A–C (A: the new
   `SiegelUnit/ProductForm`; B: `LevelN/GenusFF`; C: `ModularPolynomialCoset`), so all three may run
   concurrently **after** the manager's wiring lane; B needs its own wall time (§5.1).
7. **The surface gate, at review (recipe §5).** Run it on B in particular: drop `private` from
   `GenusFF`'s 15 prelude declarations, `check_port --force` the module, and read the three numbers.
   Every `ok` is a pin-faithful statement the pin states public (both the genus source and the 1,123
   source carry it), so promoting it is the pin's own surface, not new mathematics; every `MISMATCH`
   is a prelude copy re-spelled in the module (keep it private); every `MISSING` is a port-side
   helper. Nothing about the proofs changes — only `private`, and the checker's spelling where it
   objects. A's new module and C's insertion get the same experiment; their only port-private
   helpers are the two `IsIntegral` re-spellings. Running the gate on B is optional for the wave's
   green state but is the honest way to say what the module's checked surface is.

## 7. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. the cut | **5 rows / 2,426 silo / 2,046 net** (≈2,066 hand) | not the instrument's 6 / 2,450: the 24 is unstatable, and the 36 leaves on the corrected read |
| 2. the orders | **A (1,175), B (1,123), C (128)**; A is one story of three layers, B and C are single-story orders | 3 dispatches, disjoint files |
| 3. the definition layer | **none** — six `Def_` modules, gate_scan 0 missing | no def-lane work |
| 4. the manager lane | **wiring only**: 6 `spec-pin:` lines for A's new module, 2 each for B and C, plus prose | no promotions, no migrations, no new definitions |
| 5. the homes | A **new** `SiegelUnit/ProductForm.lean`; B **insert** `LevelN/GenusFF.lean`; C **insert** `ModularPolynomialCoset.lean` | 1 new module, 2 insertions, **no migration** |
| 6. the risk | B's `main_K` at the pin's 6.4M / 1.6M caps: probe first, split along the pin's factoring, replace the synthInstance cap by an explicit instance, report as FR-0074 if unmet | the set's only schedule risk |
| 7. the 36 row and the 261 | **defer** (shelf 1 §0.1/§8, unchanged): the `ModularForm` Gamma₁ basis theorem, ≈4.8k raw / ≈2.1k `S_` | not a row of this shelf |
| 8. the 24 row | **defer** to the padic-Tate-module programme | not statable |
| 9. the withheld pair | **defer** unchanged (610 silo MC, `abelJacobiCard_genus`'s 144-node / 66k programme) | not a row of this shelf |
| 10. the leaves | **defer** the 262 / 64,874 other-namespace rows (FR-0040); MC leaves are empty | nothing to cut |

## 8. The forecast

The five rows' direct consumers, read off the graph (each consumer counted once, whole file — a
bound, not a price), in the two readings the read reports:

| row | cone consumers (D–S) | project consumers |
|---|---|---|
| A (249) | **252** — `SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd` | + 1,267 `exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral` (needs two more unported premises) |
| A (469) | 252 | — |
| A (457) | 252 | — |
| B (1,123) | **689** — `genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd` | + 833 `natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index`, 700 `natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset` |
| C (128) | **1,133** — `WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`; **292** — `….exists_equiv_addSubgroup_isAddCyclic_isRoot_…` | **23** in all, headed by 4,896 `exists_frobeniusSemilinear_torsionModel_ofJ_univ`, 4,118 `CharPModel.FibreModel.spPlace_surjective`, 3,445 `PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed`, 2,515 `exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ`, 594, 546, 501, … (the mod-ℓ / Igusa / CharPModel block) |

**What becomes ready because of the set, re-read not guessed.** Landing all five and re-running
`analyze` with the five added to `F` (the corrected read):

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 932 / 378,519 | **927 / 376,093** |
| frontier F | 1,483 / 748,847 | 1,488 / 751,273 |
| ready rows | 66 / 14,085 | 62 |
| `ModularCurve` ready | 6 / 2,450 | **2 / 276** (252 + the 24) |
| leaves (all namespaces) | 262 / 64,874 | 262 / 64,874 (MC leaves still 0 / 0) |
| became ready because of the set | — | **1 row / 252 silo** — `SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd` |

`needed` moves by exactly the five rows' silo (−2,426 lines, −5 nodes) with no extra declaration,
and the MC shelf is reduced to the one new row plus the deferred 24. **The larger blocks do not
open**: the 1,267 needs two more rows besides 249, the 833/700 pair each needs a sibling, and C's
1,133/292 and its 23-project block each carry other unported premises — the same "a bound is not a
price" that shelf 2 recorded. C's value is that it is a *premise* of that block, not that it makes
any row ready.

## 9. Reproduce, and the three numbers

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc3shelf.json
python3 frontier.py --selfcheck
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast > build/mc3shelf-corr.json
python3 port_advise.py --with-defs --nodes <the 5 rows> --json build/mc3-defs.json
python3 port_advise.py $(cat build/mc3-nodes5.txt) --json build/mc3-adv5.json   # the set price
python3 port_plan.py --json build/mc3-adv5.json
# per order: port_advise.py --nodes … --json build/mc3-<order>.json; port_plan.py --json …
python3 twin_scan.py --node <row> …                      # -> new x6
cd ../../lean && python3 spec/gate_scan.py --pin Definitions/Def_<module>.lean \
  --rows S_ModularCurve_<stem>
# the forecast: analyze(fr, target, frontier | {the 5}, avoided, None, "union", ready=True,
#   include_leaves=True, sort_by="silo") twice, then diff the ready rows
```

(`build/mc3-nodes5.txt` holds one `--nodes NAME` per row; `twin_scan` takes `--node` once per row.)

**The three numbers.**

1. **What the set consumes**: 5 rows / 2,426 silo; **2,046 net new math lines** by `port_plan`
   (2,299 declaration lines, 4 duplicate, 127 boilerplate, 249 already in the port — of which the
   165-line 1,123 prelude is in-port only from inside `GenusFF`, and 20 lines are type-only `def`
   matches), or **≈2,066** by hand. Three orders; **one new module, two insertions, no migration,
   no definition layer, no promotion**.
2. **The read it starts from**: `needed` **931 / 378,258** (corrected **932 / 378,519**); frontier
   1,484 / 749,108 (corrected 1,483 / 748,847); ready 66 / 13,860 (corrected 66 / 14,085);
   `ModularCurve` ready **7 / 2,486** (corrected **6 / 2,450**, cut 5 / 2,426); MC leaves **0 / 0**;
   MC demand 102 / 56,185; withheld 4 / 831; cone 2,103 / 982,173, avoided 140 / 74,620.
   `--selfcheck` PASSes. Every figure reproduces shelf 2 §12 exactly, so the tree has not moved.
3. **What the shelf leaves**: the 24 Tate-module row, the 261 → 36 chain (a `ModularForm` story), the
   withheld pair (610 MC), the 262 other-namespace leaves — and, inside this cut, nothing: the five
   rows are the whole remaining `ModularCurve` ready block. The re-read after landing must confirm
   the three numbers above (recipe §7): the consumed 2,426, the new `needed`, and the one row the
   set makes ready.

## 10. What this shelf does not do

- **The 261 chain and the 36 row** — the `ModularForm` Gamma₁ basis theorem, ≈4.8k raw / ≈2.1k `S_`.
  The corrected read prints its head at 261 silo; it is a `ModularForm` row, not this column's.
- **The Tate-module programme** — `Def_EllipticCurve_TateModule` (883 / 69), the withheld pair
  (610), and the unstatable 24; one programme,
  [TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md).
- **The mod-ℓ / X_HFunctionFieldBar / CharPModel block** — C's 1,133/292 and its 23 project
  consumers are its doors, not its body; it is its own column, gated on several rows at once.
- **The 262 leaves / 64,874 lines of other namespaces** — named and deferred (FR-0040).

## 11. The landing, measured (2026-11-01)

**All five rows landed, in the three orders, the same day.** Every module is green on §6's gates 1–6
and was re-checked by the manager: checker re-run on the module, module build under `flock`/`timeout`,
`#print axioms` re-printed, consumer zone re-run. Two agents, one at a time (A + C, then B); no tree
build was ever run.

| order | module | lines | checker | notes |
|---|---|---:|---|---|
| A | `SiegelUnit/ProductForm.lean` (**new**) | 1,216 | **3 ok / 0 / 0** | the three headlines at the wrappers' verbatim text (the pin's `Ord` sum is inlined in the wrappers too); 96 private declarations; **no declaration exceeded the 200k loop** — the whole module is silent at the cap, so this order carries no wall |
| B | `LevelN/GenusFF.lean` (insert) | 784 → **1,758** (+976/−2, the two deletions are re-worded header lines) | **3 ok / 0 / 0** | one public headline + 51 private; the host's 16 prelude declarations reused by qualified name, not copied, not promoted; **the wall did not bite** (below) |
| C | `ModularPolynomialCoset.lean` (insert) | +121 | **35 ok / 0 / 0** | `IgusaSepAux` block + 4 private helpers; **two** extra mathlib imports (`RatFunc.Basic`, `RootsOfUnity.AlgebraicallyClosed`) because the pin `S_` file is `import Mathlib`-only (FR-0085) |
| manager | review: axioms, merged consumer zone, surface gate | — | — | all five headlines `[propext, Classical.choice, Quot.sound]`; the merged `spec/ModularCurveReady3Consumer.lean` (337 lines, orders A–C in one file, the three per-order zones retired) is **0 errors**; no warnings attributable to any of the three modules; no forbidden `set_option`, no `sorry` |

**B's wall, measured — it was one instance search, and it evaporated.** The pin's 6.4M
`maxHeartbeats` on `main_K` and its module-level `synthInstance.maxHeartbeats 1600000` both come from
a *single* search: `Module.Free ↥(ℚ̄⟮y⟯) FF` inside `Module.finite_of_finrank_pos`, on the concrete
`adjoin` term. It cannot be handed over — `Module.Free.of_divisionRing` is absent from the closure,
and supplying it is rejected on an instance-path mismatch (`Semiring` from `DivisionRing.toRing` vs
from `SubsemiringClass.toCommSemiring`; instance arguments are data). Stating the same fact at a
*variable* intermediate field (`finiteDimensional_of_finrank_pos_intermediate`, 5 lines, private) made
it instant, and `main_K` then needs **no split** — it elaborates inside the 200k loop, sitting between
100k and 200k (it overruns at 100k, deterministically, in the first conjunct's `natCard_doubleCoset_le`
application). That is the residual risk to record: a later edit or a mathlib bump could push it over,
and the split points are the pin's three conjuncts. This is the same shape as shelf 2's order C, where
an explicit `Module.Free`/`finrank_pos_iff_of_free` replaced the pin's instance cap (FR-0088, IF-005).

**The surface gate, run (recipe §5 / §6 gate 7).** On a copy of the module with `private` dropped from
the 16 prelude declarations the checker reads **19 ok / 0 mismatch / 0 missing**: every one of them is
a pin-faithful statement the pin states public in both sibling `S_` files, so promoting them would be
the pin's own surface and not new mathematics. Nothing consumes them, so the module keeps them
`private`, and the numbers are the record of what the checked surface *would* be.

**What B dropped, and why it is not a loss.** Of the pin's 83 declarations, 23 are the host prelude,
1 is the public `LevelN.T_pow_mem_Gamma`, 1 is the prescribed `isDomain_ring` substitution, 50 are
written privately and 1 is public. Two (`liftE_apply`, `liftHom_apply`) are declared and never used in
the pin — dead scaffolding, the §3.1 "no self-consumed lemmas" case; and five (`E₄_smul`, `E₆_smul`,
`TinvS_smul_ρ`, `denom_TinvS_ρ`, `ρ_ne_one`) are the pin's *route* to facts the host prelude already
establishes (`E₄_rho`, `jAnalytic_rho`, `jAnalytic_I` and their proofs, written in shelf 2's D3). The
pin's `liftHom_eq_one_iff`/`liftHom_ker` are covered by the host's `liftHom_pow_eq_one_iff` at `n = 1`.
No public statement is affected; the checker's `0 missing` is the mechanical confirmation.


**Deviations, all statement-preserving.** §A4's helper table drifts in *namespace* as well as in
binder: `T_mem_Gamma1`/`Gamma_le_Gamma1` are `ModularForm.Level.*`, `qParam_one_eq_pow`/`natCast_pos`
are `X1DiamondRational.*`, and the port's `qParam_one_eq_pow` is ℍ-valued with `[NeZero N]` against
the pin's ℂ-valued `0 < N`, so the ℂ form was re-spelled in six lines (FR-0081). `restrictMF`,
`isIntegral_intCast`, `isIntegral_natCast` are written `private`, not imported and not promoted — the
dispatch errata, since the port had no public copy. Worth recording for the next pass:
`ModularForms/Level/Gamma1Slash.lean:86` carries a **public** `ModularForm.Level.restrictF` which is
the same four-line definition, so a promotion lane exists if a second consumer ever needs it. Five
v4.34 renames in the 457 block (FR-0083), and C's `solution` writes the pin's `letI`/`haveI` as
`let`/`have` — the `HahnSeries` algebra diamond of FR-0079/IF-004, verified to stay defeq. dedup finds
**0 clusters** on both modules; `move_dead` reports no public dead declaration, two private
declarations kept for pin fidelity (`coe_restrictMF` and the 457 file's
`exists_int_discriminant_qExpansion_coeff`), and FR-0086 records that the tool is blind to `private`
at column 0, so its "0 dead" is not evidence.

**The re-read after A and C** (§0's command, without the `--unport` correction, so this is the raw
column — and it lands on the figure the bookkeeping predicts, to the line):

| figure | shelf start | after A + C | expected |
|---|---:|---:|---:|
| `needed [F terminal]` | 931 / 378,258 | **927 / 376,955** | 931 − 4 nodes, 378,258 − 1,303 lines (249+469+457+128) |
| frontier F | 1,484 / 749,108 | **1,488 / 750,411** | +4 / +1,303 (the four rows join the frontier) |
| ready rows | 66 | **63** | 66 − 4 landed + 1 newly ready |
| `ModularCurve` ready | 7 / 2,486 | **4 / 1,435** | the 1,123, the 24, the raw 36 (the 261 shadow, uncorrected in this run) and the **new 252** |
| leaves (all namespaces) | 262 / 64,874 | 262 / 64,874 | unchanged; MC leaves still 0 / 0 |
| withheld | 4 / 831 | 4 / 831 | unchanged |

So §8's forecast has already paid its first instalment: `SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`
(**252**) is now a ready row, gated on the 249 row alone, exactly as §8 predicted — the landing
consumed 1,303 of the 2,426 silo and made one row ready. The 36 appears only because this run does
not carry the 261 `--unport` correction; the corrected read drops it as before.

**The re-read after the set** — the recipe §7 number, and the forecast of §8 checked line by line
(the same command, again without the `--unport` correction):

| figure | shelf start | after all five | forecast (§8) | verdict |
|---|---:|---:|---:|---|
| `needed [F terminal]` | 931 / 378,258 | **926 / 375,832** | 932 → 927 / 376,093 (corrected) | exact: −5 nodes, −2,426 lines |
| frontier F | 1,484 / 749,108 | **1,489 / 751,534** | +5 / +2,426 | exact |
| ready rows | 66 | **62** | 62 | exact |
| `ModularCurve` ready | 7 / 2,486 | **3 / 312** (corrected **2 / 276**) | 2 / 276 | exact on the corrected read; the extra row is the raw 36 |
| leaves (all namespaces) | 262 / 64,874 | 262 / 64,874 | unchanged | exact; MC leaves still 0 / 0 |
| cone / avoided / withheld | 2,103 / 982,173 · 140 / 74,620 · 4 / 831 | same | unchanged | exact |

**The one row the set makes ready is `SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`
(252)**, and it did become ready — the whole of §8's "what becomes ready" claim, no more and no less.
`needed` moved by exactly the five rows' silo with no extra declaration, so the consumed figure of §9
(2,426) and the new `needed` both hold; the larger blocks (the 1,267, the 833/700 pair, C's 1,133/292
and its 23 project consumers) did **not** open, exactly as §8 said.

**What the wave leaves on the `ModularCurve` shelf:** the corrected `ModularCurve` ready block is now
**2 rows / 276 silo** — the deferred 24 (`rep_tateModule_jOne_comm`, unstatable until the
padic-Tate-module programme lands `Def_EllipticCurve_TateModule`) and the newly ready 252 — plus the
raw 36 (the 261 chain's tail, a `ModularForm` story). Nothing else in the column is ready.

## 12. The next row, ported (2026-11-01)

The row §8 predicted — `SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`, 252 silo, the one
row the wave made ready — was ported by the manager, not dispatched: at 252 silo and 235 net
declaration lines it is a transcription, not a route.

| figure | value |
|---|---|
| home | **new** `SiegelUnit/PeakedAuxiliary.lean`, 298 lines (44 of header/docstring) |
| imports | `SiegelUnit/ProductForm` (the three landed headlines), `SiegelUnit/BernoulliWeight` (`exists_peaked_exponent`), `NumberTheory/ModularForms/CongruenceSubgroupLattice` (the `±Γ₁` ↔ entries dictionary) — **no mathlib import** (FR-0090) |
| public | `ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`, the wrapper's text verbatim |
| private | the pin's four `UEven` lemmas (`addOrderOf_dvd_sum_of_invariant`, `gcd_dvd_weight`, `natCast_dvd_sum_weight`, `isIntegral_pow_mul_of_le`), all referenced |
| checker | **1 ok / 0 mismatch / 0 missing** |
| build | `✔ Built … (6.2s)`, exit 0, silent; no declaration over the 200k edit loop (first pass) |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| dedup / move_dead | 0 duplicate clusters; 0 dead (all four privates referenced) |
| consumer zone | `spec/ModularCurveReady3Consumer.lean` grew a `[D]` block: the row instantiated at `N = 4` — the least level at which the peak hypothesis is satisfiable, since it needs `β 1 0 ∉ {0, 1, -1}` in `ZMod N` — with the hypothesis discharged at the concrete `β = Low 2` through the same subgroup dictionary, and three consequences read that the headline does not state: the width-`1` expansion's *exact* order `m₀`, `ϑ ≠ 0`, and the peak decay at that `β`. **0 errors** |

The one statement-preserving deviation: the pin writes `haveI : NeZero N := ⟨by omega⟩`; the port
writes `have : NeZero N := ⟨by omega⟩` (the `linter.style.haveILetI` gate; the `have` form still
registers the instance and the proof is unchanged — FR-0084).

**The re-read after this landing** (same command as §0/§11):

| figure | after the wave | after the peaked row |
|---|---:|---:|
| `needed [F terminal]` | 926 / 375,832 | **925 / 375,580** (= −1 node, −252 lines) |
| frontier F | 1,489 / 751,534 | 1,490 / 751,786 |
| ready rows | 62 | 62 (the 252 left, one row entered) |
| `ModularCurve` ready | 3 / 312 raw (2 / 276 corrected) | **3 / 309 raw (2 / 273 corrected)** |
| leaves / withheld | 262 · 4 | 262 · 4 |

**What this landing makes ready is `ModularCurve.exists_gamma1_peaked_auxiliary_form` (249 silo)**, the
general form of the same statement in the `ModularCurve` namespace (its pin is
`P2M/Sol/S_ModularCurve_exists_gamma1_peaked_auxiliary_form.lean`; its 2 premises are this row and
`SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion`, ported in
`SiegelUnit/Eisenstein.lean`, so it is statable now). So the `ModularCurve` block is again two rows plus the raw 36: that 249, the
unstatable 24 (`rep_tateModule_jOne_comm`, waiting on `Def_EllipticCurve_TateModule`), and the 36 that
belongs to the 261 `ModularForm` chain. The chain of doors is now: 252 → 249 → (whatever the 249
gates), i.e. the auxiliary-form development is a sequence of small transcriptions, not a wall.

## 13. The 249 row, and a prelude promotion (2026-11-01)

`ModularCurve.exists_gamma1_peaked_auxiliary_form` (249 silo) is the general form of §12's row: the
same auxiliary form with the weight normalised to `Even (k + w)` instead of `12 ∣ w`, so that `ϑ`
multiplies into weight `k`. Ported by the manager as an **append** to `SiegelUnit/PeakedAuxiliary.lean`
(the two rows are one subject, and the second's proof starts from the first's headline), which now
carries **454 lines / 2 public headlines**.

| figure | value |
|---|---|
| public | `ModularCurve.exists_gamma1_peaked_auxiliary_form`, the wrapper's text verbatim |
| private | six helpers: the cusp-analyticity of the `S`-slash, the two `PowerSeries` coefficient laws at `m₀`, the `IsIntegral` product law, and the slash-of-a-product law |
| checker | **2 ok / 0 mismatch / 0 missing** (both headlines of the module) |
| build | `✔ Built … (6.6s)`, silent; nothing over the 200k loop |
| axioms | both headlines `[propext, Classical.choice, Quot.sound]` |
| dedup | 0 clusters |
| consumer zone | a `[E]` block: at `N = 4`, `k = 1` — the **odd** branch, which multiplies by the weight-three Eisenstein form — read to `Odd w`, `ϑ ≠ 0`, exact `m₀`-order and the peak at `Low 2`. **0 errors** |

### 13.1 The manager lane: a prelude **promotion** in `ProductForm`, measured first

The 249's proof needs the `S`-conjugate group and its `Thetaform` — which `ProductForm` already holds
`private`. Copying ~150 lines would have been the third copy of the pin's prelude, so the manager ran
the surface gate on a **copy** of the module before deciding: with `private` dropped from the shared
block, the checker read **16 ok / 2 mismatch / 1 missing**. The two `MISMATCH`es were binder-only
(`Thetaform`/`coe_Thetaform` written with explicit `{N} [NeZero N] {w}` against the pin's section
variables) and the `MISSING` was `coe_restrictMF`, which the pin does not state. So the promotion went
in as: 15 declarations public at the pin's binders, `coe_restrictMF` left `private`.

`ProductForm`'s checked surface therefore went **3 ok → 18 ok / 0 mismatch / 0 missing**: every one of
the 15 is a pin statement the pin states public in the 469 source. This is the honest form of the
promotion rule — *two* consumers now exist (ProductForm's own 469/457 layers and this module), so the
surface is not being bought for one caller. `omit [NeZero N] in` reproduces the pin's binder spelling
and still parses at v4.34 (FR-0091 corrects shelf 2's note that it did not).

### 13.2 The re-read

| figure | after §12 | after the 249 |
|---|---:|---:|
| `needed [F terminal]` | 925 / 375,580 | **924 / 375,331** (= −1 node, −249 lines) |
| frontier F | 1,490 / 751,786 | 1,491 / 752,035 |
| ready rows | 62 | 61 |
| `ModularCurve` ready | 3 / 309 raw (2 / 273 corrected) | **2 / 60 raw** (1 / 24 corrected) |

**Nothing became ready from this landing**, and the `ModularCurve` ready block is now exactly the two
deferred rows: the raw 36 and the unstatable 24. (The 249's own consumer set is the `ModularForm`
Γ₁(N) basis chain, which is unported in the `ModularForm` — non-cuspidal — form; see §13.3.)

### 13.3 The 36 row is **not** a tuck-in: it is the top of the non-cuspidal Γ₁(N) basis chain

`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` is 36 lines, and the instrument reads it
ready — but only because of FR-0047's last-name shadow: its engine is
`ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (**261**), and the port holds only
`CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (`ModularForms/WeightOne/Gamma1IntegralBasis.lean:871`),
which satisfies a name-based "ported" test and not the statement. A name-exact audit of the chain
(the 36's premises, then theirs) finds **8 nodes absent**, all of them the `ModularForm` (or shared
`WLight`) versions:

| missing node | pin lines | port has instead |
|---|---:|---|
| `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` | 261 | `CuspForm.…` (shadow) |
| `ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp` | 448 | `CuspForm.…` |
| `ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply` | 341 | `CuspForm.…` |
| `ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even` | 128 | `CuspForm.…` |
| `ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even` | 913 | `CuspForm.…` |
| `ModularForm.finiteDimensional_of_isArithmetic` | 42 | — |
| `WLight.exists_mdifferentiable_div_of_monicRel` | 183 | — |
| **total** | **2,316** | |

`frontier.py --target ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` states the shadow
directly — "target is ported" with `needed [literal] 1 node / 325 lines` — so the literal debt starts
at 1,086 lines (261 + 448 + 341 + 36) before the two `_of_even` splits and the two shared lemmas.
That is the "≈2.1k `S_`" of [TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §8, and it is a two-dispatch
wave (the same cut by parity: `_of_even` at 128 and 913, then the general rows), not a tuck-in.
Nothing about it is blocked: the Eisenstein premise of both general rows is ported
(`ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq`,
`ModularForms/WeightOne/Gamma1Basis.lean:843`), and so is the second premise of the 36 itself.
**The next `ModularCurve` wave is therefore this chain, and the read must carry `--unport` on the five
shadowed `ModularForm.` names until it lands** — otherwise the 36 keeps reading ready while being
unstatable.
