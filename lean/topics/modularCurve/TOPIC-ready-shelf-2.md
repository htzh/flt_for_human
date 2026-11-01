# Ready shelf 2 — the `ModularCurve` residue: six successors, scoped (2026-10-31)

**Status: landed (2026-10-31).** All six rows are in, all gates green, and the shelf re-read
is §12. The scoping read is §0; the ground-prep lane is §11. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
the AC column's [SET 10](../algebraicCurve/SET-10.md) left. This is the residue of ready shelf 1
([TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md), all 18 rows landed): **six rows / 1,478 silo /
1,242 net** by the instrument (≈1,150 by the hand read of §3), cut into **four orders**. **No
definition gate, no migration**; one optional two-declaration promotion lane (§3.3). The 36 row,
the 261-silo chain head the 36 hangs from, and the 24 Tate-module row are named and deferred
(§0.2); the withheld pair is not this shelf's.

The set's own figure changed under it in a way worth recording first: the **265 row entered the
shelf because SET 10 landed**. Before that landing the `ModularCurve` ready block was exactly the
seven rows shelf 1 left (1,273 silo); un-porting SET 10's `genusFF_eq` row reproduces that figure
(§0.1).

| order | rows (`ModularCurve.` dropped) | silo | net | home |
|---|---|---:|---:|---|
| **A — the Siegel product** | `SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow` | 364 | 348 | insert `SiegelUnit/Integrality.lean` |
| **B — coset roots and the Φ₂ fibre** | `ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex` + `.fibrePoly_j_eq_prod_veluQuotient2_j` | 375 | 306 | insert `ModularPolynomialCoset.lean` + `ModularPolynomialFibreTwo.lean` |
| **C — the constant extension of the q-expansion function field** | `genusFF_qExpFunctionFieldC_eq_of_ringHom` + `transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC` | 436 | 345 (≈270 hand) | new `X1/FunctionFieldConstExt.lean` |
| **D — the special places of X(N)** | `LevelN.exists_place_ord_jGen_le_two_three_level` | 303 | 243 | new `LevelN/SpecialRamification.lean` |
| | **6** | **1,478** | **1,242** | 4 inserts, 2 new modules |

§0 the read and its delta; §1 the cut; §2 the rows; §3 the pricing and the false negatives; §4 the
homes and the import direction; §5 the traps; §6 the gates; §7 the calls; §8 the forecast; §9
reproduce and the three numbers; §10 what this set does not do; §11 the ground prep as landed.

No Lean was run while scoping: the read is `frontier.py`'s cached graph, the pricing
`port_advise`/`port_plan`, `twin_scan`, `gate_scan` and the port's own import lines.

## 0. The read

Canonical, with `--selfcheck` and the corrected pass as the recipe requires:

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc2shelf.json
python3 frontier.py --selfcheck
# the corrected read: the FR-0047 shadow on the 261 chain (§0.2)
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast > build/mc2shelf-corr.json
# the provenance check for the 265 row (§0.1)
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed
```

**`--selfcheck` PASSes** (live frontier: 1,313 `Thm_` source nodes, 1,478 by declared names, 1,478
union nodes / 747,630 raw `S_` lines) — no false ported marker, so the only correction this pass
needs is the 261 name shadow, as on shelf 1.

| figure | this read | SET 10's read | shelf 1's landing read (§10) |
|---|---:|---:|---:|
| `needed [F terminal]` | **937 / 379,736** | 940 / 380,062 | 942 / 380,709 |
| frontier F | 1,478 / 747,630 | 1,475 / 747,304 | 1,473 / 746,657 |
| ready rows, all namespaces | 67 / 12,912 | 68 / 12,946 | 68 / 13,294 |
| leaves, all namespaces | 262 / 64,874 | 262 / 64,874 | 262 / 64,874 |
| `ModularCurve` ready rows | **8 / 1,538** | 7 / 1,273 | 7 / 1,273 |
| `ModularCurve` leaves | 0 / 0 | 0 / 0 | 0 / 0 |
| `ModularCurve` demand | 108 / 57,663 | 108 / 57,663 | 108 / 57,663 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | 4 / 831 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 | same | same |

The "SET 10's read" column is that note's §0 figures; its `ModularCurve` row is the pre-landing state,
verified in §0.1, and the demand has not moved since shelf 1.

**Read the delta, and it is exactly SET 10's trio.** `needed` 940 / 380,062 → **937 / 379,736** is
−3 nodes / −326 lines, the three rows [SET 10](../algebraicCurve/SET-10.md) landed; the frontier
moves the other way by the same 3 / 326. Nothing else moved `needed` on this tree. The `ModularCurve`
ready block's only movement is the 265 row (+265), §0.1.

**The corrected read.** `--unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (the
`CuspForm` last-name shadow, FR-0047) moves `needed` to **938 / 379,997**, ready to 67 / 13,137 and
the `ModularCurve` block to **7 / 1,502**: the 36 row `exists_sum_smul_eq_of_isIntegralQExp_gamma1`
leaves, and the 261-silo `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` **enters** as a
ready row — the chain's real head, in the `ModularForm` namespace, not on this shelf (§0.2). The
`needed` delta is the 261 itself (+1 node / +261 lines). Both figures are quoted below; the cut is
the six rows of §0.3.

**The withheld block is unchanged and is not this shelf's** — the four rows / 831 silo of
[TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §0: two `ModularCurve` Tate-module rows
(`moduleFinite_and_free_padicInt_tateModule_jH` 327, `moduleFinite_padicInt_tateModule_jOne` 283) on
`AlgebraicCurve.Pic0.abelJacobiCard_genus`, and two `AlgebraicCurve` rows (126, 95) on the prunable
Abel–Jacobi subject. The `ModularCurve` part is 610 silo.

### 0.1 The 265 row is SET 10's `ModularCurve` consumer

`genusFF_qExpFunctionFieldC_eq_of_ringHom` is the MC statement that
`AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed` — SET 10's EQ row — is exactly
the hypothesis it needs: its premise list is that row, `isCurveOver_of_transcendental_of_perfectField`
and `LaurentSeries.eq_C_coeff_zero_of_isAlgebraic`, and nothing else. Un-porting the EQ row
(third command above) returns `needed` 938 / 379,763 and the `ModularCurve` ready block to
**7 / 1,273**, i.e. shelf 1's five successors (364, 347, 303, 171, 28) plus the 36 and the 24. The
shelf therefore grew by 265 silo, and the row that now opens order C is exactly the recipe §7
question ("what became ready because of the set") answered for SET 10.

### 0.2 The rows named and deferred

| node | silo | why it is not cut |
|---|---:|---|
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | its only substantive premise is `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (the 261), which the port holds only as a `CuspForm` last-name shadow; the corrected read drops the row (§0). The chain is the `ModularForm` Gamma₁ basis theorem, ≈4.8k raw / ≈2.1k `S_` lines — [TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §8's deferral, unchanged. |
| `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` | 261 | it is **on the corrected shelf as a ready row** (261 silo), and it is the chain's head, not a row of this column: a `ModularForm` set of its own if the manager wants the chain, otherwise the 36 stays one edge above it. |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | its premises are ported (MC-4's `JOne.galois_smul_heckeAlgOne_smul`) but its *statement* is `TateModule.rep p …`: the pin's `Definitions/Def_EllipticCurve_TateModule.lean` (883 lines / 69 declarations) is unported and the port has no `TateModule.rep` at all; D2's `rationalHeckeRepOne`/`RationalTateModule` are deferred with it. Not statable. It is the padic-Tate-module programme's row ([TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md)); its statement's `hcomm` hypothesis is this shelf's 28-line row, so order B removes one hypothesis without making the row statable. |

**The leaves.** `ModularCurve` leaves are **0 / 0**, so the `--include-leaves` read is for the
column's sake only; the 262 rows / 64,874 lines of other namespaces are named and deferred
(FR-0040), exactly as on shelf 1.

### 0.3 The shelf, quoted whole

| row (`ModularCurve.` dropped) | silo | prem | prem pruned | lev | status |
|---|---:|---:|---:|---:|---|
| `SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow` | 364 | 2 | 0 | 3 / 4 | **cut, order A** |
| `ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex` | 347 | 4 | 0 | 1 / 5 | **cut, order B** |
| `ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j` | 28 | 2 | 0 | 1 / 4 | **cut, order B** |
| `genusFF_qExpFunctionFieldC_eq_of_ringHom` | 265 | 3 | 0 | 2 / 6 | **cut, order C** |
| `transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC` | 171 | 2 | 0 | 2 / 61 | **cut, order C** |
| `LevelN.exists_place_ord_jGen_le_two_three_level` | 303 | 4 | 0 | 2 / 3 | **cut, order D** |
| `exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 2 | 0 | 1 / 3 | corrected-read only; deferred §0.2 |
| `rep_tateModule_jOne_comm` | 24 | 1 | 0 | 1 / 6 | unstatable; deferred §0.2 |
| | **1,538** | | | | 1,478 cut · 60 deferred |

`premises_unported` is 0 on all eight; `premises_pruned` is 0 on all eight, so the FR-0044 guard
does not bite here.

## 1. The cut

**Six rows / 1,478 silo / 1,242 net**, four orders. The four orders are 303–436 silo each and
together exactly the recipe's §5 dispatch size (1,300–1,600 silo); every order is one story with one
home decision. The rows that are not cut are not rows of this shelf (§0.2), so **this cut is the
whole of the `ModularCurve` ready block**.

What is deliberately *not* one order:

- **A is alone** although it is 364 silo: its subject is the Siegel function's q-expansion, its
  engine is SET-MS4's 1,057-line `SiegelUnit/Integrality.lean`, and it shares no pin file with
  anything else on the shelf (`port_advise`: *no name is proved in two or more of the target
  files*). It is the chain head, not part of a pair.
- **B's two rows are one story with two statements** — the pin's own `CosetRootFormalAux` block and
  the level-2 fibre capstone — and the 28 row is two lines on top of premises that order B's sibling
  and SET-MS7 have already landed. Cutting it alone would be an order of 11 lines; cutting it later
  would leave a landed theorem unused.
- **C's two rows are one transfer engine, two conclusions**: the same `coeffMap`/`coeffEmb` base
  change along $`\mathbb{Q} \to K`$, one stating fullness of `laurentBaseChange` (§2, item 5), one
  stating that the genus survives the extension (item 4). They go in one module for the same reason
  the pin puts the two engines in two files that share the coefficients.
- **D is alone** although it is 303 silo and uses `qExpFunctionFieldC`-adjacent vocabulary: its field
  model is `LevelN.ring N → K`, not $`\mathbb{Q}(X(\Gamma))`$, and its subject is the ramification of
  $`j`$ at the elliptic points and cusps of $`X(N)`$. It is also the set's only row whose proof
  consumes the `TateSlots/Invariants` analytic-order engine.

## 2. The rows

Each pin `S_` file is a **flat public surface** (`port_advise` drags: 0 helpers in every one of the
six), so the transcription is the file, not a headline plus a private prelude. Figures are the
`S_` file's lines.

1. **A — `SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow` (364).** The pin's `SExpPi`
   block: the `IsIntPS`/`Expands` product bookkeeping (≈130 lines), then an ≈200-line `main` that
   instantiates SET-MS4's `exists_isIntegral_hasSum_siegelFun` once per pair $`(r,s)`$, assembles
   the power series $`\prod A_{rs}^{12Ne(r,s)}`$, multiplies the `HasSum`s with
   `hasSum_qParam_mul`, and pushes the limit at $`i\infty`$ through the product. The pin's own
   `#print axioms solution` on line 362 is an artifact, not a gate.
2. **B — `…exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex` (347).** The pin's
   `CosetRootFormalAux`: a **width-parametrised** `An h f` (analyticity of the q-expansion at width
   $`h`$), `Nice`, the finite-product/sum/power q-expansion lemmas, then the ≈175-line root argument
   on the polynomial $`\Phi_N(j(q^N), Y)`$. Its four premises are MS-3's U10 engine
   (`qExpansion_cosetTranslate_eq_cosetSubst`), the velu column's
   `eval_E4_cube_div_discriminant_coset_eq_zero` (`ModularPolynomialE4Cube.lean`),
   `JqIntegralRatios`' `jqModC_eq_qExpansion_E4_cube_div_discriminant` and `QParamUnique`'s
   `laurent_qParam_coeff_unique`.
3. **B — `…fibrePoly_j_eq_prod_veluQuotient2_j` (28).** Two lines: `rw [phi_eq_phiTwo data]` then
   `exact fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j …`. Both premises are in the port
   (`ModularPolynomialLevelTwo.lean:383`, `ModularPolynomialFibreTwo.lean:302`), and the latter's
   conclusion already spells the pin's explicit `@WeierstrassCurve.j K _ _ ⟨isUnit_iff_ne_zero.mpr
   (hΔ i)⟩` argument, so the statement transcribes by copy.
4. **C — `genusFF_qExpFunctionFieldC_eq_of_ringHom` (265).** The pin's `QExpConstExt` block:
   `coeffMap_ofPowerSeries`/`coeffMap_intSeriesC` (the latter **private** in the port),
   `coeffMap_injective`, the `coeffMap` map into `qExpFunctionFieldC K Γ`, the generation lemma
   `le_map_adjoin_range`, the finite-dimensional descent, transcendence transport, then the
   headline through SET 10's genus trio. Its three `Def_` modules (`X1`, `Repartitions`,
   `IsCurveOver`) are landed, gate_scan: 0 missing.
5. **C — `transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC`
   (171).** The pin's `FullnessGamma1` block: `coeffEmb` transfer lemmas, `finrank_adjoin_eq_relfinrank`
   (18 lines), the fullness theorem `laurentBaseChange K (qExpFunctionFieldC ℚ Γ) =
   qExpFunctionFieldC K Γ`, then a ≈45-line `solution` that feeds MS-6's finrank/index bound. **The
   port already holds the engine** — see §3.1; the instrument's 148 is a ceiling.
6. **D — `LevelN.exists_place_ord_jGen_le_two_three_level`
   (303).** The pin's `SpecialRamification` block: $`E_4,E_6`$ at $`i`$ and $`\rho`$, the two
   stabiliser-cardinality bounds, the analytic order of $`j-j(\tau_0)`$, the two place-existence
   lemmas (`exists_place_ord_sub_le` from `LevelN.exists_place_analyticOrderAt_eq_mul_ord`,
   `exists_place_ord_neg_ge` from `LevelN.exists_algHom_laurentSeries_qExpansion` and the cusp
   order), then `main` assembling the three bounds $`\le 2`$, $`\le 3`$, $`\ge -N`$.

**The premise audit, by hand (the SET 9–10 lesson).** All 17 premise nodes are in the port at the
pin's statement or more general, read this pass (not last-name matched):

| premise | port home | statement read |
|---|---|---|
| `SiegelUnit.exists_isIntegral_hasSum_siegelFun` | `SiegelUnit/Integrality.lean:1069` | arbitrary `N`, `r`, `s` — the pin's general form |
| `hasSum_qParam_mul` | `ModularForms/Hauptmodul.lean:119` | width `h`, power series — verbatim |
| `qExpansion_cosetTranslate_eq_cosetSubst` | `ModularPolynomialCoset.lean:464` | the U10 engine, `qExpand`-shaped |
| `ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero` | `ModularPolynomialE4Cube.lean:484` | verbatim |
| `jqModC_eq_qExpansion_E4_cube_div_discriminant` | `JqIntegralRatios.lean:134` | verbatim |
| `laurent_qParam_coeff_unique` | `Analytic/QParamUnique.lean:236` | verbatim |
| `ModularPolynomialData.phi_eq_phiTwo` | `ModularPolynomialLevelTwo.lean:383` | level 2, verbatim |
| `fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j` | `ModularPolynomialFibreTwo.lean:302` | verbatim, with the explicit `j` instance argument |
| `AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed` | `Genus/ConstantFieldExtensionConsequences.lean:527` | SET 10's EQ row |
| `AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField` | `IsCurveOver/Transcendental.lean:119` | verbatim |
| `LaurentSeries.eq_C_coeff_zero_of_isAlgebraic` | `RingTheory/LaurentSeriesAlgebraic.lean:93` | verbatim |
| `finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index` | `X1/FunctionFieldIndex.lean:303` | the pin's general `Γ ≤ Γ'` form |
| `transcendental_jqModC` | `Degree/PhiDegree.lean:74` | `[CommRing K]` — more general than the pin's |
| `LevelN.exists_algHom_laurentSeries_qExpansion` | `LevelN/FieldGalois.lean:821` | verbatim |
| `LevelN.exists_place_analyticOrderAt_eq_mul_ord` | `LevelN/Places.lean:1170` | verbatim |
| `meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two` | `TateSlots/Invariants.lean:1539` | verbatim |
| `Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` | `AlgebraicCurve/Place/LaurentSeriesModel.lean:691` | verbatim (the private helper at :658 is not the row's) |

No shadow: each is a single declaration at the pin's statement, and the three "same last name"
neighbours the instrument flagged (`coeffEmb_intSeriesC` at `K` vs the port's `L`,
`coeffMap_intSeriesC` at `K₀ → K` in `Frobenius/QExpModL` at `K → K`, `jAnalytic_I` in
`LevelN/GenusFF`) are *specialisations*, not the general statements the rows consume — read, not
imported.

## 3. The pricing, and the two false negatives

`port_advise` per order, `port_plan` on each JSON:

| order | raw `S_` | declaration lines | boilerplate | duplicate copies | already in port | **net** |
|---|---:|---:|---:|---:|---:|---:|
| A (364) | 364 | 348 | 16 | 0 | 0 | **348** |
| B (347 + 28) | 375 | 334 | 41 | 0 | 28 | **306** |
| C (265 + 171) | 436 | 382 | 54 | 0 | 37 | **345** |
| D (303) | 303 | 274 | 29 | 0 | 31 | **243** |
| set | **1,478** | **1,338** | **140** | **0** | **96** | **1,242** |

`port_plan`'s four sections: **port once** — *no name is proved in two or more of the target files*,
so there is no shared prelude to write once (the six pin files are six independent developments);
**generalise** — one name in the target set differs only in binders (`qParam_one_eq_pow`, 37 pin
files / 9 statements) and nine share a name with a different statement (the two `SiegelUnit` files
disagree on `isIntegral_intCast`'s binder, the three `coeffEmb_*` lemmas on `K` vs `L`, `An` and its
`mul`/`add`/`smul` on width 1 vs width `h`); take the wrapper's binders. 13 more names have one target
copy and a duplicate elsewhere in the pool (a home may serve both). **drags** — 0 helpers on all six
files.

**3.1 The 171 row's price is a ceiling (§2, recipe §3).** `port_advise` reports *every target
declaration new* for 171, but the port already holds

- `ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq` (`X1/CoeffMap.lean:250`) — the row's own
  engine, same statement (the pin writes `K`/`Γ` from file-level `variable`s, the port inline);
- `BCEqProof.image_intFormRatiosC` (`:219`) and `BCEqProof.coeffEmb_mem_adjoin` (`:235`) — the pin's
  `image_intFormRatiosC`/`coeffEmb_mem_adjoin`;
- `coeffEmb_injective` (`Defs/Laurent.lean:367`), `coeffEmb_intSeriesC` (`JqIntegralRatios.lean`),
  `algebraMap_laurentSeries_eq_C` (`X1/FunctionFieldIsAlgClosed.lean`),
  `coeffEmb_algebraMap` (`X1/Pic0Correspondence.lean`).

What is genuinely new is `coeffEmb_ne_zero_iff` (4 lines), `finrank_adjoin_eq_relfinrank` (18) and
the 36-line headline proof: **≈60–80 net, not 148** (FR-0078 records why the instrument cannot see
this: the pin side's section variables are not lifted into the shape tier).

**3.2 The definition gate: none, after the hand read.** `port_advise --with-defs` puts **eleven**
`Def_` modules / 251 declarations in the six wrappers' closure, and **236 of the slice's 344
declarations (≈1,375 lines) already have the statement in the port** (231 importable, 5 private).
`spec/gate_scan.py` on each statement `Def_` module reports **0 missing** for
`SiegelFunction`, `PrimCosetReps`, `X0`, `JqCoeff`, `FibrePoly`, `VeluOrderTwo`,
`LevelNFunctionField`, `X1`, `IsCurveOver`, `Repartitions` — the six rows are statable against the
landed layer. The one apparent gate is a name-anchored false negative and is closed by reading:

| gate_scan MISS (`Def_ModularCurve_QAdicPlaceMod`, D) | pin lines | port declaration | statement read |
|---|---:|---|---|
| `jqModC_ne_zero_def` | 5 | `jqModC_ne_zero_of_nontrivial` (`X0/FunctionFieldFull.lean:99`) | `jqModC R ≠ 0`, `[Nontrivial R]` |
| `order_jqModC_def` | 10 | `order_jqModC` (`Defs/JqCoeff.lean:208`) | `(jqModC R).order = -1`, `[CommRing] [Nontrivial]` |
| `order_qExpandC` | 20 | `order_qExpand` (`Degree/LaurentGlue.lean:72`) | `(qExpand R N f).order = N * f.order`, no `f ≠ 0` hypothesis — more general |

So **A, B, C, D have no definition gate, no migration and no new definition**; the MC definition
wave covers these rows.

**3.3 The four port-private helpers, and the one manager lane to consider.** `port_advise` lists
four declarations of the six rows as *only port-private*:

| pin declaration | lines | port private copy | row |
|---|---:|---|---|
| `E₆_I` | 10 | `LevelN/GenusFF.lean:152` (a **public** copy exists at `TateSlots/Invariants.lean:1031`) | D |
| `ρ_ne_one` | 7 | `TateSlots/Invariants.lean:1052` | D |
| `coeffMap_ofPowerSeries` | 9 | `PhiGenIntegrality.lean:91` (the **public** copy is `Frobenius/Defs.lean:69`) | C |
| `coeffMap_intSeriesC` | 6 | `X1/CoeffMap.lean:94` (as `coeffMap_intSeriesC_gen`) | C |

Two of the four need nothing: `E₆_I`'s public copy (`TateSlots/Invariants.lean:1031`) is in a module
order D imports anyway, and `coeffMap_ofPowerSeries`' public copy is at `ModularCurve/Frobenius/Defs.lean:69`
at the pin's statement. The remaining two are cheap either way, and the call is:

- **promote two** (**landed**): `ρ_ne_one` is public at `ModularCurve.JMultiplicity.ρ_ne_one`
  (`TateSlots/Invariants.lean:1052`) and `coeffMap_intSeriesC_gen` is public as
  `ModularCurve.QExpAutBaseChange.coeffMap_intSeriesC` (`X1/CoeffMap.lean:96`). Both builds are
  green and silent (9 s / 24 s), `check_port --force` reads **154 ok** / **95 ok** (0 mismatch,
  0 missing), and both matched their pin declarations through the *existing* wire sources
  (`S_…meromorphicOrderAt_…:110`, `S_…existsUnique_algEquiv_…:28`) before the new wire lines were
  added; the lines stay because the two pin `S_` files of this shelf state them too. 13 lines.
- **or re-spell them** (not taken) in the two new modules: 13 lines, the pin's own prelude shape,
  `ok` on the checker, and a two-copy `dedup.py` cluster with the pin's duplication as the reason.

The lane ran **before** the wave, as required: both host modules (`TateSlots/Invariants`,
`X1/CoeffMap`) are premises' modules of orders D and C, so a mid-wave edit would rebuild under a
worker. The two new `spec-pin:` lines are on those modules; do not remove them.

## 4. The homes, and the import direction

The rule is subject first, then import direction (recipe §4): every premise's port module must sit
at or below the home. Every premise's port module is a leaf or an AC/MC module below the proposed
homes; each proposed home was checked against the port's imports (no cycle, no migration).

| order | row | home | why | host size / dependents |
|---|---|---|---|---|
| A | 364 | insert `ModularCurve/SiegelUnit/Integrality.lean` (+ `import FLTForHuman.ModularForms.Hauptmodul`) | the module is the integrality of Siegel q-expansions; the product is its second half | 1,094 lines / **0 importers** |
| B | 347 | insert `ModularCurve/ModularPolynomialCoset.lean` (+ `import …ModularPolynomialE4Cube`, `…JqIntegralRatios`) | coset substitution is the module's subject; its private `hasSum_laurent`/`qTwist` are usable in-module | 551 / **0** |
| B | 28 | insert `ModularCurve/ModularPolynomialFibreTwo.lean` (+ `import …ModularPolynomialLevelTwo`) | the Φ₂ fibre is the module's subject; `LevelTwo` does not import `FibreTwo`, so the edge is acyclic | 315 / **0** |
| C | 265 + 171 | **new** `ModularCurve/X1/FunctionFieldConstExt.lean` | "the q-expansion function field under a constant extension" is one subject with two conclusions; imports `X1.FunctionFieldIndex`, `AlgebraicCurve.Genus.ConstantFieldExtensionConsequences`, `AlgebraicCurve.IsCurveOver.Transcendental`, `RingTheory.LaurentSeriesAlgebraic` | new |
| D | 303 | **new** `ModularCurve/LevelN/SpecialRamification.lean` | the ramification of $`j`$ at the elliptic points and cusps of $`X(N)`$; imports `LevelN.Places`, `LevelN.FieldGalois`, `TateSlots.Invariants`, `AlgebraicCurve.Place.LaurentSeriesModel` | new |

**Why not put C's rows where the port already has their engines.** 171's theorem lives in
`X1/FunctionFieldIndex.lean` (MS-6) — the module FR-0074's `transfer_finrank` sits in — and 265's
neighbours are spread over `X1/CoeffMap.lean` (1,228 lines, imported by the function-field tower)
and `X1/Structure.lean`. Inserting into `FunctionFieldIndex` would edit the one MC module with a
recorded 240k-heartbeat declaration, and inserting into `CoeffMap` would edit a hub; a new module
above both is cascade-free and costs nothing on build time (recipe §5: build time is not a homing
consideration). The subject is the constant extension, so the new module earns its name.

**No legacy home.** None of the six proposed homes appears in `spec/old_check_stmts.py`'s
`PORT_FILES`: the two new modules are fresh and the three insertion hosts are already wired, so the
set has **no migration**.

## 5. The traps, and the ground prep

1. **The set's one real risk is elaboration cost, and it is not uniform.** Three of the six pin files
   carry a `set_option` heartbeat cap (which the port may not copy — playbook §3, no module
   carries one):

   | row | pin cap | where |
   |---|---|---|
   | A (364) | `maxHeartbeats 12800000` | the ≈200-line `main` |
   | C (265) | `synthInstance.maxHeartbeats 1600000` (module) + `maxHeartbeats 3200000` | `genusFF_eq` |
   | C (171) | `synthInstance.maxHeartbeats 1600000` + `maxHeartbeats 3200000` | `solution` |
   | B (347), B (28), D (303) | none | — |

   A's 12.8M is the set's wall: the port's build cap is 4M (`lakefile.lean`) and the edit loop is
   200k, so the pin's transcription may not fit. Plan: state the headline and probe it with
   `sorry`-cut lemmas **in `tmp/`**, not in the module; the pin's own factoring (`hdata`, `hE`,
   `hCst`, `key`) is where to split; avoid `convert` over the $`\mathbb{Z}/N \times \mathbb{Z}/N`$
   product, and never bump the cap. C's two rows are the same risk at 3.2M and sit next to FR-0074
   (§3.1): 171 consumes `FunctionFieldIndex`'s `transfer_finrank` and needs another
   `IntermediateField`/finrank transport, which is the one declaration in the port known to want
   240k. **If a declaration cannot meet the 200k loop, report it as a localised overrun (the
   FR-0074 form) with the module still building, instead of raising the cap or dropping a gate.**
2. **The coset root block does not exist in the port at width `h`.** `ModularCurve.DeepCosetAux.An`
   (`ModularPolynomialE4Cube.lean:131`) is `AnalyticAt (cuspFunction 1 f) 0` — the **width-1
   specialisation** of the pin's `An h f`, and its `qExpansion_finset_prod`/`_sum_smul` are stated
   at `qExpansion 1`. `port_advise` offers them as "binder variants"; they are *weaker statements*
   and cannot serve order B, whose proof needs width `N` (FR-0078). Import only
   `pow_mul_div_pow`, `cosetPt`, `qParam_one_eq_pow` (`ModularPolynomialE4Cube`,
   `ModularPolynomialCoset`, `ModularForms/QExpansionCoeff`); write the width-`h` `An`/`Nice` block
   in its own namespace, as the pin's `CosetRootFormalAux` does. The module's **private**
   `hasSum_laurent` (`ModularPolynomialCoset.lean:439`, generalised to `hper`/`hhol`) can be used
   from the same file: derive the pin's `Nice`-shaped version in three lines or restate it.
3. **`coeffMap_intSeriesC` is the 265 proof's one non-importable step** (the equality is used by
   `le_map_adjoin_range`), and the port's public `coeffMap_mem`/`coeffMap_algebraMap'` cover the
   rest. Promote or re-spell (§3.3).
4. **Pin artifacts to drop:** the `attribute [-instance]`/`[-simp]` walls on every file (the port's
   convention is not to transcribe them — the modules above already build silent without them), the
   `p2m_open`/`p2m_export`/`p2m_reactivate` lines, `autoImplicit false` (project-universal), the
   linter options where the port's own modules do not need them, and `#print axioms solution`
   (A, pin line 362). The three `set_option`s in C are defect markers, not budgets.
5. **The 28 row's statement has an explicit instance argument.** The pin's right-hand side is
   `∏ i, (X - C (@WeierstrassCurve.j K _ (W.veluQuotient2 …) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩))`;
   the port's premise spells exactly that, so copy it, and do not let Lean insert a different
   `IsUnit` argument (the statement is the deliverable, not the proof).
6. **D's `K` is an abstract fraction field.** Its statement quantifies `K` with `[Algebra ℂ K]`,
   `[Algebra (LevelN.ring N) K]`, `[IsScalarTower]`, `[IsFractionRing]`; the consumer zone needs a
   concrete instantiation (the worker's call — the port's `LevelN/FunctionField` model or
   `FractionRing (LevelN.ring N)` if the tower instances exist), and the row itself is stated
   abstractly as the pin does.
7. **The `LaurentSeries` algebra diamond can make two port premises incomposable.** `LevelN`'s
   `exists_algHom_laurentSeries_qExpansion` produces its `E : K →ₐ[ℂ] LaurentSeries ℂ` at
   `HahnSeries.powerSeriesAlgebra`; `AlgebraicCurve/Place/LaurentSeriesModel.lean` pins
   `HahnSeries.instAlgebra` and states the place/order dictionary at that spelling. An `AlgHom`
   cannot be transported between the two (every `AlgHom.mk`/`toRingHom`/`local instance` variant
   dies on "synthesized type class instance is not definitionally equal…"), and pinning either
   spelling file-wide breaks the other side (the producer's file flips `QExpBridge`'s mixed
   spellings; a consumer's pin breaks its uses of `E`). **The fix, landed as
   `AlgebraicCurve/Place/LaurentSeriesRingHom.lean` (`own:`), is to state the dictionary for a
   *ring hom* `F →+* LaurentSeries K` plus the constants identity `f (algebraMap K F c) =
   HahnSeries.C c`** — that carries no `LaurentSeries`-side algebra instance — with
   `HahnSeries.instAlgebra` pinned inside the glue module. Order D imports it and passes
   `E.toRingHom` (§11).
8. **The 265 headline is a two-line application of SET 10's trio once the transfer is in place**
   (`genusFF_eq_of_constantFieldExtension_of_isAlgClosed K₀ (qExpFunctionFieldC K₀ Γ) K
   (qExpFunctionFieldC K Γ) ⟨x, hx, hfin⟩ ⟨_, hx', hfin'⟩ hgen`), so the risk is entirely the
   `coeffMap` transfer block, not the genus step.

## 6. The gates, per order

1. `python3 spec/check_port.py --force lean/FLTForHuman/<module>.lean` → **0 mismatch, 0 missing**;
   every added declaration `ok`, or a `pin:`/`own:` row the manager writes in
   `spec/decl_markers.tsv` (nobody else writes one). For the new modules the `spec-pin:` header
   carries the wrapper and the `S_` file (one line each).
2. `#print axioms` on every headline (`364`, `347`, `28`, `265`, `171`, `303`) →
   `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
3. The module's own `lake build` under `flock` and `timeout`, and **the module silent**; a
   `Replayed` line is not evidence the `.olean` exists — build the defining module explicitly after
   a promotion or an insertion (FR-0033). Never a bare whole-tree build (rule 5, user's agreement).
4. `dedup.py` / `move_dead.py` on each module; the wrapper-over-engine `shape` clusters stay with
   the reason recorded — in this set the width-`h` `An`/`Nice` block, the pin's own `main`/`solution`
   pair in A, and (if the lane is declined) the two re-spelled helpers.
5. One `spec/` consumer zone for the wave (proposed `spec/ModularCurveReady2Consumer.lean`,
   one zone per order), with a real cross-module composition and no `#check`s:
   A composes the product's `HasSum`/`d 0` with `SiegelUnit/Basic`'s product law; B composes
   `cosetConj` roots with `phi_eq_phiTwo` and the new `fibrePoly` row at `N = 2`, and with
   `nonempty_modularPolynomialData`; C composes the genus equality with `laurentBaseChange` and
   `laurentBaseChange_qExpFunctionFieldC_eq` and `coeffEmb_ne_zero_iff`/`finrank_adjoin_eq_relfinrank`
   (`place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC` is a *consumer* of C2, not a port row);
   D instantiates the three ord bounds at a
   concrete `K` and composes them with `exists_place_analyticOrderAt_eq_mul_ord`. **The error count
   is the deliverable metric.**
6. No `set_option maxHeartbeats`, no `set_option synthInstance.maxHeartbeats`, no warnings, and no
   worker edits a module another order is building against. Files are disjoint across A–D (A:
   `SiegelUnit/Integrality`; B: `ModularPolynomialCoset`, `ModularPolynomialFibreTwo`; C:
   `X1/FunctionFieldConstExt`; D: `LevelN/SpecialRamification`), so all four may run concurrently
   **after** the promotion lane if it is taken.

## 7. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. the cut | **6 rows / 1,478 silo / 1,242 net** (instrument), ≈1,150 after §3.1 and §3.3 | not the instrument's 8 / 1,538: the 36 is the 261 chain (corrected read), the 24 is unstatable |
| 2. the orders | **A (364), B (375), C (436), D (303)**; A and D are single-story orders, B and C pairs | 4 dispatches, disjoint files |
| 3. the definition layer | **none** — eleven `Def_` modules landed, gate_scan 0 missing after the hand read of the three `QAdicPlaceMod` names | no def-lane work |
| 4. the manager lane | **two promotions** (`ρ_ne_one`, `coeffMap_intSeriesC`) before the wave — or re-spell both in-module (§3.3) | 13 lines, 2 wires; it unblocks C and D from private copies |
| 5. the homes | A insert `SiegelUnit/Integrality`; B insert `ModularPolynomialCoset` + `ModularPolynomialFibreTwo`; C new `X1/FunctionFieldConstExt`; D new `LevelN/SpecialRamification` | 3 inserts, 2 new modules, **no migration** |
| 6. the risk | A's 12.8M and C's 3.2M heartbeat caps: probe first, split along the pin's own factoring, report as FR-0074 if unmet | the set's only schedule risk; C also consumes FR-0074's own declaration |
| 7. the 36 row and the 261 | **defer** (shelf 1 §0.1/§8, unchanged): the `ModularForm` Gamma₁ basis theorem, ≈4.8k raw / ≈2.1k `S_` | not a row of this shelf |
| 8. the 24 row | **defer** to the padic-Tate-module programme: `Def_EllipticCurve_TateModule` (883 / 69) + D2's `rationalHeckeRepOne`; B's 28 removes its `hcomm` hypothesis | not statable |
| 9. the withheld pair | **defer** unchanged (610 silo MC, `abelJacobiCard_genus`'s 144-node / 66k programme) | not a row of this shelf |
| 10. the leaves | **defer** the 262 / 64,874 other-namespace rows (FR-0040); `ModularCurve` leaves are empty | nothing to cut |

## 8. The forecast

The six rows' direct consumers, read off the graph with their `S_` line counts (each consumer
counted once, whole file — a bound, not a price):

| row | consumers | the block it opens |
|---|---:|---|
| A (364) | 4 | 249, 469, 457, **1,267** — the Siegel form $`u_\mu \Delta^t`$ on $`\Gamma_1(q)`$ and the chain to `exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral` |
| B (347) | 5 | 644, 128, 62, **766**, **767** — separability of $`\Phi_N`$ over $`K(X)`$ and the `FullLevel` chart-algebra pair |
| B (28) | 4 | 102, 83, **1,133**, 518 — separability of $`\Phi_2(j_0,Y)`$ for non-integral $`j_0`$, roots as Vélu quotient $`j`$-invariants, and the cyclic-subgroup bijection |
| C (265) | 6 | 267, **689**, 112, 354, 856, 104 — the genus of $`X_H(M)`$ at $`\ell \nmid M`$ (both directions) and the characteristic-$`p`$ genus of $`X_1(M)`$ |
| C (171) | **61** | 8 of them carry 4,581: **47**, **1,468**, 163, 370, **1,057**, 725, 648, 103 — `place_deg_eq_one`, the pinned specialisation family, regular differentials, the complex place dictionary, the two-chart models |
| D (303) | 3 | **1,123**, 346, 721 — fibre lower bounds for $`j`$ over $`0,1728,\infty`$, the ramification bounds for $`j`$ on $`X(\Gamma)`$ over $`\bar{\mathbb{Q}}`$, and the cusps of $`X_H(N)`$ |

Together the 30 consumers named here carry ≈15.8k `S_` lines against the set's 1,478 — the same
keystone shape shelf 1 had: six rows of 28–364 silo each holding open blocks of 600–1,500. C's 171
is the hinge of the block (61 consumers, and the next MC programme's `place_deg_eq_one` is its
47-line first step), and B's pair closes the Φ-story that SET-MS7's level-two module began.

## 9. Reproduce, and the three numbers

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc2shelf.json
python3 frontier.py --selfcheck
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast > build/mc2shelf-corr.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed   # §0.1
python3 port_advise.py --with-defs --nodes <the 6 rows> --json build/mc2-defs.json
python3 port_advise.py $(cat build/mc2-nodes6.txt) --json build/mc2-adv.json   # the set price
python3 port_plan.py --json build/mc2-adv.json
# per order: port_advise.py --nodes … --json build/mc2-<order>.json; port_plan.py --json …
python3 twin_scan.py --node <row> --node <row> …        # -> new x6
cd ../../lean && python3 spec/gate_scan.py --pin Definitions/Def_ModularCurve_QAdicPlaceMod.lean \
  --rows S_ModularCurve_LevelN_exists_place_ord_jGen_le_two_three_level   # the 3-MISS hand read
```

(`build/mc2-nodes6.txt` holds one `--nodes NAME` per row; `twin_scan` takes `--node` once per row.)

**The three numbers.**

1. **What the set consumes**: 6 rows / 1,478 silo; **1,242 net new math lines** by `port_plan`
   (1,338 declaration lines, 0 duplicate copies, 140 boilerplate, 96 already in the port), and
   ≈1,150 by the hand read (171 is ≈70–80, not 148; the two promotions remove 13 more from C/D).
   Four orders; **three insertions, two new modules, no migration, no definition layer**.
2. **The read it starts from**: `needed` **937 / 379,736** (corrected 938 / 379,997); frontier
   **1,478 / 747,630** (corrected 1,477 / 747,369); ready 67 / 12,912 (corrected 67 / 13,137);
   `ModularCurve` ready **8 / 1,538** (corrected 7 / 1,502, cut 6 / 1,478); MC leaves **0 / 0**;
   MC demand 108 / 57,663; withheld 4 / 831; cone 2,103 / 982,173, avoided 140 / 74,620.
   `--selfcheck` PASSes. The `needed` delta from SET 10's read is exactly SET 10's trio, and the MC
   shelf's delta is exactly SET 10's 265 consumer (§0.1).
3. **What the shelf leaves**: the 36 row, the 261 chain head the corrected read exposes (261 silo,
   §0.2) and the 24 Tate-module row, the withheld pair (610 silo MC), the 262 other-namespace
   leaves, and — inside this cut — nothing: the six rows are the whole remaining `ModularCurve`
   ready block. A re-read after landing is required (recipe §7) before anything is said about the
   next one.

## 10. What this set does not do

- **The 261 chain and the 36 row** — the `ModularForm` Gamma₁ basis theorem, ≈4.8k raw / ≈2.1k
  `S_`. The corrected read prices its head `exists_basis_gamma1_qCoeff_mem_range_ratCast` at 261 silo
  and prints it as ready; it is a `ModularForm` row, not this column's. Whoever takes the chain
  starts there.
- **The Tate-module programme** — `Def_EllipticCurve_TateModule` (883 lines / 69 declarations), the
  withheld pair (610), and the false ready `rep_tateModule_jOne_comm` (24); one programme,
  [TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md)'s
  T1/T2. Order B removes that row's `hcomm` hypothesis but does not make it statable.
- **The mod-ℓ / X_HDRModelAtP block** — order C's genus rows are its *first* consumers (265's
  689-line `genusFF_xHFunctionFieldBar_le…`), not its whole; that block is its own programme, gated
  on the Tate layer it shares with the withheld pair.
- **The 262 leaves / 64,874 lines of other namespaces** — named and deferred (FR-0040).

## 11. Ground prep, as landed (2026-10-31)

| item | edit | result |
|---|---|---|
| promotion | `TateSlots/Invariants.lean`: `private lemma ρ_ne_one` → `lemma ρ_ne_one`; header prose records it; one `spec-pin:` line added for the 303 `S_` file | build green, 9 s, silent; **154 ok / 0 / 0** |
| promotion | `X1/CoeffMap.lean`: `private theorem coeffMap_intSeriesC_gen` → `theorem coeffMap_intSeriesC` (5 internal uses renamed); header prose corrected; one `spec-pin:` line added for the 265 `S_` file | build green, 24 s, module silent; **95 ok / 0 / 0** |
| wiring | `ModularPolynomialFibreTwo.lean` had **no `spec-pin:` line** (tier 3, never diffed); the two lines for its own row were added | **1 ok / 0 / 0**; no Lean edit, no build |
| definitions | none | eleven `Def_` modules landed, gate_scan 0 missing (§3.2) |
| migrations | none | none of the five homes is legacy |

No Lean statement or proof was changed: the two promotions are `private` removals (one with a
rename at the pin's name), the third item is checker metadata.

**Wave 1 (same day).** Orders **B and C landed** under the work order: B's two rows in
`ModularPolynomialCoset.lean` (checker **34 ok / 0 / 0**; the pin's whole public width-`h` prelude
matched verbatim, 14 added, not the predicted 1 — more surface, still clean) and
`ModularPolynomialFibreTwo.lean` (**2 ok**), C's two rows in the new
`ModularCurve/X1/FunctionFieldConstExt.lean` (365 lines, **11 ok / 0 / 0**, and — the good surprise —
**no heartbeat cap needed**: the pin's 3.2M + 1.6M synthInstance markers are replaced by an explicit
`Module.Free` and `Module.finrank_pos_iff_of_free`, so the module is silent at 200k). The consumer
zone `spec/ModularCurveReady2Consumer.lean` has zones B and C at 0 errors. dedup `--within --tier
shape`: one pre-existing pin-intrinsic `VeluTwoSym.main`→headline cluster, none from the new
declarations.

**D was blocked and is landed** — the bridge (trap 7), `AlgebraicCurve/Place/LaurentSeriesRingHom.lean`,
`1 own / 0 / 0`, build green in 2.1 s, silent, turned the cusp step into a direct application of
`exists_ord_mul_eq_order_of_ringHom` to `E.toRingHom`; the re-dispatch landed
`ModularCurve/LevelN/SpecialRamification.lean` (310 lines, 18 public, **18 ok / 0 / 0**, axioms
clean, build 4.4 s, silent at 200k, dedup 0 clusters). Its one structural deviation: `omit … in
theorem` does not parse in this toolchain, so the pin's `variable (M) (K)` block is split into
three — the declaration text is unchanged and all 18 statements match.

**B, C and D are in**; the consumer zone has zones B, C, D at 0 errors. **A is running** as a
second lane against `SiegelUnit/Integrality.lean` (364 pin lines, the pin's 12.8M `main` cap the
one open risk); its consumer zone is a separate file until the manager merges.
- **No tree build, no cap overrides, no marker rows written by a worker, no promotion except the
  lane of §3.3.** Every module is gated on its own build at the project cap; a whole-tree build
  waits for a milestone and the user's agreement.

## 12. The landing, measured (2026-10-31)

All six rows landed, in the four orders, with the manager lane of §11 and one bridge (§5.7).

| order | module | lines | checker | notes |
|---|---|---:|---|---|
| B | `ModularPolynomialCoset.lean` (insert) | +320 | **34 ok / 0 / 0** | the pin's whole width-`h` prelude went public at its verbatim statements (14 added, not the predicted 1) |
| B | `ModularPolynomialFibreTwo.lean` (insert) | +28 | **2 ok / 0 / 0** | the two-line Φ₂ fibre capstone |
| D | `LevelN/SpecialRamification.lean` (new) | 310 | **18 ok / 0 / 0** | the whole pin prelude public; the cusp step via the ring-hom bridge, no instance transport |
| A | `SiegelUnit/Integrality.lean` (insert) | +404, purely additive | **116 ok / 0 / 0** | private `SExpPi` prelude + headline; **the pin's 12.8M cap is not needed — the block compiles at 20k** |
| C | `X1/FunctionFieldConstExt.lean` (new) | 365 | **11 ok / 0 / 0** | the pin's 3.2M + 1.6M synthInstance marks replaced by an explicit `Module.Free`; silent at 200k |
| manager | `AlgebraicCurve/Place/LaurentSeriesRingHom.lean` (new) | 76 | **1 own / 0 / 0** | the ring-hom place dictionary (FR-0079) |
| manager | `TateSlots/Invariants.lean`, `X1/CoeffMap.lean` | — | **154 ok**, **95 ok** | the two promotions of §11 |

Every edit loop is silent at 200k; every module build is green; `#print axioms` on the six
headlines is `[propext, Classical.choice, Quot.sound]`; dedup finds only pin-intrinsic pairs
(`VeluTwoSym.main`→headline in B2, `isIntegral_zeta`/`isIntegral_exp_of_pow` in A) and no cluster
from the new declarations; the consumer zone `spec/ModularCurveReady2Consumer.lean` (orders A–D,
merged into one file) is **0 errors**. One deviation to keep: `omit … in theorem` does not parse in
this toolchain, so D's single `variable (M) (K)` block is split into three (declaration text
unchanged, all 18 statements still match).

**The re-read** (`§0`'s command, after the wave):

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 937 / 379,736 | **931 / 378,258** (corrected 932 / 378,519) |
| frontier F | 1,478 / 747,630 | 1,484 / 749,108 (corrected 1,483 / 748,847) |
| ready rows | 67 / 12,912 | 66 / 13,860 |
| `ModularCurve` ready | 8 / 1,538 | **7 / 2,486** (corrected 6 / 2,450) |
| leaves (all namespaces) | 262 / 64,874 | 262 / 64,874 (MC leaves still 0 / 0) |

`needed` moved by exactly the six rows' silo (**−1,478 lines, −6 nodes**) with no extra
declaration, and `--selfcheck` still PASSes (1,319 `Thm_` sources, 1,484 union nodes). The
`ModularCurve` block is now the five rows that entered plus the deferred 24 (the corrected read
drops the 36, as before).

**Five rows became ready because of the set** — the recipe §7 number:

| entered row | silo | it became ready because of |
|---|---:|---|
| `SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` | 249 | A |
| `SiegelUnit.isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` | 469 | A |
| `SiegelUnit.qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` | 457 | A |
| `ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero` | 128 | B1 |
| `ModularCurve.natCard_doubleCoset_le_card_fibres_of_finrank_eq_index` | 1,123 | D |

2,426 silo in all. The next `ModularCurve` cut is therefore the Siegel form chain (1,175 silo, the
three rows of A's block) and the fibre-lower-bound row (1,123) — one new shelf pass, not a
continuation of this one. The forecast's other blocks did **not** open: `place_deg_eq_one_…` (47)
and the 265 genus-at-`ℓ` consumers have other unported premises, exactly as §8 said a bound is not
a price.

**Frictions recorded on the way:** FR-0078 (the shape tier does not lift the pin's section
variables — 171 priced at a ceiling), FR-0079 (the `LaurentSeries` algebra diamond makes two port
premises incomposable; the ring-hom bridge), FR-0080 (four v4.34 deprecation renames in the pin's
`main`).

**Successor (2026-11-01).** [TOPIC-ready-shelf-3.md](TOPIC-ready-shelf-3.md) is that pass. On the
unchanged tree it re-measures the five-row residue this section predicted — 2,426 silo, corrected,
plus the unstatable 24 — and cuts it into three orders. Its one revision of this section's reading is
that the 1,123 row's pin prelude is already written privately in `LevelN/GenusFF.lean` (the pin
carries the same prelude in both sibling `S_` files), so that row is a 165-line-cheaper insertion
there and not the new-module work this section's forecast implied.
