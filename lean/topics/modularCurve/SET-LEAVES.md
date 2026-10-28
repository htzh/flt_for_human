# SET-LEAVES — the leaves block's rows, scoped and ground-prepped

**Status: scoped and ground-prepped (2026-10-27); six orders in two waves, not yet dispatched.**
This is the row half of the `ModularCurve` leaves programme. The definition layer those rows are
written over landed as [SET-LEAVESDEF.md](SET-LEAVESDEF.md) (96 declarations, ten modules); what
remains is the **32 rows / 6,797 silo** of the leaves block, priced here at **5,093 net new math
lines**, cut as six orders of 760–1,480 silo and dispatched **three at a time**. The recipe is
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md); the shelf
that named these stories is [TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §0.4/§3.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`. Read 2026-10-27, after the leaves' definition wave.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mcleaves.json
python3 frontier.py --selfcheck
# the corrected read (the MD-001 chain, the 261 shadow and the AC shadow)
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1 \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast \
  --unport AlgebraicCurve.weilReciprocity > build/mcleaves-corr.json
```

| figure | instrument | corrected |
|---|---:|---:|
| `needed [F terminal]` | 992 / 395,624 | 994 / 395,985 |
| ready, all namespaces | 66 / 14,036 | 66 / 13,865 |
| leaves, all namespaces | 294 / 71,671 | 294 / 71,671 |
| `ModularCurve` ready | 5 / 2,015 | 4 / 1,979 |
| **`ModularCurve` leaves** | **32 / 6,797** | **32 / 6,797** |
| withheld (FR-0044) | 4 | 4 |

**The leaf set is the same on both reads** — the three false-ported markers all sit in the ready
block, so no correction moves a leaf row. `--selfcheck` **PASS**. The leaves view is 294 rows /
71,671 silo; the `ModularCurve` block is 32 of them / 6,797. The other **262 rows / 64,874** belong
to `AutomorphicForm` (91), `NumberField` (48) and the rest of the column and are **not** this set
(FR-0040: named and deferred, not silently dropped).

**The withheld block is unchanged and is not this shelf's.** Four rows, 831 silo: two
`ModularCurve` Tate-module rows (`moduleFinite_and_free_padicInt_tateModule_jH` 327,
`moduleFinite_padicInt_tateModule_jOne` 283) whose blocking premise is
`AlgebraicCurve.Pic0.abelJacobiCard_genus`, and two `AlgebraicCurve` rows on the prunable
Abel–Jacobi subject (126, 95). They wait on the Abel–Jacobi programme and the absent `TateModule`
definition layer; they are quoted and deferred, not cut.

### 0.1 The definition gate is landed; every row is statable

[SET-LEAVESDEF.md](SET-LEAVESDEF.md) landed the eight pin `Def_` modules the leaves name — 96
declarations over ten port modules — and measured the shelf's 391-line four-module estimate wrong
in both directions (`X0ModL` 3 declarations not 43; `RatFuncPlaces`' `Place.Congr` tail and
`CohCarrier.HeckeData` unlisted). **This set does not touch the definition layer.** The one absent
module no leaf row names is `Def_EllipticCurve_TateModule` (883 pin lines / 69 declarations), which
belongs to the withheld pair and the padic-Tate-module topic; it stays out.

A statement audit of all 32 wrappers against the port (the §0 test of the recipe, "`needed = 1` is
a premise claim, not a statement claim") finds every named object present:
`HeckeDiamondInputsAll` (`X1/Inputs.lean`), `HeckeDiamondInputsHAll` (`XH/Operators.lean`),
`JOne`/`x1FunctionFieldBar` (`X1/Defs.lean`), `JH`/`xHFunctionFieldBar` (`XH/FunctionField.lean`),
`heckeOperatorOneBar` (`X1/HeckeModule.lean`), `diamondHBar` (`XH/Operators.lean`),
`heckeOperatorHAlong` (`XH/HeckeOperator.lean`), `AlgebraicCurve.Pic0.congr`
(`AlgebraicCurve/Pic0Congr.lean`), `periodAlongOf` (`ModularForms/EichlerShimura/PeriodOf.lean`),
`cosetTwoVarPoly`/`cosetConj`/`primCosetReps` (`Defs/PrimCosetReps.lean`), `cosetSubst`
(`Defs/PhiGen.lean`), `ModularPolynomialData` (`Defs/Polynomial.lean`), `tateLaurent`
(`Defs/TateFormal.lean`), `laurentBaseChange`/`coeffMap`/`qExpand` (`Defs/Laurent.lean`),
`qExpFunctionFieldC`/`intFormRatiosC` (`X1/Defs.lean`), `etaProd`/`jNum`/`evalAtJ`/`eisenstein4`
(`Defs/Jq.lean`), `siegelFun` (`Defs/SiegelFunction.lean`), `UpperHalfPlane.J` (mathlib),
`ZMod.unitOfCoprime` (mathlib).

## 0.2 The pricing

`port_advise` over the 32 nodes (64 target files, 547 declarations) and `port_plan`, then per
order. Net new math lines are the rows' own proofs, deduplicated across each order's files and
net of what the port already holds; the landed definition layer is **not** in this figure.

| order | stories | rows | silo | decl lines | dup | boiler | in-port | **net** | suspect |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| LV-1 | L-siegel | 4 | 1,158 | 1,101 | 157 | 57 | 27 | **917** | 2 |
| LV-2 | L-starbank (norm) | 3 | 995 | 931 | 52 | 64 | 60 | **819** | 0 |
| LV-3 | L-starbank (Hasse) + L-tate | 5 | 760 | 681 | 180 | 79 | 0 | **501** | 2 |
| LV-4 | L-coset + L-eta | 7 | 1,051 | 923 | 136 | 128 | 27 | **760** | 0 |
| LV-5 | L-x1coeff | 7 | 1,348 | 1,230 | 81 | 118 | 80 | **1,069** | 0 |
| LV-6 | L-other | 6 | 1,485 | 1,383 | 11 | 102 | 345 | **1,027** | 0 |
| | | **32** | **6,797** | **6,249** | **617** | **548** | **539** | **5,093** | 4 |

The per-order nets sum exactly to the whole-set 5,093 — no cross-order dedup is left over, because
the only shared preludes are intra-story and each order owns its story's module (§2). Two
corrections to the shelf's figures: the leaves' net is **5,093**, not the ≈5,870 the shelf priced
off the 34-row block (the two `tatePowerSeries` rows left the block in the first wave); and LV-6's
in-port 345 is real — `diamondOneBar_comm`'s engine is largely `X1/DiamondCorrespondence.lean`'s.

The **4 suspect substitutions** are the parser's type-only `def` matches (`Kbar2` → `BassSerre.Gp` in
LV-3, `hahnMapRingHom` → `ModularCurve.coeffMap`) — read them, do not import them blind. The §2
`pref`/`sprod` shape hits (LV-1) are the pin's `SiegelPerE96` prelude matching the port's private
`SiegelUnit.Basic` engine: real, and the reason row 155 is homed in that module.

## 0.3 The stories and the six orders

The eight shelf stories are kept as subjects; L-siegel and L-starbank split at their two modules,
L-coset and L-eta bundle because each is small and both are `X0`-coefficient algebra over the same
three legacy definition modules.

| order | story | rows (`ModularCurve.` dropped) | silo | home |
|---|---|---|---:|---|
| **LV-1** | L-siegel | `SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even` (504), `SiegelUnit.sum_totient_…_eq_zero` (323), `SiegelUnit.sum_levelBernoulliWeight_add_mul` (176) | 1,003 | **new** `ModularCurve/SiegelUnit/BernoulliWeight.lean` |
| | | `SiegelUnit.siegelFun_add_level` (155) | 155 | insert `ModularCurve/SiegelUnit/Basic.lean` |
| **LV-2** | L-starbank (norm) | `StarBank.deltaNorm` (471), `StarBank.closure` (304), `StarBank.onePoint` (220) | 995 | **new** `ModularCurve/StarBank/Norm.lean` |
| **LV-3** | L-starbank (Hasse) | `StarBank.starK` (210), `StarBank.count` (192), `StarBank.eisInt_series` (161), `StarBank.eisInt_not_dvd_num` (156) | 719 | **new** `ModularCurve/StarBank/Hasse.lean` |
| | L-tate | `c4_tateLaurent` (41) | 41 | insert `ModularCurve/Defs/TateFormal.lean` |
| **LV-4** | L-coset | `ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex` (152), `eq_cosetTwoVarPoly_of_forall_isRoot` (149), `separable_cosetTwoVarPoly` (149), `hasSum_cosetSubst_coeff_mul_qParam_pow` (72) | 522 | **new** `ModularCurve/ModularPolynomialCoset.lean` |
| | L-eta | `hasSum_coeff_etaProd_pow` (244), `coeff_jNum_le_six` (237), `eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero` (48) | 529 | insert `ModularCurve/JqCoefficients.lean` |
| **LV-5** | L-x1coeff | `existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap` (468), `finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap` (314), `exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_…_of_T_mem` (211), `mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC` (120), `isIntegral_adjoin_of_isIntegral_adjoin_coeffMap` (98), `laurentBaseChange_qExpFunctionFieldC_eq` (92), `linearIndependent_coeffMap_comp_of_linearIndependent` (45) | 1,348 | **new** `ModularCurve/X1/CoeffMap.lean` |
| **LV-6** | L-other | `pic0Congr_jOne_jH_bot_compat` (536) | 536 | **new** `ModularCurve/X1/Pic0Correspondence.lean` |
| | | `diamondOneBar_comm` (468) | 468 | insert `ModularCurve/X1/DiamondCorrespondence.lean` |
| | | `realizeOf_eq_div` (57) | 57 | insert `ModularCurve/ComplexPlaceDictionaryOf.lean` |
| | | `periodAlongOf_eq_neg_conj_periodAlongOf_J_smul` (98) | 98 | insert `ModularForms/EichlerShimura/PeriodOf.lean` |
| | | `eq_qExpansionDiffAlong_of_isQExpansionDiffAlong` (167) | 167 | insert `ModularCurve/Period/QExpansionDiff.lean` |
| | | `tendsto_atImInfty_of_hasSum_qParam` (159) | 159 | insert `ModularCurve/Analytic/QParamUnique.lean` |

**Waves.** Wave A: LV-1, LV-2, LV-3 (9 new/edited Lean files, 2,913 silo / 2,237 net). Wave B:
LV-4, LV-5, LV-6 (12 files, 3,884 silo / 2,856 net). Three agents per wave. File disjointness holds
across each wave: no order's file appears in another's, so only the build lock is shared.

## 1. Homes, and why

Method as in the recipe §4: pin wrapper and `S_` proof read by hand, the port module holding every
named object identified, then the home taken to be at or above all of them. Every home below is a
**new module** or an existing **wired** module; the three legacy modules this set needs as homes
were migrated in the ground prep (§2), so no order pays a migration.

| row | home | why this module |
|---|---|---|
| 504, 323, 176 | new `SiegelUnit/BernoulliWeight.lean` | the level-`N` Bernoulli weight `wt` and its span/sum algebra; mathlib-only (the three `S_` files import **no** pin `Def_` module), so a cascade-free new module; 323/176 share a 158-line prelude, written once here |
| 155 | `SiegelUnit/Basic.lean` | `siegelFun`'s own identities; the row's engine (`qa`/`pref`/`sprod`, `siegelFun_eq`, `multipliable_one_sub_pow_mul`) is already `private` in this module and the row is its consumer |
| 471, 304, 220 | new `StarBank/Norm.lean` | the σ-norm of Δ, the total-ramification closure and the one-point case: one subject, three headlines over the `qTwist`/`qExpand`/`etaProd` API; `StarBank.delta_pow_ne` (M10) stays in the legacy `ModularPolynomialStarBank.lean`, which this module **imports** |
| 210, 192, 161, 156 | new `StarBank/Hasse.lean` | the Hasse hypothesis (`starK`), the root count (`count`) and the Eisenstein integrality that feeds them (`eisInt_series`/`eisInt_not_dvd_num`, whose 99-line prelude is written once here); the pin puts all four in the `StarBank` subject |
| 41 | `Defs/TateFormal.lean` | `c4_tateLaurent` is a one-line statement about `tateLaurent`, defined in this module beside `tateA4`/`eisenstein6`; migrated in the prep (§2) |
| 152, 149, 149, 72 | new `ModularPolynomialCoset.lean` | the primitive-coset two-variable polynomial: roots, uniqueness, separability and the `cosetSubst` coefficient sum; sits over the legacy `Defs/PrimCosetReps.lean` + `Defs/JqCoeff.lean` (imported, not edited) and shares its 93-line `cosetConj_injOn` prelude here |
| 244, 237, 48 | `JqCoefficients.lean` | the low coefficients of the integral `q`-expansion: this module already proves `etaProd`'s pentagonal identity and `jNum`'s coefficients 1–2, exactly the engine rows 244/237 need; row 48 is the `evalAtJ` window-vanishing that the same coefficient comparison gives. Migrated in the same touch (§2) |
| 468, 314, 211, 120, 98, 92, 45 | new `X1/CoeffMap.lean` | the coefficient-map dictionary over the q-expansion function fields (`qExpFunctionFieldC`, `intFormRatiosC`, `coeffMap`, `laurentBaseChange`); the seven rows are one theory and share the 95-line `linearIndependent_coeffMap`/`coeffMap_mem` prelude |
| 536 | new `X1/Pic0Correspondence.lean` | the `JOne ≃+ JH` identification's compatibility with the Hecke, diamond and Galois actions; above `Pic0Congr`, `X1/HeckeModule`, `XH/Operators` |
| 468 | `X1/DiamondCorrespondence.lean` | the diamond correspondents' engine is this module's (`conjForm`, `coeffMap_intSeriesC`, `isIntegralQExp_intCast`, `ne_zero_of_isIntegralQExp` are already public here); `diamondOneBar_comm` is its commutation headline |
| 57 | `ComplexPlaceDictionaryOf.lean` | `realizeOf` is defined here; the row is its value on a ratio of two modular forms |
| 98 | `EichlerShimura/PeriodOf.lean` | `periodAlongOf` is defined here; the row is its `J`-conjugation law |
| 167 | `Period/QExpansionDiff.lean` | `IsQExpansionDiffAlong`/`qExpansionDiffAlong` are defined here; the row is the uniqueness that makes the choice canonical. Migrated in the prep (§2) |
| 159 | `Analytic/QParamUnique.lean` | the pin's whole private engine for this headline (`coeff_unique`, `periodic`, `mdifferentiable`, `discFun`, `tendsto_atImInfty`) is already transcribed **here**, `private`; the row is the public headline over it. Migrated in the prep (§2) |

The pin's own `S_` files are the proof source for every row; the `Theorems/` wrapper is the
statement authority (`check_port` diffs against both, one `spec-pin:` line each).

**No row of the set cites another row of the set.** The six orders are independent; the shared
pieces are the ported definition modules and the migrated engine modules.

## 2. The ground prep — measured

**Three migrations, all landed before dispatch.** Each module was on
`spec/old_check_stmts.py`'s `PORT_FILES`; the touch that homes a row there pays the migration
(recipe §4), and the manager pays it before the worker arrives:

| module | its own wire | `check_port --force` | `PORT_FILES` |
|---|---|---|---|
| `ModularCurve/Defs/TateFormal.lean` | `Definitions/Def_ModularCurve_TateFormal.lean` | **26 ok / 0 / 0 / 0 own** | row deleted |
| `ModularCurve/Period/QExpansionDiff.lean` | `Definitions/Def_ModularCurve_QExpansionDiff.lean` | **2 ok / 0 / 0 / 0 own** | row deleted |
| `ModularCurve/Analytic/QParamUnique.lean` | the two `qParam_coeff_unique` silos | **2 ok / 0 / 0 / 0 own** | row deleted |

The wires name only the sources of the declarations **already** in the port. The rows' own
`Them_`/`S_` lines are added by the order that lands the row: a `spec-pin:` naming a wrapper whose
statement is not yet in the tree is MD-001's false-ported marker, and `frontier.py` credits the
source tier before the statement exists. `frontier.py --selfcheck` still **PASS** after the three
migrations, and no shelf figure moved.

**One promotion is not owed, and one is deferred by design.** The `port_advise` report lists 23 pin
declarations that exist only as port-`private`: they are the `QParamUnique` engine (13),
`SiegelUnit/Basic.lean`'s `siegelFun` engine (7), `coeff_one_etaProd` (1), and two adapters. No leaf
row's proof needs one across a module boundary: the first two groups are *in* their row's home
module and stay `private` (MC-5a's and this set's recorded reading of the pin's own `private`), and
`coeff_one_etaProd` is not used by any leaf row — the pin's `S_StarBank_deltaNorm` uses the
`map_etaProd_eq_tprod`/`expand_tprod_one_sub_X_pow` family instead, and `delta_pow_ne` already owns
its private copy in `ModularPolynomialStarBank.lean`. So no `private` → public edit is made for the
leaves.

**Two marker rows, written by the manager.** `JqCoefficients.lean`'s two pre-existing public
declarations (`coeff_jq_zero`, `coeff_jq_one`) are the port's own statements (its header records
that FLT has no declaration for those two facts), so the module cannot be wired without them:

```
FLTForHuman/ModularCurve/JqCoefficients.lean   ModularCurve.coeff_jq_zero   own: the port's own low coefficient of jq (no pin statement)
FLTForHuman/ModularCurve/JqCoefficients.lean   ModularCurve.coeff_jq_one    own: the port's own low coefficient of jq (no pin statement)
```

They are in `spec/decl_markers.tsv` before LV-4 dispatches, so the worker's `check_port` reports
`0 missing` once its three `spec-pin:` lines are in. The `PORT_FILES` row for `JqCoefficients.lean`
is deleted at the wave's review, when the wire exists (deleting it earlier would leave the module
unverified between the two edits).

**No refactor of existing modules is needed beyond the three migrations.** The dedup the report
finds (38 names proved in ≥2 target files, ≈974 removable lines) is *intra-story*: `sum_*` in
L-siegel, `eisInt_*` in L-starbank, `cosetConj_injOn` in L-coset, `linearIndependent_coeffMap`/
`coeffMap_mem` in L-x1coeff, and the wrapper-over-private-headline pairs of each StarBank row. Each
order owns one module per story, so each prelude is written once by construction; the two
wrapper/`S_` statement pairs per row are the pin's own pattern and are the two `spec-pin:` lines,
not duplicate content.

## 3. Per-order traps

**LV-1 (L-siegel).** (i) Three of the four `S_` files import **no** pin `Def_` module: this is a
mathlib-only finite/Fourier computation, and the new module is cascade-free. (ii) 504 is analytic,
not algebraic: the `wt` weight is characterised through the Fourier series of the second Bernoulli
polynomial (`hasSum_cos_div_sq`, `tsum_psi_eq_sum_residues`, `stdAddChar_eq_cosZ_add_sinZ`); the
pin's `wt` is a `def` while the wrapper inlines the polynomial — state `wt` public at the pin's
name (it is the `S_` copy's declaration) and the headline at the wrapper's statement. (iii)
323/176 share their 158-line prelude (`sum_zmod_comp_val_affine`, `sum_range_affine_unit`,
`sum_zmod_Bt`, `emod_progression`, `gcd_bookkeeping`, …): once, in the new module. (iv) 155 goes
into `SiegelUnit/Basic.lean` beside the `siegelFun` engine; its new lemmas (`qa_add_level`,
`pref_add_level`, `sprod_add_level` and the three `_left` forms) are public in the pin, so public
here; do **not** touch the module's existing `private` engine. (v) `qa_ne_zero`/`multipliable_…`
already exist `private` there — use them, do not restate.

**LV-2 (StarBank norm).** (i) 471's proof is a topological-product computation
(`map_etaProd_eq_tprod`, `expand_tprod_one_sub_X_pow`, `rescale_tprod_one_sub_X_pow`,
`prod_one_sub_root_mul`, `prod_twist_factor`, the `uFam`/`hFam`/`gFam` family): read
`PowerSeries.WithPiTopology` first — the convergence API is the part that bites. (ii) The pin
declares each headline `private` in its `S_` file and restates it in the public wrapper; state each
**once**, public, at the wrapper's name (the precedent is `ModularPolynomialStarBank.lean`'s
`delta_pow_ne`). (iii) `closure`'s hypotheses are the four relations of the star datum; keep the
wrapper's binder order. (iv) The module needs `Defs/QExpandCharP`'s `map_intCast_pow_char_eq_qExpand`
only if the worker's route crosses characteristic `p` — 471/304/220 do not; do not import it.

**LV-3 (StarBank Hasse + L-tate).** (i) `eisInt_series`/`eisInt_not_dvd_num` share a 99-line
prelude (`eisInt_not_dvd_den_shift`, `eisInt_coeff`, `eisInt_dvd_den`,
`eisInt_bernoulli_ne_zero`): once. (ii) `starK`'s statement carries the Hasse hypothesis as a
**hypothesis** (`hHasse`), so the module does not prove it; it is the *implication* to the star
polynomial. (iii) `count`'s `Kbar2` substitution is a parser artefact (`BassSerre.Gp`): it is the
pin's private abbreviation for the algebraic closure, and LV-3 writes it locally. (iv) `starK`
carries `[CharP K ℓ]`; the `ℓ = 2, 3` cases are excluded by `5 ≤ ℓ` in the Euler hypotheses — keep
both binders. (v) `c4_tateLaurent` is **one line** at the wrapper's statement; `Defs/TateFormal.lean`
is now wired (§2), so it needs only its own two `spec-pin:` lines added and the module built.

**LV-4 (L-coset + L-eta).** (i) 522 and 529 are two modules and two subjects: `ModularPolynomialCoset`
(the coset polynomial) and `JqCoefficients` (the integral q-expansion coefficients). (ii) 152's
proof is a **descent from ℂ to an arbitrary field `K`** (`conjR`, `phiAt`, `coeffMap_*`); the
port's `coeffMap` API (`Defs/Laurent.lean`) and `ModularPolynomialData` (`Defs/Polynomial.lean`) are
the vocabulary. (iii) `eq_cosetTwoVarPoly_of_forall_isRoot` and `separable_cosetTwoVarPoly` share
`cosetConj_injOn` (63 lines) and three coefficient lemmas: once, in the new module, public at the
`S_` names (the pin has them public). (iv) `hasSum_cosetSubst_coeff_mul_qParam_pow` is the
`qParam`/`HasSum` form of `cosetSubst`; `cosetSubst` is `Defs/PhiGen.lean`'s (legacy; **import**,
do not edit). (v) In `JqCoefficients.lean` the pentagonal-series route is already there
(`etaProd_eq_pentagonalSeries`, `coeff_etaProd_*`, `coeff_jNum_one/two`); extend it to order 6 for
237 and to `etaProd ^ a` for 244, and prove 48 by the window-`[-n, 0]` coefficient comparison.
`evalAtJ` is `Defs/Jq.lean`'s. (vi) The module is still on `PORT_FILES`: add its three `Them_` and
three `S_` `spec-pin:` lines with the rows, run `check_port --force`, and report the counts; the
manager deletes the `PORT_FILES` row at review.

**LV-5 (L-x1coeff).** (i) The seven rows are one theory over `X1/Defs.lean`'s
`qExpFunctionFieldC`/`intFormRatiosC` and `Defs/Laurent.lean`'s `coeffMap`/`laurentBaseChange`; all
seven in one new module, which is what makes the 95-line `linearIndependent_coeffMap`/
`coeffMap_mem` prelude payable once. (ii) 468 is an **existence-and-uniqueness of an algEquiv**
over the base change `φ : K₀ →+* K`; its proof builds `Rsub`/`iotaR`/`sigmaR`/`eR` and concludes
through `algEquiv_eq_of_iota` — do not shortcut it into a `RingEquiv` transport. (iii) The
wrappers of 468 and 314 carry `attribute [-simp] ModularCurve.qExpandAlgHomC_apply
ModularCurve.jqNModC_one`; keep those `attribute` lines **out** of the module (their purpose is the
pin's elaboration; the port's `qExpandAlgHomC` is an abbrev of `qExpandAlg`, SET-LEAVESDEF §4). (iv)
211's `hT : ModularGroup.T ∈ Γ` is statement-level; `laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)`
is the hypothesis `hx`. (v) 120 is an `↔` between two membership predicates: both sides are
`X1/Defs.lean`'s, and the proof is `coeffMap`-bookkeeping. (vi) `coeffMap_intSeriesC` is **already
public** in `X1/DiamondCorrespondence.lean` — import it, do not restate.

**LV-6 (L-other).** (i) Six rows, six files, four of them existing modules: this is the set's
cross-file order. (ii) 536's statement is a `let e := Pic0.congr …` under which three commutations
are asserted; the engine (`slashForm`, `ιC`, `qC`, `IsDiaGen`, the `_heq` family) is 56 declarations
and half of it is already in `X1/DiamondCorrespondence.lean`/`X1/AtkinLehnerExchange.lean`. (iii)
468's engine is `X1/DiamondCorrespondence.lean`'s, so the row is a short proof there — **not** a new
module. (iv) 167's module is `Period/QExpansionDiff.lean` (migrated): the row's 19-declaration
prelude includes the `Etale.Field`/`Kaehler` imports the pin's `S_` file carries. (v)
`tendsto_atImInfty_of_hasSum_qParam` is the public headline of `QParamUnique.lean`'s existing
private engine (migrated); its proof is the port's own private `tendsto_atImInfty`, and the wire
line for its wrapper must be added **with** the statement. (vi) 98's wrapper carries an
`attribute [-simp] ModularCurve.Period.jConjMat_* / jConjSL_coe / charInvolution_apply` line: the
names are `PeriodHomPair.lean`'s; keep them out of the module too (they are the pin's elaboration
aids, and `PeriodHomPair.lean` is already wired and simp-clean).

## 4. Gates, per order

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing, 0 own** beyond the two
   recorded `JqCoefficients` rows; every added declaration `ok`.
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
3. The module's own `lake build` under `flock`/`timeout`; the edit loop at
   `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000`; **no**
   `set_option maxHeartbeats`, no suppression, no `set_option` copied from the pin.
4. `python3 tools/deps/dedup.py --within --tier shape` on each module → 0 clusters (a
   wrapper-over-private-headline pair of the pin's own shape is the one recorded exception).
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; no `spec/decl_markers.tsv` row from a
   worker.
6. The `spec-pin:` block names the `Them_` wrapper and the `S_` copy of each row it transcribes, and
   nothing else; `JqCoefficients.lean`'s wire is the one exception to "add and migrate", recorded in
   §2.
7. A `spec/` consumer zone per wave, with real cross-module composition and no `#check`s; the
   error count is the deliverable metric.

**Build discipline (copy into each order).** Edit loop `timeout 120 lake env lean
-DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is low on purpose: a declaration that
exceeds it has an instance-inference defect. Never raise `maxHeartbeats`, never add a module
`set_option`. `lake build <module>` per finished file, serialized with `flock` and bounded with
`timeout`. Per wave, build only the wave's affected targets — **never a whole-tree `lake build`**.
A whole-tree build happens once, at the session's end, only after the user agrees to it.

## 5. What this set does not do

- **The 262 non-`ModularCurve` leaf rows** (64,874 silo) — other columns' shelves, named and
  deferred (§0).
- **The withheld block** (4 rows / 831 silo) — the Abel–Jacobi programme and `TateModule`.
- **The ready block's five rows** (1,176 M9 successor, 611, 168, 36, 24) and the false ready — the
  successors of the earlier waves, for the next brief.
- **`Def_EllipticCurve_TateModule`** (883 / 69) — no leaf row names it.
- **No surface promotion and no whole-tree build.** The three migrations are the only existing
  modules edited before dispatch; the two `JqCoefficients` markers are checker metadata.

## 6. The landing — wave A (2026-10-27)

**LV-1, LV-2, LV-3 landed: 12 rows / 2,913 silo / 2,237 net.** Five files (three new): 
`SiegelUnit/BernoulliWeight.lean` (881 lines, 67 checked declarations), `SiegelUnit/Basic.lean`
(509 → 623, +9 checked), `StarBank/Norm.lean` (926, 50 checked), `StarBank/Hasse.lean` (605, 11
checked), `Defs/TateFormal.lean` (185 → 218, 27 checked — the 26 migrated ones intact). **164
checked declarations `ok` / 0 mismatch / 0 missing / 0 own / 0 kw**, axioms clean on all twelve
headlines, `dedup.py --within --tier shape` 0 clusters per module, zero warnings, no `set_option`
added, no marker row written by a worker. The wave's affected-target build is
`lake build` on the five modules: success, 4,096 jobs. The consumer zone
`spec/ModularCurveLeavesConsumer.lean` (four zones: `starbank`, `bernoulli`, `siegel`, `hasse`) is
at **0 errors, 0 warnings**: `press`+`deltaNorm` discharge `closure`'s two hypotheses and `closure`
discharges `count`'s divisibility; 504's span characterisation is read off the `s`-dilate together
with 323's totient sum; 155's level shift is shown to preserve `siegelFun`'s vanishing.

**The shelf, measured after the wave.** `needed` **992 / 395,624 → 980 / 392,711** (−12 / −2,913 =
exactly the wave's silo); ready 66 / 14,036 → **69 / 14,973**; the `ModularCurve` ready block
5 / 2,015 → **8 / 2,952**; leaves 294 / 71,671 → **282 / 68,758**; the `ModularCurve` leaves block
32 / 6,797 → **20 / 3,884**; `--selfcheck` **PASS**; frontier 1,433 / 734,440. **Three successors
entered**: `SiegelUnit.exists_peaked_exponent` (373) and
`SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul` (191) — the `wt` span and the level shift's
consequences — and `exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq`
(373). They are named here, not cut: the shelf's next brief starts from them.

**Two things the wave measured, for the record.** (i) The pin's `S_` namespaces (`Ws47.BSpan`,
`Ws18BDist`, `Ws18BDeg`, `SiegelPerE96`, `W1`) are carried on the *pin-public* auxiliaries because
`check_port` matches them by name and 67 `ok` is worth more than a rename plus 64 `pin:` rows; the
port's own private adapters are named by subject. (ii) The pin's 504 `set_option maxHeartbeats
800000` and the `c4_tateLaurent` wrapper's `synthInstance.maxHeartbeats 400000` were not copied and
not needed: both modules elaborate at the 200,000 edit-loop cap.

## 7. The landing — wave B, and the set closed (2026-10-27)

**LV-4, LV-5, LV-6 landed: the remaining 20 rows / 3,884 silo.** Nine files (three new):

| module | lines | `check_port` |
|---|---:|---|
| `ModularPolynomialCoset.lean` (new) | 400 | 16 ok / 0 / 0 / 0 |
| `JqCoefficients.lean` (+3 rows, migrated) | 207 → 747 (740 after the manager's prune) | 52 ok / 0 / 0 / **2 own** |
| `X1/CoeffMap.lean` (new) | 1,204 | 93 ok / 0 / 0 / 0 |
| `X1/Pic0Correspondence.lean` (new) | 529 | 4 ok / 0 / 0 / 0 |
| `X1/DiamondCorrespondence.lean` (+468) | 777 → 1,047 | 88 ok / 0 / 0 / 0 |
| `ComplexPlaceDictionaryOf.lean` (+57) | 180 → 239 | 12 ok / 0 / 0 / 0 |
| `EichlerShimura/PeriodOf.lean` (+98) | 225 → 274 | 24 ok / 0 / 0 / 0 |
| `Period/QExpansionDiff.lean` (+167) | 38 → 127 | 3 ok / 0 / 0 / 0 |
| `Analytic/QParamUnique.lean` (+159) | 231 → 245 | 3 ok / 0 / 0 / 0 |

**295 checked declarations `ok`** across the nine modules, axioms clean on all twenty headlines,
`dedup.py --within --tier shape` 0 clusters per module, zero warnings, no `set_option` copied from
the pin (the pin's `set_option maxHeartbeats 3200000` on the 244 row and its
`synthInstance.maxHeartbeats 1600000` were not needed), no marker row written by a worker. The
wave's affected-target build is green (4,490 jobs). `move_dead.py` flagged three private
declarations as unreachable (`Γ1`, `coeffEmb_algebraMap`, `Kbar2`); they are **not** dead — the first
is an `abbrev` used in a dozen declarations' *types*, the last is used by the module's `example`
probes, and the tool reads only proof bodies (FR-0070) — so none was cut. Two manager edits closed
the modules:
`JqCoefficients.lean`'s `PORT_FILES` row deleted (its wire is now its own), and its dead
`private coeff_etaProd_zero` pruned — the statement is the public `constantCoeff_etaProd` of
`Defs/Jq.lean`, so it was a §2.4 duplicate and unreachable after the new `LowCoeffs` engine.
The wave's consumer zones were added as they landed: `spec/ModularCurveLeavesConsumer.lean` now has
**eleven zones** (`starbank`, `bernoulli`, `siegel`, `hasse`, `coset`, `eta`, `coeffmap`, `pic0`,
`period`, `qexpdiff`, `cusp`) at **0 errors / 0 warnings**.

**The shelf: the `ModularCurve` leaves block is empty.** `needed` **980 / 392,711 → 960 / 388,827**
(−20 / −3,884 = exactly the wave's silo); ready 69 / 14,973 → **81 / 20,199**; the `ModularCurve`
ready block 8 / 2,952 → **20 / 8,178**; leaves 282 / 68,758 → **262 / 64,874**, and the
`ModularCurve` leaves block **20 / 3,884 → 0 / 0**; `--selfcheck` **PASS**; frontier
1,433 / 734,440 → **1,455 / 738,539**.

**Twelve successors entered, and they are the column's next brief.** The wave's declarations made
twelve `ModularCurve` rows ready: `qExpansionDiffAlong_val_eq_diffQExp`,
`exists_isIntegral_hasSum_siegelFun` (both the Siegel unit's and the differential's next steps),
`heckeDiamondCommuteBar`, `diamondHBar_mul`, `phi_eq_phiTwo`,
`exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC` (the sibling of
the 211 row, without the `T`-hypothesis),
`finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index`,
`eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow`,
`qExpansion_cosetTranslate_eq_cosetSubst`, `exists_complexPlaceDictionaryOf`,
`arithmeticGalois_complexConjAlgEquiv_smul_pt`, `ofAlgAut_smul_pt_eq_pt_inv_smul`. With the earlier
three (the 1,176 M9 successor, 611, 168, 373, 373, 191, 36, 24) the `ModularCurve` ready block is
20 / 8,178 — a successor shelf, not a leaf shelf.

**Plan against actual, honestly.** The set's aggregate held: 5,093 net priced against ≈5,700 lines
written including headers and docstrings (the playbook's 1.0–1.3 ratio). **One order's composition
was mis-priced**: LV-6's 1,027 net was right in total but its credit was wrong — `port_advise`
credited 345 in-port lines to the rows of 468 and 536 by *shape*-matching pin declarations to
`X1/DiamondCorrespondence.lean`/`AtkinLehnerExchange.lean` lemmas with different statements, and
LV-6's worker had to write ~270 (the `exists_gamma0`/`algEquiv_ext_of_ratios`/`diamondAut_comm`
chain) and ~430 (the `gAlpha`/`gBeta`/`IsDiaGen`/`Pic0.congr` transport) of them. The allowance for
duplicates and boilerplate absorbed the gap, so the aggregate did not move — but "already in the
port" in this report means *importable*, and a shape-tier match across carriers is a prompt to
read the two statements, exactly as the recipe says. A second, smaller correction: rows 468's and
536's engines are *sibling nodes'* engines, not free preludes; a leaf row that re-proves its
sibling's engine is new work and should be priced as such.
