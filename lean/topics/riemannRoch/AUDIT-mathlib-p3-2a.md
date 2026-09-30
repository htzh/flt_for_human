# Mathlib-first substitution audit — the phase-3.2a ℙ¹ place/ord dictionary (P3.2a)

**Method:** `lean/porting-playbook.md` §2.2 (audit the route, mathlib first), after
the phase-1/2/3.1 templates [`AUDIT-mathlib.md`](AUDIT-mathlib.md),
[`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md) and
[`AUDIT-mathlib-p3-1.md`](AUDIT-mathlib-p3-1.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Measured inventory:
[`tools/deps/build/p32a_inventory.txt`](../../../tools/deps/build/p32a_inventory.txt)
(80 rows) and node list
[`tools/deps/build/p32a_nodes.txt`](../../../tools/deps/build/p32a_nodes.txt).

Sources, in pin order:

- [`Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean)
  (86 ln, 14 declarations — see the correction in §1)
- the 11 dictionary `S_` files of
  [`P2M/Sol/`](https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b3/P2M/Sol),
  the dominant one being
  [`S_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap.lean)
  (1,263 ln, 70 inventory rows = 67 public + 3 `private`), plus ten tiny files
  (196 ln, 10 `solution` rows).

**Class convention** (unchanged from phases 1–3.1). SUBSTITUTE = the port can import
an existing declaration instead of proving the row: an already-landed port lemma or a
mathlib constant whose *type* is the pin's, or a pin `def`/`abbrev`/instance whose body
is `rfl`-equal to a mathlib/port term. PROOF-INGREDIENT = the statement is bespoke (it
mentions pin vocabulary) but the proof is a short assembly of named mathlib/port
lemmas. BESPOKE = a definition/structure/class/`Prop` introducing new vocabulary, or an
instance with no mathlib/port counterpart; these are the recorded negatives and the
real work.

**Scratch evidence:** `lean/ScratchAuditP32a.lean` (gitignored; deleted at the
phase-3.2a closeout after the set was accepted — the classifications above remain
the record), compiled from `lean/` with

```bash
timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP32a.lean
```

**final run clean, exit 0, 4.66 s wall** (233 lines of `#check` output; the only two
diagnostics are the deliberate deprecation probes `dif_pos` and
`Polynomial.degree_sub_lt`). The file contains:

- **A** — the three ℙ¹ nodes as one-line applications of already-ported declarations;
- **B** — the `RatFunc.inftyValuation` ledger and the `rfl`/`IsEquiv` bridge to the
  port's `placeInfty`;
- **C** — the `RatFunc.intDegree` ledger;
- **D** — the unported `placeOfPoint` block, with a compile-checked sketch
  (`ProtoPlaceOfPoint`) of all five declarations;
- **E** — the whole `Place.IsRational`/`residueInv`/`evalAt` interface and the seven
  generic evaluation nodes, compile-checked again (`ProtoPlaceEvaluation`);
- **F** — the six unported `Divisor.evalFun_*` algebra nodes, compile-checked
  (`ProtoEvalFun`);
- **G–I** — the drift ledger, the DVR/`num`-`denom`/root API ledger and the
  big-file proof-ingredient ledger.

Everything below that is marked "probe A…/…" is a term or `#check` in that file.

## 1. Summary — class counts per file

| pin source | SUBSTITUTE | PROOF-INGREDIENT | BESPOKE | rows |
|---|---:|---:|---:|---:|
| `Def_AlgebraicCurve_PlaceEvaluation` (file 1) | 0 | 9 | 5 | 14 |
| big `S_…ord_placeOfPoint_algebraMap` | 5 | 62 | 3 | 70 |
| ten tiny `S_` files | 0 | 10 | 0 | 10 |
| **total** | **5** | **81** | **8** | **94** |
| proof-reached, out-of-set (added scope) | 0 | 10 | 1 | 11 |

**Correction 1 — file (1) has 14 declarations, not 13.** The brief's count omits the
top-level `WeilReciprocity`: the `Place` namespace holds 9 declarations, `Divisor`
holds 4, and `WeilReciprocity` is a further top-level `def` outside both namespaces
(pin lines 18, 20, 24, 27, 31, 36, 41, 45, 52 | 61, 64, 68, 71 | 79). This is the
same class of count slip phase 3.1 recorded for an anonymous instance.

**Correction 2 — the 11 `S_` files carry 80 rows, and the work order's 91 is
80 + the 11 wrapper theorems.** The big file contributes 70 rows (67 public including
`solution`, plus three `private`: `isUnit_algebraMap`, `ofOption`,
`ofOption_bijective`); each tiny file contributes one `solution`. The 91 in
`WORKORDER-P3-2a-p1-dictionary.md` §0 is the 22-file count, not 22 S-file declarations.

**Correction 3 — the measurement is a lower bound: two proof-reached blocks are
outside it.** §5.1 and §5.2: the big file names `placeOfPoint` and 4 companions
(dropped by the port's AC0 `Defs/RatFuncPlaces.lean`) and six
`Divisor.evalFun_*` laws from the unported
`Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean` (160 ln, 15 decls) plus six
`S_AlgebraicCurve_Divisor_evalFun_*` files (78 ln). This is exactly the
"close a measurement over proof-reached targets" failure §2.1 warns about.

**Headline.** The phase is almost entirely proof-level: 81 of 94 in-set rows and all
11 out-of-set rows are PROOF-INGREDIENT; the 8 BESPOKE rows are five new objects in
file (1) plus `principalDivisor`/`placeEquivOption`/`ofOption` in the big file. Two
route facts dominate:

1. The port's `Place.placeInfty` is **built from `RatFunc.inftyValuation`**, so the
   whole infinity block is one step from mathlib (`Defs/RatFuncPlaces.lean:253–268`),
   and the port has already proved the general lemmas that the pin's
   `deg_placeInfty`/`ord_placeInfty`/`ord_placeInfty_algebraMap` are one-line
   applications of.
2. The `principalDivisor` degree block does **not** reduce to `RatFunc.intDegree`; it
   reduces to the port's UFD-induction master lemma
   `RationalFunctionField.degree_eq_zero_of_forall_eq_ord`
   (`PrincipalDivisors/RatFuncDegree.lean:401`). `intDegree` is confined to the two
   `ord_placeInfty` leaves and the pin's `WFg` helper.

## 2. `Def_AlgebraicCurve_PlaceEvaluation.lean` (14 rows)

| pin decl (line) | class | mathlib / port name | evidence |
|---|---|---|---|
| `Place.IsRational` (18) | **BESPOKE** | `Function.Surjective` | `Prop`; no mathlib/port analogue (grep: `IsRational` absent under `FLTForHuman/`) |
| `Place.algebraMap_residueField_injective` (20) | PROOF-INGREDIENT | `(algebraMap K v.ResidueField).injective` | one mathlib call |
| `Place.residueInv` (24) | **BESPOKE** | `Function.invFun` | new `def`; `Function.invFun` (probe E) |
| `Place.algebraMap_residueInv` (27) | PROOF-INGREDIENT | `Function.invFun_eq` | probe E |
| `Place.residueInv_algebraMap` (31) | PROOF-INGREDIENT | `Function.leftInverse_invFun` | probe E |
| `Place.evalAt` (36) | **BESPOKE** | `dite` / `dif_pos` | new `def`; the `open Classical in` is load-bearing (a plain `def` fails to synthesize `Decidable`, probe E) |
| `Place.evalAt_of_mem` (41) | PROOF-INGREDIENT | **`dite_eq_left`** | pin's `dif_pos` is deprecated; the v4.34 spelling `dite_eq_left hf` elaborates verbatim (probe E) |
| `Place.algebraMap_evalAt` (45) | PROOF-INGREDIENT | `IsLocalRing.ResidueField.algebraMap_eq`, `IsScalarTower.algebraMap_apply` | probe E |
| `Place.evalAt_one` (52) | PROOF-INGREDIENT | `map_one`, `residueInv_algebraMap` | probe E compiles verbatim (including the bare `one_mem _`) |
| `Divisor.evalFun` (61) | **BESPOKE** | `Finsupp.prod` | new `def` |
| `Divisor.evalFun_def` (64) | PROOF-INGREDIENT | `rfl` | |
| `Divisor.evalFun_zero` (68) | PROOF-INGREDIENT | `Finsupp.prod_zero_index` | probe F |
| `Divisor.evalFun_single` (71) | PROOF-INGREDIENT | `Finsupp.prod_single_index` | probe F |
| `WeilReciprocity` (79) | **BESPOKE** | — | `Prop`; no consumer inside the set; port `def` at the pin statement |

## 3. The big dictionary `S_` file (70 rows)

`S_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap.lean`, pin order.
`node` marks the eleven public nodes (the `solution` at 1262 is the `ord_placeOfPoint_algebraMap`
node and duplicates row 26).

| pin decl (line) | class | mathlib / port name | evidence |
|---|---|---|---|
| `isRational_of_deg_eq_one` (58) | PROOF | `Place.isRational_iff_deg_eq_one` (this set) | `.2 h` |
| `deg_eq_one_of_isRational` (61) | PROOF | idem | `.1 hv` |
| `ord_finitePlace_ne_zero_iff` (72) | PROOF | port `Place.ord_ofHeightOneSpectrum_ne_zero_iff`, `heightOneSpectrumOfIrreducible_asIdeal`, `Ideal.mem_span_singleton` | one `rw` |
| `inftyValuation_isEquiv_adicValuation` (81) | PROOF | port `Place.isEquiv_adicValuation_of_valuationSubring_eq` | **probe B2**; `rfl` after `placeInfty_toValuationSubring` |
| `placeInfty_ne_ofHeightOneSpectrum` (85) | **SUBSTITUTE** | port `RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum` (`RatFuncDegree.lean:78`) | **probe A4**; same name, same type |
| `eq_ofHeightOneSpectrum_or_eq_placeInfty` (98) | **SUBSTITUTE** | port `RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty` (`RatFuncDegree.lean:61`) | **probe A4**; same name, same type |
| `exists_sub_algebraMap_intDegree_neg` (112) | **SUBSTITUTE** (promotion) | port `private` `RationalFunctionField.exists_sub_algebraMap_intDegree_neg` (`RatFuncDegree.lean:205`) | same type; promote it, else transcribe 51 ln. The port's `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` subsumes its use |
| `deg_placeInfty` (163) | **node**, PROOF | port `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` + `placeInfty_ne_ofHeightOneSpectrum` | **probe A1**; one line |
| `le_exp_neg_one_of_lt_one` (194) | PROOF | `WithZero.exp_log`, `exp_le_exp`, `omega` | pin's name is `AlgebraicCurve.le_exp_neg_one_of_lt_one` (outside `namespace Place`), correcting work order §3 |
| `isUnit_algebraMap` (208, priv) | **SUBSTITUTE** | port `private` `Place.isUnit_algebraMap` (`Defs/Place.lean:238`) | same name/type; pin-private, so also keep local |
| `adicValuation_algebraMap` (214) | **SUBSTITUTE** (promotion) | port `private` `Place.adicValuation_algebraMap` (`Defs/Place.lean:243`) | same type |
| `ord_ofHeightOneSpectrum_eq_zero_of_notMem` (227) | PROOF | port `Place.ord_ofHeightOneSpectrum_ne_zero_iff` | contrapositive, one line |
| `ord_placeInfty` (239) | **node**, PROOF | port `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum` | **probe A2** |
| `ord_placeInfty_algebraMap` (248) | **node**, PROOF | previous + `RatFunc.intDegree_polynomial` | **probe A3** |
| `single_add_single_apply_eq_ord` (258) | PROOF | port `private` general `single_add_single_apply_eq_ord` (`RatFuncDegree.lean:303`) specialized at `placeInfty` | the port's copy is *more general* (`{vinf}` + `hvinf`), so a one-line specialization, not a type-identical import |
| `degree_single_add_single` (292) | PROOF | port `private` general `degree_single_add_single` (`RatFuncDegree.lean:347`), specialized | idem |
| `principalDivisor` (301) | **BESPOKE** | `Finsupp.mk` / `Finsupp.ofSupportFinite` | new `def`; uses `finite_setOf_ord_ne_zero` (port public) |
| `principalDivisor_apply` (306) | PROOF | `rfl` | |
| `principalDivisor_isPrincipal` (309) | PROOF | `Divisor.IsPrincipal` | |
| `degree_principalDivisor` (313) | PROOF | port `degree_eq_zero_of_forall_eq_ord` (`RatFuncDegree.lean:401`) | **probe A5**; exactly the pin's one call |
| `sum_ord_mul_deg_eq_zero` (317) | PROOF | `Finsupp.sum_single`, `map_sum`, `Divisor.degree_single` | probe I |
| `placeOfPoint_ne_placeInfty` (336) | PROOF | needs `placeOfPoint` (**out-of-set**, §5.1); `placeInfty_ne_ofHeightOneSpectrum` | |
| `ord_placeOfPoint_algebraMap_eq_mul` (343) | PROOF | `pow_rootMultiplicity_dvd`, `le_rootMultiplicity_iff`, `ord_mul`, `ord_zpow`, `zpow_natCast` | probes D/E |
| `dvd_ord_placeOfPoint` (382) | PROOF | `RatFunc.num_div_denom`, `ord_mul`, `ord_inv`, `dvd_add` | probe H |
| `ord_placeOfPoint_X_sub_C` (396) | PROOF | `IsDiscreteValuationRing.exists_irreducible`, `Place.ord_coe_irreducible`, `Int.isUnit_iff`, `isUnit_of_dvd_one` | probes E/H; the mathlib DVR route, no port `uniformizer` needed |
| `ord_placeOfPoint_algebraMap` (417) | **node**, PROOF | two rows above | |
| `exists_eq_placeOfPoint` (423) | PROOF | `exists_irreducible_span`, `IsAlgClosed.degree_eq_one_of_irreducible`, `IsAlgClosed.exists_root`, `dvd_iff_isRoot`, `Ideal.span_singleton_eq_span_singleton` | probe D |
| `eq_placeOfPoint_or_eq_placeInfty` (441) | PROOF | previous + port `eq_ofHeightOneSpectrum_or_eq_placeInfty` | |
| `ofOption` (449, priv def) | **BESPOKE** | `Option.elim` | pin-private |
| `ofOption_bijective` (452, priv) | PROOF | `placeOfPoint_injective`, `placeOfPoint_ne_placeInfty` | pin-private |
| `placeEquivOption` (465) | **BESPOKE** (def) | `Equiv.ofBijective` | new named equivalence |
| `placeEquivOption_symm_some` (470) | PROOF | `rfl` | |
| `placeEquivOption_symm_none` (474) | PROOF | `rfl` | |
| `placeEquivOption_placeOfPoint` (478) | PROOF | `Equiv.ofBijective … .symm_apply_apply` | |
| `placeEquivOption_placeInfty` (483) | PROOF | idem | |
| `deg_eq_one_of_isAlgClosed` (487) | PROOF | `eq_placeOfPoint_or_eq_placeInfty`, `deg_placeOfPoint`, `deg_placeInfty` | |
| `algebraMap_polynomial_ne_zero` (502) | PROOF | `RatFunc.algebraMap_ne_zero` | probe H |
| `algebraMap_C` (506) | PROOF | `IsScalarTower.algebraMap_apply`, `Polynomial.algebraMap_eq` | |
| `evalAt_placeOfPoint_algebraMap` (510) | PROOF | `Place.evalAt_congr`, `Place.evalAt_algebraMap`, `rootMultiplicity_pos` | probe E |
| `evalAt_placeOfPoint_X_sub_C` (532) | PROOF | previous + `Polynomial.eval`/`simp` | |
| `mem_placeInfty_of_intDegree_nonpos` (541) | PROOF | port `Place.mem_of_ord_nonneg`, `ord_placeInfty` | probe E |
| `evalAt_placeInfty_eq` (545) | PROOF | `Place.evalAt_congr`, `Place.evalAt_algebraMap`, `mem_placeInfty_of_intDegree_nonpos` | |
| `evalAt_placeInfty_X_sub_C_div` (574) | PROOF | `div_sub_one`, `RatFunc.intDegree_div`, `natDegree_C`, `natDegree_X_sub_C` | probes C/H/I |
| `principalDivisor_X_sub_C` (606) | PROOF | `single_add_single_apply_eq_ord`, `natDegree_X_sub_C` | |
| `ord_X_sub_C` (615) | PROOF | `principalDivisor_apply` | |
| `ord_X_sub_C_placeOfPoint_of_ne` (621) | PROOF | `Finsupp.single_eq_of_ne`, `placeOfPoint_injective` | probe I |
| `ord_X_sub_C_placeOfPoint_self` (629) | PROOF | idem | |
| `ord_X_sub_C_placeInfty` (634) | PROOF | idem | |
| `isRational_placeOfPoint` (642) | PROOF | `Place.isRational_of_deg_eq_one`, `deg_placeOfPoint` | |
| `principalDivisor_X_sub_C_div` (645) | PROOF | `ord_mul`, `ord_inv`, `ord_X_sub_C` | |
| `evalAt_placeOfPoint_X_sub_C_div` (665) | PROOF | `Place.evalAt_mul`, `Place.evalAt_inv`, `evalAt_placeOfPoint_X_sub_C` | probe E |
| `isRational_of_isAlgClosed` (689) | PROOF | `Place.isRational_of_deg_eq_one`, `deg_eq_one_of_isAlgClosed` | |
| `algebraMap_const_ne_zero` (694) | PROOF | `simpa` | |
| `ord_ne_zero_of_mem_support` (701) | PROOF | `Finsupp.mem_support_iff` | probe I |
| `sum_ord_eq_zero` (707) | PROOF | `sum_ord_mul_deg_eq_zero`, `deg_eq_one_of_isAlgClosed` | |
| `zpow_sum_eq_prod` (715) | PROOF | `Finset.cons_induction`, `zpow_add₀` | probe F |
| `principalDivisor_congr` (723) | PROOF | `subst` | |
| `reciprocity_algebraMap_right` (730) | PROOF | `Place.evalAt_algebraMap`, `Place.ord_algebraMap`, `zpow_sum_eq_prod` | probe E |
| `reciprocity_mul_right` (746) | PROOF | `Divisor.evalFun_add`, `evalFun_mul`, `evalFun_ne_zero` (**out-of-set**, §5.2) | probe F |
| `reciprocity_mul_left` (774) | PROOF | previous | |
| `reciprocity_zpow_right` (787) | PROOF | `Divisor.evalFun_zsmul`, `evalFun_zpow_left` (**out-of-set**) | probe F |
| `reciprocity_zpow_left` (803) | PROOF | previous | |
| `exists_algebraMap_of_forall_ord_eq_zero` (813) | PROOF | `WfDvdMonoid.exists_irreducible_factor`, `Polynomial.isUnit_iff`, `RatFunc.isCoprime_num_denom`, `ord_finitePlace_ne_zero_iff`, `algebraMap_C` | probes H/I |
| `crossRatio_reciprocity` (859) | PROOF | `evalAt_placeOfPoint_X_sub_C_div`, `evalAt_placeInfty_X_sub_C_div`, `Divisor.evalFun_single_sub_single` | probe F |
| `reciprocity_of_forall_ord_eq_zero` (883) | PROOF | previous + `exists_algebraMap_of_forall_ord_eq_zero` | |
| `ord_div_zpow` (891) | PROOF | `ord_mul`, `ord_inv`, `ord_zpow` | probe E |
| `ord_X_sub_C_eq_zero_of_ne` (898) | PROOF | `ord_X_sub_C`, `Finsupp.single_eq_of_ne` | |
| `reciprocity_linear` (904) | PROOF | `Finset.sum_lt_sum_of_nonempty`, `Finset.card_le_card`, `Finset.card_erase_of_mem`, `eq_placeOfPoint_or_eq_placeInfty` | probes D/I; 213 pin ln, all mathlib assembly |
| `reciprocity_of_ord_placeInfty_eq_zero` (1117) | PROOF | previous + `Finset.sum_singleton` | 145 pin ln |
| `solution` (1262) | **node** | `ord_placeOfPoint_algebraMap` (row 26) | the P2MW wrapper's `solution` |

## 4. The ten tiny `S_` files (10 rows)

Each file's only declaration is `solution`, whose statement is the public node in the
table. The names are the pin's `Theorems/Thm_AlgebraicCurve_*` wrapper names.

| node (pin file, ln) | class | mathlib / port name | evidence |
|---|---|---|---|
| `Place.evalAt_algebraMap` (13) | PROOF | `evalAt_of_mem`, `Place.coe_algebraMap`, `IsLocalRing.ResidueField.algebraMap_eq`, `IsScalarTower.algebraMap_apply`, `residueInv_algebraMap` | proto E compiles verbatim |
| `Place.evalAt_congr` (35) | PROOF | `Place.mem_maximalIdeal_iff_adicValuation_lt_one`, `IsLocalRing.residue_eq_zero_iff`, `WithZero.exp_log`, `exp_lt_exp` | proto E compiles verbatim |
| `Place.evalAt_mul` (11) | PROOF | `algebraMap_residueField_injective`, `algebraMap_evalAt` | proto E; the pin's `apply …` transcribes unchanged |
| `Place.evalAt_ne_zero` (27) | PROOF | `Place.mem_of_ord_nonneg`, `IsDiscreteValuationRing.exists_irreducible`, `Place.exists_unit_mul_zpow`, `IsLocalRing.residue_ne_zero_iff_isUnit` | proto E |
| `Place.evalAt_inv` (18) | PROOF | `evalAt_mul`, `evalAt_one`, `eq_inv_of_mul_eq_one_right` | proto E |
| `Place.evalAt_zpow` (31) | PROOF | `evalAt_mul`, `evalAt_inv`, `Place.ord_zpow`, `zpow_natCast`, `zpow_negSucc` | proto E |
| `Place.isRational_iff_deg_eq_one` (21) | PROOF | `AlgEquiv.ofBijective`, `Subalgebra.bot_eq_top_iff_finrank_eq_one`, `Algebra.mem_bot` | proto E; the mathlib rank-one algebra fact is exact |
| `RationalFunctionField.deg_placeInfty` (14) | **node**, PROOF | port `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` | **probe A1**; the pin S-file itself calls this pin theorem |
| `RationalFunctionField.ord_placeInfty` (14) | **node**, PROOF | port `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum` | **probe A2**; idem |
| `RationalFunctionField.ord_placeInfty_algebraMap` (12) | **node**, PROOF | previous + `RatFunc.intDegree_polynomial` | **probe A3** |

## 5. Reuse wins, with probe evidence

### 5.1 The unported `placeOfPoint` block (5 rows, out-of-set)

`Defs/RatFuncPlaces.lean` records the deliberate drop ("`placeOfPoint` (236–274) …
occur in the cone only inside the pin's `attribute [-simp]` walls"). That reasoning
does not survive the dictionary: the big file's public statements and the `isRational_*`
block name `placeOfPoint` throughout. The block is pin
`Def_AlgebraicCurve_RatFuncPlaces.lean:236–274` and transcribes directly on the public
port API (`finitePlace`, `heightOneSpectrumOfIrreducible`,
`heightOneSpectrumOfIrreducible_asIdeal`, `Place.ofHeightOneSpectrum_injective`,
`deg_finitePlace`) plus `Polynomial.irreducible_X_sub_C`, `natDegree_X_sub_C`,
`Ideal.span_singleton_eq_span_singleton`, `dvd_iff_isRoot`. `ProtoPlaceOfPoint` in the
scratch compiles all five:

```lean
def placeOfPoint (a : K) : Place K (RatFunc K) := finitePlace K (irreducible_X_sub_C a)
theorem placeOfPoint_eq_ofHeightOneSpectrum (a : K) : … := rfl
theorem placeOfPoint_injective : Function.Injective (placeOfPoint K) := …
theorem deg_placeOfPoint (a : K) : (placeOfPoint K a).deg = 1 := by
  rw [placeOfPoint, deg_finitePlace, natDegree_X_sub_C]
```

`placeOfPoint` itself is BESPOKE (one `def`); its four lemmas are PROOF-INGREDIENT.
(The worker's `P1Dictionary.lean` header already records this promotion.)

### 5.2 The unported `Divisor.evalFun_*` algebra nodes (6 rows, out-of-set)

The big file imports `Theorems/Thm_AlgebraicCurve_Divisor_{evalFun_add, evalFun_mul,
evalFun_ne_zero, evalFun_zsmul, evalFun_zpow_left, evalFun_single_sub_single}`, none of
which exists under `FLTForHuman/` (grep count 0 for each). Their pin home is
`Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean` (160 ln, 15 decls) plus
six `S_AlgebraicCurve_Divisor_evalFun_*` files (78 ln). They are pure mathlib assembly
on the new `Place.evalAt` interface:

| node (S-file ln) | mathlib name |
|---|---|
| `Divisor.evalFun_add` (13) | `Finsupp.prod_add_index`, `zpow_add₀`, `Finset.mem_union` |
| `Divisor.evalFun_mul` (12) | `Finsupp.prod_congr`, `Finsupp.prod_mul`, `mul_zpow` |
| `Divisor.evalFun_ne_zero` (9) | `Finset.prod_ne_zero_iff`, `zpow_ne_zero` |
| `Divisor.evalFun_zsmul` (12) | `Finsupp.prod_of_support_subset`, `Finsupp.support_smul`, `Finset.prod_zpow`, `zpow_mul` |
| `Divisor.evalFun_zpow_left` (15) | `Place.evalAt_zpow`, `Finset.prod_zpow`, `mul_comm` |
| `Divisor.evalFun_single_sub_single` (17) | `Finsupp.support_single_subset`, `evalFun_add`, `zpow_one`, `zpow_neg_one` |

`ProtoEvalFun` compiles all six verbatim (probe F). Note these are **public** pin
declarations with their own `Theorems/` wrappers; if the worker keeps its copies
`private` inside `P1Dictionary.lean`, the checker never sees them (they are not in the
work order's `SOURCES`) and 3.2b–d cannot import them. Either append the six wrappers
to `SOURCES` and land them public, or record the intentional omission.

### 5.3 The infinity block is one step from `RatFunc.inftyValuation`

The port's `placeInfty` **is** `inftyValuation`'s valuation subring
(`Defs/RatFuncPlaces.lean:253`), so:

```lean
example (K : Type*) [Field K] [DecidableEq (RatFunc K)] :
    (placeInfty K).toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := rfl
```

and the pin's `inftyValuation_isEquiv_adicValuation` is the port bridge at `rfl`
(probe B2):

```lean
example : (RatFunc.inftyValuation K).IsEquiv (placeInfty K).adicValuation :=
  Place.isEquiv_adicValuation_of_valuationSubring_eq (placeInfty K) (w := …) rfl
```

`RatFunc.inftyValuation`/`inftyValuationDef`/`.X`/`.X_zpow`/`.X_inv`/`.C`/`.polynomial`/
`_apply`/`_of_nonzero`, `RatFunc.inftyValued` and `RatFunc.CompletionAtInfty` are all
present in `Mathlib/FieldTheory/RatFunc/Valuation.lean` (probe B). There is **no**
mathlib lemma of the form `placeInfty.ord = WithZero.log ∘ inftyValuation`; the
connection is the port's `Place.ord_eq_neg_log_of_valuationSubring_eq` plus
`RatFunc.inftyValuation_of_nonzero` and `log_exp`.

### 5.4 The three ℙ¹ nodes, already discharged

The pin's own tiny `S_` files prove `deg_placeInfty`/`ord_placeInfty`/
`ord_placeInfty_algebraMap` by calling pin theorems
`deg_eq_one_of_forall_ne_ofHeightOneSpectrum` and
`ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum`, which the port has **already
ported publicly at the same names** in `PrincipalDivisors/RatFuncDegree.lean`
(lines 255 and 188). The three nodes are therefore one-liners (probes A1–A3); no pin
proof body is transcribed.

### 5.5 The `principalDivisor` degree block

`degree_principalDivisor` is the pin's one call
`degree_eq_zero_of_forall_eq_ord (principalDivisor hf) fun _ => rfl`, and the port's
master lemma of that name already exists (`RatFuncDegree.lean:401`, proved by UFD
induction over numerator and denominator). `sum_ord_mul_deg_eq_zero` then only needs
`Finsupp.sum_single`, `map_sum` and `Divisor.degree_single`. **No `intDegree` route
applies to this block** — `intDegree` appears only in `ord_placeInfty` and the pin's
`WFg` helper.

### 5.6 The DVR route

`ord_placeOfPoint_X_sub_C` is the only row that needs a uniformizer, and it uses the
mathlib route directly: `IsDiscreteValuationRing.exists_irreducible`,
`Place.ord_coe_irreducible`, `Int.isUnit_iff`, `isUnit_of_dvd_one`. The port's
`Place.uniformizer`/`coe_uniformizer` are not on the path.
`IsDiscreteValuationRing.irreducible_iff_uniformizer`, `.addVal`, `.addVal_uniformizer`
and `.eq_unit_mul_pow_irreducible` all exist in v4.34.0 (probe H) but are **not needed**
by any 3.2a row.

## 6. Route options

- **R1 — import `placeOfPoint` into the dictionary, do not re-privatize it.** The
  block belongs to the `P¹` place vocabulary (`Defs/RatFuncPlaces.lean` is its pin
  home); writing it once at the pin names in `P1Dictionary.lean` is acceptable for the
  set, but 3.2b–d will want it. Promoting it back into `Defs/RatFuncPlaces.lean` (the
  file that documents the drop) is the cleaner home; either way it must be public.
- **R2 — the `evalFun_*` laws are a new public module, not private helpers.**
  `Defs/PlaceEvaluationAlgebra.lean` (160 ln) is the pin's home; the six S-file nodes
  are one public declaration each. Landing them public at the pin names is required
  for the big file's `reciprocity_*` rows and for the `SOURCES` checker to see them.
- **R3 — the two `private` WFj helpers are already public in spirit.**
  `single_add_single_apply_eq_ord` and `degree_single_add_single` are `private` in
  `RatFuncDegree.lean` but are general lemmas (`{vinf}` + `hvinf`); specialising them
  is one line. Promoting the general forms is preferable to a second transcription.
- **R4 — the infinity block does not need the pin's `exists_sub_algebraMap_intDegree_neg`**
  if `deg_placeInfty` is landed as the one-line application of the port's general
  lemma. Keep the pin declaration (the checker wants it) but prove it by promoting the
  port's private copy, not by re-doing the 51-line `leadingCoeff` argument.
- **R5 — `WeilReciprocity` has no consumer in the set.** Land the `def` for
  faithfulness, but do not build a `Divisor.evalFun_*`-style API around it.
- **R6 — `intDegree` is not a route for the divisor block** (see §5.5); do not spend
  budget trying to express `principalDivisor`'s degree zero through it.

## 7. API drift (v4.34.0) — what the worker must change

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `dif_pos hf` (file 1:43) | deprecated → `dite_eq_left hf` | rename; `dite_eq_left hf` elaborates verbatim against the landed `evalAt` (probe E) |
| `Polynomial.degree_sub_lt hdegeq hnum0 hlc` (big:159, inside `exists_sub_algebraMap_intDegree_neg`) | deprecated → `Polynomial.degree_sub_lt_left` (same signature; `Mathlib/Algebra/Polynomial/Degree/Defs.lean:543`) | rename |
| `Polynomial.multiplicity` / `Polynomial.emultiplicity` (brief lead) | **do not exist**; only root `multiplicity`/`emultiplicity` | the pin uses `rootMultiplicity`; no change needed |
| `RatFunc.inftyValuation` needs `[DecidableEq (RatFunc K)]` | present (`Valuation.lean`) | keep the pin's `[DecidableEq]` binders; `classical` in proofs |
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` (global drift table) | relevant if the worker copies a `simp only [Set.mem_setOf_eq]` |
| `Polynomial.degree_sub_lt` / `dif_pos` in any other imported pin proof | deprecated | the same two renames |

No other drift was found on the set's path: `Finsupp.prod_*`, `Finset.prod_zpow`,
`zpow_add₀`, `zpow_mul`, `mul_zpow`, `RatFunc.num_div_denom`, `RatFunc.isCoprime_num_denom`,
`Polynomial.isUnit_iff`, `WfDvdMonoid.exists_irreducible_factor`,
`IsDiscreteValuationRing.*`, `Subalgebra.bot_eq_top_iff_finrank_eq_one`,
`IsLocalRing.residue*`, `Function.invFun*` all keep the pin's names and shapes
(probes F–I), and the pin's `one_mem _` (in `evalAt_one`) and `apply
v.algebraMap_residueField_injective` (in `evalAt_mul`) transcribe unchanged (probe E).

## 8. Recorded negatives

Confirmed against mathlib `v4.34.0`; phrased so the search is not repeated.

1. **No `Place.IsRational`/`residueInv`/`evalAt`/`evalFun`/`WeilReciprocity` anywhere
   in mathlib or under `FLTForHuman/`.** The interface is genuinely new. The only
   reusable mathlib pieces are `RingHom.injective`, `Function.invFun`/`invFun_eq`/
   `leftInverse_invFun`, `IsLocalRing.residue*` and
   `Subalgebra.bot_eq_top_iff_finrank_eq_one`.
2. **No mathlib trace/residue API for `Place.IsRational`.** The port's
   `hasSeparableResidue_of_perfectField` uses `Algebra.trace_ne_zero`
   (`Mathlib/RingTheory/Trace/Basic.lean:517`), which is unrelated to the
   `Function.Surjective (algebraMap K v.ResidueField)` interface (probe G). Do not
   look for a trace route to `isRational_iff_deg_eq_one`.
3. **No `Polynomial.multiplicity`/`Polynomial.emultiplicity`.** The pin's consumer is
   `Polynomial.rootMultiplicity`, whose API is `pow_rootMultiplicity_dvd`,
   `le_rootMultiplicity_iff`, `rootMultiplicity_pos` and `rootMultiplicity_pos'`
   (`Mathlib/Algebra/Polynomial/Div.lean`).
4. **No mathlib lemma stating `placeInfty.ord = -intDegree` or
   `placeInfty.ord = -log ∘ inftyValuation`.** The route is the port's
   `ord_eq_neg_log_of_valuationSubring_eq` and
   `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum`.
5. **No `placeOfPoint` in the port.** Deliberately dropped (`Defs/RatFuncPlaces.lean`
   header, pin lines 236–274); the dictionary must restore it.
6. **No `Divisor.evalFun_add`/`evalFun_mul`/`evalFun_ne_zero`/`evalFun_zsmul`/
   `evalFun_zpow_left`/`evalFun_single_sub_single` in the port.** They live in the
   unported `Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean`.
7. **No `intDegree` route to `principalDivisor`'s degree.** Mathlib's
   `RatFunc.intDegree_add_le` bounds `intDegree` of a sum but says nothing about the
   divisor of an arbitrary rational function; the port's UFD induction is the route.
8. **`IsDiscreteValuationRing.{irreducible_iff_uniformizer, addVal, addVal_uniformizer,
   eq_unit_mul_pow_irreducible}` are present but off-path.** The pin's `ord` is
   `-log ∘ adicValuation`, not `addVal`; `exists_irreducible` is the only DVR lemma
   used.
9. **`RatFunc.CompletionAtInfty`/`inftyValued` exist** but are not needed by 3.2a:
   the pin's dictionary is valuation-free beyond `inftyValuation` itself.

## 9. What this changes for `WORKORDER-P3-2a-p1-dictionary.md` §4

**Scope / measurement.**

- File (1) is **14 rows**, not 13: add `WeilReciprocity`.
- The measured set is **80 S-file rows** (70 + 10), plus 11 wrappers = the 91 the
  work order quotes; state which is which.
- Add **5 out-of-set `placeOfPoint` rows** (pin `Def_AlgebraicCurve_RatFuncPlaces`
  236–274, §5.1).
- Add **6 out-of-set `evalFun_*` rows** (pin
  `Def_AlgebraicCurve_PlaceEvaluationAlgebra` + its six S-files, §5.2), and decide
  public-vs-`private` for them; if public, they need their own `SOURCES` entries.

**Discharged proofs (mark import-discharged; the statements still land).**

- `RationalFunctionField.{placeInfty_ne_ofHeightOneSpectrum,
  eq_ofHeightOneSpectrum_or_eq_placeInfty}` — import `PrincipalDivisors/RatFuncDegree`.
- `RationalFunctionField.{deg_placeInfty, ord_placeInfty, ord_placeInfty_algebraMap}`
  — one-line applications of `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` /
  `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum`.
- `RationalFunctionField.{exists_sub_algebraMap_intDegree_neg, adicValuation_algebraMap}`
  and `Place.isUnit_algebraMap` — promote the same-typed `private` port copies, or
  transcribe.
- `degree_principalDivisor` — one call to `degree_eq_zero_of_forall_eq_ord`.

**Imports the worker may use.**

- `PlaceEvaluation.lean`: `Mathlib.RingTheory.LocalRing.ResidueField.Basic`,
  `Mathlib.Algebra.BigOperators.Finsupp.Basic`, plus
  `FLTForHuman.AlgebraicCurve.Defs.{Place, Divisor}` (as landed).
- `P1Dictionary.lean`: `Mathlib.FieldTheory.RatFunc.{Degree, Valuation}`,
  `Mathlib.Algebra.Polynomial.Div` (`rootMultiplicity`),
  `Mathlib.Algebra.Polynomial.RingDivision` (`irreducible_X_sub_C`),
  `Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition`
  (`Subalgebra.bot_eq_top_iff_finrank_eq_one`),
  `Mathlib.Algebra.BigOperators.Group.Finset.Defs` (`Finset.prod_zpow`),
  `Mathlib.NumberTheory.RatFunc.Ostrowski` (the dichotomy),
  `Mathlib.RingTheory.DedekindDomain.Factorization` (primes),
  plus `FLTForHuman.AlgebraicCurve.PrincipalDivisors.RatFuncDegree` and
  `…Defs.{PlaceEvaluation, PlaceEvaluationAlgebra}`.
- Do **not** add `Mathlib.RingTheory.Polynomial.Roots`: that module path has no olean
  in this checkout (probe failure); `Polynomial.roots` is reachable through the
  RatFunc imports.

**Stop-early risks.**

- Risk 1 (the big file's 66 other public declarations are verbatim transcriptions) is
  real but bounded: every row's ingredients are named above and the hard ones
  (`reciprocity_linear` 213 ln, `reciprocity_of_ord_placeInfty_eq_zero` 145 ln) were
  classified PROOF-INGREDIENT because every step is a named `Finset`/`Finsupp` lemma.
  The one genuinely assembled proof in the set is `exists_algebraMap_of_forall_ord_eq_zero`
  (the UFD/coprimality argument) — budget it.
- Risk 2 (API drift beyond a rename) **fires twice**: `dif_pos` → `dite_eq_left` (with
  the `unfold evalAt` wrinkle) and `Polynomial.degree_sub_lt` →
  `Polynomial.degree_sub_lt_left`. Both are one-line.
- Risk 3 (a proof needs a declaration outside the measured files) **fires**: §5.1 and
  §5.2. The work order §6's protocol applies — resolve locally `private` with the
  statement verbatim and report the pin `file:line`, or re-scope to include the
  `PlaceEvaluationAlgebra` module.

**Checker wiring.** Append `Def_AlgebraicCurve_PlaceEvaluation.lean`, the eleven
`Thm_*` wrappers, then the eleven `S_*` files to `SOURCES`; append
`FLTForHuman/AlgebraicCurve/Defs/{PlaceEvaluation,P1Dictionary}.lean` to `PORT_FILES`.
If the `evalFun_*` nodes land public, append their wrappers too, otherwise add an
`OWN_PROOFS`/exemption note.

## 10. Appendix — module map for the named constants

| name | module |
|---|---|
| `RatFunc.{inftyValuation, inftyValuationDef, inftyValuation_apply, inftyValuation_of_nonzero, inftyValuation.X, .X_zpow, .X_inv, .C, .polynomial, inftyValued, CompletionAtInfty}` | `Mathlib/FieldTheory/RatFunc/Valuation.lean` |
| `RatFunc.{intDegree, intDegree_zero, intDegree_one, intDegree_C, intDegree_X, intDegree_polynomial, intDegree_mul, intDegree_inv, intDegree_div, intDegree_add_le}` | `Mathlib/FieldTheory/RatFunc/Degree.lean` |
| `RatFunc.{num, denom, num_ne_zero, denom_ne_zero, num_div_denom, isCoprime_num_denom, algebraMap_ne_zero, X_ne_zero}` | `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean`, `Mathlib/FieldTheory/RatFunc/Defs.lean` |
| `Polynomial.{rootMultiplicity, pow_rootMultiplicity_dvd, le_rootMultiplicity_iff, rootMultiplicity_pos, IsRoot, dvd_iff_isRoot, roots}` | `Mathlib/Algebra/Polynomial/Div.lean` |
| `Polynomial.{irreducible_X_sub_C}` | `Mathlib/Algebra/Polynomial/RingDivision.lean` |
| `Polynomial.{natDegree_X_sub_C, X_sub_C_ne_zero}` | `Mathlib/Algebra/Polynomial/Degree/Operations.lean` |
| `Polynomial.{degree_sub_lt_left, degree_eq_natDegree, leadingCoeff_mul, leadingCoeff_ne_zero, natDegree_lt_natDegree, degree_mul, degree_C, isUnit_iff}` | `Mathlib/Algebra/Polynomial/Degree/*`, `Mathlib/Algebra/Polynomial/*` |
| `IsDiscreteValuationRing.{exists_irreducible, irreducible_iff_uniformizer, addVal, addVal_uniformizer, exists_units_eq_smul_zpow_of_irreducible}` | `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` |
| `IsLocalRing.{residue, residue_surjective, residue_eq_zero_iff, residue_ne_zero_iff_isUnit, ResidueField.algebraMap_eq}` | `Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean` |
| `Subalgebra.bot_eq_top_iff_finrank_eq_one` | `Mathlib/LinearAlgebra/Dimension/FreeAndStrongRankCondition.lean` |
| `Algebra.{trace_ne_zero}` | `Mathlib/RingTheory/Trace/Basic.lean` |
| `Function.{invFun, invFun_eq, leftInverse_invFun}` | `Mathlib/Logic/Function/Basic.lean` |
| `dite_eq_left` | core/`Init` (the v4.34 spelling of `dif_pos`) |
| `Finsupp.{prod_zero_index, prod_single_index, prod_add_index, prod_mul, prod_of_support_subset, sum_single, mem_support_iff, support_eq_empty, add_apply, single_eq_same, single_eq_of_ne, support_smul}` | `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean`, `Mathlib/Data/Finsupp/SMulWithZero.lean` |
| `Finset.{prod_ne_zero_iff, prod_zpow, sum_lt_sum_of_nonempty, card_le_card, card_erase_of_mem, eq_empty_or_nonempty, mem_union, cons_induction}` | `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`, `Mathlib/Data/Finset/*` |
| `zpow_add₀`, `zpow_mul`, `mul_zpow`, `zpow_neg_one`, `zpow_one`, `zpow_natCast`, `zpow_negSucc`, `eq_inv_of_mul_eq_one_right`, `isUnit_of_dvd_one`, `Int.isUnit_iff` | `Mathlib/Algebra/GroupWithZero/Basic.lean`, `Mathlib/Algebra/Group/Basic.lean`, `Mathlib/Algebra/Group/Int.lean` |
| `WfDvdMonoid.exists_irreducible_factor`, `Ideal.{mem_span_singleton, span_singleton_eq_span_singleton}` | `Mathlib/RingTheory/*` |
| `IsAlgClosed.{degree_eq_one_of_irreducible, exists_root}` | `Mathlib/FieldTheory/IsAlgClosed/Basic.lean` |

Port declarations referred to above: `FLTForHuman/AlgebraicCurve/Defs/RatFuncPlaces.lean`
(`finitePlace`, `deg_finitePlace`, `placeInfty`, `placeInfty_toValuationSubring`,
`ofHeightOneSpectrum_injective`), `…/Defs/Place.lean` (`Place`, `ord`, `adicValuation`,
`mem_of_ord_nonneg`, `exists_unit_mul_zpow`, `ord_coe_irreducible`,
`ord_eq_neg_log_of_valuationSubring_eq`), `…/PrincipalDivisors/RatFuncDegree.lean`
(`eq_ofHeightOneSpectrum_or_eq_placeInfty`,
`placeInfty_ne_ofHeightOneSpectrum`, `deg_eq_one_of_forall_ne_ofHeightOneSpectrum`,
`ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum`,
`degree_eq_zero_of_forall_eq_ord`, `finite_setOf_ord_ne_zero`),
`…/Defs/PushPull.lean` (`mem_of_ord_nonneg`, `ord_nonneg_of_mem`),
`…/Defs/Divisor.lean` (`Divisor`, `Divisor.degree`, `Divisor.degree_single`,
`Divisor.IsPrincipal`).

## 11. State at audit time

The phase-3.2a worker started before this note closed and has already written

- `FLTForHuman/AlgebraicCurve/Defs/PlaceEvaluation.lean` (104 ln) — file (1),
  including the `dif_pos` → `dite_eq_left` rename;
- `…/Defs/P1Dictionary.lean` (1,344 ln) — the eleven nodes and the big file's 70 rows,
  including the `placeOfPoint` restoration (§5.1) and the
  `le_exp_neg_one_of_lt_one` name correction (§7);
- `…/Defs/PlaceEvaluationAlgebra.lean` (185 ln) — the pin's
  `Def_AlgebraicCurve_PlaceEvaluationAlgebra` laws at their pin names
  (`evalFun_add_of_forall_ne_zero`, `evalFun_mul_of_forall_mem`,
  `evalFun_ne_zero_of_forall_ne_zero`, `evalFun_zsmul_divisor`,
  `evalFun_zpow_left_of_ord_eq_zero`, `evalFun_single_sub_single`, …), i.e. §5.2 is
  being discharged as a separate public module.

The classifications above remain the route record. The outstanding items to re-check
against the landed files are: the six **wrapper** names
(`Divisor.evalFun_{add,mul,ne_zero,zsmul,zpow_left}`) are private adapters in
`P1Dictionary.lean` delegating to the public `_of_forall_*` laws — decide whether the
wrappers' own `Theorems/` files belong in `SOURCES`; and the
`PORT_FILES`/`SOURCES` wiring (no `PlaceEvaluation`/`P1Dictionary`/
`PlaceEvaluationAlgebra` entry could be found in `spec/check_flt_statements.py` at
audit time).
