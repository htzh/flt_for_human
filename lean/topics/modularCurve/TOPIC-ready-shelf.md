# The `ModularCurve` ready shelf — the whole family, scoped (2026-10-27)

**Status: scoped, not landed.** This is the first scoping of the **entire** `ModularCurve` shelf of
the Deligne–Serre column with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). It reads
**both** blocks — the 26 ready rows / 8,748 silo and the 34 graph leaves / 7,331 silo — corrects
the one false-marker chain (MD-001 and the `ModularForm`/`CuspForm` shadow behind it), audits the
**definition vocabulary** that a premise-based frontier cannot see, prices the corrected 25-row
shelf's rows at **7,292 net new math lines** on the whole-set read (≈8,430 with the definition
wave), and cuts a **seven-order programme** whose first wave is three orders / 2,565 silo. Its
shelf counts supersede
[TOPIC-levelN-and-modular-polynomial.md](TOPIC-levelN-and-modular-polynomial.md) ("Ready shelf,
part 1", the A/B record of 2026-10-09): those rows have landed, and this is their successor
generation. The family is large — 22× the AC set's 390 silo — and this is the first time it is
read as one set.

**Successor (2026-10-27).** Story **M1** is now scoped to the row in
[SET-MC7.md](SET-MC7.md) (the shelf's MC-7): its definition gate is landed
(`ModularCurve/Defs/QExpReductionModL.lean`, 29 decls, `29 ok / 0 / 0`), the
`CuspForm_Gamma1HeckeOperators` half of the gate turned out to be already ported under the H2
names (§0.2's 32 lines are not a gate), MD-001 is closed, and the row is re-cut as three
independent worker orders of ≈150–850 lines.  Read SET-MC7 §0 before using this note's M1
figures: the story is unchanged in silo (2,755) but its *work* figure is not.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`. Read date 2026-10-27, after SET 8's landing; the read is `frontier.py`'s cached graph
(≈5 s) and the pricing is `port_advise`/`port_plan` (text only).

| figure | instrument | corrected (§0.1) |
|---|---:|---:|
| `ModularCurve` ready rows | 26 / 8,748 silo | **25 / 8,668** |
| `ModularCurve` leaves | 34 / 7,331 | 34 / 7,331 |
| `ModularCurve` demand | 184 / 81,744 | 185 / 81,780 |
| `ModularCurve` withheld (FR-0044) | 2 / 610 | 2 / 610 |
| ready, all namespaces | 86 / 20,274 | 86 / 19,834 |
| leaves, all namespaces | 296 / 72,205 | 296 / 72,205 |
| `needed [F terminal]` | 1,018 / 404,790 | 1,020 / 404,926 |
| frontier F | 1,390 / 721,642 | 1,388 / 721,506 |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mcshelf.json
python3 frontier.py --selfcheck
# the corrected read (the MD-001 chain, §0.1); the full correction also unports the 261 row
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1 \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast \
  --unport AlgebraicCurve.weilReciprocity > build/mcshelf-corrected.json
```

**The MC block is 26 ready rows / 8,748 silo — and it has leaves for the first time.** The
`--include-leaves` clause is not free here: 34 `ModularCurve` leaves / 7,331 silo sit in the
block — the third-largest namespace row of the leaves view, after `AutomorphicForm`'s 91 and
`NumberField`'s 48. They are read as a *second shelf* and every one is named or deferred in §3. The ready block's silo is 43 % of the whole
ready shelf's 20,274; the MC demand, 184 nodes / 81,744 silo, is 6.7× the AC demand and the largest
namespace row of the column.

**`--selfcheck` names MD-001 alone**, as after SET 7; its node is the MC 36 row of §0.1. No other
metadata entry touches the MC shelf.

**The withheld block is two `ModularCurve` rows / 610 silo**, both on the prunable subject:

| withheld row | silo | blocking premise (in the avoided set R) |
|---|---:|---|
| `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` | 327 | `AlgebraicCurve.Pic0.abelJacobiCard_genus` |
| `ModularCurve.moduleFinite_padicInt_tateModule_jOne` | 283 | `AlgebraicCurve.Pic0.abelJacobiCard_genus` |

They are the pair scoped in [TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md): one set, a
13-declaration shared rank engine (191 removable lines), **not** this shelf's — their gate is
`abelJacobiCard_genus`'s 144-node / 66k-line Abel–Jacobi program, plus the absent
`TateModule` definition layer (69 declarations, the T1 plan of that note). Quote them and defer.

**The delta against the last MC read.** The shelf has grown, not shrunk: "part 1" read 32 ready
rows / 8,362 silo on 2026-10-09 (subjects A–D), the column plan's §2 listed 13 on 2026-10-19, and
the recent waves' successors have brought it to 26 / 8,748. The growth is visible per subject:
the level-`N`/`Φ_N` story's successors (510, 134, 62), the Tate/twist successors (185, 144, 637,
254), the Hecke-Galois four (272, 265, 27, 27), the Siegel/Eisenstein three, and the
constant-reduction three that no topic owns yet.

## 0.1 The correction: the MD-001 chain, and the 80/36/261 false ready

The instrument's 26 MC rows include one that cannot be transcribed:
`ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem` (80). Its only substantive premise is
`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36), which the frontier reads as
ported because `ModularCurve/X1/IntegralityJqNModC.lean:64,68` carries a stale `spec-pin:` for it
(MD-001; the module's own prose says "Not ported here"). The 36 row itself is **not** port-true:
its one substantive premise is `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (261),
read ported through the **`CuspForm` twin's last name** in
`ModularForms/WeightOne/Gamma1IntegralBasis.lean` — the shadow MD-001 calls "the deeper
undercount", and the plan's C2 §9 already records that the cuspidal subspace cannot stand in for
the Eisenstein part. So the chain is 261 → 36 → 80 and **neither 36 nor 80 is a row of this
shelf**; the corrected MC shelf is **25 / 8,668**.

| node | silo | marker | why it is false |
|---|---:|---|---|
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | `spec-pin:` in `X1/IntegralityJqNModC.lean:64,68` (MD-001) | no declaration anywhere; its own premise 261 is unported |
| `ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem` | 80 | inherits the 36 | a **false ready**: `needed = 1` while its premise is a false marker, so it is not in the withheld block either (that block is the prune set's) |
| `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` | 261 | last-name shadow (`CuspForm` twin) | different statement (Eisenstein vs cuspidal); the plan's C2 §9 prices its chain at ≈4.8k raw / ≈2.1k `S_` lines |

The AC shadow (`AlgebraicCurve.weilReciprocity`) does not touch the MC block. Correcting the whole
two-block read needs the 36 and the 261 as well as the AC shadow; the full read is the one quoted
in the figure table. **No MC row is cut on the instrument's 26.**

## 0.2 The definition-vocabulary audit — why this family is not an AC-style cut

The frontier's readiness is **premise-based**: it walks the `Theorems/Thm_*` citation edges and
does not read the statement's `Definitions/Def_*.lean` imports, nor the `S_` file's proof-level
`Def_` imports. The AC set of SET 8 happened to have its whole definition layer ported; the MC
shelf does **not** — and this is the first time the gap is measured. `port_advise --with-defs` on
the 25 rows puts **26** wrapper-level `Def_` modules in the closure, and the `S_` files import
**11 more** that the wrapper route does not reach.

**Fully ported (21 of them).** Every public declaration has a public port statement:
`AlgebraicCurve_{CanonicalDivisor, ConstantReduction, IsCurveOver}`, `CohCarrier_Level`,
`ModularCurve_{FibrePoly, HeckeDifferential, JqCoeff, PhiGen, TateFormal, TateSlots, X0, X1Diamond,
X1HeckeOperator}`, `ModularCurve_{LaurentCoeff, PrimCosetReps, QExpansionDiff}`,
`EisensteinSeries_EisensteinG`, `PeriodPair_Uniformization`, `WeierstrassCurve_{Velu,
OddOrderSummingSet, ReductionMap}`. No gate for the stories that only touch these.

**Partially ported (16 modules).** The missing declarations are the **statement vocabulary and
the engine** of the story, and the row's statement or proof cannot be written without them. The
counts are the full declaration spans in the pin (`line → next declaration`), not just the
statement line:

| pin `Def_` module | missing | lines | the missing names, in one line | story |
|---|---:|---:|---|---|
| `ModularCurve_QExpReductionModL` | 26/29 | 295 | `laurentReduction`, `laurentReductionPic0`, `reductionQExpModL`, `IsPlaceReductionQExpModL`, `eq_of_agree`, … | M1 |
| `ModularCurve_X1HeckeModule` | 36/42 | 203 | `heckeGenOne`, `heckeModuleOneBar`, `tateHeckeRepOne`, `rationalHeckeAlgebraOne`, `RationalRankTwoNebentypus`, … | M5 |
| `CohCarrier_Fricke` | 28/28 | 164 | `frickeMat`, `frickeHom`, `frickeEquiv`, `frickeH1`, `frickeH1L`, … | M9 |
| `CuspForm_HeckeOperatorFormsGammaH` | 14/25 | 158 | `diamondLinH`, `heckeULinH`, `heckeTLinH` and their `coe_*` laws | M6 |
| `ModularCurve_PeriodHomPair` | 23/24 | 140 | `jConjMat`, `jConjSL`, `jConjGamma0`, `charInvolution`, `periodHomPair` | leaves |
| `AlgebraicCurve_Pic0Congr` | 15/15 | 106 | `congr`, `degZeroCongr`, `map_principal_degZeroCongr`, … | leaves |
| `ModularCurve_ComplexPlaceDictionaryOf` | 11/11 | 102 | `realizeOf`, `ComplexPlaceDictionaryOf`, `ofGamma0`, `toGamma0`, … | leaves |
| `CohCarrier_Inst` | 7/8 | 80 | `heckeTL`, `diamondL`, `opFamily`, `MLAt` | M9 |
| `ModularCurve_XHOperators` | 9/16 | 56 | `diamondHBar`, `genOpH`, `genOpH_T/U/dia`, `tateGenOpH` | M5, M9 |
| `ModularCurve_X0ModL` | 5/20 | 43 | `coeffMap_jqModC`, `coeffMap_jqNModC`, `jqModC_pow`, `full_degeneracyC_map_le` | leaves |
| `ModularCurve_XH` | 7/25 | 35 | `torsionGaloisRep`, `tateGaloisRep`, `tateEnd` | M9 |
| `ModularCurve_ResidualRealization` | 2/2 | 34 | `IsResidualRealization`, `CyclotomicDeterminant` | M7 |
| `CuspForm_Gamma1HeckeOperators` | 4/70 | 32 | `mdifferentiable_heckeU`, `mapGL_apply`, `isUnit_wt`, `det_mod` | M1 |
| `ModularCurve_SiegelFunction` | 2/2 | 23 | **`siegelFun`**, `siegelFun_def` | M4 |
| `ModularCurve_PeriodOf` | 5/24 | 21 | `peterssonOf`, `peterssonIntegrandOf`, `*_gamma0` | M6 |
| `ModularCurve_X1` | 3/35 | 17 | `torsionGaloisRep` and its two `coe_*` laws | M3, M8 |

Also, two **private** helpers the port lacks, which the manager writes locally with the rows:
`int_eq_zero_of_forall_dvd'` (4 lines, `QExpReductionModL`) and `span_stable` (13 lines,
`PeriodOf`). Total missing definition lines: **1,509**, of which the ready block's modules carry
**1,118** and the leaves' the remaining **391**.

**What this means for the cut.** The shelf cannot be cut on the instrument's figure, and not even
on the rows' own `port_plan` figure: the gates are structural. A **definition wave is the first
work of the programme** for every story with a gate, exactly as the recipe's §4 gives the manager
the definition layer. The gates are cheap in lines (1,118 for the whole ready block) but they
must land first, at the pin's names, with their own wires. The audit also settles the false
question "is the row ready?" — a row whose statement names `siegelFun` is not ready until
`siegelFun` exists, whatever `needed = 1` says.

**Two in-flight orders to close.** `WORKORDER-JQ2` (`jqNModC_mem_modularFunctionFieldC_mul_prime`)
and `WORKORDER-CL4` (`package_of_socket`, its two tails, `map_intCast_pow_char_eq_qExpand`, …) are
marked *open* in their files, but their declarations are in the tree
(`ModularCurve/FunctionFieldGeneration/{MffCMulPrime,PrimePowerStepAnyField}.lean`,
`ModularCurve/Defs/QExpandCharP.lean`). They are not on this shelf; the bookkeeping should close
their records before the next wave re-reads the shelf.

## 0.3 The pricing

**The whole-set read.** `port_advise --with-defs` over the 25 rows (74 target files, 1,390
declarations) and `port_plan`:

| budget line | value |
|---|---:|
| raw `S_` lines | 8,668 |
| declaration lines | 8,144 |
| duplicate copies (port once) | 410 |
| boilerplate | 524 |
| already in the port (vetted) | 442 |
| **net new math lines** | **7,292** |
| substitutions | 518 trusted / 46 suspect |

The **46 suspect** rows are the parser's type-only `def` matches and need a hand read before they
are trusted. The report's top suspects are `RationalRankTwoNebentypusOf` (16 lines) and
`HeckeDiamondInputsAll` (15) against `PeriodPair.DiscriminantNeZero`, then `LaurentReductionInputs`
(12), `HeckeInputsOneAlong` (9), `HeckeDiamondInputsHAll` (8), `HeckeBetaOneBarIntegral` /
`ModularPolynomialFamily` / `twistFun` (7 each — the last is the genuine one, ported as
`ModularCurve.qTwistFun`), `JOne` (6) and `ReductionInputsQExpModL` (6). Treat those as "check
the statement" rows, not as free imports. The strongest genuine in-port blocks are
`Gamma1HeckeOperators` (283 once / 261 inport), the Siegel `jtp_term`/`theta_eq` engine (143,
**0** in port), the constant-reduction `gaussRing`/`laurentBaseChange_le` block (142 / 110
inport), `ConstantReduction`'s `ord_algebraMap`/`ord_smul` (83 / 83), the `coeffMap_diffQExp`
block (63 / 63), and `StarBank.delta_pow_ne`'s 66.

**What the 7,292 does and does not include.** The whole-set read prices the **25 rows' own
proofs**; `--with-defs` added the 26 wrapper-level `Def_` files to the *substitution* analysis,
not to the budget, so the definition gates are **not** inside the 7,292. The ready block's gate
is **1,118 lines** (the 874 wrapper-level plus the 244 of the two proof-level `CohCarrier`
modules, `Inst` 80 + `Fricke` 164; `CohCarrier_Level`, `LaurentCoeff`, `PrimCosetReps`,
`QExpansionDiff`, `PeriodPair_Uniformization`, `EisensteinG` are fully ported), plus the two
private helpers (17). The ready programme is therefore ≈**8,430 net** (7,292 + 1,118 + 17).

**Per-story prices** (the rows' own runs; the small excess over the 7,292 aggregate is cross-story
dedup). `gate` is the story's missing-definition lines; `total` = rows + gate:

| story | rows | silo | rows-net | gate | total |
|---|---:|---:|---:|---:|---:|
| M1 constant reduction / correspondence | 953, 934, 868 | 2,755 | 2,243 | 327 | **2,570** |
| M2 modular polynomial, one level up | 510, 134, 62 | 706 | 630 | 0 | **630** |
| M3 Tate slots, twists and the tate `j` | 185, 144, 637, 254 | 1,220 | 1,114 | 17 | **1,131** |
| M4 Siegel unit and Eisenstein | 390, 224, 220 | 834 | 634 | 23 | **657** |
| M5 Galois action on Hecke operators | 272, 265, 27, 27 | 591 | 474 | 259 | **733** |
| M6 period lattice and parabolic homs | 464, 350 | 814 | 758 | 179 | **937** |
| M7 residual realization / semisimple descent | 403 | 403 | 364 | 34 | **398** |
| M8 X₁ function field: separability, canonical divisor | 363, 22 | 385 | 338 | 0 (X1's 17 in M3) | **338** |
| M9 X_H/X₁ Fricke and the q-expand norm | 384, 322 | 706 | 536 | 279 (80+164+35; `XHOperators` is in M5) | **815** |
| M10 StarBank Δ and char-`p` | 254 | 254 | 224 | 0 | **224** |
| **ready block** | **25** | **8,668** | **7,315** | **1,118** | **≈8,433** |

**The leaves block**: 34 rows / 7,331 silo, a `port_advise` aggregate of **5,479 net** (42 trusted
/ 2 suspect substitutions; 377 in-port lines from the ported `LaurentCoeff`/`PrimCosetReps`/
`QExpansionDiff`/`PhiGen`/`JqCoeff` API), plus **391** lines of definition gate
(`PeriodHomPair` 140, `Pic0Congr` 106, `ComplexPlaceDictionaryOf` 102, `X0ModL` 43) ≈ **5,870 net**.
It is a second programme, not a first wave.

## 0.4 The stories

**The ready block (25 rows) in ten stories.** Subjects are the pin `S_` files' own: each story is
one mathematical subject with 1–4 rows.

| story | what it is | rows |
|---|---|---|
| **M1** | the Hecke correspondence on X₁/X_H and its constant reduction mod ℓ: the `diamondAutBar`/`diamondLinOne` and `heckeBetaOneBar`/`heckeAlphaOneBar` q-expansion identities | 953, 934, 868 |
| **M2** | the modular polynomial one level up: the fibre product over the Vélu quotients, multiplicativity of `Φ` under `ℓ · M`, and the degree bound on its coefficients | 510, 134, 62 |
| **M3** | the Tate slots and the tate `j`: `qTwist` on non-toric points, `(tateLaurent K).j = jqModC K`, the Γ₁ integral q-expansion/toric-point theorem, and the E₄³/Δ orbit statement | 185, 144, 637, 254 |
| **M4** | the Siegel unit: `siegelFun` under `SL(2, ℤ)`, its differentiability, and the weight-3 Eisenstein integral q-expansion | 390, 224, 220 |
| **M5** | the Galois action on the Hecke operators: the `JOne`/`JH` module structure, the `genOpH` commutativity, and the two diamond commutations | 272, 265, 27, 27 |
| **M6** | the period lattice's Hecke-diamond stability and the parabolic-homs/period-lattice linear equivalence | 464, 350 |
| **M7** | the residual realization and semisimple descent of a 2-dimensional mod-`p` representation | 403 |
| **M8** | the X₁ function field: separability of `qExpFunctionFieldC` over `K⟮jq⟯`, and the canonical divisor | 363, 22 |
| **M9** | Fricke and the q-expansion norm: `qExpand_norm_heckeBetaHBar` and the slash-Fricke sum | 384, 322 |
| **M10** | StarBank's Δ and char-`p`: `Δ^p` is not a constant times `q^p` in characteristic `p` | 254 |

**The leaves block (34 rows) in eight stories.** They are *not* ready and *not* cut here; named
and deferred, per the recipe (FR-0040).

| leaf story | rows | silo | what it is |
|---|---:|---:|---|
| **L-siegel** | 4 (504, 323, 176, 155) | 1,158 | the level-Bernoulli weight span and the addition law of the Siegel unit |
| **L-starbank** | 7 (471, 304, 220, 210, 192, 161, 156) | 1,714 | the StarBank: `deltaNorm`, the closure/one-point/count algebra, `starK`, and the Eisenstein integrality (`eisInt_*`) |
| **L-tate** | 3 (267, 267, 41) | 575 | the Tate formal series `c₄`/`c₆` and `c4_tateLaurent` |
| **L-coset** | 4 (152, 149, 149, 72) | 522 | the primitive-coset two-variable polynomial: roots, uniqueness, separability, the `cosetSubst` coefficient sum |
| **L-x1coeff** | 7 (468, 314, 211, 120, 98, 92, 45) | 1,348 | the X₁ coefficient dictionary: `existsUnique` of the field iso, the finrank bound, `laurentBaseChange`, integrality and linear independence of `coeffMap` |
| **L-eta** | 2 (244, 237) | 481 | the eta-product coefficient sums and `coeff_jNum ≤ 6` |
| **L-other** | 7 (536, 468, 167, 159, 57, 48, 98) | 1,533 | `pic0Congr_jOne_jH_bot_compat`, `diamondOneBar_comm`, `eq_qExpansionDiffAlong`, `tendsto_atImInfty`, `realizeOf_eq_div`, `eq_zero_of_natDegree…`, `periodAlongOf_eq_neg_conj…` |
| **total** | **34** | **7,331** | |

The leaves' silos are the pin `S_` lines; the aggregate net is 5,479 (their own `port_advise`
run, without definitions). They are deferred story-by-story: a leaf is a graph leaf (no theorem
premises), so it can be cut in any order once its `Def_` vocabulary exists, and several are the
natural companions of ready stories (`L-tate` beside M3, `L-siegel` beside M4, `L-starbank` beside
M10, `L-x1coeff` beside M8, `L-other`'s period rows beside M6).

## 1. The programme

Seven orders for the ready block, ≈8,430 net lines (the per-story split sums to 8,433); the
definition work is the manager's and precedes the gated orders. Sizes are the recipe's 1,300–1,600 silo except where a subject is
smaller and the gate argues for bundling.

| order | stories | rows | silo | net (rows + gate) | gate before it |
|---|---|---:|---:|---:|---|
| **MC-1** | M2 (modular polynomial) | 3 | 706 | 630 | none |
| **MC-2** | M3 (Tate/twist) | 4 | 1,220 | 1,131 | the X1 17-line check (`torsionGaloisRep` may not be used) |
| **MC-3** | M8 + M10 (X₁ field; StarBank Δ) | 3 | 639 | 562 | none (StarBank gains a 1-line import) |
| **MC-4** | M6 + M5 (period; Hecke Galois) | 6 | 1,405 | 1,670 | PeriodOf 21, HeckeOpForms 158, X1HeckeModule 203, XHOperators 56 |
| **MC-5** | M4 + M7 (Siegel; residual) | 4 | 1,237 | 1,055 | SiegelFunction 23 (+ its 143-line jtp engine), ResidualRealization 34 |
| **MC-6** | M9 (Fricke) | 2 | 706 | 815 | XH 35, CohCarrier Inst 80, Fricke 164 (XHOperators is MC-4's) |
| **MC-7** | M1 (constant reduction / correspondence) | 3 | 2,755 | 2,570 | QExpReductionModL 295, Gamma1HeckeOperators 32 |
| | **ready block** | **25** | **8,668** | **≈8,430** | **≈1,118** |

**The first wave is MC-1, MC-2, MC-3** (2,565 silo / ≈2,323 net): the three stories with no gate
(or a 17-line check), one new module for M3 and none elsewhere, and the smallest blast radius.
Dispatch them as worker orders, one per order, per the column's workflow; the manager holds the
definition wave for MC-4–MC-7 and the consumer/gate reviews between.

**Why this order.** MC-1 is the clean first order: the whole definition layer is ported, the
three homes are existing wired modules, the shared prelude is 9 lines. MC-2 is the largest
*ungated* subject and its homes are one new module; MC-3 is two small subjects that share the X₁
definition and a one-line import. The gated orders come after, cheapest gate first (M4+M7 at
57 lines of gate, M6+M5 at 438, M9 at 279, M1 at 327 but the biggest rows) — with MC-7 last
because it is the largest and its gate is the largest single module.

**Deviations from the size rule.** MC-2 and MC-3 are below 1,300 silo because the subject
boundaries and the gates, not the size, set them; MC-7 is above 2,400 because M1 is one subject
(three rows over one correspondence engine) and splitting it would pay the `QExpReductionModL`
gate twice — the recipe's "one story per order" is kept, at a size the reviewer may split into
953 and 934+868 if preferred.

**The leaves programme** (34 rows / 7,331 / ≈5,870) is a *second* programme of ≈4 orders; it
starts only after the ready block's definition wave, because its largest gates
(`PeriodHomPair`, `Pic0Congr`, `ComplexPlaceDictionaryOf`) are its own. It is named and deferred
here, not cut.

## 2. The rows

`silo` is the pin `S_` line count; `prem` the pin's `import Theorems.Thm_*` count; `lev` the
corrected read's cone / project consumers; `gate` the row's share of the story's definition
lines (§0.2); the story's `net` is in §0.3.

| story | node (`ModularCurve.` dropped) | silo | prem | lev | gate |
|---|---|---:|---:|---:|---:|
| M1 | `exists_constantReduction_pic0Map_eq_reductionQExpModL` | 953 | 3 | 1 / 4 | 295 |
| M1 | `coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne` | 934 | 3 | 1 / 2 | 32 |
| M1 | `coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd` | 868 | 2 | 1 / 2 | — |
| M2 | `ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed` | 510 | 2 | 1 / 1 | — |
| M2 | `ModularPolynomialData.dvd_resultant_of_mul` | 134 | 3 | 1 / 1 | — |
| M2 | `ModularPolynomialData.natDegree_coeff_le` | 62 | 2 | 1 / 10 | — |
| M3 | `exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum` | 637 | 2 | 2 / 2 | 17 |
| M3 | `exists_smul_eq_of_E4_cube_div_discriminant_eq` | 254 | 1 | 1 / 2 | — |
| M3 | `qTwist_nonToricPoint_of_pow_eq_one` | 185 | 2 | 1 / 1 | — |
| M3 | `j_tateLaurent` | 144 | 1 | 3 / 11 | — |
| M4 | `siegelFun_specialLinearGroup_smul` | 390 | 1 | 1 / 1 | 23 |
| M4 | `SiegelUnit.differentiableOn_siegelFun` | 224 | 1 | 1 / 1 | — |
| M4 | `SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion` | 220 | 3 | 1 / 1 | — |
| M5 | `JOne.galois_smul_heckeAlgOne_smul` | 272 | 1 | 1 / 4 | 203 |
| M5 | `galois_smul_genOpH_comm` | 265 | 1 | 2 / 21 | 56 |
| M5 | `heckeOperatorOneBar_comm_diamondOneBar` | 27 | 2 | 1 / 1 | — |
| M5 | `heckeOperatorHAlong_diamondHBar_comm` | 27 | 2 | 1 / 6 | — |
| M6 | `periodLatticeOf_gammaH_heckeDiamondStable` | 464 | 5 | 1 / 2 | 179 |
| M6 | `exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup` | 350 | 6 | 1 / 2 | — |
| M7 | `exists_semisimple_descent_of_trace_det_mem_range_finite` | 403 | 3 | 1 / 3 | 34 |
| M8 | `isSeparable_adjoin_qExpFunctionFieldC_gamma1` | 363 | 2 | 2 / 4 | — |
| M8 | `hasCanonicalDivisor_x1FunctionFieldBar` | 22 | 3 | 1 / 1 | — |
| M9 | `exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion` | 322 | 3 | 2 / 5 | 279 |
| M9 | `qExpand_norm_heckeBetaHBar` | 384 | 2 | 1 / 1 | — |
| M10 | `StarBank.delta_pow_ne` | 254 | 1 | 1 / 1 | — |
| | **ready block** | **8,668** | | | **1,118** |

(The rows' own `net` is measured at the **story** level in §0.3 — the whole-set read gives
7,292 and the per-story sum 7,315; the per-row split is not separately measured and is not
quoted here. `gate` is the row's share of the story's definition lines, §0.2.)

Demand is inverted relative to size again: the 22-line canonical-divisor row has 1 consumer, the
144-line `j_tateLaurent` 11 project consumers, the 265-line Galois row 21, and the 350-line
period row 2.

## 3. Homes

Method as in the recipe §4: pin `S_` premises → statement-identical port module → the modules
above all of them in the port's import closure, then confirm against the proof's subject. The
2026-10-27 check (a short `rglob` over the tree's `import FLTForHuman.…` lines):

| story | above-all check | home | note |
|---|---|---|---|
| M1 (953) | only `ModularCurve/XH/JHDescent.lean` above its premises — wrong subject | **new** `ModularCurve/QExpReduction.lean` (+ the `laurentReduction` engine) | the def module's subject *is* the reduction; the new module carries both the missing defs and the row |
| M1 (934) | **no** module above `QCoeffLevelOne` + `FunctionFieldBaseChange` + `IsCurveOver/Transcendental` | **new** `ModularCurve/QExpReductionCorrespondence.lean` | the q-expansion correspondence on the X₁/X_H quotient |
| M1 (868) | **no** module above `X1/HeckeDegree` + `X1/AtkinLehnerExchange` | **new** `ModularCurve/X1/HeckeCorrespondence.lean` | same subject, X₁ side |
| M2 (510) | `ModularPolynomialVelu.lean` is the only module above its premise | **insert** `ModularPolynomialVelu.lean` | its own module, 5 ok today |
| M2 (134, 62) | `ModularPolynomialUniquenessIrreducible.lean` is above all three | **insert** `ModularPolynomialUniquenessIrreducible.lean` | the uniqueness/irreducibility subject, already hosts `eq_all`/`phiIrreducible_all` |
| M3 (185) | `TateSlots/CoefficientFormulas.lean` is above both | **insert** (legacy migration) | in `PORT_FILES`; the touch must migrate it (wire, delete row, silent build, dedup) |
| M3 (144) | `ModularCurve/Degree/FinrankAdjoinJqNModC.lean` above `X1/IntegralityJqNModC.lean` | **insert** `Degree/FinrankAdjoinJqNModC.lean` or a new `X1/TateLaurentJ.lean` | the statement is one line over the defs; the premise module is `X1/IntegralityJqNModC` |
| M3 (637, 254) | `Elliptic/PeriodPair/InvariantsTorsion.lean` has **no** module above it | **new** `ModularCurve/TateSlots/Invariants.lean` | the two rows share the premise; the new module is above it and imports it |
| M4 (390, 224) | `ModularForms/JacobiThetaTripleProduct.lean` has no module above it | **new** `ModularCurve/SiegelUnit/Basic.lean` (+ `SiegelFunction` defs) | the Siegel unit's home; the 143-line jtp engine lands with it |
| M4 (220) | no module above `EisensteinSeries` + `Eisenstein/ConstTermCubeIntegral` | **insert** the same new module | it imports both |
| M5 (272) | many modules above the one premise; the X1 def is the gate | **insert** `ModularCurve/X1/HeckeModule.lean` (the port's 6/42 module) | the def home; the row goes there |
| M5 (265, 27) | above `XH/DiamondLift.lean` etc. | **insert** `ModularCurve/XH/Operators.lean` | the def home (7/16 today) |
| M5 (27, X1) | `X1/DiamondLift.lean` | **insert** `ModularCurve/X1/DiamondLift.lean` | the diamond commutation |
| M6 (464, 350) | `Period/HeckeStability.lean` is the only module above both | **insert** `Period/HeckeStability.lean` | the period/Hecke subject |
| M6 (350)'s six premises | `Period/PeriodLatticeBasis.lean` is above all of them | **insert** `Period/PeriodLatticeBasis.lean` | the 350 row's six premises are the two basis modules, `ParabolicHoms`, `EichlerShimura/ExistsEquivariantPrimitive` and `WeightOne/Basic`; the basis module is above the other five |
| M7 (403) | **no** module above `RepresentationTheory/*` + `GaloisRep/Deformation/FiniteDescent` | **new** `ModularCurve/ResidualRealization.lean` | the def + the row |
| M8 (363) | `X1/FunctionFieldIsAlgClosed.lean` is above both premises | **insert** `X1/FunctionFieldIsAlgClosed.lean` | the separability of the field |
| M8 (22) | `X1/Structure.lean` is above both (and is in `PORT_FILES`) | **insert** (legacy migration) | the canonical divisor of the curve; migrate in the same touch |
| M9 (384) | **no** module above `X1/AtkinLehnerExchange` + `XH/HeckeDegree` | **new** `ModularCurve/XH/QExpandNorm.lean` | the `qExpand` norm of the β-operator |
| M9 (322) | **no** module above `FrickeReciprocity` + `PowerSeries/GaloisDescent` + `Gamma0Integral` | **new** `ModularCurve/XH/FrickeSlash.lean` (+ the `CohCarrier` Inst/Fricke defs) | the Fricke slash sum |
| M10 (254) | `ModularPolynomialStarBank` is above nothing of `QExpandCharP` | **insert** `ModularPolynomialStarBank.lean` + `import Defs/QExpandCharP` (1 line) | acyclic (the CharP def does not reach StarBank) |

The legacy migrations are part of the order price, not an argument against the home (recipe
§4): `TateSlots/CoefficientFormulas.lean` and `X1/Structure.lean` are in `PORT_FILES`; the touch
that adds a declaration to either migrates it (its own `spec-pin:` wire, deletion of the
`PORT_FILES` row — its `SOURCES` rows stay —, silent build, `dedup.py`/`move_dead.py`).

**No row of the set cites another row of the set.** The stories are independent; the shared
pieces are the definition modules (the manager's) and the ported API. The only cross-story
sharing is the X₁ def module (M3, M8) and `XHOperators` (M5, M9) — both in the gate table.

## 4. Per-order traps

**MC-1 (M2).** (i) 510 is a wrapper over the ported `fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental`
(`ModularPolynomialVelu.lean`) at the `_of_isAlgClosed` binder shape: the pin adds
`[IsAlgClosed K]`/`HahnSeries.isAlgClosed_rat`; do not re-prove the product form. (ii) 134's
`dvd_resultant_of_mul` reads `phiIrreducible_all` (`ModularPolynomialUniquenessIrreducible`) and
`transcendental_jq` (`Defs/Jq`); the home is above both. (iii) 62's `natDegree_coeff_le` is a
two-premise wrapper over `evalSymm_of_prime`/`swapBivar_eq_of_evalSymm`; its 62 pin lines are
short, so read the `S_` proof for the one substantive step before accepting the story's 630 as
its price. (iv) `ModularPolynomialUniquenessIrreducible` was handed to the new wire (5 ok / 0 / 0);
keep its wire intact.

**MC-2 (M3).** (i) 637's statement is a five-object existential (B, D, b, d and the Fourier
identities); its `S_` file is 637 lines with 90 declarations, of which the port already has the
`X1`/`TateSlots` API. (ii) 254 is the `E₄³/Δ` orbit statement; its
proof is `PeriodPair.lattice_eq_of_g2_eq_of_g3_eq` (ported) plus the classical `SL(2,ℤ)` action —
watch the `ℍ`/`UpperHalfPlane` coercions. (iii) 144 is one line over `tateLaurent`/`jqModC`; its
premise `eisenstein4_cube_sub_mk_sq` is in the **deferred** `X1/IntegralityJqNModC.lean` region
(MD-001's module!) — the row does not use the deferred 36 node, but it lives in the module whose
wire is scheduled to be cleaned; do not clean it in this order. (iv) 185's `qTwist` is the
ported `qTwistFun`; the 46-suspect list's `twistFun` row is this. (v) The new
`TateSlots/Invariants.lean` imports `Elliptic/PeriodPair/InvariantsTorsion.lean`, a top-level
`Elliptic` module; keep the `ModularCurve` namespace of the two rows, do not rename the premise.

**MC-3 (M8 + M10).** (i) 363's `hx : (x : LaurentSeries K) = jqModC K` is the statement's
hypothesis; the proof is the `FunctionFieldIsAlgClosed` API + `order_jqModC` (ported). (ii) 22's
`HasCanonicalDivisor` is an `AlgebraicCurve` class; the home `X1/Structure.lean` is **legacy** —
the order must migrate it in the same touch. (iii) M10's `delta_pow_ne` is the char-`p`
`Δ^p ≠ C γ q^p`; the `map_intCast_pow_char_eq_qExpand` premise is the CL4 node (already in the
tree, `Defs/QExpandCharP.lean`); the home gains a 1-line import of that module. (iv) 254's `S_` file sets no
`set_option`; no heartbeat risk in this order.

**MC-4 (M6 + M5).** (i) M5's four rows sit on two definition modules (203 + 56 lines) and one
shared `SemilinearAut.pic0_correspondence_smul` (SET 7's 23-line AC row) — the gate must land
first, or the rows are not even statable. (ii) 272's `heckeModuleOneBar` is a `Module` instance;
the pin's `letI := heckeModuleOneBar M σ` in the statement means the transcription is
instance-sensitive; follow the `heckeModuleOneBar_smul_def` route. (iii) M6's 464's premises
`CuspForm.stableT/U/D` are in `Period/HeckeStability.lean`; the home is that module. (iv) 350's
six premises are all `Period/…` modules; the `periodMapOf`/`periodOf` dictionary is ported
(`ModularForms/EichlerShimura/ExistsEquivariantPrimitive.lean`); the row is the
`LinearEquiv`/basis form. (v) `PeriodOf`'s 21-line gate (`peterssonOf`) is a def + two `_gamma0`
lemmas; the manager's.

**MC-5 (M4 + M7).** (i) `siegelFun` is absent: the 2-declaration `Def_ModularCurve_SiegelFunction`
is the whole definition layer, but its *engine* (`jtp_term`, `theta_eq`, the q-product) is a
143-line shared prelude the port lacks (0 in port); the def wave must write it with the row.
(ii) 390 is the `SL(2, ℤ)`-slash invariance of `siegelFun`, 224 is its
`DifferentiableOn` ∧ `MDifferentiable` pair — different assertions over the same function,
cut as one because they share the `siegelFun` definition and the 143-line jtp engine. (iii) 220's
Eisenstein integrality is independent (`EisensteinSeries` is ported) and might be cut with the
M4 story for its subject, or alone. (iv) M7's `IsResidualRealization`/`CyclotomicDeterminant`
(34 lines) are defs, then the 403 row is the `Representation` descent; the home is a new
`ModularCurve/ResidualRealization.lean` above the three `RepresentationTheory`/`GaloisRep`
premises. (v) `siegelFun` is built from the Jacobi triple product (`ModularForms/JacobiThetaTripleProduct`,
ported); the convergence API (`qParam`/`tprod`) is the part to read first.

**MC-6 (M9).** (i) The gate is the largest of the ready block's: `CohCarrier_Inst` 80 +
`CohCarrier_Fricke` 164 + `XH` 35 + `XHOperators` 56 (shared with M5). The `CohCarrier` modules
live in `ModularForms/CohCarrier/` (ported `Level`, absent `Inst`/`Fricke`), so the manager's
home is `ModularForms/CohCarrier/{Inst,Fricke}.lean` (the pin's `Def_` names) — not a
`ModularCurve` module. (ii) 322's statement is the slash-Fricke sum over `ℚ`-rational
q-expansions; its three premises are ported; the missing piece is the Fricke `H¹`/`frickeH1L`
layer. (iii) 384's `qExpand_norm_heckeBetaHBar` is the norm of the β-operator's q-expansion; the
`AtkinLehnerExchange`/`HeckeDegree` premises are ported.

**MC-7 (M1).** (i) The gate is `QExpReductionModL`'s 26 declarations / 295 lines: the whole
`laurentReduction`/`laurentReductionPic0`/`reductionQExpModL` engine, plus one private
`int_eq_zero_of_forall_dvd'`. The port already has its `gaussRing`/`laurentBaseChange_le`/`cross`
block (110 of 142 lines), so the engine is a *rearrangement* plus the missing 295, not a
from-scratch theory. (ii) 953's statement is the `pic0Map`/`reductionQExpModL` identity; 934 and
868 are the q-expansion correspondences of the two Hecke faces. (iii) `CuspForm_Gamma1HeckeOperators`'
4 missing declarations are `mdifferentiable_heckeU`, `mapGL_apply`, `isUnit_wt`, `det_mod`; the
port's `ModularForms/Defs/Gamma1HeckeOperators.lean` has the other 66. (iv) The
`ConstantReduction` def (14/14) is ported; the `ModularCurve_QExpReductionModL` def is not — the
row's statement uses `reductionQExpModL`, so the def must land first. (v) 868's home is new; its
`heckeBetaOneBar`/`heckeAlphaOneBar` defs are ported (`X1HeckeOperator` 23/23).

## 5. The gates

As in the recipe §6, per order:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, every added
   declaration `ok` (or a manager-written `own:`/`pin:` row). The def wave's modules each carry
   their own wire (the pin `Def_` file and the wrapper/S_ files of the rows they serve).
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The order's own modules only, under `flock`/`timeout`: no tree build, no dependents, the module
   silent at the 200k cap. (`SiegelUnit`/`SiegelFunction` and `QExpReduction` are the two to
   watch; the pin's `S_` files' heartbeat settings are defensive.)
4. `dedup.py` / `move_dead.py` on each module; wrapper-over-engine `shape` clusters stay with the
   reason recorded (the `ModularPolynomialUniqueness` 2-copy cluster is the known one).
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats`; no
   worker writes a `spec/decl_markers.tsv` row.
6. Each module's `spec-pin:` block gains the wrapper and the `S_` copies; a legacy home migrates
   in the same touch (wire, delete the `PORT_FILES` row, silent build, dedup/move_dead); no false
   wire is added (MD-001's two `spec-pin:` lines, 64 and 68 of `X1/IntegralityJqNModC.lean`, are
   the MC column's own next edit — close them, do not copy them).
7. A `spec/` consumer zone per wave with a real cross-module composition (no `#check`s), whose
   error count is the deliverable metric: for the first wave, the M2 rows composed with the
   ported `ModularPolynomialVelu` API and the M8 canonical divisor with `HasCanonicalDivisor`'s
   `AlgebraicCurve` API; the M3 rows' `tateLaurent`/`qTwist` identities composed with the Tate
   slots API.

## 6. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. the cut | **the corrected 25-row shelf, cut as seven orders**, not the instrument's 26 | the 80/36/261 chain is not ported; the shelf is 25 / 8,668 |
| 2. the first wave | **MC-1 (M2), MC-2 (M3), MC-3 (M8+M10)**, 2,565 silo / ≈2,323 net, as three worker orders | the gate-free/short-gate stories establish the family's first landed slice and the consumer zone |
| 3. the definition wave | **the manager's, before MC-4 to MC-7**, 1,118 lines over 12 modules, at the pin's names and homes; the two private helpers included | the gated stories cannot be stated without it; the def modules' missing declarations are itemised in §0.2 |
| 4. the new modules | **M1 needs three** (`QExpReduction`, `QExpReductionCorrespondence`, `X1/HeckeCorrespondence`), **M3 one** (`TateSlots/Invariants`), **M4 one** (`SiegelUnit/Basic`), **M7 one** (`ResidualRealization`), **M9 two** (`XH/QExpandNorm`, `XH/FrickeSlash`) | eight new modules, each cascade-free; the existing homes take M2/M6/M8/M10 |
| 5. the legacy homes | `TateSlots/CoefficientFormulas.lean` and `X1/Structure.lean` **migrate in the same touch** as their rows (M3-185, M8-22) | two migrations, not avoided on cost grounds (recipe §4) |
| 6. the leaves block | **defer as eight named stories (34 rows / 7,331 / ≈5,870)**; cut after the ready block's definition wave, story by story, the `L-tate`/`L-siegel`/`L-x1coeff`/`L-other` ones beside their ready siblings | the leaves are 7,331 silo — 84 % of the ready block's 8,748 — and cannot be dropped from the brief (FR-0040) |
| 7. the withheld pair | **defer** to `abelJacobiCard_genus`'s programme (144 nodes / 66k) + the `TateModule` definition layer (69 decls); the T1/T2 plan of `TOPIC-padic-tate-module.md` | not a row of this shelf |
| 8. the in-flight records | **close WORKORDER-JQ2/CL4's status lines** — their declarations are in the tree | bookkeeping only; no Lean |

**The waves after MC-4, scoped at declaration level (2026-10-27).** MC-5 and MC-6 are opened as
their turns come (one wave at a time); this is the scoping that fixes their rows, gates and homes
now, so that the def wave's decisions are carried forward and no re-pricing is needed when the turn
arrives. Every premise named below was checked by name on this tree; every definition they name is
in the port (the def wave's D3/D5/D6/D7).

| wave | rows | defs in place | premises (all ported) | homes | orders | net |
|---|---|---|---:|---|---:|---:|
| **MC-5** (M4) | 390, 224 | D6 `siegelFun` | `jacobiTheta_two_eq_tprod` (`JacobiThetaTripleProduct`) | **new** `ModularCurve/SiegelUnit/Basic.lean` — the two `siegelFun` rows plus the ≈143-line jtp engine (`jtp_term`, `theta_eq`), 0 in port | 1 | ≈634 (story, de-duplicated; per row 358 + 190) |
| **MC-5** (M4) | 220 | — | `EisensteinSeries`' three (`EisensteinSeries`, `Eisenstein/ConstTermCubeIntegral`) | insert `EisensteinSeries`-adjacent home (`ModularForms/EisensteinSeries.lean` or a new `ModularCurve/SiegelUnit/Eisenstein.lean`) | 1 | 188 |
| **MC-5** (M7) | 403 | D7 `IsResidualRealization`, `CyclotomicDeterminant` | `RepresentationTheory/SubfieldBasis`, `Burnside`, `GaloisRep/Deformation/FiniteDescent` | **new** `ModularCurve/ResidualRealization.lean` | 1 | 363 |
| **MC-6** (M9) | 322 | D5 `frickeMat`…`frickeH1L` | `FrickeReciprocity`, `PowerSeries/GaloisDescent`, `WeightOne/Gamma0Integral` | **new** `XH/FrickeSlash.lean` (+ the pin `S_` file's `frickeGL`/`frickeForm`, 0 in port) | 1 | 261 |
| **MC-6** (M9) | 384 | D3 `diamondHBar`/`genOpH`, D5 | `X1/AtkinLehnerExchange`, `XH/HeckeDegree` | **new** `XH/QExpandNorm.lean` | 1 | 216 (108 lines now read in port — D3/D5's gift) |

Its row list is the four MC rows of the block (403, 390, 224, 220) — **not**
`rep_tateModule_jOne_comm`, which entered the shelf with MC-4 and is a false ready (its statement
names `TateModule`; see §7). So MC-5 is three orders (≈1,185 net with the jtp engine counted once) and MC-6 two (477), and
neither has a manager lane left: no promotion, no migration (all four homes are new modules, and none
is on `PORT_FILES`), and the definition gate is landed. The one thing MC-5 owns that the def wave
did **not** land is the Jacobi-triple-product engine (`jtp_term`, `theta_eq`, the q-product
convergence) — the shelf's §0.3 calls it the rows' shared prelude (143 lines, 0 in port); it is the
first thing MC-5a writes, `private` to the new module. The deferred definitions come back with the
**leaves** programme, not with these two waves: `PeriodOf`'s petersson block with the `L-other`
period rows, `CohCarrier.HeckeData` with the leaves' `pair_*` rows, `ModularCurve_XH`'s torsion trio
with the M9 successors.

**Call 3 is discharged (2026-10-27)** — but not at this table's price, and the difference is
recorded: the definition wave for MC-4/5/6 landed as **7 modules / 539 pin declaration lines (84 declarations) /
121 checked declarations**, not the 774-line remainder of the 1,118 (MC-7's 338 landed first).
The audit behind the change is declaration-level rather than module-level: see
[WORKORDER-MCDEF-definition-wave.md](WORKORDER-MCDEF-definition-wave.md) §0.1, whose
`spec/gate_scan.py` is the instrument. Two of the twelve modules in this table's §0.2 are not any
ready row's (`PeriodOf`'s petersson block, `ModularCurve_XH`'s torsion/Tate block) and are
deferred there with their reasons; three ready rows (`350`, `220`, `384`) never had a gate.

## 7. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mcshelf.json
python3 frontier.py --selfcheck
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1 \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast \
  --unport AlgebraicCurve.weilReciprocity > build/mcshelf-corrected.json
python3 port_advise.py --with-defs <the 25 --nodes flags> --json build/mc-defs.json
python3 port_plan.py --json build/mc-defs.json
# per-story: port_advise.py <story --nodes> --json build/mc-<story>.json; port_plan.py --json …
python3 twin_scan.py --node <each row>
python3 spec/check_port.py --force <module>
```

**The three measured numbers.**

1. **What the programme consumes**: the corrected shelf 25 rows / 8,668 silo; **7,292 net new
   math lines** on the whole-set read (8,668 raw, 8,144 declaration lines, 410 duplicate copies,
   524 boilerplate, 442 in-port) — the rows' own proofs; the **definition wave adds 1,118 lines**
   (874 wrapper-level + 244 proof-level) and the two private helpers (17), so the ready programme
   is ≈ **8,430 net**; seven orders; eight new modules; two legacy migrations. The leaves block
   is a separate ≈5,870.
2. **The read it starts from** (the corrected baseline, after SET 8): `needed` **1,020 / 404,926**;
   86 ready / 19,834; 296 leaves / 72,205; the four FR-0044 withholdings (831); MC ready
   **25 / 8,668**, MC demand **185 / 81,780**; frontier **1,388 / 721,506**.
3. **What the first wave should leave** (read off the same graph; the forecast, not yet a
   measurement): the three orders' 10 rows (3 + 4 + 3) leave the shelf, and their successors
   enter.  The measured figure is the next pass's job; the first wave's own consumer zone is
   the deliverable metric in the meantime.

**The forecast's shape.** The ready block's seven orders, at ~1,200–1,600 silo each, are the
column's next ~3 sessions; the leaves' four-order programme follows; the withheld pair waits on
the Abel–Jacobi programme. The shelf is *growing* as the recent waves' successors arrive (10 →
13 → 26 since the column plan), so the programme is a running one, not a one-off cut: the
successors of the first wave are where the next brief starts.

**The first wave landed (2026-10-27): MC-1, MC-2, MC-3 — the ready block's first ten rows.**
One read over the three sets: instrument `needed` 1,016 / 402,071 → **1,004 / 398,972** (corrected
1,018 / 402,432 → **1,006 / 399,333**); ready 83 / 17,475 → **75 / 15,689**; the `ModularCurve`
shelf 23 / 5,949 → **15 / 4,163** (corrected 22 / 5,913 → 14 / 4,127); MC demand 182 / 79,025 →
**170 / 75,926**; frontier +16 nodes / +3,637 lines (ten cut headlines plus six further pin
declarations the wave made ported, MC-2b's four `tatePowerSeries` nodes among them); leaves
296 / 72,205 → **294 / 71,671**.  **Two rows became ready out of the leaves block** —
`c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1` and
`meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two` — and they are M3's
next cut.  Six new or edited modules: `AlgebraicCurve/Differential/AutTrace.lean` (97),
`ModularCurve/Defs/QExpReductionModL.lean` (365), `X1/GaussResidue.lean` (533),
`X1/DiamondCorrespondence.lean` (778), `X1/HeckeCorrespondence.lean` (738),
`ConstantReductionQExp.lean` (274), plus the wave's insertions into
`ModularPolynomialVelu.lean` (959), `ModularPolynomialUniquenessIrreducible.lean` (332),
`TateSlots/CoefficientFormulas.lean` (322), `Degree/FinrankAdjoinJqNModC.lean` (531),
`TateSlots/Invariants.lean` (938), `X1/FunctionFieldIsAlgClosed.lean` (772),
`X1/Structure.lean` (212), `ModularPolynomialStarBank.lean` (399), and the single-copy shrink of
`X1/QExpRegularProlongation.lean` (681 → 228).  Two legacy migrations were paid
(`TateSlots/CoefficientFormulas.lean`, `X1/Structure.lean`) and one pre-existing tree defect fixed
(FR-0055).  The sets' records are [SET-MC1.md](SET-MC1.md), [SET-MC2.md](SET-MC2.md),
[SET-MC3.md](SET-MC3.md); the rectification audit is
[WORKORDER-MC7d-rectify-engine-homes.md](WORKORDER-MC7d-rectify-engine-homes.md).

**The successor read (2026-10-27, SET MC-7 §0).** After MD-001's wire close, measured on this
tree: `--selfcheck` **PASS**; instrument `needed` **1,019 / 404,826**, MC **26 / 8,704** (the 80
row leaves as a false ready, the 36 row enters); corrected (two markers: the 261 shadow and
`AlgebraicCurve.weilReciprocity`) `needed` **1,021 / 405,187**, ready 86 / 20,059, MC
**25 / 8,668** (unchanged), MC demand **185 / 81,780**, frontier **1,387 / 721,245**.  The
corrected `needed` line quoted in the table above (1,020 / 404,926) does **not** reproduce from
the documented command; SET MC-7 §0.1 and FR-0051 record the delta (the 261 node's own lines).

**The definition wave landed (2026-10-27): the gates of MC-4, MC-5 and MC-6.** Seven modules —
`ModularForms/Defs/GammaH.lean` (inserted: the three `Γ_H` operators), `ModularCurve/X1/HeckeModule.lean`
(inserted: `HeckeAlgOne` and its module structure), `ModularCurve/XH/Operators.lean` (inserted:
`diamondHBar`, `genOpH`; the legacy module migrated off `PORT_FILES`), and the four new
`ModularForms/CohCarrier/{Inst,Fricke}.lean` and `ModularCurve/Defs/{SiegelFunction,ResidualRealization}.lean`
— **84 declarations added, 121 `ok`, 0 mismatch, 0 missing, 0 own**, axioms clean, zero warnings, no option,
`dedup.py` 0 clusters, and a six-zone `spec/ModularCurveDefWaveConsumer.lean` at 0 errors. The
wave moves no shelf figure (a definition layer is not a premise; `needed` stays **1,004 / 398,972**,
MC ready **15 / 4,163**, leaves 294 / 71,671, frontier 1,408 / 727,998 — the read in
[WORKORDER-MCDEF-definition-wave.md](WORKORDER-MCDEF-definition-wave.md) §0). What it changes is
statability: MC-4 (`464`, `350`, `272`, `265`, and the two 27-line commutations), MC-5 (`390`, `224`,
`220`, `403`) and MC-6 (`322`, `384`) are writable, with 350/220/384 needing nothing new. Deferred
with their absent premises named: the pin's `TateModule` sections of `X1HeckeModule`, `XHOperators`
and `XH`; `CohCarrier_Inst`'s `hdata`/`MLAt` (and the unlisted `Def_CohCarrier_HeckeData`), and
`PeriodOf`'s petersson block. Three checker gaps were met and recorded (FR-0056/0057/0058).

**MC-4 landed (2026-10-27): M6 + M5, six rows.** Measured: `needed` **1,004 / 398,972 → 998 /
397,567** (−6 / −1,405 = exactly the six rows' silo); ready 75 / 15,689 → **70 / 14,308**; MC ready
15 / 4,163 → **10 / 2,782**; frontier 1,408 / 727,998 → **1,415 / 729,584**; leaves unchanged; the
six modules edited (no new module) came out **84 checked declarations `ok` / 0 mismatch / 0 missing /
1 pre-existing `own`**, axioms clean, zero warnings, no `set_option` added, 0 dedup clusters, and
`spec/ModularCurveMC4Consumer.lean` at 0 errors. The set paid **two legacy migrations** in the same
touch (`X1/DiamondLift.lean` and `XH/DiamondLift.lean`, which also corrected the brief's
import-direction error, FR-0059) and needed no promotion. The record is
[SET-MC4.md](SET-MC4.md); four of the five orders' briefs were corrected by worker findings
(SET-MC4 §5.1).

**One row became ready because of the set, and it is a false ready.**
`ModularCurve.rep_tateModule_jOne_comm` (24) entered the shelf: its *premises* are ported (one of
them MC-4c's) but its *statement* is `TateModule.rep …`, i.e. it names the absent
`Def_EllipticCurve_TateModule` and D2's deferred `rationalHeckeRepOne`/`RationalTateModule`. It is
the padic-Tate-module topic's row and the withheld pair's neighbourhood; **MC-5 must not cut it**.
That is the def-wave audit's FR-0049 shape, met again — the readiness test cannot see it, the
statement audit can.

## 8. What this programme does not do

- **The 80/36/261 chain.** The 36 row (MD-001) and the 80 row are false-ready, and the 261
  `ModularForm` row is a separate chain (≈4.8k raw / ≈2.1k `S_` lines, the C2 §9 subject). They are
  named, not cut; whoever takes them starts with the `ModularForm` basis theorem.
- **The two withheld Tate-module rows (610 silo).** The `abelJacobiCard_genus` programme and the
  `TateModule` definition layer; the T1/T2 plan of `TOPIC-padic-tate-module.md` is the record.
- **The leaves block (34 / 7,331).** Named by story and deferred (§0.4/§3); they are not part of
  the seven orders.
- **The `CuspForm`/`CohCarrier` definition modules of the leaves** (`PeriodHomPair`,
  `Pic0Congr`, `ComplexPlaceDictionaryOf`, `X0ModL`): deferred with the leaves.
- **No surface promotion, no whole-tree build.** The definition wave is new surface, not a
  promotion; every module is gated on its own build at the project cap; a tree build waits for a
  milestone and the user's agreement.