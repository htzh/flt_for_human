# Ready shelf 1 — the `ModularCurve` successor shelf (2026-10-28)

**Status: wave 1 landed (2026-10-28); waves 2–3 scoped, not dispatched.** MS-1 (Fricke–Galois),
MS-2 (the Hecke–diamond laws) and MS-3 (j-order, coset, diffQExp) are in, six rows, and so is the
manager lane; what remains of this shelf is MS-4 to MS-7 (12 rows / 5,687 silo). The measured
landing is §9; the set records are [SET-MS1.md](SET-MS1.md), [SET-MS2.md](SET-MS2.md),
[SET-MS3.md](SET-MS3.md), [SET-MSDEF.md](SET-MSDEF.md). *Naming*: this is the first **numbered** ready shelf of the
family. [TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) stays the family-level document (the whole
shelf's read, the ten stories, the seven orders and the leaves programme); each later pass
re-measures the residue and writes `TOPIC-ready-shelf-N.md`, so the numbering is the sequence of
cuts, not the sequence of subjects. This one scopes the shelf that the family document's §7
leaves as its own successor — "the successor shelf (20 rows / 8,178: the 1,176 M9 row, 611, 373
×2, 191, 168, and the twelve rows the last wave's declarations made ready)". It re-measures it, removes the **two** rows that are not rows
of this shelf (§0.1), audits the definition layer at the **declaration** level with
`spec/gate_scan.py` (§0.2: one module, 2 declarations, 37 pin lines) and the **private
shadows** with `twin_scan` (§0.2: one promotion, a 34-line leaf), prices the corrected
**18 rows / 8,118 silo** at **6,432 net new math lines** (§0.3), and cuts a **seven-order
programme in three waves**, opening with three orders / 2,431 silo / 2,060 net (§1). Its
figures supersede the shelf note's §7 successor line and its forecast.

The recipe is [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md).
The programme it succeeds is the ready block's seven orders ([TOPIC-ready-shelf.md](TOPIC-ready-shelf.md)
§1) and the leaves' six ([SET-LEAVES.md](SET-LEAVES.md)).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`. Read 2026-10-28, on a tree **unchanged since SET-LEAVES landed**: the read
reproduces the recorded baseline figure for figure (§0), which is the stability check this pass
gets for free. The pricing is `port_advise`/`port_plan` (text only); the definition audit is
`spec/gate_scan.py`, `twin_scan.py` and a hand read of the pin statements.

| figure | instrument | corrected (§0.1) | this shelf (§0.1) | after wave 1 (§9) | **after all 18 rows (§10)** |
|---|---:|---:|---:|---:|---:|
| `needed [F terminal]` | 960 / 388,827 | 962 / 389,188 | — | 954 / 386,396 | **942 / 380,709** |
| ready, all namespaces | 81 / 20,199 | 81 / 20,028 | — | 77 / 18,418 | **68 / 13,294** |
| leaves, all namespaces | 262 / 64,874 | 262 / 64,874 | — | 262 / 64,874 | 262 / 64,874 |
| `ModularCurve` ready | 20 / 8,178 | 19 / 8,142 | **18 / 8,118** | 16 / 6,397 | **7 / 1,273** |
| `ModularCurve` leaves | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| `ModularCurve` demand | 126 / 65,781 | 126 / 65,781 | — | 120 / 63,350 | **108 / 57,663** |
| withheld (FR-0044) | 4 / 831 (2 MC / 610) | 4 / 831 | 4 / 831 | 4 / 831 | 4 / 831 |
| frontier F | 1,455 / 738,539 | 1,453 / 738,178 | — | 1,461 / 740,970 | **1,473 / 746,657** |
| avoided R (prunable) | 140 / 74,620 | 140 / 74,620 | 140 / 74,620 | 140 / 74,620 | 140 / 74,620 |

The whole 18-row shelf accounts for exactly **5,687 lines** of the drop from wave 1
(5,715 = the 12 remaining rows' silo, minus the 28-line successor that entered the shelf), and the
seven rows on the shelf after it are the five successors (364, 347, 303, 171, 28) plus the two
known non-rows (the 36 chain, the 24 Tate-module row).

The corrected-after-wave-1 column reads `needed` 956 / 386,757, ready 77 / 18,247, MC ready
15 / 6,361, frontier 1,459 / 740,609.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc2shelf.json
python3 frontier.py --selfcheck          # PASS
# the corrected read: the 261 name shadow and the AC shadow (§0.1)
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast \
  --unport AlgebraicCurve.weilReciprocity > build/mc2shelf-corr.json
# the private-shadow probe (§0.2), either instrument
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularCurve.qExpansion_E6_eq_map_mk > build/mc2-u1.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --port-public-only > build/mc2shelf-pub.json
```

**The family has no leaves left, and that changes the shape of this scoping.** The leaves block
landed whole ([SET-LEAVES.md](SET-LEAVES.md)): `ModularCurve` leaves are **0 / 0**, so this
shelf is read with `--include-leaves` for the column's sake (262 rows / 64,874 in other
namespaces, FR-0040: named and deferred, not this set) and not because a `ModularCurve` row
hides there. The ready block is 20 rows / 8,178 — the whole of what the last two waves made
ready — and the `ModularCurve` demand is 126 nodes / 65,781 lines, i.e. this shelf is 12 % of
the family's remaining demand by line count and the rest is the mod-ℓ/Tate programme.

**The read is stable.** `needed` 960 / 388,827, leaves 262 / 64,874, frontier 1,455 / 738,539,
MC ready 20 / 8,178: every one of these is the figure [TOPIC-ready-shelf.md](TOPIC-ready-shelf.md)
§7 records for the post-leaves tree. No row entered or left the shelf between the two passes,
so the deltas this note reports are *corrections of the read*, never movement of the tree.

**`--selfcheck` PASSes** — the false-marker inventory is empty (MD-001's wire was closed by SET
MC-7 and no new one has appeared). The two corrections below are not `spec-pin` artifacts: they
are a name shadow and a statement audit, which is why the corrected read is `--unport` on two
non-`ModularCurve` nodes.

**The withheld block is unchanged and is not this shelf's** — the four rows / 831 silo of
[TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §0: two `ModularCurve` Tate-module rows
(`moduleFinite_and_free_padicInt_tateModule_jH` 327, `moduleFinite_padicInt_tateModule_jOne`
283) on `AlgebraicCurve.Pic0.abelJacobiCard_genus`, and two `AlgebraicCurve` rows on the
prunable Abel–Jacobi subject (126, 95). They wait on the Abel–Jacobi programme plus
`Def_EllipticCurve_TateModule`; quote and defer.

## 0.1 The correction: the 261 chain, the Tate-module row, and the 36

The instrument's 20 rows include three that cannot be transcribed, and the corrected read plus
one statement audit removes all three.

| node | silo | why it is not a row of this shelf |
|---|---:|---|
| `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` | — | in the **demand**, not the shelf: the `CuspForm` twin's last name shadows it (FR-0047), which is why the 36 row below reads ready |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | its only substantive premise is the 261 above, so it is a false ready on the corrected read; the chain is 261 → 36 and the shelf note's §8 already defers it (the `ModularForm` Gamma₁ basis theorem, ≈4.8k raw / ≈2.1k `S_` lines) |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | its *premises* are ported (`JOne.galois_smul_heckeAlgOne_smul`, MC-4) but its *statement* is `TateModule.rep …`: the absent `Def_EllipticCurve_TateModule` (883 pin lines / 69 declarations) and D2's deferred `rationalHeckeRepOne`/`RationalTateModule`. Not statable |

The first two are one chain, and the corrected read handles them: `--unport` the 261 and
`needed` moves 960 / 388,827 → 962 / 389,188 (+2 nodes: the 261's 261 lines and the AC
`weilReciprocity`'s 100), the shelf loses the 36 row (19 / 8,142) and **MC demand does not
move** — the 36 row was already in demand, only its readiness was fictional. The 36 row is
[TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §8's deferred chain, unchanged; do not cut it here.

The third is the statement audit the recipe §0 demands ("`needed = 1` is a premise claim, not a
statement claim"): `twin_scan --node` returns `new` on all 18 real rows (§0.3), and the 24 row's
`TateModule` vocabulary is missing outright. It is the padic-Tate-module topic's row
([TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md)) and the withheld pair's
neighbourhood. **One relation worth recording**: its statement takes `hcomm :
HeckeDiamondCommuteBar M` as a *hypothesis*, which is this shelf's U7 28-line row — so U7 is
that programme's first brick, and landing it removes one of the row's hypotheses without making
the row statable.

So the shelf is **18 rows / 8,118 silo**: 8,178 − 36 − 24.

## 0.2 The definition audit — one gate and one promotion

The frontier's readiness is premise-based, so a row whose statement names an unported structure
reads ready. The shelf note measured that gap at module granularity (1,118 lines for 12
modules) and the def wave corrected it to the declaration level with `spec/gate_scan.py`
([WORKORDER-MCDEF-definition-wave.md](WORKORDER-MCDEF-definition-wave.md) §0.1). This pass runs
the same instrument over the successor shelf: for every row, every pin `Def_` module imported by
its wrapper **and** its `S_` file, the declarations the `S_` text (and its intra-module closure)
actually uses, and whether the port has them **publicly**.

**Twenty-five `Def_` modules are in the 18 rows' closure.** `port_advise --with-defs` puts 20 of
them on the wrapper route (58 target files, 1,262 declarations, `Def_EllipticCurve_TateModule`
among them — it belongs to the excluded 24 row); the `S_` files import six more that the wrapper
route does not reach (`CohCarrier_Fricke`, `ModularCurve_PhiGen`, `ModularCurve_X0ModL`,
`FLTPrelim_Modularity`, `FLTPrelim_Ramification`, `WeierstrassCurve_ReductionMap`). The result is
that the definition layer is **landed**, with one exception:

| pin `Def_` module | public decls | rows using it | used | **missing** | lines |
|---|---:|---:|---:|---:|---:|
| `ModularCurve_XHDiamondModL` | 2 | 373-XH | 2 | **2** | **37** |
| `ModularCurve_X0` | 61 | 734, 410-φ, 144 | 27 | 0 | 0 |
| `ModularCurve_X1` | 35 | 648, 442, 441, 168, 166 | 9 | 0 | 0 |
| `ModularCurve_X1HeckeModule` | 42 | 28 | 5 | 0 | 0 |
| `ModularCurve_TateSlots` | 37 | 373-XH, 168 | 1 | 0 | 0 |
| `CohCarrier_Fricke` | 28 | 1176 | 7 | 0 | 0 |
| `ModularCurve_XH` | 25 | 684, 373-XH | 3 | 0 | 0 |
| `ModularCurve_PeriodHomPair` | 24 | 648 | 0 | 0 | 0 |
| `ModularCurve_HeckeDifferential` | 22 | 62 | 10 | 0 | 0 |
| `ModularCurve_PhiGen` | 50 | 410-φ | 6 | 0 | 0 |
| `ModularCurve_XHOperators` | 16 | 1176, 410-dh | 5 | 0 | 0 |
| `ModularCurve_LaurentCoeff` | 15 | 734, 442, 166 | 6 | 0 | 0 |
| `ModularCurve_ArithmeticGalois` | 13 | 648 | 5 | 0 | 0 |
| `GaloisRep_ComplexConjugation` | 13 | 648 | 2 | 0 | 0 |
| `ModularCurve_JqCoeff` | 11 | 734, 442, 441, 410-φ | 4 | 0 | 0 |
| `ModularCurve_ComplexPlaceDictionaryOf` | 11 | 684, 648, 441 | 2 | 0 | 0 |
| `AlgebraicCurve_BaseChangeGalois` | 45 | 684 | 5 | 0 | 0 |
| `ModularCurve_ClassicalModularPolynomials` | 10 | 410-φ | 4 | 0 | 0 |
| `ModularCurve_QExpansionDiff` | 6 | 62 | 4 | 0 | 0 |
| `ModularCurve_PrimCosetReps` | 5 | 144 | 0 | 0 | 0 |
| `ModularCurve_SiegelFunction` | 2 | 1057, 191 | 2 | 0 | 0 |
| `ModularCurve_X0ModL` | 20 | 442 | 2 | 0 | 0 |
| `WeierstrassCurve_ReductionMap` | 20 | 442 | 3 | 0 | 0 |
| `FLTPrelim_Modularity` | 13 | 734 | 1 | 0 | 0 |
| `FLTPrelim_Ramification` | 3 | 442 | 1 | 0 | 0 |

**The gate.** `Def_ModularCurve_XHDiamondModL` is 50 pin lines and two declarations:
`IsDiamondPullbackModL` (a `Prop` over `ρ : Γ₀(M) →* (qExpFunctionFieldC K (Γ_H M H) ≃ₐ[K] …)`,
20 lines) and `coe_apply_eq` (its projection lemma, 17 lines). It is the
Γ_H-level sibling of the ported X₁ diamond pullback (`X1DiamondPullback` in
`ModularCurve/X1/DiamondAut.lean`, 545 lines of precedent, whose `sigma`/`isDiamondAut` API is
what the pin's `IsDiamondAutHBar` was built from), and its statement vocabulary is *not* the
absent Tate-module layer: nothing in it names `TateModule`. It serves **one** row (373-XH).
The manager's, 37 lines, at the pin's names, as a new `ModularCurve/Defs/XHDiamondModL.lean`.

**The promotion.** `twin_scan --node ModularCurve.qExpansion_E6_eq_map_mk` returns
`twin-private`: the port holds the statement as a 15-line `private theorem` inside
`namespace EisensteinCube` of `ModularCurve/X1/IntegralityJqNModC.lean:97`, byte-identical to
the pin's public theorem, while the pin states it publicly with its own `Thm_`/`S_` pair (a
34-line leaf, 2 cone consumers, 10 project consumers). Two rows — 373-XH and 168 — cite it as a
premise, so neither can be transcribed until it is public *at the pin's name*. This is the
recipe §4 promotion case, and the frontier cannot see it: the name tier scans **private** port
declarations (a documented limit of `tiers()`), so the node reads ported. Two independent
instruments confirm the effect exactly — `--unport` it, and `needed` moves +1 node / +34 lines
while the shelf drops 2 rows / 541 silo (8,178 → 7,637); `--port-public-only`, and the MC shelf
moves by the same two rows, plus a 650-line `AlgebraicCurve` row
(`Divisor.pushforwardNormFormula_of_finiteDimensional`, private in
`AlgebraicCurve/PrincipalDivisors/Transcendence.lean:359` behind its own `spec-pin:`) that the
instrument had also read ported — the same mechanism on a row rather than a premise, and the
larger instance of it (FR-0071). The manager's, ~15 lines plus its `spec-pin:` wire, in
`X1/IntegralityJqNModC.lean` (the module whose MD-001 wire was just closed — this is its next
edit, and the private helper is already there).

**The manager lane landed (2026-10-28, before wave 1 finished).** Both items are in, each with its
own build and its own wire ([WORKORDER-MSDEF-gate-and-promotion.md](WORKORDER-MSDEF-gate-and-promotion.md)):

| item | file | checker | axioms |
|---|---|---|---|
| the gate | **new** `ModularCurve/Defs/XHDiamondModL.lean` (80 lines: the pin's two declarations + its `variable` block, one `spec-pin:`) | **2 ok / 0 / 0 / 0** | clean |
| the promotion | `ModularCurve/X1/IntegralityJqNModC.lean` (`qExpansion_E6_eq_map_mk` public at `ModularCurve.…`, `EisensteinCube` re-opened after it, two `spec-pin:` lines; the `S_` copy's three Bernoulli helpers are not transcribed — the proof decides `bernoulli 6 = 1/42` by `decide +kernel` — and the header says so) | **3 ok → 4 ok / 0 / 0 / 0** | clean |

`twin_scan --node ModularCurve.qExpansion_E6_eq_map_mk` flipped **`twin-private` → `twin-public`**, and
the read is unchanged by both (the promotion only made an already-counted node importable; the gate
is a definition layer). **U4 is therefore statable**, and MS-7 has no manager lane left.

**What this means for the cut.** Sixteen rows / 7,577 silo need no manager work at all: the
definition layer of the successor shelf is the two waves' gift. Two rows / 541 silo (U4) need
the 37-line def *and* the promotion, so **U4 is the one order that waits on the manager's
lane**. The old audit's 1,118-line, 12-module figure does not recur anywhere in this shelf.

## 0.3 The pricing

**The whole-set read.** `port_advise` over the 18 nodes (36 target files, 765 declarations —
`Def_EllipticCurve_TateModule` is excluded with its row) and `port_plan` (a 47-node premise
slice):

| budget line | value |
|---|---:|
| raw `S_` lines | 8,118 |
| declaration lines | 7,705 |
| duplicate copies (port once) | 552 |
| boilerplate | 413 |
| already in the port (vetted) | 721 |
| **net new math lines** | **6,432** |
| substitutions | 118 trusted / 5 suspect |

**All 18 rows are `new`.** `twin_scan` over the set returns `new` for every one — no row is a
statement the port already holds under another name, so there is no free import and no
namespace-split decision to make. The largest in-port credits are real but must be hand-read:
the 198 lines of U6's 552 are the `FunctionFieldIsAlgClosed` residue block
(`isAlgebraic_residueField` 59, `residueTopHom` 17, `map_mem_adjoin` 15,
`image_intFormRatiosC` 14, `map_mem_qExpFunctionFieldC` 12 — five of six verified public in a
module MC-3 created), but the sixth, `Φ_injective` (15), is name-matched to a **private**
`WeightOne/Gamma1Basis` Φ over a different map, so ≈15 of those 198 are new. That is FR-0069's
rule, met again on a smaller scale.

**The 5 suspect substitutions are all type-only `def` matches** and none of them is an import:
`ratioField` → `modularFunctionField` (9 lines; both are `IntermediateField ℚ (LaurentSeries ℚ)`,
different fields), `frickeGL` → `AtkinLehnerDatum.alGL` (5; the port *does* have the right
object publicly, `ALTraceIdentity.frickeGL` in `ModularForms/HeckeFrickeTrace.lean`, and a
private `ModularCurve.frickeGL` in `XH/FrickeSlash.lean` — U1's trap), `Nice` →
`WLight.PoleBounded` (3), `slashQ` → `slashQExpC` (3), `frickeOneConst` → `WLight.zetaN` (2).
The 6,432 already excludes them; treat the "already in the port" line as 721 − 22 if the worker
finds them genuinely new.

**Per-story prices** (each story's own `port_advise`/`port_plan` run; the sum is exactly the
whole-set 6,432 — no cross-story dedup). `gate` is the story's missing-definition lines and
manager items:

| story | rows | silo | rows-net | gate | total |
|---|---:|---:|---:|---:|---:|
| **U1** fricke–galois | 1 | 1,176 | 1,008 | — | **1,008** |
| **U2** the Siegel unit's integral q-expansion | 3 | 1,621 | 1,557 | — | **1,557** |
| **U3** the complex-place dictionary and its action | 3 | 1,773 | 1,130 | — | **1,130** |
| **U4** the toric-point dictionary (Γ₁ and Γ_H) | 2 | 541 | 442 | 37 + promotion | **479** |
| **U5** the modular polynomial at level two | 1 | 410 | 338 | — | **338** |
| **U6** the ratio dictionary and the index bound | 2 | 608 | 354 | — | **354** |
| **U7** the Hecke–diamond laws | 2 | 438 | 318 | — | **318** |
| **U8** cusp decay under integrality | 1 | 734 | 551 | — | **551** |
| **U9** the order of j − j(τ) | 1 | 611 | 569 | — | **569** |
| **U10** the coset translate | 1 | 144 | 123 | — | **123** |
| **U11** the `qExpansionDiffAlong` identity | 1 | 62 | 42 | — | **42** |
| **total** | **18** | **8,118** | **6,432** | **37 + promotion** | **≈6,480** |

Two ratios are worth reading off the last column. **U3 carries the most silo for the least new
mathematics** among the three big stories (1,130 net for 1,773 silo, 64 %; only U6's 58 % is
lower) because its three rows share one 161-line engine over 511 duplicated pin lines — write it
once, publicly, and the three headlines are short. **U2 is the most expensive per silo**
(1,557 of 1,621, 96 %): 1,057's `S_` file is 117 declarations of a self-contained
Siegel-product/domination engine, and the port has none of it (`in port 0`).

## 0.4 The stories

Eleven subjects, one per pin `S_` file's own subject; the letters are this note's, the row
numbers are the pin's `S_` line counts.

| story | what it is | rows |
|---|---|---|
| **U1** | the Fricke pull-back on the ¯ℚ-base-changed `xHFunctionFieldBar`: there is a ¯ℚ-algebra automorphism `w` sending the q-expansion ratio `x` (with `g`) to the ratio of the Fricke slash, and it is the Galois twist of the diamond action | 1176 |
| **U2** | the Siegel unit's integral q^{1/N}-expansion (`∃ c`, all `c n` integral, `N·c 0⁻¹` integral, `HasSum` and `Tendsto` at i∞), its *peaked exponent* (an arithmetic `m`/`Ord` making `Ord 1 0` minimal), and the product of `siegelFun` over ℤ/N × ℤ/N under SL(2, ℤ) | 1057, 373, 191 |
| **U3** | the complex-place dictionary: existence for any Γ ∋ T, the pull-back along γ ∈ Γ₀(M) (`σ` sends `pt τ` to `pt γ⁻¹τ`), and coefficientwise conjugation (`pt τ ↦ pt(J·τ)`) | 441, 684, 648 |
| **U4** | the toric-point dictionary: the two Tate-slot ratios `c₄(1+12x)/c₆` and `(x+6x²+2a₄)/c₄` lie in `qExpFunctionFieldC K Γ₁` and in `qExpFunctionFieldC K (Γ_H M ⊥)`, with the diamond pullback mod L | 168, 373 |
| **U5** | the modular polynomial at level two: `data.Φ = phiTwo` for every `ModularPolynomialData 2` | 410 |
| **U6** | the ratio dictionary and the index bound: every element of `laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)` is a modular-form ratio, and `adjoin K {jqModC}` is finite-dimensional over `qExpFunctionFieldC K Γ` with finrank ≤ `Γ'.index` (for `Γ ≤ Γ'` with the `±1` condition) | 166, 442 |
| **U7** | the Hecke–diamond laws: `⟨dd'⟩ = ⟨d⟩⟨d'⟩` on `J_H`, and `HeckeDiamondCommuteBar M` (the three X₁ commutations as one `Prop`) | 410, 28 |
| **U8** | cusp decay: under integrality of `X^{2M}·j^{mM+1}·(j−1728)^{mM}` over ℂ[j⁻¹], the slash of `g(E₄²E₆)^m` is eventually dominated by that of `hΔ^m` at i∞ | 734 |
| **U9** | the order of `j − j(τ)`: `ord_τ (E₄³/Δ − ·) = card(stabilizer τ)/2` | 611 |
| **U10** | the coset translate: the `q`-expansion of the `(a·τ+b)/d`-translate is `cosetSubst` | 144 |
| **U11** | `qExpansionDiffAlong F.val ω = diffQExp F ω` | 62 |

**What the shelf is made of, as a subject.** The last two waves' declarations show up as the
*premises* of these rows: the leaves' def wave (`ComplexPlaceDictionaryOf`, `PeriodHomPair`,
`X0ModL`, `Pic0Congr`) and the MC def wave (`X1HeckeModule`, `XHOperators`, `SiegelFunction`,
`CohCarrier.{Inst,Fricke}`) supply every structure the 18 statements name. There is no story
here that needed a definition; **every gate of this shelf is arithmetic**, and the two manager
items of §0.2 are the only ones.

## 1. The programme

Seven orders in three waves, 18 rows / 8,118 silo / ≈6,480 net (6,432 rows + 37 def + the
promotion). Sizes are the recipe's 1,300–1,600 silo except where one subject is larger (U2, U3)
or a subject is smaller and its home argues for bundling.

| order | stories | rows | silo | net (rows + gate) | manager before it |
|---|---|---:|---:|---:|---|
| **MS-1** ✓ landed | U1 (Fricke–Galois) | 1 | 1,176 | 1,008 | none |
| **MS-2** ✓ landed | U7 (Hecke–diamond laws) | 2 | 438 | 318 | none |
| **MS-3** ✓ landed | U9 + U10 + U11 (j-order, coset, diffQExp) | 3 | 817 | 734 | none |
| **MS-4** | U2 (Siegel unit) | 3 | 1,621 | 1,557 | none |
| **MS-5** | U3 (complex-place dictionary) | 3 | 1,773 | 1,130 | none |
| **MS-6** | U6 + U8 (ratio dictionary, cusp decay) | 3 | 1,342 | 905 | none |
| **MS-7** | U4 + U5 (toric dictionary, Φ₂) | 3 | 951 | 780 | **landed** (SET-MSDEF) |
| | **shelf** | **18** | **8,118** | **≈6,480** | **landed** |
| | **remaining** | **12** | **5,687** | **≈4,372** | none (the gate is landed) |

Briefs: [WORKORDER-MS1-fricke-galois.md](WORKORDER-MS1-fricke-galois.md),
[WORKORDER-MS2-diamond-laws.md](WORKORDER-MS2-diamond-laws.md),
[WORKORDER-MS3-jorder-coset-diffqexp.md](WORKORDER-MS3-jorder-coset-diffqexp.md),
[WORKORDER-MSDEF-gate-and-promotion.md](WORKORDER-MSDEF-gate-and-promotion.md),
[WORKORDER-MS4-siegel-unit.md](WORKORDER-MS4-siegel-unit.md),
[WORKORDER-MS5-place-dictionary.md](WORKORDER-MS5-place-dictionary.md),
[WORKORDER-MS6-ratio-and-decay.md](WORKORDER-MS6-ratio-and-decay.md),
[WORKORDER-MS7-toric-and-phi-two.md](WORKORDER-MS7-toric-and-phi-two.md).

**The first wave is MS-1, MS-2, MS-3** (6 rows / 2,431 silo / 2,060 net). Three properties pick
it: **no manager lane** (no gate, no promotion, no migration — §0.2, §3); **disjoint files**
(one new module each for MS-1 and MS-2, three insertions for MS-3, none shared), so all three
run concurrently under the one build lock; and **zero blast radius** — every home either does
not exist yet or has no dependents (§3). It is also the family's own "the successor of the last
landed set" cut: U1 is MC-6's successor, U7 is MC-4's, and U9/U10/U11 are the leaves' and MC-2's.

**Wave 2 is MS-4, MS-5, MS-6** (9 rows / 4,736 silo / 3,592 net): the three big new-module
stories, gate-free, files disjoint (MS-4's two insertions are Siegel modules, MS-6's one is
`X1/CoeffMap`, MS-5 is one new module). **Wave 3 is MS-7** (3 rows / 951 / 780), which waits on
the manager's two items; the two items are independent of waves 1–2, so the manager can land
them while wave 1 runs, and MS-7 can then join wave 2 if a worker is free.

**Why this order.** The three wave-1 orders are the set's cheapest and least coupled: 28-line
MS-2 has 29 project consumers, and U9's 611-line row is the only row of the set whose single pin
premise is an engine a recent set already landed (`exists_smul_eq_of_E4_cube_div_discriminant_eq`,
MC-2, in `TateSlots/Invariants`). MS-3 is the set's
tail and is deliberately three insertions into modules the last two waves created (each with
**zero** dependents, §3). The big engines come after, and MS-4 before MS-5 only because U2's
117-declaration analysis (`tprod`, `Pabs`, `pp`, the domination bound) is the set's only
analytic risk and wants a fresh worker.

**Deviations from the size rule.** MS-4 is 1,621 silo and MS-5 1,773: both are *one* subject
each and splitting either would pay its engine twice (MS-4's is 1,557 net of 1,621; MS-5's three
rows share a 161-line engine and 511 duplicated lines). MS-3 is 817 and MS-2 438 because
U7/U9/U10/U11 are four separate small subjects with four separate homes — bundling them into one
1,300-line order would put four reviewers' subjects in one worker's hands; the recipe's
"one story per order" is kept, at a size the reviewer may merge if they prefer three orders to
five in the first two waves.

### 1.1 What the manager must do before a wave is dispatched

Asked of this note directly, so it is answered directly: **waves 1 and 2 need no Lean from the
manager**; wave 3 needs two small items, and both are independent of waves 1–2. The full
pre-dispatch list:

**Before MS-1, MS-2, MS-3 (wave 1).** The three briefs, nothing else: each carries its row's pin
`S_` file and wrapper, its home and its import line, the build gate of §5, and the two decisions
this scoping leaves open rather than discovered —
(a) **U1's `frickeGL`**: the brief must name the public object (`ALTraceIdentity.frickeGL M
(NeZero.ne M)` in `ModularForms/HeckeFrickeTrace.lean:44`) so the worker neither promotes
`XH/FrickeSlash`'s private copy nor writes a third one (the pin has **no** node named
`ModularCurve.frickeGL`: 24 `S_` files declare their own `P2MW.S_…` copy, so there is no public
obligation, only a dedup one);
(b) **U10/U11's one added import each** (`Analytic/QParamUnique` into `ModularPolynomialCoset`,
`Defs/HeckeDifferential` into `Period/QExpansionDiff`), which the brief states so it is not
treated as a discovery. Plus the wave's consumer-zone file name
(`spec/ModularCurveReady1Consumer.lean`), started empty and filled at review (§5.7).

**Before MS-4, MS-5, MS-6 (wave 2).** The three briefs. The only open decision is whether MS-4
is one worker or two (1,057 alone; 373 + 191 together) — a size choice, not a gate.

**Before MS-7 (wave 3).** Two Lean items, each a single-module build, both landable while wave 1
runs — **both landed on 2026-10-28** (§0.2's table); the table is kept as the record of what they
were:

| item | file | what | wire | checker |
|---|---|---|---|---|
| the gate | `ModularCurve/Defs/XHDiamondModL.lean` (**new**) | `IsDiamondPullbackModL` (20 lines) + `coe_apply_eq` (17), at the pin's names, nothing else | the pin `Def_ModularCurve_XHDiamondModL.lean` **and** the 373-XH row's `Thm_`/`S_` (the row uses both declarations) | module absent → **2 ok / 0 / 0** |
| the promotion | `ModularCurve/X1/IntegralityJqNModC.lean` (**edit**) | move `EisensteinCube.qExpansion_E6_eq_map_mk` out of the inner namespace as public `ModularCurve.qExpansion_E6_eq_map_mk`; the pin `S_` file's three private Bernoulli helpers stay out (the port's proof uses `decide +kernel`) | add `spec-pin: Theorems/Thm_ModularCurve_qExpansion_E6_eq_map_mk.lean`, and its `S_` line only if `--force` agrees | **3 ok → 4 ok / 0 / 0** |

The manager's own verification of the pair: after both, `--selfcheck` still PASSes, the checker
reads **2 ok** on the gate module and **4 ok** on the promotion module, and `twin_scan --node
ModularCurve.qExpansion_E6_eq_map_mk` flips from `twin-private` to `twin-public`. The **read does
not move** (it stays `needed` 960 / 388,827 and MC ready 20 / 8,178): the node was already counted
ported by the name tier, so a promotion is *statability*, not demand — the same shape as the
definition wave, which moved no shelf figure either. The `--unport` experiment is the diagnostic,
not the landing: it moves `needed` to 961 / 388,861 because it forces the node unported.

**Before any dispatch, the olean check (FR-0033).** Measured today, all eleven import targets of
the three wave-1 orders carry a current `.olean` (`XH/FrickeSlash`, `XH/Operators`, `XH/Inputs`,
`X1/CoeffMap`, `X1/DiamondCorrespondence`, `X1/DiamondLift`, `X1/HeckeCommute`, `X1/HeckeModule`,
`TateSlots/Invariants`, `ModularPolynomialCoset`, `Period/QExpansionDiff`); the only module of the
programme with no `.olean` is the gate module above, which is new by design. So: **no host needs a
pre-build, no migration, no `PORT_FILES` edit, no `decl_markers.tsv` row.**

**The insertion baselines** (so a brief can state the before/after count instead of a promise):

| host | `check_port --force` today | its insertion |
|---|---|---|
| `TateSlots/Invariants.lean` | 91 ok / 0 / 0 | U9 (611) |
| `ModularPolynomialCoset.lean` | 16 ok / 0 / 0 | U10 (144) |
| `Period/QExpansionDiff.lean` | 3 ok / 0 / 0 | U11 (62) |
| `SiegelUnit/BernoulliWeight.lean` | 67 ok / 0 / 0 | U2 (373) |
| `SiegelUnit/Basic.lean` | 9 ok / 0 / 0 | U2 (191) |
| `X1/CoeffMap.lean` | 93 ok / 0 / 0 | U6 (166) |

Each order owes **at least its headline** on top of the baseline; how far above depends on the
surface gate (§5.8) and is the reviewer's to set, not the worker's to guess.

**Review-time, not pre-dispatch**: the surface gate per module (§5.8), `dedup.py`/`move_dead.py`,
the wave's consumer zone, and the post-wave re-read of the three numbers (§7).

## 2. The rows

`silo` is the pin `S_` line count; `prem` the pin's `import Theorems.Thm_*` count; `lev` the
corrected read's cone / project consumers; the story's `net` is in §0.3.

| story | node (`ModularCurve.` dropped) | silo | prem | lev | home |
|---|---|---:|---:|---:|---|
| U1 | `exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul` | 1,176 | 2 | 1 / 8 | **new** `XH/FrickeGalois.lean` |
| U2 | `SiegelUnit.exists_isIntegral_hasSum_siegelFun` | 1,057 | 1 | 1 / 1 | **new** `SiegelUnit/Integrality.lean` |
| U2 | `SiegelUnit.exists_peaked_exponent` | 373 | 3 | 1 / 1 | insert `SiegelUnit/BernoulliWeight.lean` |
| U2 | `SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul` | 191 | 2 | 2 / 4 | insert `SiegelUnit/Basic.lean` |
| U3 | `ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul` | 684 | 2 | 1 / 1 | **new** `ComplexPlaceDictionaryAction.lean` |
| U3 | `ComplexPlaceDictionaryOf.arithmeticGalois_complexConjAlgEquiv_smul_pt` | 648 | 2 | 1 / 2 | **new** `ComplexPlaceDictionaryAction.lean` |
| U3 | `exists_complexPlaceDictionaryOf` | 441 | 4 | 1 / 4 | **new** `ComplexPlaceDictionaryAction.lean` |
| U4 | `exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq` | 373 | 5 | 1 / 1 | **new** `TateSlots/ToricPointDictionary.lean` |
| U4 | `c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1` | 168 | 5 | 1 / 1 | **new** `TateSlots/ToricPointDictionary.lean` |
| U5 | `ModularPolynomialData.phi_eq_phiTwo` | 410 | 4 | 1 / 3 | **new** `ModularPolynomialLevelTwo.lean` |
| U6 | `finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index` | 442 | 6 | 6 / 74 | **new** `X1/FunctionFieldIndex.lean` |
| U6 | `exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC` | 166 | 1 | 2 / 11 | insert `X1/CoeffMap.lean` |
| U7 | `diamondHBar_mul` | 410 | 2 | 1 / 12 | **new** `HeckeDiamondCommute.lean` |
| U7 | `heckeDiamondCommuteBar` | 28 | 3 | 3 / 29 | **new** `HeckeDiamondCommute.lean` |
| U8 | `eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow` | 734 | 6 | 1 / 1 | **new** `Analytic/CuspDecay.lean` |
| U9 | `meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two` | 611 | 1 | 2 / 6 | insert `TateSlots/Invariants.lean` |
| U10 | `qExpansion_cosetTranslate_eq_cosetSubst` | 144 | 2 | 2 / 4 | insert `ModularPolynomialCoset.lean` |
| U11 | `qExpansionDiffAlong_val_eq_diffQExp` | 62 | 2 | 2 / 8 | insert `Period/QExpansionDiff.lean` |
| | **shelf** | **8,118** | | | 8 new modules / 6 insertions |

(The rows' own `net` is measured per story in §0.3; a per-row split is not separately measured
and is not quoted here. `prem` is a risk column: 442's six premises and 734's six are where a
worker stalls, not where the lines are.)

Demand is inverted relative to size, as usual: the 442-line index bound has **74** project
consumers and 6 cone consumers, the 28-line `heckeDiamondCommuteBar` 29, the 62-line diffQExp
row 8, while the 1,176-line Fricke row has 8 and the 1,057-line Siegel row 1.

## 3. Homes

Method as in the recipe §4: pin `S_` premises → statement-identical port module → the modules
above all of them in the port's import closure, then confirm against the proof's subject. The
check here is exact (declaration-name index over the port, not last names): for each row, the
port module of every premise **and** of every statement-vocabulary declaration §0.2 found
"used", then the set of port modules above all of them.

| story | above-all check | home | note |
|---|---|---|---|
| U1 (1176) | **none**: `XH/Operators` (the `IsDiamondAutHBar`/`diamondHBar` layer) and `XH/FrickeSlash` (`exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion`, which already imports `FrickeReciprocity` + `CohCarrier.Fricke`) are siblings | **new** `XH/FrickeGalois.lean` | imports `XH/Operators` + `XH/FrickeSlash`; acyclic, cascade-free |
| U2 (1057) | **none**: its one premise is in `Analytic/QParamUnique` (a mathlib-only leaf) and its statement is `siegelFun` in `Defs/SiegelFunction` | **new** `SiegelUnit/Integrality.lean` | imports `SiegelUnit/Basic` + `Analytic/QParamUnique` |
| U2 (373) | `SiegelUnit/BernoulliWeight` is above all three premises | **insert** `SiegelUnit/BernoulliWeight.lean` | the level-Bernoulli weights *are* the peaked exponent's arithmetic |
| U2 (191) | `SiegelUnit/Basic` is above both premises | **insert** `SiegelUnit/Basic.lean` | the product law of `siegelFun` beside its slash law (MC-5a's module) |
| U3 (441, 684, 648) | **none**: the premises lie in `ComplexPlaceDictionaryOf` (the def module) and `X1/CoeffMap`, plus `AlgebraicCurve/Place/ValueDictionary` and `JqIntegralRatios`; no port module is above all | **new** `ComplexPlaceDictionaryAction.lean` | imports those four plus `Defs/ArithmeticGalois`, `XH/FunctionField`, `GaloisRep/Defs/ComplexConjugation` |
| U4 (373-XH, 168) | **none**: `TateSlots/Invariants` ∧ `Degree/FinrankAdjoinJqNModC` ∧ `Defs/TateFormal` ∧ `JqAnalyticModel` (and, for 168, `X1/Defs` + `X1/Integral`) | **new** `TateSlots/ToricPointDictionary.lean` | one module for both levels; imports the five plus `Defs/XHDiamondModL` (the §0.2 gate) |
| U5 (410) | **none**: `JqCoefficients` ∧ `ModularPolynomialUniquenessIrreducible` ∧ `PhiGenSplitsAnyField` | **new** `ModularPolynomialLevelTwo.lean` | the Φ₂ identification is above all three |
| U6 (166) | `X1/CoeffMap` is above its one premise | **insert** `X1/CoeffMap.lean` | the non-`_of_T_mem` sibling of the premise, in the module that hosts the `_of_T_mem` one |
| U6 (442) | **none**: six premises in `X1/FunctionFieldResidue`, `X1/FunctionFieldDegree`, `X1/CoeffMap`, `Degree/PhiDegree`, `JqIntegralRatios`, `NumberTheory/FrobeniusAtPlace` | **new** `X1/FunctionFieldIndex.lean` | the index/reflrank subject; `RelIndex/*` is *not* above the six |
| U7 (410-dh, 28) | **none**: `XH/Operators` ∧ `XH/Inputs` ∧ `X1/CoeffMap` for 410; `X1/DiamondCorrespondence` ∧ `X1/DiamondLift` ∧ `X1/HeckeCommute` ∧ `X1/HeckeModule` for 28 | **new** `HeckeDiamondCommute.lean` | top level, the diamond sibling of `HeckeCommuteBar.lean`; the one module holding an X₁ and an X_H row |
| U8 (734) | **none**: `JqIntegralRatios` ∧ `JqAnalyticModel` ∧ `QCoeffLevelOne` ∧ `QParamUnique` (+ the `Defs`) | **new** `Analytic/CuspDecay.lean` | the decay engine |
| U9 (611) | `TateSlots/Invariants` is above its one premise | **insert** `TateSlots/Invariants.lean` | the E₄³/Δ subject already lives there (MC-2c) |
| U10 (144) | **none** (`ModularPolynomialCoset` ∧ `Analytic/QParamUnique`); insertable: `QParamUnique` imports **no** port module | **insert** `ModularPolynomialCoset.lean` + one import | the coset subject; `QParamUnique` is a mathlib-only leaf, so no cycle |
| U11 (62) | **none** (`Period/QExpansionDiff` ∧ `Period/QExpansionDerivative` ∧ `Defs/HeckeDifferential`); `QExpansionDiff` already imports `QExpansionDerivative` | **insert** `Period/QExpansionDiff.lean` + one import | one new import (`Defs/HeckeDifferential`), no cycle |
| | | **8 new modules + 6 insertions** | |

**Every home is cascade-free.** The six insertion homes — `SiegelUnit/BernoulliWeight`,
`SiegelUnit/Basic`, `X1/CoeffMap`, `TateSlots/Invariants`, `ModularPolynomialCoset`,
`Period/QExpansionDiff` — have **zero** direct dependents in the port's import graph today, so
an insertion re-elaborates its own module only; the eight new modules have no dependents by
construction. That is the leaves' and defs' gift: the modules these rows belong in were created
in the last three waves and nothing has been built on them yet.

**No migration is owed.** None of the fourteen homes is on `spec/old_check_stmts.py`'s
`PORT_FILES` (checked; the four migrations of the last two waves — `Defs/TateFormal`,
`Period/QExpansionDiff`, `Analytic/QParamUnique`, `JqCoefficients` — were paid at landing).

**No row of the set cites another row of the set.** The stories are independent; the shared
pieces are the ported API above. The only cross-story sharing is the `U4` def module and the
`U7` module's two carriers.

## 4. Per-order traps

**MS-1 (U1, 1,176).** (i) The pin proves a 125-declaration engine: `frickeGL`/`val_frickeGL`/
`det_frickeGL`/`frickeGL_mul_mul_inv`/`le_conj_frickeGL`, `frickeForm`, `scalarGL`/`frickeSqConst`,
a `qC` block (18 declarations: `qC_mul`, `qC_add`, `qC_smul`, `qC_eq_zero_iff`, …), the
`*_mem_ratios` ratio-field block, then `DiaP`/`FrP`/`wAlg`/`wEquiv`: a transport of the
diamond action through the Fricke twist. Read the pin's `solution` (line 1148) last. (ii) **The
port's two `frickeGL`s are not the pin's**: the public one is `ALTraceIdentity.frickeGL M hM`
(`ModularForms/HeckeFrickeTrace.lean:44`) and `XH/FrickeSlash.lean:91` carries a **private**
`ModularCurve.frickeGL M [NeZero M]` that is just `ALTraceIdentity.frickeGL M (NeZero.ne M)`. From
a new module the private one is not importable: use the public one (or promote the `[NeZero M]`
spelling) and do not add a third copy. (iii) `port_advise`'s suspect `frickeGL → alGL` row is
this; `alGL` is the Atkin–Lehner matrix and is *not* the Fricke matrix. (iv) The row's statement
is a five-way existential (`w` plus three `SlashFrickeSpec`-style clauses) under a `hin`
hypothesis that is the U7-ish diamond existence; keep the binder shape verbatim — the pin's
`W` binder is `GL (Fin 2) ℝ` with an `hW` matrix equality, not a `SpecialLinearGroup` element.

**MS-2 (U7, 438).** (i) `28` is one line of Lean and 28 of assembly: `HeckeDiamondCommuteBar M`
unfolds to `heckeOperatorOneBar_comm ∧ heckeOperatorOneBar_comm_diamondOneBar ∧
diamondOneBar_comm`, all three ported — do not re-prove a commutation on the way. (ii) `410`
proves `diamondAutHBar_mul` first and `diamondHBar_mul` second; its engine is
`isDiamondAutHBar_unique` + `algEquiv_ext_of_ratios` + a `coeffMap`/`ofPowerSeries` coefficient
block, and it declares its own `_root_.XHDiaMul.conj_mem_GammaH` (a pin file-local namespace) —
keep that namespace, do not fold it into `ModularCurve`. (iii) The module holds one X₁ row and
one X_H row: the `JOne` and `JH` carriers differ, and `28`'s `hcomm` is the *unproved* Prop —
the module proves it, so it must import `X1/HeckeModule` (the def) but must not assume it.

**MS-3 (U9 + U10 + U11, 817).** (i) `611`'s 63 declarations include the level-14 witnesses
`g14`/`e14`, `natCard_stabilizer_I`/`_smul`/`_eq_two`, `orbit_trichotomy` and a three-way
`case_E`/`case_generic` split — the pin's `E`/`jf` abbreviations are `E₄³/Δ`; the port's
`TateSlots/Invariants` has the 254-row engine this row's one premise is, so read that first.
(ii) `611`'s statement is over `ℍ` with an explicit `ofComplex`; the port's `UpperHalfPlane`
coercions differ from the pin's `ℍ` (the MC-2 254 row hit this). (iii) `144`'s four
declarations are a `Periodic`/`MDifferentiable`/`IsBoundedAtImInfty` triple plus the `qExpansion`
identity; the insertion needs `import ModularCurve.Analytic.QParamUnique` (a mathlib-only leaf,
no cycle) and nothing else. (iv) `62` is six declarations, five of them the pin's own prelude
over `Ω[F⁄L]`; `Period/QExpansionDiff` already imports `QExpansionDerivative`, so the only new
import is `Defs/HeckeDifferential` (checked acyclic both ways).

**MS-4 (U2, 1,621).** (i) `1,057` is a 117-declaration analytic engine with **one** premise
(`tendsto_atImInfty_of_hasSum_qParam`): `fac`/`pp`/`map_fac`/`multipliable_fac`, the `Pabs`
absolute-convergence layer (`eval_sub_one_eq`, `norm_eval_sub_one_le`, `Mfam`,
`norm_coeff_pp_le_dom`, `summable_pow_succ`), the `qN`/`qParam` bridges, and the `CoeffInt`
structure (`CoeffInt.one/.mul/.expand/.one_sub_C_mul_X`). Treat it as one order and budget the
wall time; the port has none of it (`in port 0`). (ii) `373`'s 373 lines are 12 declarations
about the level-Bernoulli weights but its *content* is an inequality chain over `ZMod N`; its
three premises are in `SiegelUnit/BernoulliWeight` and its home is that module — do not move it
to `Integrality`. (iii) `191`'s statement is a two-clause conjunction (`∏` invariance and the
second clause the pin states after it) over `∏ r s, siegelFun … ^ (12·N·e r s)`; `e` is an
arbitrary exponent function, so the identity must be proved for every `e`, not the peaked one —
the peak comes later (`exists_peaked_exponent` is a *different* row). (iv) `SiegelUnit/Basic`
and `SiegelUnit/BernoulliWeight` both end with `private` preludes (the `qC`-style helpers); their
insertions must not lift privacy wholesale (recipe §5).

**MS-5 (U3, 1,773).** (i) The 161-line engine (`qL`, `Pres` with its `Pres.mul/.add/.const`,
`realize_*_eventuallyEq`, `meromorphicOrderAt_realize_eq`, `qL_ne_zero`,
`eventually_nhdsNE_coe_iff`) is written **once** and shared by the three rows; the pin duplicates
it in all three `S_` files (511 lines), which is the set's largest dedup block. (ii) `684` and
`648` have the *same* two premises (`realizeOf_eq_div` and `exists_modularForm_mul_qExpansion_eq_
…_of_T_mem`), and the second is `X1/CoeffMap`'s — so the new module is genuinely above both.
(iii) `648`'s statement mixes `UpperHalfPlane.J` (mathlib) with `arithmeticGalois F₀
complexConjAlgEquiv` (the leaves' `Defs/ArithmeticGalois`) and `GaloisRep/Defs/ComplexConjugation`;
the `•` on `D.pt` is the `arithmeticGalois` action, not a `MulAction` — read the pin's `smul_pt_eq`
family. (iv) `441`'s proof opens with `AlgebraicCurve.Place.exists_of_orderMap` (not an MC
module): the `Place` API is the leaves' — import it, do not re-derive.

**MS-6 (U6 + U8, 1,342).** (i) `442`'s 16 declarations are 13-in-port; the port credits are
real except `Φ_injective` (see §0.3) — read the two statements before accepting 198 lines.
(ii) `442`'s pin `S_` sets `maxHeartbeats 6400000` and `synthInstance.maxHeartbeats 1600000`:
the port has never needed a pin cap (FR-0067), so **do not copy either** without measuring; the
same applies to `734`'s 3.2M. (iii) `166`'s insertion into `X1/CoeffMap` must not be deduped against the
`_of_T_mem` twin it sits beside: the twin states `ModularForm Γ k` for `Γ : Subgroup SL(2, ℤ)`,
the new row states `ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k` with an added `[Γ.FiniteIndex]`
— same mathematics, different binder shape, so check the pair before `dedup.py` does. (iv) `734`'s own `Nice` predicate and `niceSubalgebra`
are the pin's local spelling of "integral over ℂ[j⁻¹]"; `port_advise`'s suspect `Nice →
WLight.PoleBounded` is a *different* object (a pole bound), so transcribe `Nice` locally and
keep it private.

**MS-7 (U4 + U5, 951).** (i) The def first: `IsDiamondPullbackModL` + `coe_apply_eq` (37 lines)
at the pin's names, in `ModularCurve/Defs/XHDiamondModL.lean`; the row's two-argument `ρ`
statement cannot be written before it. (ii) The promotion second: `qExpansion_E6_eq_map_mk` must
be **public and at `ModularCurve.…`, not `ModularCurve.EisensteinCube.…`** — the port's copy is
inside the `EisensteinCube` namespace (§0.2); the promotion also gives it its own `spec-pin:` and
turns a 34-line leaf into a ported node (10 project consumers). (iii) `168` and `373` both need
`qExpansion_E4_eq_map_eisenstein4` (public, same module) and `tendsto`-style `qExpansion` rewriting;
`373`'s statement's `ρ` binder plus the `IsDiamondPullbackModL` hypothesis is the long one — read
the pin's `solution` after transcribing the two `w₁`/`w₂` clauses. (iv) `410` (U5) is independent
of the gate: its four premises are `coeff_jNum_le_six`, `eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero`,
`natDegree_coeff_le` (MC-1b) and `PhiGen.splits_prime_of_isPrimitiveRoot`, all ported; it also
sets 3.2M heartbeats in the pin — measure before copying. (v) U5's `S_` declares `phiTwo_coeff`,
`natDegree_phiTwoC`, `qExpandand_evalAtJ_phiTwoC` — the level-2 polynomial's own coefficient
computation; `Defs/ClassicalModularPolynomials` has `phiTwo` but check which of the three the
port has before writing them.

## 5. The gates

As in the recipe §6, per order:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, every added
   declaration `ok` (or a manager-written `own:`/`pin:` row). New modules carry their own wire
   (the pin `S_` file plus the wrapper); insertions extend the host's.
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The order's own modules only, under `flock`/`timeout`: no tree build, no dependents, the
   module silent at the 200k cap. **The lock lives in the workspace** (`flock tmp/lean-build.lock`),
   not in `/tmp`: under the harness `/tmp` is per-call, so the playbook's `/tmp/lean-build.lock`
   serializes nothing and a `timeout 90` never fires before the harness's own 60 s cap (FR-0072).
   `SiegelUnit/Integrality` (MS-4) and `TateSlots/ToricPointDictionary` (MS-7) are the two to
   watch; `ComplexPlaceDictionaryAction` is the third if the 161-line engine is inlined rather
   than shared.
4. `dedup.py` / `move_dead.py` on each module; wrapper-over-engine `shape` clusters stay with the
   reason recorded. U3's engine must be **one** copy in **one** module (three `S_` files' worth of
   duplicate is the point of the story); U1's `frickeGL`/`qC` helpers must not become a third and
   fourth private copy of a ported public object.
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; **no `set_option maxHeartbeats`**
   copied from the pin (734's 3.2M, 442's 6.4M and 410-φ's 3.2M are the three to refuse); no
   worker writes a `spec/decl_markers.tsv` row.
6. The manager's lane of §0.2 is two items in two modules: the def (`Defs/XHDiamondModL.lean`,
   new) and the promotion (`X1/IntegralityJqNModC.lean`, `private` → public at the pin's name),
   each with its wire and its own build.
7. A `spec/` consumer zone per wave with a real cross-module composition (no `#check`s), whose
   error count is the deliverable metric: wave 1 composes the Fricke/Galois `w` with the ported
   `FrickeSlash`/`CohCarrier.Fricke` API and the `heckeDiamondCommuteBar` `Prop` with
   `heckeEvalOneBar`; wave 2 composes the dictionary's `pt`/`realizeOf` with the ported
   `Place.ValueDictionary` and the Siegel integrality with `SiegelUnit/Basic`'s product law; wave
   3 composes `IsDiamondPullbackModL` with `PhiGen`'s `Φ`.
8. The **surface gate** (recipe §5): after each module lands, drop `private` from its
   declarations, re-run `check_port`, and read the three numbers. MS-5 and MS-4 both start from a
   pin file whose prelude is `private`-written, so this experiment is where their checked surface
   is set; `MISMATCH` rows are the pin's own prelude copy re-spelled (keep private) and `MISSING`
   rows are port-side helpers.

## 6. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. the cut | **18 rows / 8,118 silo**, not the instrument's 20 / 8,178 | the 36 row is the 261 chain (deferred by the shelf note), the 24 row is unstatable (`TateModule`) |
| 2. the first wave | **MS-1 (U1), MS-2 (U7), MS-3 (U9+U10+U11)**, 2,431 silo / 2,060 net, as three worker orders | no manager lane, disjoint files, cascade-free homes |
| 3. the manager lane | **two items, 37 + 15 lines**, independent of wave 1 (§1.1): `Defs/XHDiamondModL.lean` and the `qExpansion_E6_eq_map_mk` promotion | only MS-7 waits on them |
| 4. the homes | **8 new modules, 6 insertions**; no migration | every home cascade-free (the six insertion hosts have zero dependents) |
| 5. the second wave | **MS-4 (U2), MS-5 (U3), MS-6 (U6+U8)**, 4,736 silo / 3,592 net | the three big new-module stories, gate-free, files disjoint |
| 6. MS-7 (U4+U5) | **dispatch after the manager lane** (or with wave 2 if a worker is free) | 951 / 780; the 37-line def and the promotion are its whole gate |
| 7. the 36 row and the 261 | **defer** (the shelf note's §8): the `ModularForm` Gamma₁ basis chain, ≈4.8k raw / ≈2.1k `S_` | not a row of this shelf |
| 8. the 24 row | **defer** to the padic-Tate-module programme: `Def_EllipticCurve_TateModule` (883 lines / 69 declarations) + D2's `rationalHeckeRepOne`; but note U7's 28-line row supplies its `hcomm` | it is the withheld pair's neighbourhood |
| 9. the withheld pair | **defer** unchanged (610 silo, `abelJacobiCard_genus`'s 144-node / 66k programme) | not a row of this shelf |

**No leaves block, no prunable subject, no false marker.** Unlike every previous scoping in this
family, this one has nothing to name and defer besides the three rows of §0.1: the leaves are
empty, `--selfcheck` PASSes, and the definition layer is one 37-line module plus one promotion.

## 7. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc2shelf.json
python3 frontier.py --selfcheck
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast \
  --unport AlgebraicCurve.weilReciprocity > build/mc2shelf-corr.json
python3 port_advise.py --with-defs <the 18 rows + rep_tateModule_jOne_comm> --json build/mc2-defs.json
python3 port_advise.py $(cat build/mc2-nodes18.txt) --json build/mc2-adv.json           # the whole-set price
python3 port_plan.py --json build/mc2-adv.json
# per story: port_advise.py <story --nodes> --json build/mc2-<story>.json; port_plan.py --json …
python3 twin_scan.py $(sed 's/--nodes /--node /' build/mc2-nodes18.txt)   # all 18 -> new
python3 twin_scan.py --node ModularCurve.qExpansion_E6_eq_map_mk            # -> twin-private
cd ../../lean && python3 spec/gate_scan.py --pin Definitions/Def_ModularCurve_XHDiamondModL.lean \
  --rows S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq
```

**The three measured numbers.**

1. **What the programme consumes**: 18 rows / 8,118 silo; **6,432 net new math lines** (8,118
   raw, 7,705 declaration, 552 duplicate, 413 boilerplate, 721 in-port) plus the manager's 37 +
   ~15 and one promotion, so ≈ **6,480 net**; seven orders in three waves; eight new modules and
   six insertions; no migration.
2. **The read it starts from**: `needed` **960 / 388,827** (corrected 962 / 389,188); ready
   81 / 20,199; leaves 262 / 64,874; MC ready **20 / 8,178** (corrected 19 / 8,142, this shelf
   18 / 8,118); MC leaves **0 / 0**; MC demand 126 / 65,781; the four FR-0044 withholdings (831);
   frontier **1,455 / 738,539**. All of these reproduce the post-leaves figures of
   [TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §7 exactly.
3. **What the shelf unlocks** (the forecast, not a measurement): every row below is a *direct
   consumer* of a shelf row on this graph, with its own `S_` line count. The shelf is the hinge of
   the family's next programme, not the end of it.

| shelf row | consumer (first of) | silo | the block it opens |
|---|---|---:|---|
| U1 (1176) | `exists_frickeAlgEquiv_xHFunctionFieldBar` | 1,105 | the Fricke `AlgEquiv` block: `…_galois_smul` 1,097, `frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul` 1,109, `heckePic0HBarTranspose_smul_diamondHBar_…` 1,098, the X₁×X_H triple 1,149 — ≈5.5k of Fricke, plus `JHNeronObjectAtP.…` 1,626 on the Tate side |
| U2 (1057) | `SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow` | 364 | the Siegel-product chain up to `exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral` (1,267) |
| U2 (191) | `exists_modularForm_gamma1_isIntegralQExp_…` | 1,267 | the same chain, from the product side |
| U3 (441) | `ComplexPlaceDictionaryOf.heckeDivHBar_single_pt` | 1,215 | the dictionary's Hecke/place layer, then `exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf` (817, and its `_slash` 796) |
| U3 (684/648) | the `pic0_complex_xH_quotient_periodLatticeOf` pair | 817 / 796 | the Pic⁰-complex dictionary |
| U4 (373-XH) | `exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j` | 1,071 | the Γ_H slot/`DiamondPullbackModL` dictionary |
| U4 (168) | `exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg` | 950 | the Γ₁ slot dictionary |
| U5 (410) | `isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five` | 660 | the Φ₂ coefficient subring |
| U6 (442) | `exists_xHDRModelAtP_atkinLehner_generic_chart` | 2,368 | the mod-ℓ X_HDR model block (2,368 / 1,819 / 1,544 / 1,474 / 1,465 …) |
| U6 (166) | `exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash` | 1,286 | the place-order/`slash` block (1,286 / 1,077 / 1,073 / 1,028) |
| U7 (410-dh) | `exists_decompositionCharacters_…_tateModule_jH_of_ordinary` | 1,457 | the Tate-module `jH` block |
| U7 (28) | `CuspForm.IsPrimitiveForm.exists_galoisRepAdic_linearIndependent_inertia_…` | 1,586 | the Tate-module `jOne` block (1,586 / 1,468 / 1,327 / 1,283 / 1,214 …) |
| U8 (734) | `exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC` | 233 | the θ^L cusp-form dictionary |
| U9 (611) | `ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer` | 1,115 | the ramification/cardinality block (1,115 / 1,112 / 553 / 448) |
| U10 (144) | `exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist` | 1,181 | the slot/`qTwist` dictionary (1,181 / 929 / 745) |
| U11 (62) | `le_span_setOf_logarithmic_of_frobPushDiffModL_surjOn` | 962 | the Frobenius-difference/cotangent block (962 / 866 / 587) |

**The forecast's shape.** This is a *keystone* shelf: 15 of the 18 rows have a direct consumer of
600–2,400 lines, and the three largest single unlocks are U6's 442 (the 2,368-line X_HDR chart),
U1's 1,176 (1,626) and U7's 28 (the Tate-module `jOne` block, 1,586) — 1,100–2,400 lines each
from rows of 28–1,176. The Fricke block after U1 (≈5.5k silo) is the
family's next shelf, and the shelf note's §7 already names it as such; it is **not** ready and is
not cut here.

## 8. What this programme does not do

- **The 261 chain and the 36 row.** The `ModularForm` Gamma₁ basis theorem, which
  [TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §8 defers at ≈4.8k raw / ≈2.1k `S_` lines. Whoever
  takes it starts with `exists_basis_gamma1_qCoeff_mem_range_ratCast`.
- **The Tate-module programme.** `Def_EllipticCurve_TateModule` (883 lines / 69 declarations),
  the withheld pair (610 silo, `abelJacobiCard_genus`) and the false ready `rep_tateModule_jOne_comm`
  (24) — one programme, [TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md)'s T1/T2.
- **The Fricke block after U1** (≈5.5k silo of `exists_frickeAlgEquiv_*` rows): the natural next
  scoping, not this cut.
- **The `X_HDRModelAtP` / mod-ℓ block** (U6's 442 consumers, 1,400–2,400 lines each): its own
  programme, gated on the Tate layer it shares with the withheld pair.
- **No surface promotion beyond the one of §0.2, no whole-tree build.** Every module is gated on
  its own build at the project cap; a tree build waits for a milestone and the user's agreement.

## 9. Wave 1 landed — the measured numbers (2026-10-28)

Six rows, four modules, one lane. The set records are [SET-MS1.md](SET-MS1.md),
[SET-MS2.md](SET-MS2.md), [SET-MS3.md](SET-MS3.md), [SET-MSDEF.md](SET-MSDEF.md); this section is the
one read over all of them.

**The read.** Instrument `needed` 960 / 388,827 → **954 / 386,396** (−6 nodes / −2,431 lines =
exactly the six rows' silo); corrected 962 / 389,188 → **956 / 386,757**. Ready 81 / 20,199 →
**77 / 18,418** (six left, **two entered**); `ModularCurve` ready 20 / 8,178 → **16 / 6,397**
(corrected 19 / 8,142 → 15 / 6,361); MC demand 126 / 65,781 → **120 / 63,350**; leaves unchanged
262 / 64,874, MC leaves **0 / 0**; frontier 1,455 / 738,539 → **1,461 / 740,970** (+6 / +2,431, no
extra declaration); `--selfcheck` **PASS**.

**Two rows became ready because of the wave** — the successors the shelf's §7 predicted, both
entering from a §MS-3 row:

| new row | silo | it became ready because of |
|---|---:|---|
| `ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex` | 347 | U10's `qExpansion_cosetTranslate_eq_cosetSubst` |
| `LevelN.exists_place_ord_jGen_le_two_three_level` | 303 | U9's `meromorphicOrderAt_…_card_stabilizer_div_two` |

So the shelf *grew* by 650 silo while it shrank by 2,431: net −1,781, and the two new rows are the
next cut's first candidates.

**What the wave wrote** — 7 files: 3 new modules (two from the wave, one from the lane), three
insertions, one edit:

| module | state | lines | declarations | checker |
|---|---|---:|---|---:|
| `ModularCurve/XH/FrickeGalois.lean` | **new** | 1,293 | 1 public + 130 private | 1 ok |
| `ModularCurve/HeckeDiamondCommute.lean` | **new** | 468 | 2 public + 21 private | 2 ok |
| `ModularCurve/TateSlots/Invariants.lean` | insert | +614 | 1 public + 63 private | 91 → 92 ok |
| `ModularCurve/ModularPolynomialCoset.lean` | insert | +149 | 1 public + 4 private | 16 → 17 ok |
| `ModularCurve/Period/QExpansionDiff.lean` | insert | +42 | 1 public + 2 private | 3 → 4 ok |
| `ModularCurve/Defs/XHDiamondModL.lean` | **new** (lane) | 80 | 2 public | 2 ok |
| `ModularCurve/X1/IntegralityJqNModC.lean` | edit (lane) | — | 1 promoted | 3 → 4 ok |

**Nine checked declarations** (the six row headlines plus the lane's two definitions and the
promoted theorem): **0 mismatch, 0 missing, 0 own**; all nine `#print axioms` read
`[propext, Classical.choice, Quot.sound]` (re-run by me in one scratch file, not taken from the
reports); the seven module builds are green; every edit loop is silent at the 200k cap;
no `set_option` beyond the project-universal `autoImplicit false`; no `sorry`/`admit`/`axiom`/
`native_decide`; no migration; no marker row.

**The consumer zone** is [spec/ModularCurveReady1Consumer.lean](../../spec/ModularCurveReady1Consumer.lean),
three zones, **0 errors**:

- **A `[fricke]`** — MS-1's second conjunct alone (the shape the `exists_frickeAlgEquiv_*` successors
  consume) and the identity-Galois corollary `diamondAutHBar ⟨1⟩ (w x) = w x`;
- **B `[diamond]`** — `diamondHBar_mul` as `Function.comp` and iterated over a triple, and the
  28-line `heckeDiamondCommuteBar` used as the *hypothesis* of `heckeEvalOneBar`, giving a ring map
  `HeckeAlgOne →+* End (J₁(M))` whose images of two arbitrary elements commute;
- **C `[tail]`** — `diffQExp` from `qExpansionDiffAlong` (the direction the `Period` rows need), and
  the trivial coset translate `(1, 0, 1)`, which fixes the level-1 q-expansion.

**One scoping correction found while the wave-2 briefs were being written (2026-10-28).** U8's
engine is *not* new work: the pin's 734 `S_` file lives in namespace `ANb`, and
`ModularCurve/Analytic/ANb.lean` (324 lines) is that namespace already (`Nice`, `niceSubalgebra`,
`toC`, `qexpHom`, `ψ`, `nice_of_modularForm`, `ofMF`, `𝔞`). `port_advise`'s 160 in-port lines for
U8 were this block; the brief's first draft told the worker to transcribe it locally, which would
have been a third `Nice` (the port also has `ModularCurve.Nice` in `X1/FunctionField.lean:530`, a
different predicate over the same arguments). The brief was corrected before dispatch; U8's net is
therefore below the §0.3 ≈551 (the decay part only).

**The frictions the wave hit**: FR-0071 (the private-shadow ported test — this is the promotion's
mechanism, and its 650-line `AlgebraicCurve` instance is the larger one), FR-0072 (the `/tmp` build
lock is a no-op under the harness, and a foreground `timeout 90` never fires: use
`flock tmp/lean-build.lock` and repo-local logs), FR-0073 (`move_dead.py` drops non-ASCII identifiers,
so `Δ_smul` reads dead). All three are in [../../logs/frictions.md](../../logs/frictions.md).

**What wave 2 inherits.** Its three briefs need no re-pricing: the shelf's §0.3 stands (U2 1,557,
U3 1,130, U6+U8 905 net). Three corrections to carry into them, all from this wave: (i) a needmods
scan covers *port* modules, not the mathlib surface a proof adds — U9 needed three mathlib imports
the brief had ruled out (SET-MS3 §3.1); (ii) the build lock is the workspace's (FR-0072); (iii) the
in-port credits must be hand-read where they are large: MS-2's reuse was real (11 declarations
imported, not restated), while MS-1's `coeffMap_coeffEmb` credit pointed at a statement outside its
import closure and in a specialised (`≃ₐ[ℚ]`) form, so the general form was re-proved privately
(SET-MS1 §2.9).

### 9.1 The surface gate — the wave's checked surface is ~3× what the wire shows

The recipe §5's **surface gate** (drop `private`, re-run `check_port`, read the three numbers) was run
over every module the wave touched. The experiment is parse-level and cheap: copy the module with
`private` stripped and check the copy against the same wire.

| module | wired surface (today) | with `private` dropped | reading |
|---|---:|---|---|
| `XH/FrickeGalois.lean` | 1 ok | **118 ok** / 1 mismatch / 6 missing | 118 of the pin's 125 declarations are pin-faithful *public* statements; 1 mismatch is a prelude copy re-spelled, the 6 missing are v4.34 adapters — those seven stay private |
| `TateSlots/Invariants.lean` | 92 ok | **155 ok** / 0 mismatch / 0 missing | the U9 `JMultiplicity` engine is the pin's public surface, statement for statement |
| `HeckeDiamondCommute.lean` | 2 ok | **23 ok** / 0 mismatch / 0 missing | the whole `XHDiaMul` engine is pin-faithful public surface |
| `ModularPolynomialCoset.lean` | 17 ok | **20 ok** / 1 mismatch | the `CosetTranslate` engine, one re-spelled prelude |
| `Period/QExpansionDiff.lean` | 4 ok | **11 ok** / 0 mismatch | |
| `Defs/XHDiamondModL.lean` | 2 ok | 2 ok (nothing private) | |

So the wave's checked surface is ≈**330** declarations, not the 118 the wire shows, and the
transcription is far more faithful than the wire proves. The recipe's rule is to **promote what is
`ok`** and keep only the `mismatch` (a local re-spelling of the pin's own prelude) and `missing`
(port-side adapter) private. That is a mechanical pass — `sed 's/^private //'`, rebuild, re-check, re-record — and it changes
nothing mathematically but multiplies the evidence, and it makes the Fricke engine importable for the
block that follows (the ≈5.5k-silo Fricke shelf would otherwise re-prove 118 declarations that are
already here).

**The pass was executed the same day (2026-10-28), on the wave-1 modules.** What was promoted, and
what the checker now reads:

| module | wired surface | promoted | after | kept private (and why) |
|---|---:|---:|---:|---|
| `XH/FrickeGalois.lean` | 1 | **116** | **117 ok / 0 / 0** | 8: `frickeGL` (mismatch — the `ALTraceIdentity` binder shape), `mapGL_coe`/`mapGL_mul'`/`mapGL_inv'`, `coeffMap_injective'`, `wfun`/`wfun_def` (v4.34 adapters, no pin source), `LBC` |
| `TateSlots/Invariants.lean` | 92 | **61** | **153 ok / 0 / 0** | none |
| `HeckeDiamondCommute.lean` | 2 | **21** | **23 ok / 0 / 0** | none |
| `ModularPolynomialCoset.lean` | 17 | **3** | **20 ok / 0 / 0** | `hasSum_laurent` (mismatch, direct-name) |
| `Period/QExpansionDiff.lean` | 4 | **7** | **11 ok / 0 / 0** | none |
| `SiegelUnit/Integrality.lean` | 1 | **114** | **115 ok / 0 / 0** | `ArchSkel.tprod_Pc_eval` (mismatch: the v4.34 `(_hN : 0 < N)` binder) |
| `SiegelUnit/Basic.lean` | 10 | **49** | **59 ok / 0 / 0** | the 14 `SiegelTransport` adapters (v4.34 re-spellings) |
| `SiegelUnit/BernoulliWeight.lean` | 68 | **11** | **79 ok / 0 / 0** | `solution` (mismatch: the `[Fact (1 < N)]` wrapper, recorded in SET-MS4) |

The wave's checked surface is therefore **567** declarations instead of 118, every one of them a
pin-faithful statement with `0 mismatch / 0 missing / 0 own`; each module elaborates silently at the
200k cap, its build is green, and `dedup.py --module … --within --tier shape` reports 0 clusters for
all eight (the one exception is `Invariants`' pre-existing `main`↔`solution` wrapper pair, 14 lines,
already recorded in [SET-MS3.md](SET-MS3.md); MS-4's own `Integrality` has one pin-inherited
duplicate pair, 10 lines). The header prose of each touched module records the
promoted/kept split, so the next reader knows which declarations are the port's and which are
adapters.

The four wave-2/3 briefs were written before this measurement and repeat the wave-1 instruction
("the engine stays `private`, the wire is the headlines"). They are **not** wrong under the current
convention, but the reviewer's surface pass will promote the same way in each of them: expect the
same ~3× factor in `ComplexPlaceDictionaryAction`, `SiegelUnit/Integrality` and the toric module.

## 10. Landed — all 18 rows (2026-10-28)

The programme is complete: **18 of 18 rows**, six orders plus the manager lane, every row with its
brief, its checker verdict, clean axioms, a green build, zero warnings and a dedup count.

| order | rows | record |
|---|---|---|
| MS-1 Fricke–Galois | 1176 | [SET-MS1.md](SET-MS1.md) |
| MS-2 Hecke–diamond laws | 410-dh, 28 | [SET-MS2.md](SET-MS2.md) |
| MS-3 j-order / coset / diffQExp | 611, 144, 62 | [SET-MS3.md](SET-MS3.md) |
| manager lane | the gate + the promotion | [SET-MSDEF.md](SET-MSDEF.md) |
| MS-4 Siegel unit | 1057, 373, 191 | [SET-MS4.md](SET-MS4.md) |
| MS-5 complex-place dictionary | 441, 684, 648 | [SET-MS5.md](SET-MS5.md) |
| MS-6 ratio dictionary + cusp decay | 166, 442, 734 | [SET-MS6.md](SET-MS6.md) |
| MS-7 toric dictionary + Φ₂ | 373-XH, 168, 410 | [SET-MS7.md](SET-MS7.md) |

**The read** (one pass, all 18 rows in the tree): `needed` **960 / 388,827 → 942 / 380,709**; ready
81 / 20,199 → **68 / 13,294**; the `ModularCurve` shelf 20 / 8,178 → **7 / 1,273**; MC demand
126 / 65,781 → **108 / 57,663**; frontier 1,455 / 738,539 → **1,473 / 746,657**; leaves unchanged at
262 / 64,874 (the family still has **no** `ModularCurve` leaves). The whole shelf is 5,687 lines of
the 2,431-line wave-1 drop plus 4,953 lines of the rest, less the 28-line successor that entered —
see the figure table's arithmetic.

**Five successors entered the shelf, and they are the next cut**: 364
(`SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow`), 347
(`ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex`), 303
(`LevelN.exists_place_ord_jGen_le_two_three_level`), 171
(`transcendental_and_finiteDimensional_adjoin_laurentBaseChange_…`), 28
(`ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j`). The other two shelf rows are the
known non-rows: the 36 chain (§0.1) and the 24 Tate-module row.

**What the wave wrote.** 15 port files touched: **11 new or edited modules** in the orders
(`XH/FrickeGalois`, `HeckeDiamondCommute`, `TateSlots/ToricPointDictionary`,
`ModularPolynomialLevelTwo`, `X1/FunctionFieldIndex`, `Analytic/CuspDecay`,
`ComplexPlaceDictionaryAction`, `SiegelUnit/Integrality` — new; `TateSlots/Invariants`,
`ModularPolynomialCoset`, `Period/QExpansionDiff`, `SiegelUnit/Basic`, `SiegelUnit/BernoulliWeight`,
`X1/CoeffMap` — inserted into; `Defs/XHDiamondModL` and `X1/IntegralityJqNModC` — the lane).

**The checked surface, after the §9.1 pass**: ≈**700** declarations across the wave's modules, every
one `ok` against the pin, from 118 before the pass. The per-module numbers are in §9.1.

**The consumer zone** ([spec/ModularCurveReady1Consumer.lean](../../spec/ModularCurveReady1Consumer.lean))
has **six zones, 0 errors**: A `[fricke]`, B `[diamond]`, C `[tail]`, D `[toric]`, E `[ratio]`,
F `[decay]` — a real cross-module composition for every order in the programme.

**The one gate not met, named**: 442's `transfer_finrank` needs ≈240k heartbeats against the port's
200k edit-loop discipline (the pin capped it at 6.4M + 1.6M). The module builds, checks and warns
clean; the localisation and the restructuring move are in [SET-MS6.md](SET-MS6.md) §2 and FR-0074.
