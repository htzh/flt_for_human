# SET 6 — the `AlgebraicCurve` shelf after SET 5: twelve rows, four stories, and the two rows the `--ds` read cannot see

**Status (2026-10-27): landed and green.** All five lanes are in: 12 rows consumed, 11 modules
created or edited, every module `0 mismatch / 0 missing` and silent at the 200k cap, every
headline axiom-clean, the consumer zone at 0 errors, and the shelf re-read (§1.2 and §8 carry the
numbers). The two rows of §0.1 stay deferred, as decided (call 1). The note began as the run brief
for the set — cut from the D–S ready shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) — and now
records the landing as well. §0 the read and the delta; §0.1 the instrument failure that takes two of the fourteen rows out of the
set; §0.2 the definition layer (none this time); §0.3 what the pricing instruments say; §1 the
cut; §2 the rows; §3 the homes, checked against the import direction; §4 the manager's ground
prep; §5 per-order traps; §6 the gates; §7 the calls this brief asks the reviewer to settle;
§8 reproduce, the measured numbers and the forecast; §9 what the set does not do.

No tree build was run for this pass (the AGENTS rule); the read is `frontier.py`'s cached graph
(5.9 s), the pricing is `port_advise`/`port_plan` (text only, no Lean), and the two migration
probes of §4 ran `spec/check_port.py` on copies in `tmp/`, which is untracked.

| figure (this read) | value |
|---|---:|
| ready candidates, all namespaces | 96 |
| leaves, all namespaces | 296 |
| `AlgebraicCurve` rows | **14** (14 ready + 0 leaves) |
| their silo lines | **4,000** |
| of which cuttable | **12 rows / 3,779 silo** |
| of which deferred (§0.1) | **2 rows / 221 silo** |
| net new math lines, 12 rows (`port_plan`) | **1,449** (1,419 after call 5) |
| `needed [F terminal]` | 1,040 nodes / 410,470 lines |

## 0. The read, and what moved since SET 5

Canonical, as the recipe requires:

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/frontier-set6.json
```

Cone 2,103 / 982,173; avoided 140 / 74,620; literal `needed` 1,053 / 413,945; **`needed [F
terminal]` 1,040 / 410,470**; frontier 1,368 / 715,962 (1,050 / 568,228 in the cone); 96 ready
candidates and 296 leaves. `AlgebraicCurve` demand 75 / 26,044 — and **not one `AlgebraicCurve`
leaf**: the leaves block that SET 4 missed and SET 5 consumed is empty for this family.

**The delta against SET 5's landing read is zero on every figure.** SET-5.md §1.3's "after"
column is exactly 1,040 / 410,470, 96 ready, 296 leaves, 14 `AlgebraicCurve` rows / 4,000 silo and
demand 75 / 26,044. So this is a re-read with no movement: the tree is SET 5's (the uncommitted
wave on top of `7cce1da`), and the fourteen rows are precisely the "fourteen rows became ready
because of the set" that SET-5.md §1.3 lists. That identity is the check that the shelf is
SET 5's own successor shelf, not a stale one.

**What the 14 rows are, in one reading.** Four are the Weil-reciprocity/pairing family that SET
5's `FunctionField` pair uncovered (`weilReciprocity` and the three `WeilDatum` laws); four are
the constant-field-extension successors of BC4/CFE2 (`cfe_isAlgClosed`, `map_corr`,
`constantsAreBase`, and — by its engine — `evalFun_algebraMap_pushforward`); one is the trace sum
(`sum_ord_smul`); three are tails of engines already landed (`laurent`, `lspace`, `corr_smul`);
and two are the ℂ rows of §0.1.
Seven of the fourteen are priced at under 60 net new lines each; two are priced at zero or nearly
zero. This shelf is the cheapest in the column so far, and the reason is measurable (§0.3): the
port's earlier waves transcribed 4,425 of the pin lines these rows name.

### 0.1 The instrument failure — two rows cite an unported, *pruned* premise

The recipe's §1 calls `premises_unported` "zero by definition in a ready set". That is the
definition the tool implements, and it is not the truth. `frontier.py:842-845` computes

```
premises_unported = premise_counts(cites, counts, exclude=ported)
```

where `counts` is keyed by `need` — the demand with the **avoided set already removed** by
`--ds`. An avoided premise is therefore not a key, is not counted, and the readiness test
(`needed == 1`) passes. A row that must traverse the pruned subject to be *proved* is printed
exactly like a row whose premises are all ported.

The audit is two lines of the tool's own API: for each row, take its pin `S_` file's `import
Theorems.Thm_*` lines and test each premise for frontier membership **and** for
`ds_prunable` patterns/`EXTRA`. On this shelf:

| shelf | rows | rows with an unported R premise | silo |
|---|---:|---:|---:|
| ready | 96 | **4** | **831** |
| leaves | 296 | 0 | 0 |

The four are:

| row | silo | unported avoided premise | lines |
|---|---:|---|---:|
| `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` | 126 | `Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice` | 193 |
| | | `exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice` | 871 |
| `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` | 95 | `Pic0.natCard_torsion_prime_eq_pow_genus_complex` | 61 |
| `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` | 327 | `Pic0.abelJacobiCard_genus` | 193 |
| `ModularCurve.moduleFinite_padicInt_tateModule_jOne` | 283 | `Pic0.abelJacobiCard_genus` | 193 |

Both `AlgebraicCurve` rows are the complex-analytic Jacobian's: the first *is* the Abel–Jacobi
divisibility argument (`abelJacobiDiv`, `pathPeriodLattice` are its two engines), the second
consumes the "prime torsion has cardinality `p^(2g)` over ℂ" count. Neither can be ported
without porting the prunable subject's interface — which is the RR column's phase 3, and which
this column's read exists to *avoid*. They are therefore **deferred, not failed** (§9), and the
set is cut on 12 rows / 3,779 silo.

This is FR-0044. The other 12 rows pass the audit with no unported premise at all, avoided or
not, and no premise held only `private` in the port.

**The audit is now in the tool (2026-10-27).** `frontier.py --ready` applies it: a candidate
whose own proof directly cites an unported premise in the avoided set is withheld from the
shelf, reported in the ready block's `withheld` list with the premises that block it (JSON
`ready_rank.withheld`, per-row `premises_pruned`). On the tree as it stands the same read is
**86 rows**, with the four above (831 silo) in `withheld` under exactly the premises tabled
here; the 96-row figures in this section are the read as it stood when the set was cut, when
the audit was manual. One correction to the record: `premises_unported` was never zero for these four
(the read shows 2 / 1 / 1 / 1) — the field already counted an avoided direct premise, but the
readiness test ignored it and the text shelf does not print it. The fix is the guard, not a
count. [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
now tells the next pass to quote the withheld block next to the shelf.

### 0.2 The definition layer — no gate this time

`port_advise --with-defs` puts 13 pin `Definitions/Def_*.lean` modules in the closure of the 14
rows (`AdelicIndex`, `Correspondence`, `DifferentialPushPull`, `DivisorClassGroup`,
`DivisorPushPull`, `IsCurveOver`, `PlaceEvaluation`, `RatFuncPlaceInfty`, `RatFuncPlaces`,
`RegularDifferentials`, `Repartitions`, `WeilDatum`, `ModularCurve_AtkinLehner`). All thirteen are
already ported, at 0–11% not-in-port per file; the residue is three *private* helpers of
`Def_AlgebraicCurve_DivisorPushPull` (`comap_algebraMap_ne_top`, `exists_ord_pos`,
`mem_comap_iff_ord_nonneg`) that `Defs/PushPull.lean` carries publicly under the same statements
and that no row's proof consumes. Unlike SET 5 there is **no definition module to create**, so
the set has no definition gate.

### 0.3 What the pricing instruments said, and the two places they are blind

The whole set: **417 substitutions (≈4,425 lines) already in the port** — 408 byte-identical, 9
identical up to binder spelling, 9 of them held `private`; **13 names proved in ≥2 target files
(≈99 removable lines)**; **no same-name/different-statement pair among the headlines**, so no
namespace split. But the two biggest rows are mispriced by the name- and statement-anchored
tiers, in opposite directions, and both corrections decide the cut:

- **`RationalFunctionField.weilReciprocity` is a 12-line theorem, not a 1,273-line one.** The
  pin ships the same 1,260-line dictionary **twice**:
  `S_AlgebraicCurve_RationalFunctionField_weilReciprocity.lean` (1,273 ln) and
  `S_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap.lean` (1,263 ln). A file
  diff is **one `p2m_export` line and the final `solution`**: the two files' declarations are
  identical. The port transcribed the second file as `P1/Dictionary.lean` (1,228 lines), and the
  name/statement tiers match 64 of the 70 declarations there. Of the seven it cannot see — it
  reports 64 substitutions, one name occurring twice — two are public at the pin's names in
  `PrincipalDivisors/RatFuncDegree.lean`, three are in `P1/Dictionary.lean` under spellings the
  name tier misses (`principalDivisor_apply`, `placeEquivOption_symm_some`,
  `placeEquivOption_symm_none`), and one is private there. **The only genuinely new declaration is
  `solution`: a 9-line proof.** This is the recipe §2 "the pin's own duplication is the story", read as a *size*
  correction rather than a dedup one.
- **`Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed` is a
  generalisation, not a transcription.** Its 620-line file is the pin's 615-line char-0 file with
  a **three-line diff**: `[CharZero K]` dropped, `linearIndependent_of_constantFieldExtension`
  replaced by `…_of_isAlgClosed`, and one `open` line. The port holds the char-0 development in
  `Place/ConstantFieldExtension.lean` (the `ConstantFieldPlaceLift` block: `Psi`, `pureW`,
  `rangePsi`, `fracPsi`, `decomp`, `sum_ne_not_mem_span`, `ne_zero_and_inv_mem_of_add`, …), so 24
  of the 26 declarations are already there. The row's content is the **char-free statement** over
  a proof the port already has — the FR-0041 pattern (a port theorem with stronger hypotheses is
  invisible to a statement-anchored tier), and the port's own `IsCurveOver/ConstantFieldExtension.lean`
  already sets the precedent by stating the general `linearIndependent_of_constantFieldExtension_of_isAlgClosed`
  and *deriving* the char-0 one (line 699).
- **The one shared prelude is one block, and it has a public pin home.** The two small pairing
  files (`addLeft_pairing`, `pairing_ne_zero`) share 8 private support lemmas (41 lines, the
  largest "port once" cluster). Their pin-canonical public copies live in
  `Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean`, not in the `S_` files:
  a probe of the 8 statements plus the 2 headlines against that file and the two `S_` files
  checks **10 ok / 0 mismatch / 0 missing**. So the block is written **once**, publicly, at the
  pin's names (§4.3), and the big pairing row's `_i`-suffixed copies are imported rather than
  restated.
- **No binder problem worth a split.** The 19 binder-variant names are prelude spelling drift
  (`mem_of_ord_nonneg`, `ord_nonneg_of_mem`, `mem_iff_ord_nonneg`, `deg_eq_one_of_isAlgClosed`,
  `ord_placeInfty`, …); take the `Theorems/` wrapper's binders throughout. The one that matters
  in practice is `exists_ord_mul_eq_order_of_algHom_laurentSeries`, whose `S_` copy hides `K` in a
  section variable while the wrapper binds it explicitly — the row is its own headline, so the
  worker states the wrapper's text (§5, TL).

## 1. The cut — four worker orders and one manager lane

| lane | story | rows | silo | net new | homes | gate |
|---|---|---:|---:|---:|---|---|
| **M** | the ground: the char-free place lift, the constants promotion, the shared `WeilDatum` block, and the `P1/Dictionary` migration | 2 | 668 | ≈50 + 205 moved | `Place/ConstantFieldExtension.lean`, `Genus/ConstantFieldExtension.lean`, `Defs/WeilDatum.lean`, `P1/Dictionary.lean` | 4 wire touches, 2 registry deletions, 1 generalisation, 1 promotion, 1 migration |
| **WR** ([order](WORKORDER-WR1-weil-reciprocity.md)) | the Weil reciprocity theorem on ℙ¹ and the Weil pairing's laws | 4 | 1,857 | **512** | insert `P1/Dictionary.lean`; insert `Defs/WeilDatum.lean`; **new** `Pic0/WeilPairing.lean` | — |
| **TS** ([order](WORKORDER-TS1-trace-sum.md)) | the trace sum: `∑_P ord(g) • y_P^* ω = 0` for a regular `ω` over a finite cover | 1 | 629 | **423** | **new** `ResidueTheorem/TraceSum.lean` | — |
| **CFE** ([order](WORKORDER-CR1-correspondence-cfe.md)) | the correspondence on regular differentials under a constant field extension | 1 | 309 | **252** | **new** `Differential/CorrespondenceRegularCFE.lean` | — |
| **TL** ([order](WORKORDER-TL2-tails.md)) | the tails: the Laurent-series realisation, `ell` growth, the `evalFun` pushforward law, the correspondence's semilinearity | 4 | 316 | **221** | insert `Place/LaurentSeriesModel.lean`, `Defs/AdelicIndex.lean`, `Place/EvalAtNorm.lean`, `WeilExchange/GaloisRamification.lean` | — |

Totals: **12 rows / 3,779 silo / 1,419 net new** after call 5. The instrument's per-lane reads
were 512 (WR) / 423 (TS) / 263 (CFE3) / 251 (TL2) = **1,449**, with the M lane's two rows (the
char-free lift, 11 lines net, and the constants promotion, 0) counted inside CFE3; the cut moves
that 11 to M and drops the tail lane's `cd2_control` (−30), so the **worker lanes carry 1,408**
(512 / 423 / 252 / 221 — WR's 512 already counts the shared `WeilDatum` block once, 41 lines,
which M writes) and **M carries 11**. 42 new public declarations and 19 private helpers in the
four worker orders, 10 manager declarations (8 of them the shared block), 1 generalisation, 1
promotion, 1 migration, 3 new modules (`Pic0/WeilPairing`, `ResidueTheorem/TraceSum`,
`Differential/CorrespondenceRegularCFE`) and 11 wire touches (3 new wires, 8 extensions).

**The four worker orders' edits are file-disjoint** (§3 has the full home table) and only the
build lock is shared. Three orders *read* a module another order appends to — TS reads
`Defs/AdelicIndex.lean` and CFE reads `WeilExchange/GaloisRamification.lean` (through
`WeilExchange/Transport.lean`), both TL's, and TL's `EvalAtNorm` insertion reads
`P1/Dictionary.lean`, WR's — but no order needs the declaration the other appends, and every
order edit is additive. The one non-additive edit is M's: the char-0 theorem's proof body in
`Place/ConstantFieldExtension.lean`, which three orders import, so M runs before dispatch, and
no order changes an existing statement or proof body. That is the criterion SET 4/5 dispatched
on; two orders editing *one* module would still have to be serialised, and there is none.

### 1.1 The manager lane, as landed (2026-10-27)

| item | module | measured |
|---|---|---|
| the char-free place lift (§4.1) | `Place/ConstantFieldExtension.lean` | the char-0 theorem's 204-line proof is now the char-free statement `Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed`; the char-0 headline is a 6-line corollary of it; the shared linear-disjointness lemma `ConstantFieldPlaceLift.sum_ne_of_not_mem_span` is generalised (engine swapped, `[CharZero K]` dropped) — **48 ok / 0 mismatch / 0 missing**, builds silent, both headlines axioms-clean |
| the constants promotion (§4.2) | `Genus/ConstantFieldExtension.lean` | public at `AlgebraicCurve.constantsAreBase_of_isAlgClosed_of_transcendental`, 4 lines over the private engine — **18 ok / 0 / 0**, builds |
| the `WeilDatum` support block (§4.3) | `Defs/WeilDatum.lean` | the 8 lemmas + `import Defs.PlaceEvaluationAlgebra` + the `Def_…Divisorial` wire — **13 ok / 0 / 0**, builds |
| the `P1/Dictionary` migration (§4.4) | `P1/Dictionary.lean` | 26 `spec-pin:` lines, `PORT_FILES` row deleted, `SOURCES` rows kept — **69 ok / 0 / 0** before the capstone (the probe's prediction exactly) |
| the stale registry row (§4.5) | `Defs/AdelicIndex.lean` | `PORT_FILES` row deleted (it was already wired: 69 ok / 0 / 0) |

One finding from the generalisation: the port's char-0 proof did **not** use the
`linearIndependent_of_constantFieldExtension` engine at all (its prelude's linear-disjointness
lemma did, at one call, and its final step used the char-0 valuation-subring dictionary). The
char-free statement therefore swaps **two** things, not the pin's one: the engine in
`sum_ne_of_not_mem_span`, and the final `exists_toValuationSubring_eq_comap_ringHom` →
`_of_isSeparable` at a `K'`-separable transcendental. Both are the pin's own isAlgClosed file's
route; the pin's "three-line diff" is true of the prelude only.

### 1.2 The landing record, and the set's numbers

| lane | modules | added | checker before → after | build | axioms |
|---|---|---|---:|---|---|
| WR | `Defs/WeilDatum.lean` (+85), `P1/Dictionary.lean` (+53), **new** `Pic0/WeilPairing.lean` (432) | 2 + 1 + 24 (10 public / 14 private) | 13 → **15**; 69 → **70**; 0 → **10**, all / 0 / 0 | silent | four headlines clean |
| TS | **new** `ResidueTheorem/TraceSum.lean` (509) | 16 public | 0 → **16 ok** / 0 / 0 | silent | clean |
| CFE | **new** `Differential/CorrespondenceRegularCFE.lean` (359) | 4 public | 0 → **4 ok** / 0 / 0 | silent | clean |
| TL | `Place/LaurentSeriesModel.lean` (+163), `Defs/AdelicIndex.lean` (+101), `Place/EvalAtNorm.lean` (+72), `WeilExchange/GaloisRamification.lean` (+22) | 7 + 1 + 2 + 1 | 6 → **8**; 69 → **70**; 27 → **28**; 10 → **11**, all / 0 / 0 | silent | four headlines clean |

The tree carries **+1,861 lines** over 8 edited modules and 3 new ones (1,300 of them in the new
modules; the rest headers, docstrings, wires and the manager's block), against the 1,419 net new
the instrument priced for the declarations. The consumer zone is
[../../spec/AlgebraicCurveSet6Consumer.lean](../../spec/AlgebraicCurveSet6Consumer.lean) — four
zones, **0 errors**: the ℙ¹ capstone feeding the pairing theorem, the trace sum at a
correspondence, the lifted correspondence of a regular differential, and a Laurent embedding's
positive-order elements landing in a valuation ring.

**The surface experiment, run at review on `Pic0/WeilPairing.lean`.** Dropping `private` from its
14 private declarations and re-running `check_port` gives **24 ok / 0 mismatch / 0 missing** — every
one is a pin-faithful statement. They nevertheless stay `private`: the pin itself states them
`private` (they are its `_i`-suffixed local copies), so this is the one module of the set where the
surface gate's "promote every `ok`" does not apply — the rule is about declarations the pin states
*public* that a worker buried. The two other new modules have no private declarations; of the two
insertions, `Defs/WeilDatum.lean`'s block is public by the pin's own `Def_` file, and
`Place/LaurentSeriesModel.lean`'s private headline is private in the pin.

**Deviations held for review** (none changes a statement; every `check_port` hash matched):

- WR's `P1/Dictionary.lean` states the capstone at `_root_.AlgebraicCurve.RationalFunctionField.weilReciprocity`
  inside the namespace: the wrapper's fully-qualified name, spelled once (a bare
  `theorem AlgebraicCurve.…` there doubles the prefix). The checker *prints* the `_root_.` segment
  and matches the statement at the wrapper.
- WR's `Pic0/WeilPairing.lean` carries one private helper the order's list omitted,
  `prod_zpow_eq_zpow_sum_i` (needed by `evalFun_algebraMap_of_degree_eq_zero_i`); it is private in
  the pin too.
- TS imports `coeffLin_apply`/`coeffDer_apply` from `Differential/RegularDiffs.lean` instead of
  restating them (16 new declarations, not 18), and transcribes the pin's 46-line
  `residueTheorem_of_curve` because `ResidueTheorem/GeneralFromK.lean`'s headline needs an instance
  block (`Algebra (RatFunc E) FE`, `IsSeparable`, `DCoordGenerates` …) that is not in scope at the
  row's binders — the 46 lines *are* that block's construction.
- CFE uses the char-0 comap theorem (not the `_of_isAlgClosed`) and drops the pin's
  `attribute` walls; its two linter-only options are the cone's convention.
- TL drops `cd2_control` (call 5) and `liftToHahn_apply` (outside the six-declaration list; its `rfl`
  step is inlined), and pins `attribute [local instance 2000] HahnSeries.instAlgebra` for the
  `HahnSeries` algebra diamond (**FR-0045**).

## 2. The rows

`silo` is the pin `S_` file's line count (the rank key); `prem` the pin's `import Theorems.Thm_*`
premise count; `lev` cone / project consumers. All 14 were priced with `needed = 1`; the two
deferred rows are the ones whose `premises_unported` is not zero (2 and 1 — §0.1, and the fix
recorded there).

| lane | node (`AlgebraicCurve.` dropped) | silo | prem | lev | note |
|---|---|---:|---:|---:|---|
| M | `Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed` | 620 | 5 | 3 / 16 | generalisation over the port's char-0 proof |
| M | `constantsAreBase_of_isAlgClosed_of_transcendental` | 48 | 4 | 3 / 27 | promotion of a same-statement private theorem |
| WR | `RationalFunctionField.weilReciprocity` | 1,273 | 22 | 1 / 2 | one 9-line theorem; the prelude is the pin's own duplicate file |
| WR | `WeilDatum.pairing_eq_of_isPrincipal_sub` | 439 | 11 | 1 / 1 | the pairing is a class invariant |
| WR | `WeilDatum.addLeft_pairing` | 80 | 5 | 1 / 1 | `addLeft` multiplies the pairing |
| WR | `WeilDatum.pairing_ne_zero` | 65 | 2 | 1 / 1 | the pairing is nonzero |
| TS | `Differential.sum_ord_smul_pullbackAlong_eq_zero` | 629 | 10 | 1 / 1 | the column's trace/Abel sum |
| CFE | `Differential.map_correspondence_regularDifferentials_of_constantFieldExtension` | 309 | 16 | 1 / 1 | naturality + injectivity + regularity + span |
| TL | `Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` | 146 | 1 | 3 / 10 | Laurent embedding → place; RB1's successor |
| TL | `lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq` | 95 | 1 | 1 / 2 | the `ell(N·D) = N·d + 1 − g₀` growth step |
| TL | `Divisor.evalFun_algebraMap_pushforward` | 59 | 5 | 3 / 9 | the fibre-product law |
| TL | `SemilinearAut.correspondence_smul` | 16 | 2 | 1 / 5 | `g • correspondence = correspondence (g • ·)` |
| **defer** | `Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` | 126 | 6 | 1 / 1 | unported Abel–Jacobi premises |
| **defer** | `Pic0.finite_torsion_of_isAlgClosed_of_charZero` | 95 | 8 | 1 / 6 | unported ℂ torsion count |

Demand is again inverted relative to size: the 620- and 48-line M rows carry 16 and 27 project
consumers, `laurent` carries 10, while the 1,273-line `weilReciprocity` carries 2.

## 3. Homes — checked against the import direction, per row

Method as in the recipe §4: pin `S_` premise nodes → statement-identical port module
(`twin_scan`'s `PortIndex` over the cached index) → the modules above all of them; then each home
confirmed by reading the pin proof's first lines and the candidate module's own subject. The
machine table was right on all twelve this time; the subject reading changed three of them
(`EvalAtNorm` over a new evalFun module, `LaurentSeriesModel` over `ValueDictionary`, and
`Place/ConstantFieldExtension` over a "new module for the char-free lift").

| node | premises → port modules (statement lookup) | home | why |
|---|---|---|---|
| `weilReciprocity` | 22 premises → `Defs/PlaceEvaluation`, `Defs/PlaceEvaluationAlgebra`, `Defs/PushPull`, `Defs/Place`, `P1/Dictionary`, `PrincipalDivisors/RatFuncDegree` | **insert** `P1/Dictionary.lean` (migrated in the same touch, §4.4) | it is the last theorem of the very pin file this module transcribes; all 69 of the file's other declarations are already there, and the proof is `reciprocity_of_ord_placeInfty_eq_zero` at the two places — nothing new is imported |
| `pairing_eq_of_isPrincipal_sub` | `Defs/WeilDatum`, `Pic0/Torsion`, `Defs/PlaceEvaluationAlgebra`, `Defs/PlaceEvaluation`, `Defs/PushPull`, `Defs/Divisor` | **new** `Pic0/WeilPairing.lean` | no existing module is above both `Pic0/Torsion` (SET 5) and the `evalFun` laws; the subject — the pairing's well-definedness on `Pic0.torsion` — has no module of its own, and a new module is cascade-free |
| `addLeft_pairing`, `pairing_ne_zero` | `Defs/PlaceEvaluationAlgebra` (`evalFun_mul/add/ne_zero`), `Defs/PushPull` (`mem_of_ord_nonneg`), `Defs/PlaceEvaluation` | **insert** `Defs/WeilDatum.lean` | it is the `WeilDatum` laws module (`symm_pairing` is already there); it needs `import Defs.PushPull` and `import Defs.PlaceEvaluationAlgebra`, and it has **0 importers**, so the two added imports cost no cascade |
| `sum_ord_smul_pullbackAlong_eq_zero` | 10 → `ResidueTheorem/GeneralFromK`, `LocalResidue/Instance`, `Canonical/HasCanonicalDivisor`, `Genus/RatFunc`, `Canonical/DCoordGenerates`, `Differential/Coefficient`, `IsCurveOver/EssFiniteType`, `Place/ConstantFieldExtension`, `Place/FromValuationSubring`, `Differential/ConstantFieldExtension` | **new** `ResidueTheorem/TraceSum.lean` | the nearest existing module, `ResidueTheorem/RRAssembly.lean`, is above nine of the ten but **not** above `Place/ConstantFieldExtension`; the new module imports `RRAssembly` + `Place/ConstantFieldExtension` (+ the Defs the proof opens), and its subject is the residue theorem applied along a cover — the pin's own `W11AbelDiff` |
| `cfe_isAlgClosed` | `IsCurveOver/ConstantFieldExtension` (both engines), `IsCurveOver/PerfectField`, `Place/FromValuationSubring` (both headlines) | **insert** `Place/ConstantFieldExtension.lean` (the M lane) | it is the module of the char-0 twin — the same 204-line proof and the same `ConstantFieldPlaceLift` block; the generalisation is in place, next to the statement it generalises |
| `map_corr` | 16 → `IsCurveOver/ConstantFieldExtensionSpan`, `Place/FromValuationSubring`, `Differential/Coefficient` (×4), `Place/ConstantFieldExtension`, `Place/TranscendentalOfOrdNeZero`, `IsCurveOver/FinitenessTransfer`, `IsCurveOver/ConstantFieldExtension`, `Genus/ConstantFieldExtension`, `Canonical/RegularDifferentialsFinrank`, `Canonical/HasCanonicalDivisor`, `WeilExchange/Transport` | **new** `Differential/CorrespondenceRegularCFE.lean` | it needs `Genus/ConstantFieldExtension` (the genus row), which is above `Differential/ConstantFieldExtension` and `Differential/CorrespondenceRegular`; the only port module above `Genus/ConstantFieldExtension` is `ModularCurve/XH/JHDescent.lean` — the wrong subject. The new module imports `Genus/ConstantFieldExtension`, `Differential/CorrespondenceRegular` and `Place/ConstantFieldExtension` |
| `constantsAreBase` | `IsCurveOver/Transcendental`, `IsCurveOver/PerfectField`, `Place/FromValuationSubring` | **promote** in `Genus/ConstantFieldExtension.lean` (the M lane) | the engine `TorsionDescentDeriv.constantsAreBase_of_isAlgClosed` is there `private` with `[IsCurveOver K F]`; the pin's statement derives the curve instance (`isCurveOver_of_isAlgClosed_of_transcendental`) and then applies it — 4 lines at the pin's name |
| `exists_ord_mul_eq_order_of_algHom_laurentSeries` | `Place/ValueDictionary` (`exists_ord_mul_eq_order_of_hasRamBound`) | **insert** `Place/LaurentSeriesModel.lean` (+ `import Place.ValueDictionary`) | the module whose subject *is* the Laurent-series model at a place; the row is the model's inverse direction (embedding → place) over RB1's engine. `ValueDictionary` imports only `Defs/Place`, `Defs/PlacesOverDVR`, `Defs/HahnSeriesRamificationBound` and `NumberTheory/ValuationSubring/Domination`, none of which imports `LaurentSeriesModel`, so the added import is acyclic |
| `lSpace_nsmul_succ…` | `Defs/AdelicIndex` (`mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor`, SET 5) | **insert** `Defs/AdelicIndex.lean` | `LSpace`/`ell` are defined there and the SET 5 engine is its last public theorem; the row is its successor |
| `evalFun_algebraMap_pushforward` | `Defs/PushPull`, `Defs/PlaceEvaluation`, `Place/ConstantFieldExtension` (`inertiaDeg_eq_one_of_isRational`) | **insert** `Place/EvalAtNorm.lean` | its subject is the value of a function summed over a fibre with inertia degrees — exactly this module's "the value of a norm on a fibre"; it is above `Place/ConstantFieldExtension` and `Defs/PushPull`, and it has **0 importers** |
| `correspondence_smul` | `WeilExchange/GaloisRamification` (`pushforwardAlong_smul`), `Defs/Correspondence` (`pullbackAlong_smul`) | **insert** `WeilExchange/GaloisRamification.lean` | the module of the along-laws it consumes; `Defs/Correspondence` is *below* it, so the natural subject home would be a cycle — this is the same class of call as SET 5's PIC1 `mk_eq_zero_iff_aux` inline |

**No row of the set cites another row of the set.** The two lanes' internal edges are only
through the manager's ground prep: `pairing_eq` imports the `WeilDatum` block M writes, and
`map_corr` uses M's char-free place lift by its char-0 name (which M keeps, as a corollary).

## 4. Ground prep — the manager's lane, before any order dispatches

### 4.1 The char-free place lift (the set's only hub edit) — decided, generalise in place

`Place/ConstantFieldExtension.lean` carries the char-0 development
`Place.exists_comap_algebraMap_eq_of_constantFieldExtension` (line 710) — 204 lines whose only
char-0 use is the `linearIndependent_of_constantFieldExtension` call in its proof. The pin's
isAlgClosed file is the same development with that one call swapped and `[CharZero K]` dropped.
The lane:

1. state the char-free theorem at the pin's wrapper name
   `Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed`, proof copied from
   the existing one with the engine swapped (the pin's 3-line diff, §0.3); ~205 lines moved in,
2. rewrite the existing char-0 theorem's proof as a one-line application of the new theorem, its
   **statement untouched** (it is a separate pin node with 6+ importers),
3. add both `spec-pin:` pairs (the wrapper and the `S_` file) to the module's wire.

Net new math ≈ 5 lines; 205 moved; the risk is that the port's adapted proof uses `CharZero` in
one or two places the pin's text does not (the pin's own 3-line diff says it should not).

### 4.2 The `constantsAreBase` promotion

Public at the pin's name `constantsAreBase_of_isAlgClosed_of_transcendental` in
`Genus/ConstantFieldExtension.lean`: derive `IsCurveOver K F` from
`isCurveOver_of_isAlgClosed_of_transcendental x hx`, apply the private engine, add the wrapper to
the wire. 4 lines. (The pin's 28-line `S_` `solution` — the separating-transcendental route — is
*not* transcribed: the port's engine is stronger and the row's statement is a 4-line corollary of
it.)

### 4.3 The shared `WeilDatum` block — port once, publicly, at the pin's names

Extend `Defs/WeilDatum.lean` with the 8 support lemmas at their **`Def_`-file names** —
`ord_f₁_eq_zero_of_mem_support`, `ord_f₂_eq_zero_of_mem_support`, `rational_of_mem_support_left`,
`rational_of_mem_support_right`, `evalAt_f₁_ne_zero`, `evalAt_f₂_ne_zero`, `evalFun_f₁_ne_zero`,
`evalFun_f₂_ne_zero` — and add `import Defs.PushPull` + `import Defs.PlaceEvaluationAlgebra`.
Probe result: **10 ok / 0 mismatch / 0 missing** for the 8 lemmas plus the two headlines against
`Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean` and the two `S_` files;
the wire needs those three sources (plus the `Def_AlgebraicCurve_WeilDatum` and
`Thm_/S_…_symm_pairing` lines it already has). The two `S_` files' copies carry `'` primes and
the big row's copies `_i` suffixes — both are the pin's local-copy convention; the port writes
the block once and the order imports it.

### 4.4 The `P1/Dictionary.lean` migration — measured, not guessed

`P1/Dictionary.lean` (1,228 lines, 70 public declarations) is legacy (`PORT_FILES`), and the
capstone's home is there, so the module migrates in the same touch (the recipe's legacy rule):
add a `spec-pin:` block over the 26 sources it transcribes — `Def_AlgebraicCurve_PlaceEvaluation`,
`Def_AlgebraicCurve_RatFuncPlaces`, the 11 `Theorems/` wrappers, the 11 `S_` files, and the new
`Theorems/` + `S_` pair for `weilReciprocity` — delete its `PORT_FILES` row (its `SOURCES` rows
stay), and let `spec/check_port.py` take it. **Probed on a copy in `tmp/` with the final
theorem appended: 70 ok / 0 mismatch / 0 missing / 0 own.** So the migration needs no
rectification; it is 26 wire lines and one registry deletion. If the review prefers to keep the
legacy registry untouched, the fallback is the one-line `SOURCES` row for the new wrapper (the
capstone is a statement the legacy checker can match the same way) — but the recipe's rule and
the probe both point at the migration.

### 4.5 One stale registry row

`Defs/AdelicIndex.lean` is listed in `PORT_FILES` and also carries its own three-line
`spec-pin:` wire (SET 5 handed it over; the note at `old_check_stmts.py:3978` says "Do not
re-list it here", but the entry at `:3973` was left behind). Delete the row; its `SOURCES` rows
stay.

## 5. Per-order notes — the traps recorded so far

**WR.** (i) `P1/Dictionary.lean` already holds the pin's three private helpers
(`isUnit_algebraMap`, `ofOption`, `ofOption_bijective`); import them, do not restate — the
capstone's proof needs only the public `reciprocity_of_ord_placeInfty_eq_zero` and
`principalDivisor`. (ii) The `S_` `solution`'s `open Polynomial IsDedekindDomain …` line is
scaffolding; drop it. (iii) `pairing_eq`'s 17 private helpers include a *second* copy of the
support block with `_i` suffixes — the manager's §4.3 block is the same statement set; import it
and write only the genuinely new helpers (`support_zsmul_subset_i`, `isPrincipal_{neg,add}_i`,
`isPrincipal_sub_of_mk_eq_i`, `evalFun_algebraMap_of_degree_eq_zero_i`, `degree_eq_zero_of_isPrincipal_i`,
`degree_D{1,2}_eq_zero_i`, `degZero{Left,Right}_i`, `class{Left,Right}_i`). (iv)
`pairing_eq_of_addPrincipalLeft_i`, `…_sub_left_i`, `…_sub_right_i` are **public in the pin** and
are its `solution`'s engine — state all three (the checker matches them against the `S_` file);
do not bury them `private`. (v) `WeilDatum.symm_pairing` (SET 5) is imported.

**TS.** (i) The 17 substituted declarations include `coeffLin`/`coeffDer` (SET 5's promotions in
`Differential/RegularDiffs.lean`) and `differentialCoeff_D_mem`: import, do not copy. (ii) The
`attribute` walls go (the BC6/BC8 precedent). (iii) The 5 `logDer_*` lemmas (64 lines) are about an
arbitrary derivation `Θ : Derivation R L L`, not about a place — self-contained prelude; the
three uniformiser helpers before them (`coe_unifElt`, `exists_unit_mul_uniformizer_zpow`,
`exists_mem_eq_uniformizer_mul`, 31 lines) are the place's own. (iv) `main` (222 lines) is the row; `solution` is its instantiation at
the wrapper's binders. (v) The row's local `residueTheorem_of_curve` (46 lines) restates the
general residue theorem for a curve: check first whether `ResidueTheorem/GeneralFromK.lean`'s
headline replaces it (46 lines if so); the pin proves it locally because its file predates the
assembly.

**CFE.** (i) The row is the pin's 3-line diff, not a second development (§0.3); the port's own
`IsCurveOver/ConstantFieldExtension.lean` is the precedent — *state the general, derive the
special*. (ii) `map_corr`'s `solution` is a **four-conjunct** statement (naturality of the
correspondence under the Kähler map, injectivity, regular differentials map into regular, and
the span); transcribe all four, they are what the consumer uses. (iii)
`exists_smul_D_eq_smul_dCoord` (23 lines) is new. `mem_of_ord_nonneg` is public in
`Defs/PushPull.lean` — import it. `ord_coe_nonneg` has **no public port copy**: the private
`ord_coe_nonneg` in `Place/LaurentSeriesModel.lean` is a different statement (it carries
`y ≠ 0`, where the pin's is unguarded), so the row writes its own 10 lines; `mem_of_ord_nonneg'`
(6 lines) is the unguarded variant of the imported one and stays local. (iv) The proof opens with
`exists_ord_neg_of_transcendental` and the *char-0* comap theorem; both are in the M-lane's module,
unchanged.

**TL.** (i) `laurent`: take the **wrapper's** binders (`(K : Type*) [Field K]` explicit), not the
`S_` copy's section-variable spelling; keep the pin's private headline re-exported publicly; drop
`cd2_control` (it computes an instance against `laurentBaseChange`/`coeffEmb` from
`ModularCurve/XH/*`, which would invert the import direction — it is the pin's own downstream
control, not part of the headline's proof, and `check_port` does not require pin declarations to
be ported), and drop the trailing `#check`/`#print axioms` block. (ii) `lspace`: one declaration,
85 lines, no prelude — a `Finset`/`Submodule` computation over `ell(N • D)`; the
`mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor` engine is imported. (iii)
`evalfun_push`: the proof's third step is `inertiaDeg_eq_one_of_isRational`; `EvalAtNorm` already
imports the module it lives in. The only new private helper is `zpow_finset_sum'` (7 lines). (iv)
`corr_smul`: the pin's proof is a three-line `rw`; `SemilinearAut.pushforwardAlong_smul` is in the
same module, and the pullback half is the port's `Divisor.pullbackAlong_smul` in
`Defs/Correspondence` (the two-map `CrossIntertwines` form — at `ψ = φ` it is the same
proposition as the pin's `IntertwinesAlong`), which the module already imports. `HasPrincipalDivisors
K F'` is a hypothesis of the statement, not an import.

## 6. The gates, per lane (unchanged from SET 5)

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, every added
   declaration `ok` (or a manager-written `own:`/`pin:` row). `P1/Dictionary.lean`'s gate is its
   new wire (the probe's 70 ok is the baseline).
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The lane's own modules only, under `flock`/`timeout`: **no tree build, no dependents**, and
   the module silent at the 200k cap. A `Replayed` line is not evidence that its `.olean` exists
   (FR-0033).
4. `dedup.py` / `move_dead.py` on each module, with the reason recorded for every kept cluster
   (the `WeilDatum` wrapper-over-engine pairs are the pin's own shape).
5. Zero warnings; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`; the worker writes no
   `spec/decl_markers.tsv` row.
6. Each lane appends the wrapper **and** the `S_` file of every node it adds to its module's
   `spec-pin:` block.
7. A `spec/` consumer zone with a real cross-module composition (no `#check`s), whose error
   count is the deliverable metric. The natural composition is WR's capstone with TS's trace
   sum: `RationalFunctionField.weilReciprocity` gives the ℙ¹ instance that
   `WeilDatum.pairing_eq_of_isPrincipal_sub` consumes, and TS's regularity hypothesis is
   supplied by `Differential.correspondence_mem_regularDifferentials`; a second zone composes
   the CFE order's four-conjunct statement with the genus row of SET 5.

## 7. The calls this brief asks the reviewer to settle

| call | recommendation | what it changes |
|---|---|---|
| 1. the two rows with unported, pruned premises | **defer both** (FR-0044) — they are the RR column's phase 3, not this column's; the alternative is to port 1,064 lines of Abel–Jacobi interface and a 61-line ℂ torsion count *into* the cone the read exists to avoid | the cut is 12 rows / 3,779 silo, not 14 / 4,000; §9 names both |
| 2. `P1/Dictionary.lean` — insert + migrate, or a new one-theorem module | **insert + migrate** (measured: 70 ok / 0 / 0 with the final theorem appended) — legacy is not a reason to move the mathematics, and the capstone is that module's own pin file's last theorem; fallback = a one-line `SOURCES` row if the review wants the legacy registry untouched | 26 wire lines + one registry deletion, or 1 line |
| 3. the char-free place lift | **generalise in place, keep both statements, derive the char-0 one** (the port's own `linearIndependent_…_of_isAlgClosed` precedent); 205 moved / ≈5 net | makes the row M's, not a worker's; §4.1 |
| 4. the manager lane | **take it** (§4.1–§4.5) — it is the set's only hub edit, and every order reads its modules | dispatch order: M first, then the four orders concurrently |
| 5. the pin's `cd2_control` | **drop it**, recorded — it is a downstream control against the modular curve and would invert the import direction; `check_port` does not require pin declarations to be ported | −30 lines from TL |
| 6. the cut and its dispatch | **four worker orders + one manager lane, one wave, no merge** — the edits are file-disjoint and additive, so the wave is safe on SET 4/5's criterion; M first. The two "small" stories (TS 629, CFE 309) carry the most mathematics per line in the set | §1 as written; the set's net is 1,419 rather than the instrument's 1,449 |

## 8. Reproduce, what the landing moved, and the name-shadow artifact

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json   # §0
python3 port_advise.py --nodes <each row> --json build/set6-<lane>.json           # §0.3, §1
python3 port_plan.py --json build/set6-<lane>.json                                # §1's net column
python3 spec/check_port.py --force <module>                                       # §6.1
```

The per-lane figures in §1 are each lane's own read (12 rows split 4/1/1/4, the M lane's two rows
priced separately); `port_plan`'s "raw `S_` lines (47-node slice)" line counts the target files
of the lane, so the four lanes' silos sum to 3,111 and the M lane's to 668 — 3,779 with no
overlap. The whole-set read was 417 substitutions / ≈4,425 in-port lines / 1,611 net for 14 rows;
the twelve carry 1,449 (1,419 after §7 call 5).

**The three measured numbers.**

1. **What the set consumed**: 12 rows / 3,779 silo (the two of §0.1 stay deferred); the tree
   figure is §1.2's +1,861 lines.
2. **The new `needed [F terminal]`**: the instrument reads 1,040 / 410,470 → **1,026 / 406,533**,
   and the true figure is **1,028 nodes / 406,691 lines** (−12 nodes / −3,779 lines) — see the
   artifact below. `AlgebraicCurve` demand 75 / 26,044 → 61 / 22,107 recorded (true: 63 / 22,265);
   ready candidates 96 → 90; leaves 296 → 296; the frontier 1,368 / 715,962 → 1,381 / 719,841
   (12 declarations' worth of new surface).
3. **Which rows became ready**: the six of the forecast below, 1,469 silo, and nothing else —
   *with one of them invisible and one spurious*, for the reason in the artifact.

**The name-shadow artifact (FR-0047), and why figures (2) and (3) need the correction.** The
port's new capstone is `AlgebraicCurve.RationalFunctionField.weilReciprocity`, and the frontier
counts portedness by **last name**. The pin has *two* nodes with that last name — the ℙ¹ one
(ours) and the general function-field one, `AlgebraicCurve.weilReciprocity` (100 silo, which needs
`weilReciprocity_algebraMap`, 58) — so the general one is now read as "ported":

- `weilReciprocity_algebraMap` (58) has **no unported premise** and is ready, but it is not in
  `need` any more (its only consumer is read as ported) → it does not appear on the shelf;
- `weilReciprocity` (100) and its two consumers (`DivisorialWeilPairingData.toHom_injective_of_divisible`,
  496, and `Pic0.exists_antisymmWeilPairing`, 656) lose their place in `needed`; the 496 row
  *appears* on the shelf as ready although its `weilReciprocity` premise is not ported — a spurious
  ready;
- so the instrument's fall is 2 nodes / 158 lines deeper than the truth, and the shelf shows
  6 new rows where 5 are real and 1 (`toHom_injective_of_divisible`) is not.

Nothing is wrong with the port: the two pin nodes are the two rows of the next wave
(`weilReciprocity_algebraMap` 58 → `weilReciprocity` 100 → the 496/656 pair), and landing them makes
the shadow true. Until then, the next scoping pass must not read the instrument's `weilReciprocity`
as ported.

**The forecast (read off the same graph, not a promise).** After the landing, six rows whose
only unported premises are this set's become ready — 1,469 silo:

| row that should become ready | silo | unblocked by |
|---|---:|---|
| `AlgebraicCurve.mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed` | 872 | M's char-free place lift |
| `AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing` | 381 | the three `WeilDatum` laws + the `WeilPairing` module |
| `AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental` | 103 | the `constantsAreBase` promotion |
| `AlgebraicCurve.weilReciprocity_algebraMap` | 58 | the ℙ¹ capstone |
| `AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental` | 32 | the `constantsAreBase` promotion |
| `AlgebraicCurve.SemilinearAut.pic0_correspondence_smul` | 23 | TL's `correspondence_smul` |

and three more are one row behind them: `AlgebraicCurve.weilReciprocity` (100, needs
`weilReciprocity_algebraMap`), `DivisorialWeilPairingData.toHom_injective_of_divisible` (496,
needs `weilReciprocity`), `exists_forall_mem_span_pow_mul_of_forall_ord_nonneg` (118, needs
`exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental`). The expected `needed [F terminal]` fall
is the 12 rows' 3,779 silo against SET 5's measured 3,656 — a similar wave.

## 9. What this set does not do

- **The two deferred rows** (§0.1): `Place.exists_natCast_dvd_ord_sub_single_sub_single_complex`
  (126) and `Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95). They are still on the shelf
  after the landing, unchanged (the re-read shows them at the same silo), still waiting on the
  prunable interface. They are consumers of the
  prunable complex-analytic interface (`abelJacobiDiv`/`pathPeriodLattice`, and the ℂ torsion
  count `Pic0.natCard_torsion_prime_eq_pow_genus_complex`), and the interface is **not** in the
  port — SET 5's predecessor waves ported `Defs/ComplexLineIntegral.lean` but not these two
  nodes. They belong to the RR column's phase 3
  ([PRUNABLE-complex-analytic.md](../deligneSerre/PRUNABLE-complex-analytic.md),
  [TOPIC-cell-dissection.md](TOPIC-cell-dissection.md)); if that subject lands, both rows return
  to this shelf by themselves. `Pic0.finite_torsion_of_forall_primePow` (SET 5) is already in
  `Pic0/Torsion.lean`, so the second is a 68-line tail once its ℂ count exists.
- **The general prescribed-divisor row** (`Place.exists_natCast_dvd_ord_sub_single_sub_single`,
  267 silo) that the deferred ℂ engine feeds: it was never on this shelf (three of its premises
  are unported), and it stays off it.
- **The consumers of the pairing laws beyond `Pic0.torsion.exists_addMonoidHom_eval_eq_pairing`**
  (`Pic0.exists_antisymmWeilPairing` 656, `DivisorialWeilPairingData.toHom_injective_of_divisible`
  496, …): they are on the shelf but one or two rows further out (§8), and they are the wave after
  this one, not part of it.
