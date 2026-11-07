# SET-AF18 — the right action on the cusp carrier and the convolution adjoint

**Status: LANDED 2026-11-07** — the manager's lane plus one dispatch of three orders, all gates green; **§5.1 records the landing and the re-read**, exact on every figure against §8's forecast, and the six predicted rows are the six that became ready. Read off the
D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF17 left, with one ground-prep lane (two false-marker repairs and one promotion, §3) landed
before the cut. It is the **eighteenth** `AutomorphicForm`-serving set, and it is the second set in
the right-action story AF17 opened: where AF17 ported right convolution's *derivatives* and right
translation's *adjoint*, this one ports **right convolution's adjoint**, **right translation as an
operator on the cusp carrier**, and **what right convolution preserves**.

The set is **10 rows / 1,453 silo of rows (1,418 union of demands)**, **1,166 declaration lines of
which 1,135 are new, in 35 declarations** (10 public headlines and 25 helpers) — in **three orders
over four new modules**. It is a **transcription** set: 31 of its 1,166 declaration lines are already
in the port (three prelude declarations the pin proves twice), so `port_plan` reads **1,200 net new
math lines**.

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| A — the adjointness of right convolution for the twisted pairing | 1 | 661 | 526 | new `Adelic/RightConvAdjoint.lean` |
| B — right translation on the cusp carrier | 3 | 385 | 332 | new `Adelic/Cusp/SpectrumTranslation.lean` |
| C — what right convolution preserves, and how it commutes | 6 | 407 | 277 | new `Adelic/RightConvPreservation.lean` + `Adelic/RightConvComm/Action.lean` |
| | **10** | **1,453** | **1,135** | four files, one dispatch, three workers |

The work orders are `lean/tmp/WORKORDER-AF18A-rightconv-adjoint.md`,
`…-AF18B-carrier-translation.md` and `…-AF18C-operator-algebra.md` (tmp is not published).

## 0. The read

### 0.1 The figures

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af18.json
python3 frontier.py --selfcheck
```

| figure | value (AF17's landing) | after this set's ground prep | SET-AF17 §5.1 (at its landing) |
|---|---:|---:|---:|
| `needed [F terminal]` | 838 / 344,897 | **836 / 344,831** | 838 / 344,897 |
| `needed [literal]` | 851 / 348,372 | 849 / 348,306 | 851 / 348,372 |
| frontier F | 1,577 / 782,469 | 1,579 / 782,535 | 1,577 / 782,469 |
| ready rows, all namespaces | 61 / 16,105 | **64 / 17,200** | 61 / 16,105 |
| ready rows, `AutomorphicForm` | 31 / 9,871 | **35 / 10,998** | 31 / 9,871 |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 | 225 / 57,500 |
| leaves, `AutomorphicForm` | 56 / 11,461 | 56 / 11,461 | 56 / 11,461 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (1,394 `Thm_` sources, 1,577 names) | **PASS** (1,397 / 1,579) | PASS (1,392 / 1,573) |
| correction needed | none | none | none |

The first column reproduces SET-AF17's landing figure **exactly**, every row of it — the tree has
not moved since (the FFG work of 2–7 Nov is in another area, and the D–S read is identical). So the
read is a re-read, not a remembered shelf, and the delta quoted below is measured against it.

### 0.2 The instrument was wrong before the mathematics was: a third false ported marker

The `--selfcheck` **passes**, and the ready shelf still carried a row whose premise the port does not
have. `NumberField.AdeleRing.secondCountableTopology` (62 silo: the adèle ring is second countable)
was read as **ported** because the port declares a *different* lemma with the same last name —
`RestrictedProduct.secondCountableTopology`
(`Topology/Algebra/RestrictedProduct/TopologicalSpace.lean`) — which is the FR-0047 shadow
mechanism, now met a third time (after `AlgebraicCurve.weilReciprocity` and
`Place.isRational_of_isAlgClosed`). `twin_scan --node` says `relative` (same last name, different
statement), i.e. the pin's *statement* has no declaration in the port, although its *mathematics* is
there: `NumberField.AdelicCountability.instSecondCountableAdeleRing` proves it as a `scoped
instance`, at a name the pin's wrapper does not carry.

The corrected read is one flag:

```bash
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
  --unport NumberField.AdeleRing.secondCountableTopology --json > build/shelf-af18-corr.json
```

| figure | instrument | corrected |
|---|---:|---:|
| `needed [F terminal]` | 838 / 344,897 | **839 / 344,959** |
| ready rows | 61 / 16,105 | **57 / 15,611** |
| leaves | 225 / 57,500 | 226 / 57,562 |

**Four rows leave the shelf** (494 silo), and none of them is this column's:

| row | silo |
|---|---:|
| `NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo` | 32 |
| `NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod` | 215 |
| `NumberField.AdelicHaar.adelicAddHaar_setOf_fst_apply_eq_eq_zero` | 128 |
| `NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero` | 119 |

and so do three AF rows *indirectly* — `isCuspidalFn_rightConv`, `isKfSmooth_rightConv`,
`rightConv_rightConv_eq_rightConv_rightConv_comp_inv` are gated on the 32-line leaf, which is gated on
the 62-line node. All four were read "ready" by the instrument and were not. §3 is the repair, and it
is why this set's ready shelf is quoted *after* it.

### 0.2b …and a fourth, found by a worker

Order B's worker met the same mechanism again, in the one place the scoping audit got wrong:
`AutomorphicForm.IsCuspidalFn.rightTranslate` (11 lines — cuspidality survives right translation) is a
pin node with its own `Theorems/` wrapper, was read as ported by the last-name shadow of the port's
several `rightTranslate` declarations, and is **absent from the port**; its only consumer is order B's
`rightTranslate_mem_cuspMemberSubmodule`, and *that row's* readiness therefore rested on the shadow
too. Its prerequisite `AutomorphicForm.constantTerm_rightTranslate` (10 lines) was absent as well (it
sat in the *literal* demand and in no shelf block). Neither is this column's mathematics: both are
constant-term API, and `Adelic/ConstantTerm.lean` is their home.

§3.4 is the repair. Note what the instrument did with it: porting the two rows moved `needed [F
terminal]` **not at all** (826 / 343,413 before and after), moved `needed [literal]` by **−1 / −10**
(839 / 346,888 → 838 / 346,878) and the frontier by **+1 / +10** — because the 11-line shadowed node
was already in `F` and the 10-line node sat inside its (already "ported") terminal demand. A shadow
therefore cancels out of the headline figure by construction, which is exactly why the shelf, not the
headline, is where it has to be looked for.

### 0.3 Why this block, and what it beats

The candidate blocks on the AF shelf, and the measured return of each (AF17's §0.2 figures, still
exact because the shelf is unchanged):

| candidate block | rows | silo | rows readied | silo readied |
|---|---:|---:|---:|---:|
| **the right action, continued (this set)** | 10 | 1,453 | **+6** | **+1,415** |
| the Hecke/Petersson tail (§7) | 7 | 947 | +1 | +23 |
| the Weyl pair (§7) | 2 | 2,640 | 0 | 0 |
| the indicator row (§7) | 1 | 1,043 | 0 | 0 |
| the `SmoothCuspRealizationAt` trio (§7) | 3 | 1,407 | 0 | 0 |
| the `weylInv` pair (§7) | 2 | 577 | 0 | 0 |
| the isotypic/cuspidal-spectrum block (§7) | 7 | 925 | 0 | 0 |

This set is the only block on the shelf that pays back what it costs: its landing readies **six rows
/ 1,415 silo**, i.e. the next set's subject, which is the `CuspidalSpectrum` carrier API for right
convolution (`integral_smul_apply_toCuspSubcarrier_…` 510, `…_integral_mul_rightTranslate` 463,
`exists_norm_toCarrier_rightConv_le` 253, `rightConv_mem_cuspMemberSubmodule` 70 at 10/13,
`map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv` 66,
`apply_mem_cuspSubcarrier_of_isLift_rightConv` 53 at 7/7). Two of the rows it consumes are themselves
one edge behind it (`exists_isCuspLift_rightTranslate_and_norm_le`, `rightTranslate_rightConv_of_isLevelSphericalOfType`)
and are taken as part of the same story. The five bulk blocks still measure **zero** return — they are
6,592 silo, 60 % of the AF ready shelf — and taking one of them is a decision to land bulk, not
progress.

**One story, three facets.** Right translation and right convolution are the two halves of the right
`GL₂(𝔸)`-action on automorphic functions; AF17 ported right translation's adjoint for the twisted
pairing plus right convolution's unipotent derivative and Casimir commutation. What is missing and
now ready is the rest of the operator picture: convolution's own adjoint (order A), translation as a
bounded operator on the `L²` carrier together with its cusp subcarrier (order B), and the two
operator-algebra facts the next set consumes — what convolution preserves (cuspidality, `K_f`
smoothness) and how it commutes with translation and the Casimir (order C).

## 1. The rows

| row (`AutomorphicForm.` dropped) | silo | work | decls | prem | lev | what it states |
|---|---:|---:|---:|---:|---:|---|
| `adjoint_rightConv_weightedPairing_of_isLsXiFunction` | 661 | **526** | 25 | 4 | 3/12 | the twisted pairing of `u * g` against `v` equals that of `u` against `v * g*`, `g* y = conj (g y⁻¹) |det y|^-σ`, with both sides `MemLp 2` on `Φ₀` |
| `CuspidalSpectrum.exists_isLift_rightTranslate` | 217 | **198** | 1 | 2 | 7/9 | the right translations by `y`, `y⁻¹` lift to bounded operators on `Carrier F Φ₀ σ`, adjoint up to `|det y|^σ`, with `‖T‖ ≤ |det y|^(σ/2)` |
| `CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule` | 112 | **94** | 1 | 3 | **20/23** | right translation preserves the cusp-member submodule — the highest-fan-in row in the set |
| `CuspidalSpectrum.exists_isCuspLift_rightTranslate_and_norm_le` | 56 | **40** | 1 | 2 | 4/4 | the same lift on the cuspidal subcarrier, with the same norm bound |
| `isCuspidalFn_rightConv` | 104 | **81** | 2 | 4 | 8/13 | convolution by a factorisable test function preserves cuspidality |
| `isKfSmooth_rightConv` | 70 | **57** | 1 | 1 | 7/21 | … and `K_f`-smoothness |
| `rightConv_rightConv_eq_rightConv_rightConv_comp_inv` | 80 | **65** | 2 | 1 | 1/1 | associativity: `(φ * f) * h = φ * (h * f∘inv)` |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | **23** | 1 | 1 | 2/3 | convolving a translate is translating with the conjugated kernel |
| `rightTranslate_rightConv_of_isLevelSphericalOfType` | 63 | **15** | 1 | 1 | 3/5 | for level-spherical `f`, a row-isometry translate passes through the convolution |
| `archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex` | 55 | **36** | 1 | 3 | 1/2 | both right actions commute with the Casimir and its conjugate |
| | **1,453** | **1,135** | **35** | | |

Three of these rows are **one edge behind the shelf head** and are taken as part of the same story
(SET 10's precedent): `exists_isCuspLift_rightTranslate_and_norm_le` needs the two lift rows,
`rightTranslate_rightConv_of_isLevelSphericalOfType` needs the conjugated-kernel row, and the three
right-convolution rows need §3's promotions.

**The premise audit, by hand.** Every premise of every row is in the port at the right statement —
checked by reading each port declaration's statement against its `Theorems/` wrapper, not by last
name. The load-bearing ones:

| premise | port home |
|---|---|
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` (all four AF rows) | `Adelic/RightTranslateAdjoint.lean` (SET-AF17) |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | `Adelic/RightConvDerivatives.lean` (SET-AF17) |
| `archCasimirAtComplex_rightTranslate_archComplexGLAt`, `…_rowIsometryInclAt_of_ne` | `Adelic/ArchCasimirComplex.lean` |
| `isMulRightInvariant_adelicGLHaar` | `NumberTheory/AdelicHaar/MulRightInvariant.lean` |
| `continuous_ideleNorm_det`, `measurableSet_setOf_ideleNorm_det_mem_Icc` | `NumberTheory/NumberField/TateGlobal/Defs.lean` |
| `exists_hasModulus_of_isAutomorphicFnAt_of_continuous`, `IsCuspidalFn.rightTranslate` | `Cusp/SpectrumCarrierAPI.lean`, `Adelic/ConstantTerm.lean` |
| `continuous_unipotentGL2`, `continuous_and_hasCompactSupport_of_isFactorizableTestFn` | `Adelic/ConstantTerm.lean`, `Adelic/FactorizableTestFn.lean` |
| `IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport` | `Topology/Algebra/LocallyCompactSupport.lean` |
| `NumberField.AdeleRing.secondCountableTopology`, `…_generalLinearGroup_finTwo` | `NumberTheory/AdelicLevel/Countability.lean` (**this set's §3**) |

**The definition gate.** The wrappers import `Definitions/Def_AutomorphicForm_CuspidalSpectrumCarrier`
(`Carrier`, `IsSlabFundamentalDomain`, `HasModulus`, `weight`, `weightedMeasure`, `IsLift`),
`…_CuspidalConstituent` (`rightTranslate`, `IsLevelSphericalOfType`'s companions),
`…_RightConvolution`, `…_FactorizableTestFn`, `…_ArchDerivCasimirComplex`,
`…_ProductionPinsGeneral`, `Def_NumberField_TateGlobalZeta`, `Def_NumberField_AdelicBox`,
`Def_AutomorphicForm_SmoothAutomorphicFnAt`. All are ported (`Cusp/SpectrumCarrier.lean` 41/41,
`Cusp/Constituent.lean`, `Adelic/RightConvolution.lean`, `Adelic/FactorizableTestFn.lean`,
`Adelic/ArchDerivCasimirComplex.lean`, `Adelic/CarrierPins.lean`, …). There is **no definition gate**
for this set and **no unported structure in any of the ten statements** — all ten elaborate today
(§3.3's skeletons are the measurement).

## 2. The price

`port_advise` / `port_plan` over the ten rows:

* **substitute**: three declarations already in the port — `slab`, `ideleNorm_one'`,
  `ideleNorm_inv'`, all **byte-identical**, all `private` in `Adelic/RightTranslateAdjoint.lean`
  (the pin proves its 24-line prelude in both the `rightTranslate` and the `rightConv` `S_` files).
  The pin has them `private` too, so the port keeps the pin's own second copy rather than promoting a
  private prelude (the recipe's §5 surface gate: the pin's local spelling stays private).
* **port once**: the set's only name proved twice inside its own files is
  `rightConv_rightConv_eq_rightConv_rightConv_comp_inv`, whose `S_` file proves the statement twice
  (`Ws1.L0.main` and `solution` delegating to it). Write it once; the pin's `main` is private
  machinery, not a node.
* **generalise**: no same-name pair, no binder variant. The only spelling difference inside the set
  is the pin's own (`isKfSmooth_rightConv`'s statement is over `AdelicGL2`, the two convolution rows'
  over `GL (Fin 2) (AdeleRing …)`); the statements are frozen as the wrappers have them.
* **drags**: `0 helpers` on every row's public surface — the set's public surface is 10 headlines and
  one pin-public helper (`G2Aux.constantTerm_eq_zero_of_eq_integral_kernel`), which is real
  mathematics (the Fubini step) and is public at the pin's name.
* `--with-defs`: the closure adds six `Def_` modules —
  `Def_AutomorphicForm_CuspidalSpectrumCarrier` (41 declarations), `…_FactorizableTestFn` (10),
  `…_RightConvolution` (5), `…_SmoothAutomorphicFnAt` (16), `Def_NumberField_AdelicBox` (36),
  `Def_NumberField_TateGlobalZeta` (15) — and **every one of their declarations has a public port
  declaration** (`Cusp/SpectrumCarrier.lean`, `Adelic/FactorizableTestFn.lean`,
  `Adelic/RightConvolution.lean`, `Adelic/SmoothAutomorphicFn.lean`, `NumberTheory/AdelicBox.lean`,
  `NumberTheory/NumberField/TateGlobal/Defs.lean`). The definition layer is therefore **0 lines of
  this set**, and the only declaration-level duplication the tool finds is the pin's own second copy
  of the three prelude declarations above (`slab` has 13 copies across the pin pool).

**Budget.** raw `S_` lines 1,418 → declaration lines 1,166 → 31 already in the port → **1,135 to
write**; `port_plan`'s once-cost after dedup is 1,224 with **1,200 net new math lines**. The measured
ratio of SET-AF17 was written ÷ net = 1,369 ÷ 1,326 = **+3.2 %**, so expect ~1,230 lines.

## 3. Ground prep (manager's lane — landed before the cut)

Three items, all landed, checked and built on 2026-11-07. They are **not** orders.

### 3.1 `NumberField.AdeleRing.secondCountableTopology` (62 silo) — false marker repaired

`NumberTheory/AdelicLevel/Countability.lean` now exports, in `namespace NumberField.AdeleRing` and at
the pin's own statements, the two theorems whose *mathematics* the module already had as `scoped
instance`s:

* `secondCountableTopology (K) : SecondCountableTopology (AdeleRing (𝓞 K) K)` — the pin's
  `S_NumberField_AdeleRing_secondCountableTopology` headline, proved by the module's own
  `instSecondCountableAdeleRing`;
* `secondCountableTopology_generalLinearGroup_finTwo (K) : SecondCountableTopology (GL₂(𝔸_K))` — the
  pin's 32-line leaf, proved by `M₂(𝔸_K)` second-countable + `Units.isEmbedding_embedProduct`.

Two `spec-pin:` wires each (wrapper + `S_`), and the module's twelve grandfathered `-- pin:` markers
were stripped into one wire for the bruhat `S_` file, which is the file all twelve came from — so the
module is now **fully wired and checker-green**: `check_port --force` reads **4 ok / 0 mismatch /
0 missing** (the two new theorems and the two declarations of the block the old checker could see),
where it was tier-3 unchecked before.

Effect on the read: `needed` 838/344,897 → **836/344,831**, frontier 1,577 → 1,579, and the shelf
**readies four rows / 494 silo** (the 32-line leaf — a genuine leaf, whose only premise is the 62 —
plus the three `NumberField.AdelicHaar` rows that were waiting on it). The three AF rows gated on the
leaf become this set's order C.

### 3.2 `AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport` — a promotion

`Adelic/RightConvRegularity.lean` held this as `private theorem continuous_rightConv` (the pin's row
`continuous_rightConv_of_continuous_of_hasCompactSupport`, 66 silo, is a pin-*public* node the module
already proved for its own headline). It is now **public at the pin's name and statement** (binder
spellings `φ, hφ, g, hg, hgc` and the `GL (Fin 2) (AdeleRing (𝓞 F) F)` spelling, which is what the
wrapper has), with two new `spec-pin:` wires; `check_port --force` reads **2 ok / 0 mismatch / 0
missing**. Its `let mSpace`/`have hBorel`/`have hHaar` walls replace the pin's `letI`/`haveI` under
the no-suppression rule (the linter-clean form; `have`/`let` register local instances).

Effect on the read: the row leaves the shelf and **two rows are readied** —
`exists_integral_rightConv_eq_rightConv` (514) and
`exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` (429), 943 silo. They are
the Hecke-coset averaging story and are **not** in this set (§7); they are AF19's opening.

### 3.3 The four skeletons

| module | lines | wires | status |
|---|---:|---:|---|
| `Adelic/RightConvAdjoint.lean` | 118 | 2 | elaborates, **1 `sorry` warning** (order A's headline) |
| `Adelic/Cusp/SpectrumTranslation.lean` | 116 | 6 | elaborates, **3 `sorry` warnings** |
| `Adelic/RightConvPreservation.lean` | 121 | 6 | elaborates, **4 `sorry` warnings** (3 headlines + the `G2Aux` helper) |
| `Adelic/RightConvComm/Action.lean` | 118 | 6 | elaborates, **3 `sorry` warnings** |

All seven public headlines and the `G2Aux` helper are **stated verbatim from their wrappers** and
`check_port --force` reads **11 ok / 0 mismatch / 0 missing / 0 own** across the four modules: the
statements are the pin's before a line of proof is written. The ten imports each module needs were
settled here (order C needed `Topology/Algebra/LocallyConstantCompactSupport` added; the others were
right first time), so a worker's missing import is a genuine report, not a guess.

### 3.4 The two constant-term rows of §0.2b (found during the dispatch)

`Adelic/ConstantTerm.lean` now states the two pin nodes at the pin's own statements and names:
`AutomorphicForm.constantTerm_rightTranslate` (10 lines: the constant term of `x ↦ f (x * h)` at `g`
is the constant term of `f` at `g * h`, by re-association under the integral) and
`AutomorphicForm.IsCuspidalFn.rightTranslate` (11 lines: cuspidality survives right translation),
with four `spec-pin:` wires (wrapper + `S_` for each). Both are four lines of mathematics —
`constantTerm` is `∫ q, f (u q * g)`, so the first is `simp only [constantTerm, constantTermIntegrand,
mul_assoc]` and the second applies the first — and both are transcribed at the *wrapper's* spelling
(`AutomorphicForm.constantTerm`, `AutomorphicForm.IsCuspidalFn` qualified; explicit `{Q}`/`{G}`
binders), which is what the checker diffs: an unqualified statement is a `MISMATCH`, not a match.
`check_port --force` reads **13 ok / 0 mismatch / 0 missing**.

Order B's row 2 had already inlined the second (3 lines, its deviation 7); the inline proof is
correct and stays — replacing it with the new lemma is a one-line simplification for that module's
next touch, not a landing gate.

**No `Def_` node, no migration, no legacy edit, no new `set_option`, no promotion left over.**

## 4. Homes

| order | module | why there |
|---|---|---|
| A | `AutomorphicForm/Adelic/RightConvAdjoint.lean` | the right-*convolution* half of the twisted-pairing adjointness, sibling of `RightTranslateAdjoint.lean` in the same directory (`Adelic/`), same prelude, same namespace family (`LocalIntertwining.WeightedPairingAdjoint`) |
| B | `AutomorphicForm/Adelic/Cusp/SpectrumTranslation.lean` | right translation *on the carrier*: the subject of `Cusp/SpectrumCarrier.lean` (`Carrier`, `IsLift`) and `Cusp/SpectrumSubrep.lean` (`IsCuspLift`, `cuspSubcarrier`); a new module rather than an insertion, because the carrier modules are frozen and 300–330 lines each |
| C | `AutomorphicForm/Adelic/RightConvPreservation.lean` | "what convolution preserves" — the sibling of `RightConvRegularity.lean`/`RightConvStructurePreservation.lean`, whose headline consumes exactly these three facts |
| C | `AutomorphicForm/Adelic/RightConvComm/Action.lean` | "how convolution commutes with the right action" — inside the existing `RightConvComm/` theory directory (the `rightConv_rightConv_comm` development), which is where a reader looks for a commutation fact |

**Import direction, all four checked by building the skeletons (§3.3):** A imports
`RightTranslateAdjoint` + `DetNormSlabFundamentalDomain` + `AdelicHaar/{GeneralLinear,MulRightInvariant}`
+ `TateGlobal/Defs`; B imports `Cusp/{SpectrumCarrier,SpectrumCarrierAPI,SpectrumPairing,SpectrumSubrep,Constituent}`
+ `RightTranslateAdjoint`; C1 imports `RightConvolution`, `ConstantTerm`, `SmoothAutomorphicFn`,
`CarrierPins`, `FactorizableTestFn`, `TestFnTop`, `LocallyConstantCompactSupport`,
`AdelicLevel/Countability`; C2 imports `RightConvolution`, `Cusp/Constituent`, `ArchSpherical`,
`ArchCasimir{,Complex}`, `ArchDerivCasimirComplex{,API}`, `ArchDerivRightConvComplex`,
`RightConvDerivatives`. No cycle; every home sits above its proof's premises.

**Disjoint files, disjoint pin sources**: A, B and C share no declaration, no module and no pin file,
so all three orders are safe concurrently (only the build lock is shared).

## 5. The cut

**Three orders, four modules, three workers.** See §1 for the row tables and the work orders for the
detail; the build gate for each order is the recipe's (§6 of the scoping note), plus this set's three
additions:

1. **No `set_option`, of any kind.** The port is linter-clean by converting `letI`/`haveI` to
   `let`/`have` (which do register local instances in this Lean, measured in §3.2), not by silencing;
   `maxHeartbeats` overrides are a defect marker and no module of this set carries one.
2. **The statement texts are frozen** — the checker already reads all eleven `ok`, so any edit to a
   signature is a defect by definition.
3. **One consumer file per order** (`spec/AutomorphicFormSetAF18{A,B,C}Consumer.lean`), so three
   workers never touch one file; the manager merges or keeps them at review.

### 5.1 The landing (2026-11-07)

**Files.** `Adelic/RightConvAdjoint.lean` 99 (skeleton) → **689** (30 declarations: 29 `private` +
the headline); `Adelic/Cusp/SpectrumTranslation.lean` 116 → **430** (3, all public);
`Adelic/RightConvPreservation.lean` 121 → **249** (4, all public); `Adelic/RightConvComm/Action.lean`
118 → **137** (3, all public); three consumers — `spec/AutomorphicFormSetAF18AConsumer.lean` (155),
`…B…` (79), `…C…` (153). **40 declarations** written against the worklist's 35 (§ below).

| order | rows | plan (worklist) | written | decls | module |
|---|---:|---:|---:|---:|---|
| A | 1 | 526 | **590** | 30 | `RightConvAdjoint.lean` 689 |
| B | 3 | 332 | **314** | 3 | `Cusp/SpectrumTranslation.lean` 430 |
| C | 6 | 277 | **147** | 7 | `RightConvPreservation.lean` 249 (+128) · `RightConvComm/Action.lean` 137 (+19) |
| | **10** | **1,135** | **1,051** | **40** | four files |

**Plan against actual**: **1,051 lines written against 1,135 planned, −7.4 %**; the shortfall is
entirely order C, which the brief predicted would be composition (rows 5, 6 and 7 are 19 lines of
gluing in total, not the 74 the worklist priced). Order A ran +12 % (the Fubini block is the pin's,
with two instance walls the pin had as scoped instances turned into local `have`s). The declaration
count is 40, not 35, and the difference is fully explained: the worklist counts **theorem-kind**
declarations only, so it omits order A's two defs (`μ`, `wt`) and treats the pin's `ideleNorm_one'`
and `ideleNorm_inv'` as "imported" — they are `private` in `RightTranslateAdjoint.lean`, hence not
importable, so order A wrote its own copies as planned (§2).

**Gates** (all re-run by the manager on the landed tree):

1. `check_port --force` per module: **1 / 3 / 4 / 3 = 11 ok, 0 mismatch, 0 missing, 0 own, 0 kw**
   — every declaration of the set is a pin statement, public and private alike (the private ones
   under the dropped-`private` reading, which the checker matches by content hash).
2. `#print axioms` on all **eleven** (ten headlines + the pin-public `G2Aux` helper), at their
   pin-qualified names → `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
   (`lean/tmp/af18/axioms-all.lean`).
3. Four module builds green and **silent** (`flock`/`timeout`, 3,901 jobs for the last one); the
   edit loop silent on all four.
4. `dedup --within` per module: 30 / 3 / 4 / 3 declarations, **0 duplicate clusters**, 0 removable
   lines. `move_dead --dry-run`: 0 dead in three modules; order A has **one** dead declaration,
   `kernel_integrable` (pin `:168`) — dead in the pin too, so it is the pin's unreachable
   mathematics and stays (§3.8).
5. Three consumers, **0 errors / 0 warnings** each, no `#check`, no `sorry`. A: the adjoint kernel
   `g*` written out with `(g*)* = g`, the pairing read both ways, and the pairing at `(u*g*, v)` from
   `(u, v*g)`. B: existence of `T`, `T'`, `S` with both exponent bounds and `IsCuspLift` fed by row
   2's membership. C: rows 2+3 in `IsCuspidalFn`'s definitional form, row 4 re-associated twice, rows
   5+6 composed into "conjugation by a row-isometry translate is invisible for level-spherical `f`",
   row 7 projected into one Casimir commutation per side. Order C's zone 1c reads §3.2's promoted
   `continuous_rightConv_of_continuous_of_hasCompactSupport`, so the triple-convolution flatten assumes
   exactly **one** fact (a compact-support hypothesis on the derived factor) instead of three.

**Deviations, by class** (every one statement-neutral; the checker is the proof):

* **mathlib drift (v4.34)**: `orthogonalProjection` → `orthogonalProjectionOnto` (three names),
  `Submodule.coe_norm` → `Submodule.norm_coe`, `ContinuousLinearMap.smul_apply` → `smul_apply`,
  `inv_mul_cancel_right` gone (residual closed by `group`), and `haarScalarFactor`'s scalar is `ℝ≥0`
  where the pin wrote `ℝ≥0∞` (the `IsInvInvariant` derivation, five lines).
* **instance walls**: the pin's `letI`/`haveI` and its eight countability/second-countability scoped
  instances become named `have`/`let` at the same terms, using §3.1's two public theorems — *no*
  `set_option` anywhere. Order A also re-derives `sigmaFinite_μ` (the pin's `inferInstance` does not
  synthesize: the port has no instance for `SigmaFinite (adelicGLHaar …)`, second countability is the
  ingredient) and replays the pin's `IsInvInvariant` derivation inline, because the port has no such
  instance and no importable one.
* **two port gaps found from the work orders' own instructions** (the manager's audit had claimed the
  first was present): `IsCuspidalFn.rightTranslate` (§3.4, now public) and `IsInvInvariant
  (adelicGLHaar …)` (no instance; `RepTheory/AntiInvolutionHaar` has one but importing it was not this
  order's price). Order B inlined the first in three lines; both are recorded rather than worked
  around in a hub module.
* **statement-neutral spelling**: `𝓝` → `nhds` and qualified `MeasureTheory.integral_mul_*` where the
  module's `open`s differ from the pin's; `haveI` walls that the module header already carries as
  `attribute [local instance]` are not repeated; the pin's `attribute [-instance]`/`[-simp]` header
  walls are not transcribed anywhere.
* **one structural edit**: order B swapped two declarations (row 2 must precede row 3, which calls it).
  Statement texts byte-identical, checker 3 ok, `dedup` clean.

**The re-read is exact against §8's forecast.**

| figure | before (after §3) | after | Δ | forecast |
|---|---:|---:|---:|---|
| `needed [F terminal]` | 836 / 344,831 | **826 / 343,413** | −10 / −1,418 | −10 / −1,418 ✓ |
| `needed [literal]` | 849 / 348,306 | **838 / 346,878** | −11 / −1,428 | −10 / −1,418, plus §3.4's 10-line node ✓ |
| frontier F | 1,579 / 782,535 | **1,590 / 783,963** | +11 / +1,428 | +10 / +1,418, plus §3.4 ✓ |
| ready rows | 64 / 17,200 | **62 / 17,281** | 8 out, 6 in: +81 | +81 ✓ |
| leaves | 225 / 57,500 | 225 / 57,500 | — | — ✓ |
| `--selfcheck` | PASS | **PASS** (1,409 sources / 1,590 names) | — | — |

**Rows readied: the predicted six, in the predicted order** — 510, 463, 253, 70, 66, 53 silo
(1,415 in all), i.e. the `CuspidalSpectrum` carrier API for right convolution. AF's ready shelf is now
**33 rows / 11,079 silo**, of which AF19's subject is 1,415.

## 6. Risk register

1. **Order A is a 526-line Fubini development with a three-conjunct statement** (`MemLp`,
   `MemLp`, integral identity) and a four-premise row. The engine is the port's own
   `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` (AF17) plus the Haar re-indexings; the
   pin's `swap_identity`/`lhs_eq`/`rhs_eq` block (420–619) is the bulk of it. Its risk is length, not
   shape: the pin's proof transcribes. The one trap is that the statement's slab is spelled *inline*
   twice (in `hΦ₀` and `hFD`), so the proof must `change`/`show` through the private `slab` def.
2. **Order B's row 1 is a closure/projection construction, not algebra**: `L0 : contMemberSubmodule →
   Carrier`, the topological closure of its range, the orthogonal projection onto it, then the
   pairing identity and the squared-norm identity. The pin's route is the port's idiom
   (`DenseRange` + `orthogonalProjection`); a Riesz-representation rewrite would be a different proof
   and is not the order.
3. **Order B's row 2 carries the highest fan-in in the set (20 in-cone / 23 project)** and its
   `IsKfSmooth` half is a `MulAction.stabilizer` conjugation argument — the one place where the
   `K = finiteAdelicGL2Subgroup` normality is used. It is transcribed, not invented.
4. **Order C is cheap but has one real proof** (`isCuspidalFn_rightConv`'s Fubini-through-the-constant
   term). The rest is composition of landed rows; a worker who finds itself re-proving an
   `archCasimirAtComplex` commutation is off-route.
5. **The pin's `attribute [-simp]`/`attribute [-instance]` header walls are not port content.** They
   exist because the pin's `Def_` stubs register instances the real proof does not want. Order A
   resolves a `simp` locally if one misbehaves; no worker transcribes a wall.
6. **Pin-public helper.** `G2Aux.constantTerm_eq_zero_of_eq_integral_kernel` is public in the pin and
   is public in the port (order C); it is real mathematics, not a port-side helper, and the checker
   matches it at the pin's name.

## 7. What this set does not do

- **It does not take the two rows its own promotion readies** —
  `exists_integral_rightConv_eq_rightConv` (514) and
  `exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` (429). They are the
  Hecke-coset averaging engine (`∫_U rightConv y f = rightConv y f'` with `f'` bi-`U`-invariant) and
  the adèlic Borel–Fubini fact that feeds it: a different story, and AF19's opening.
- **It does not take the Hecke/Petersson tail** (7 rows / 947 silo, measured return +1 / +23):
  `cosetSum_rightConv_of_isLevelSphericalOfType` 173, `peterssonIntegral_self_ne_zero_…` 192,
  `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` 138, and the small `CuspidalSpectrum` /
  `isFinTestFactor` rows. Cheap, and the natural companion of order C, but a different subject (the
  coset sums and the Petersson integral).
- **It does not take the five bulk blocks**, still measured to ready nothing: the Weyl pair
  (2,640 — deferred for the sixth consecutive pass), the indicator row (1,043), the
  `SmoothCuspRealizationAt` trio (1,407), the isotypic/cuspidal-spectrum block (925), the `weylInv`
  pair (577). That is 6,592 silo, 60 % of the ready shelf; taking one is landing bulk, and the brief
  says so.
- **It does not take the `su2` string** (681 + 755) **nor the `diagOne` family** (2,098 in four rows,
  still blocked on the unported
  `TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` — which *is* on the shelf
  at 63 silo and 11/73 leverage, a natural AF19 or AF20 opener).
- **The 4 withheld rows / 831 remain** the prunable complex-analytic subject (the `Pic0`/`place`
  rows and the two ModularCurve Tate-module rows); they are not this column's work.
- **No `Def_` gate, no migration, no legacy module edited**; four new modules, one edited (`Countability.lean`,
  which was touched for §3.1 and is now wired and green) and one (`RightConvRegularity.lean`) edited
  for §3.2.

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af18.json
python3 frontier.py --selfcheck
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
  --unport NumberField.AdeleRing.secondCountableTopology --json > build/shelf-af18-corr.json
python3 port_advise.py --nodes <each of the ten rows> --json build/af18-advise3.json
python3 port_plan.py --json build/af18-advise3.json
python3 build/af-worklist.py adjoint_rightConv_weightedPairing_of_isLsXiFunction \
  CuspidalSpectrum_exists_isLift_rightTranslate CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule \
  CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le isCuspidalFn_rightConv \
  isKfSmooth_rightConv rightConv_rightConv_eq_rightConv_rightConv_comp_inv \
  CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj \
  rightTranslate_rightConv_of_isLevelSphericalOfType \
  archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex \
  > build/af18-worklist.md
```

**The forecast (measured by simulating the landing: the four skeletons carry all ten headlines, so the
frontier already reads the set as ported).**

| figure | before (after §3) | after | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 836 / 344,831 | **826 / 343,413** | −10 / −1,418 |
| `needed [literal]` | 849 / 348,306 | **839 / 346,888** | −10 / −1,418 |
| frontier F | 1,579 / 782,535 | **1,589 / 783,953** | +10 / +1,418 |
| ready rows | 64 / 17,200 | **62 / 17,281** | 8 out, 6 in: +81 silo (= −1,334 + 1,415) |
| leaves | 225 / 57,500 | 225 / 57,500 | — |

**Rows readied (6 / 1,415 silo):**

| row | silo | prem | lev | what it is |
|---|---:|---:|---:|---|
| `CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact` | 510 | 3 | 1/1 | averaging a cusp-subcarrier vector over a compact open subgroup |
| `CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate` | 463 | 3 | 1/1 | … with right translates of the test function |
| `CuspidalSpectrum.exists_norm_toCarrier_rightConv_le` | 253 | 4 | 1/1 | the `toCarrier` norm bound for a convolution |
| `CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule` | 70 | 6 | **10/13** | convolution preserves the cusp-member submodule |
| `CuspidalSpectrum.map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv` | 66 | 3 | 1/1 | the level subcarrier under a convolution lift |
| `CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv` | 53 | 2 | **7/7** | applying a convolution lift to a cusp-subcarrier vector |

The last four are the `CuspidalSpectrum` carrier API for right convolution — AF19's subject, already
cut.

**The landing section (§5 of the recipe) is filled at review**: files and lines per order, the
checker counts at both visibility readings, the axioms blocks, `dedup`/`move_dead`, the consumer error
counts, and the exact re-read against this forecast.

## Appendix A — the AF shelf, every row accounted for

### The ready block — **35 rows / 10,998 silo** (after §3)

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `adjoint_rightConv_weightedPairing_of_isLsXiFunction` | 661 | 4 | 3/12 | **SET-AF18 order A** |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `exists_integral_rightConv_eq_rightConv` | 514 | 3 | 2/3 | deferred (§7 — readied by §3.2) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` | 429 | 3 | 1/1 | deferred (§7 — readied by §3.2) |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_isLift_rightTranslate` | 217 | 2 | 7/9 | **SET-AF18 order B** |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred (§7) |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7, Hecke/Petersson) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7, Hecke/Petersson) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7, Hecke/Petersson) |
| `CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule` | 112 | 3 | 20/23 | **SET-AF18 order B** |
| `isCuspidalFn_rightConv` | 104 | 4 | 8/13 | **SET-AF18 order C** |
| `rightConv_rightConv_eq_rightConv_rightConv_comp_inv` | 80 | 1 | 1/1 | **SET-AF18 order C** |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | **SET-AF18 order C** |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred |
| `archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex` | 55 | 3 | 1/2 | **SET-AF18 order C** |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | deferred |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | **SET-AF18 order C** |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred |

Two more of this set's rows are one edge behind this block and are taken with it:
`CuspidalSpectrum.exists_isCuspLift_rightTranslate_and_norm_le` (56) and
`rightTranslate_rightConv_of_isLevelSphericalOfType` (63, itself behind the 35-line row above).

### The leaves block — **56 rows / 11,461 silo** (unchanged from SET-AF17)

| leaf | silo | lev | disposition |
|---|---:|---:|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 3/4 | deferred (§7) |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 1/3 | deferred |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 2/15 | deferred |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 2/7 | deferred |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | deferred |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | deferred |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | deferred |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | deferred |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | deferred |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred |
| the remaining 36 leaves (≤192 silo each, 4,161 silo) | | | deferred, as in SET-AF17 |

## Appendix B — the per-row worklist

`build/af-worklist.py` over the ten rows (`build/af18-worklist.md` has the declaration-level detail).

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `adjoint_rightConv_weightedPairing_of_isLsXiFunction` | 557 | 31 | 526 | 25 |
| `CuspidalSpectrum_exists_isLift_rightTranslate` | 198 | 0 | 198 | 1 |
| `CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule` | 94 | 0 | 94 | 1 |
| `CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le` | 40 | 0 | 40 | 1 |
| `isCuspidalFn_rightConv` | 81 | 0 | 81 | 2 |
| `isKfSmooth_rightConv` | 57 | 0 | 57 | 1 |
| `rightConv_rightConv_eq_rightConv_rightConv_comp_inv` | 65 | 0 | 65 | 2 |
| `CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 23 | 0 | 23 | 1 |
| `rightTranslate_rightConv_of_isLevelSphericalOfType` | 15 | 0 | 15 | 1 |
| `archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex` | 36 | 0 | 36 | 1 |
| **10 rows** | **1,166** | **31** | **1,135** | **36** |

36 pin declarations; one is the pin's own second copy of a statement
(`rightConv_rightConv_eq_rightConv_rightConv_comp_inv`'s private `Ws1.L0.main`), so **35 are written**:
the 10 public headlines, order A's 24 `private` prelude helpers, and the pin-public `G2Aux` Fubini
helper.
