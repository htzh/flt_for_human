# SET-AF17 — right convolution as an operator: its adjoint, its derivatives, and what it preserves

**Status: LANDED 2026-11-02** — the manager's layer plus one dispatch, all four rows, all gates green;
**§5.1 records the landing and the re-read**, which is exact on every figure and readies the four
predicted rows. The order is
[WORKORDER-AF17-rightconv-operator.md](WORKORDER-AF17-rightconv-operator.md): all three module skeletons
exist, build and wire clean (`check_port --force` 0 / 0 / 0 on each), and
`lean/tmp/probe-af17-statements.lean` states all four headlines with exactly four `sorry` warnings.
Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF16 left. It is the **seventeenth** `AutomorphicForm`-serving set, and it is the first since AF15
whose landing is measured to *open* more than a token amount of work: **4 rows / 1,434 silo consumed,
4 rows / 1,045 silo readied**, including a 661-line row and the shelf's highest-fan-in node
(`CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule`, 112 silo, **20 in-cone / 23 project
consumers**).

The set is **4 rows / 1,434 silo / 1,326 net lines** (`port_plan`) — **1,317 lines to write in 103
declarations** (the worklist) — in **three orders over three new modules**. It is a **transcription**
set in the AF11 sense: only **4 of its 1,330 declaration lines are in the port**, and 51 of its 103
declarations are pin-public, so its checked surface is the largest the column has attempted.

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| A — the adjointness of right translation for the twisted pairing | 1 | 433 | 397 | new `AutomorphicForm/Adelic/RightTranslateAdjoint.lean` |
| B — the derivatives of right convolution: unipotent, and the complex Casimir | 2 | 711 | 648 | new `AutomorphicForm/Adelic/RightConvDerivatives.lean` |
| C — what right convolution preserves | 1 | 290 | 272 | new `AutomorphicForm/Adelic/RightConvStructurePreservation.lean` |
| | **4** | **1,434** | **1,317** | three files, one dispatch |

## 0. The read

### 0.1 The figures

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af17-scope.json
python3 frontier.py --selfcheck
```

| figure | value | SET-AF16 §5.1 (at its landing) |
|---|---:|---:|
| `needed [F terminal]` | **842 / 346,331** | 842 / 346,331 |
| `needed [literal]` | 855 / 349,806 | 855 / 349,806 |
| frontier F | **1,573 / 781,035** | 1,573 / 781,035 |
| ready rows, all namespaces | 61 / 16,494 | 61 / 16,494 |
| ready rows, `AutomorphicForm` | **31 / 10,260** | 31 / 10,260 |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 |
| leaves, `AutomorphicForm` | **56 / 11,461** | 56 / 11,461 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (1,392 `Thm_` sources, 1,573 declared names) | PASS (1,392 / 1,573) |
| correction | **none needed** | none needed |

Same tree as SET-AF16's landing — the promotion of `MaximalCompactFactors`'s six declarations (§5.1
item 5) does not move the frontier, because the frontier already counted them as `private` names. Zero
delta on every row, no correction owed. Appendix A quotes both blocks whole (31 / 10,260 and 56 /
11,461); 4 rows / 1,434 are this set's and 83 are deferred (§7).

### 0.2 Why this block, and the four it beats

Every candidate was forecast by simulating its landing (`build/af14-forecast.py`):

| candidate block | rows | silo | rows readied | silo readied |
|---|---:|---:|---:|---:|
| **right convolution as an operator (this set)** | 4 | 1,434 | **+4** | **+1,045** |
| the Hecke/Petersson tail (§7) | 7 | 947 | +1 | +23 |
| the Weyl pair (§7) | 2 | 2,640 | 0 | 0 |
| the flat-section indicator row (§7) | 1 | 1,043 | 0 | 0 |
| the `SmoothCuspRealizationAt` trio (§7) | 3 | 1,407 | 0 | 0 |
| the `weylInv` pair (§7) | 2 | 577 | 0 | 0 |
| the isotypic/cuspidal-spectrum block (§7) | 7 | 925 | 0 | 0 |

The set is the only candidate on the AF shelf whose landing pays back most of itself, and the payback is
not marginal: it readies **`adjoint_rightConv_weightedPairing_of_isLsXiFunction` (661, 3/12)** — the
right-convolution half of the very statement it ports the right-*translation* half of — plus
`CuspidalSpectrum.exists_isLift_rightTranslate` (217, 7/9), and the two rows that make the cusp
subrepresentation module's API tick (112 at 20/23 and 55). Two reasons to take it now rather than the
bigger blocks:

- **The five other ready blocks are measured to ready nothing** (the Weyl pair, the indicator row, the
  `SmoothCuspRealizationAt` trio, the `weylInv` pair, the isotypic block), and three of them have now been
  deferred in four or five consecutive passes. The column's ready shelf is 10,260 silo of which 5,257 is
  in blocks with no return; taking one of those is a decision to spend a dispatch on bulk, and the brief
  says so instead of pretending otherwise.
- **This block is one story in the operator sense**, which is the right way to read it: right convolution
  by a factorizable test function is an operator on automorphic functions, and the four rows are its
  adjoint for the twisted pairing (`∫ u(xy) conj v(x) |det x|^-σ = |det y|^σ ∫ u(x) conj v(xy⁻¹) |det x|^-σ`
  with the two `MemLp` side conditions), its derivative along the unipotent flow (with the derivative
  again factorizable, and linear in the direction), its action under the complex archimedean Casimir
  (`archCasimirAtComplex (rightConv x f) = rightConv (archCasimirAtComplex x) f`, and the same for the
  conjugate Casimir), and the list of structures it preserves (cuspidality, `K_f`-smoothness, level
  invariance, and the Hecke-eigen property away from the exceptional set).

### 0.3 What a landing would change — the forecast

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 842 / 346,331 | **838 / 344,897** | −4 / −1,434 ✓ (the four rows' silo, exact) |
| `needed [literal]` | 855 / 349,806 | **851 / 348,372** | −4 / −1,434 ✓ |
| frontier F | 1,573 / 781,035 | **1,577 / 782,469** | +4 / +1,434 ✓ |
| ready rows, all namespaces | 61 / 16,494 | **61 / 16,105** | 4 out, 4 in: −389 silo (= −1,434 + 1,045) |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 | — |

**Rows readied (4 / 1,045 silo):**

| row | silo | prem | lev | what it is |
|---|---:|---:|---:|---|
| `adjoint_rightConv_weightedPairing_of_isLsXiFunction` | 661 | 4 | 3/12 | the same adjointness for **right convolution** instead of right translation — the pair's second half |
| `CuspidalSpectrum.exists_isLift_rightTranslate` | 217 | 2 | **7/9** | a lift of a cusp member through right translation |
| `CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule` | 112 | 3 | **20/23** | right translation preserves the cusp-member submodule — the highest-fan-in node on the shelf, and the first row this column has readied whose *consumers* are 20 |
| `archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex` | 55 | 3 | 1/2 | the Casimir and the conjugate Casimir commute past right translation as well as right convolution |

That last pair is the whole point: after this set, **AF18 is the same subject continued** — the two
`rightTranslate` rows and the right-convolution adjoint, 990 silo, and then the `CuspidalSpectrum` API
that consumes them.

## 1. The four rows

| row (`AutomorphicForm.` dropped) | silo | work | decls | prem | lev | what it states |
|---|---:|---:|---:|---:|---:|---|
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | **397** | 37 | 4 | 4/10 | for an Ls-Xi function pair `u`, `v` of the same character `ξ`, a fundamental domain `Φ₀` inside a determinant window, and `y : GL₂(𝔸)`: the right translates `u (· * y)` and `v (· * y⁻¹)` are `MemLp 2`, and `∫_{Φ₀} u (xy) conj (v x) |det x|^-σ = |det y|^σ ∫_{Φ₀} u x conj (v (x y⁻¹)) |det x|^-σ` |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | **360** | 30 | 2 | 1/2 | three facts at once: `t ↦ rightConv φ f (g * n(t v))` has derivative `rightConv φ (∂_v f) g` at `0`; `∂_v f` is again a factorizable test function; and `∂_{a v + b w} f = a ∂_v f + b ∂_w f` |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | 321 | **288** | 18 | 6 | 1/1 | for a continuous, archimedean-smooth `x` whose first and second `archDerivAtComplex` derivatives are continuous, and any factorizable, arch-bi-finite `f`: `rightConv x f` is again smooth in the same sense, and both Casimirs commute past it, `archCasimirAtComplex (rightConv x f) = rightConv (archCasimirAtComplex x) f` (and `…BarAtComplex`) |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | **272** | 18 | 2 | 2/11 | for a smooth cusp realization `R` at the production pins and an `f` supported on the positive part of the level subgroup: `rightConv R.toFun f` is cuspidal, `K_f`-smooth, level-invariant, and a Hecke-coset eigenfunction at every `v` outside `R.exceptionalSet` |

**Visibility is the set's largest problem and its cheapest check.** Row 2 is a **flat public surface** and
row 3 of **18** declarations; rows 1 and 4 are private preludes with one public headline each (36 and 17
`private`). At the landing the readings measured **50** at the pin's visibility (1 + 48 + 1) and **103** at
the dropped-`private` surface — the two together are the statement check, and a `MISMATCH` in either is a
real defect. (The brief's first figures, 54 and 103, counted the pin's public *surface* for order B rather
than the 48 declarations written; §5.1 records the correction.)

**Namespaces** (one per pin file): `WeightedPairingTranslate` (row 1, the pin's own name), `UnipDeriv`
(row 2), `CommConvC41` (row 3 — renamed `ComplexCasimirComm`), `RightConvPreserve` (row 4). The four
headlines are **public at their pin names** — `AutomorphicForm.<name>` — not inside the helper
namespaces (FR-0135).

## 2. The price

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction \
  --nodes AutomorphicForm.hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear \
  --nodes AutomorphicForm.archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex \
  --nodes AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset \
  --json build/af17-advise.json
python3 port_plan.py --json build/af17-advise.json     # 1,434 raw / 1,330 decl / 4 in port / 1,326 net
python3 build/af-worklist.py rightTranslate_adjoint_weightedPairing_of_isLsXiFunction \
  hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear \
  archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex \
  isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
```

`port_plan`: raw **1,434** → declaration lines **1,330** → no duplicate copies → **−4 already in the
port** → **NET NEW 1,326**; boilerplate 104; **107 distinct declaration groups**. The worklist (Appendix
B): **1,325 declaration lines, 8 imported, 1,317 to write in 103 declarations**.

### 2.1 The substitution block is one line, and there is no port-once block

| pin declaration | row | lines | port copy | reading |
|---|---|---:|---|---|
| `continuous_archEntries` | 2 | 4 | `AutomorphicForm.IsFactorizableTestFn.lift_continuous_archEntries` (`FactorizableTestFnArchSmoothLeft.lean`) | byte-identical, **public**, tier 3: import |

That is the whole substitution block — `port_advise` reports **1 trusted, 0 suspect**, and the one row is
genuinely importable (checked, unlike SET-AF15's and SET-AF16's first passes). **`port_plan`'s port-once
block is empty** and the four pin files share no declaration: this is a transcription set in the AF11
sense, where the work is the mathematics and not the bookkeeping. The honest net is therefore **1,326**,
and the 4-line substitution is real.

**Two things this set does *not* have, and worth saying because the last three sets had them:** no
type-only `def` false positive (FR-0134), and no `private`-twin masquerading as reuse (FR-0133). The
advise file was right about both, and the manager checked the one row's visibility rather than assuming
it.

## 3. The definition gate

`spec/gate_scan.py` over the eleven `Def_` modules of the four wrappers' closure:

| pin `Def_` module | port home | used (max) | missing |
|---|---|---:|---:|
| `Def_AutomorphicForm_ArchDerivCasimirComplex` | `…/Adelic/ArchDerivCasimirComplex.lean` | **12/32** | **0** |
| `Def_AutomorphicForm_FactorizableTestFn` | `…/Adelic/FactorizableTestFn.lean` | 4/10 | **0** |
| `Def_AutomorphicForm_AdelicLsXi` | `…/Adelic/LsXi.lean` | 3/11 | **0** |
| `Def_AutomorphicForm_SmoothCuspRealization` | `…/Adelic/Cusp/SmoothRealization.lean` | 3/25 | **0** |
| `Def_NumberField_AdelicBox` | `…/NumberTheory/AdelicBox.lean` | 3/36 | **0** |
| `Def_AutomorphicForm_RightConvolution` | `…/Adelic/RightConvolution.lean` | 1/5 | **0** |
| `Def_AutomorphicForm_ConstantTerm` | `…/Adelic/ConstantTerm.lean` | 4/10 | **0** |
| `Def_AutomorphicForm_CentreCutSiegelSet` | `…/Adelic/WindowedSiegel/CentreCutSet.lean` | 1/22 | **0** |
| `Def_NumberField_TateGlobalZeta` | `…/NumberField/TateGlobal/Defs.lean` | 1/15 | **0** |
| `Def_AutomorphicForm_ProductionPinsGeneral`, `…_CuspidalConstituent` | imported by the wrappers, unused by any statement | 0 | **0** |

**No `Def_` node, no promotion, no migration**: every used declaration is ported and public, and the one
heavy gate (`ArchDerivCasimirComplex`, 12 declarations) is a wired module. Two of the eleven port homes
are legacy (`NumberTheory/AdelicBox.lean`, `…/Adelic/ConstantTerm.lean` — checked against `PORT_FILES`)
and are only imported, so no migration is owed.

## 4. The homes

**Three new modules, one per order.**

- **Order A — `FLTForHuman/AutomorphicForm/Adelic/RightTranslateAdjoint.lean`** (row 1). Subject: the
  adjointness of right translation for the `ξ`-twisted weighted pairing on a fundamental domain. Imports
  `…/Adelic/LsXi` (`IsLsXiFunction`), `…/Adelic/Basic` (`globalPoints`),
  `…/NumberTheory/AdelicHaar/GeneralLinear.lean` (`adelicGLHaar`),
  `…/NumberTheory/NumberField/TateGlobal/Defs.lean` (`TateGlobal.ideleNorm`),
  `…/Adelic/DetNormSlabFundamentalDomain.lean` (the `IsFundamentalDomain` instances on this domain — the
  only port module where `IsFundamentalDomain (globalPoints …).range` is produced for a determinant
  window), and `Mathlib.MeasureTheory.Function.L2Space` for `MemLp`.
- **Order B — `FLTForHuman/AutomorphicForm/Adelic/RightConvDerivatives.lean`** (rows 2, 3). Subject: the
  first-order structure of right convolution — along the unipotent flow and under the complex Casimirs.
  Imports `…/Adelic/RightConvolution` (`rightConv`), `…/Adelic/RightConvRegularity`,
  `…/Adelic/FactorizableTestFn` (+ `…ArchSmooth{,Complex,Left}`), `…/Adelic/ArchDerivCasimirComplex`
  (`archCasimirAtComplex`, `archCasimirBarAtComplex`, `IsArchSmoothAtComplex`, `archDerivAtComplex`),
  `…/Adelic/ArchType`/`IsotypicCuspSpace` (`IsArchBiFinite`, `ArchTypeFamily`),
  `…/NumberTheory/InfiniteAdeleRing` (`ringEquiv_mixedSpace`), `…/NumberTheory/NumberField/…`
  (`mixedEmbedding.mixedSpace` via mathlib), and mathlib's derivative/`MemLp` modules.
- **Order C — `FLTForHuman/AutomorphicForm/Adelic/RightConvStructurePreservation.lean`** (row 4).
  Subject: what right convolution preserves — cuspidality, `K_f`-smoothness, level invariance, and the
  Hecke-coset eigen property. Imports `…/Adelic/RightConvolution`, `…/Adelic/ConstantTerm` (`IsCuspidalFn`),
  `…/Adelic/SmoothAutomorphicFn` (`IsKfSmooth`), `…/Adelic/Cusp/SmoothRealization`
  (`SmoothCuspRealizationAt`, `IsHeckeCosetEigenfunctionAt`), `…/Adelic/ProductionPinsGeneral`
  (`productionPinsOf`), `…/NumberTheory/AdelicBox`, `…/Adelic/WindowedSiegel/{CentreCutSet,Set}`,
  `…/Adelic/FactorizableTestFn`, `…/Adelic/HeckeEigensystem`, `…/NumberTheory/AdelicLevel/Level`.

**Import direction, measured.** Every module imported is *below* its target: the `RightConv*`,
`Factorizable*`, `ArchDeriv*`, `LsXi`, `Cusp/*` and `NumberTheory/*` layers are all below the new
modules, and nothing in the file set imports another new module. The three orders are **mutually
independent** — the four rows are all at layer 0 of the slice — so they are parallel-safe.

## 5. The cut

**Three orders, one dispatch, three workers.**

| order | rows | silo | lines | decls | module |
|---|---:|---:|---:|---:|---|
| A — the adjointness | 1 | 433 | 397 | 37 | `RightTranslateAdjoint.lean` |
| B — the derivatives | 2 | 711 | 648 | 48 | `RightConvDerivatives.lean` |
| C — what is preserved | 1 | 290 | 272 | 18 | `RightConvStructurePreservation.lean` |
| | **4** | **1,434** | **1,317** | **103** | three files |

**Disjoint files, disjoint pin files, no cross-citation**: the three orders are safe concurrently.
Order B carries the cost (648 lines, 48 declarations, and row 3's six premises), order A the single
biggest declaration count (37), order C the widest import list.

**The manager's layer** is the three skeletons with their `spec-pin:` wires (eight lines in all), their
imports and opens; a **statements probe of all four headlines**; and the §2.1 instruction ("import the
one substitution; the rest is new"). No `Def_` node, no promotion, no migration, no legacy edit.

**Gates, per order** (recipe §6):

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, and the ok count measured
   **at both readings**: at the pin's visibility the set has **50** public declarations (1 + 48 + 1 — order B
   is 48, all public), and the dropped-`private` reading is **103**. Strip `private` with a pattern that drops
   the *modifier* (`sed 's/^private //'`), not one keyed on the keyword: `private noncomputable def` is a
   declaration form and a keyword-keyed `sed` under-reads by two (FR-0136). A `MISMATCH` at either is a
   mis-transcription; a `MISSING` at the dropped reading is a port-side helper (keep it `private`).
2. `#print axioms` on all four headlines → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` silent and its own
   `flock`/`timeout 280 lake build`. No tree build, no dependents.
4. `dedup.py --within` / `move_dead.py --dry-run` per module; the pin's own intra-file structures stay
   with the reason recorded.
5. `spec/AutomorphicFormSetAF17Consumer.lean` — **one zone per order**, real compositions, no `#check`,
   no `sorry`:
   - **A**: apply the adjointness to a pair of Ls-Xi functions and read the pairing at `y` from the
     pairing at `y⁻¹`, with the `|det y|^σ` factor explicit; then note the `MemLp` conjuncts are exactly
     what the integral needs;
   - **B**: compose the unipotent derivative with the Casimir commutation: `∂_v (archCasimirAtComplex (rightConv x f)) = archCasimirAtComplex (∂_v (rightConv x f))`
     — both sides computed by the two headlines, with the factorizability conjuncts as the side conditions;
   - **C**: feed the preservation row's output (`rightConv R.toFun f` is cuspidal and `K_f`-smooth) into
     `IsCuspidalFn`'s definitional form and read the level invariance at a `k` in the level subgroup.
   Each zone imports the new module(s) it composes; error count is the deliverable metric.
6. Zero warnings, no `sorry`/`admit`/`axiom`/`native_decide`, no `set_option` beyond `autoImplicit false`,
   no new import without a report.

### 5.0 The manager's layer (landed 2026-11-02)

Three skeletons — `RightTranslateAdjoint.lean` 63 lines (two `spec-pin:` lines, seven imports),
`RightConvDerivatives.lean` 71 (four wires, ten imports) and `RightConvStructurePreservation.lean` 65 (two
wires, eleven imports) — each silent, each built green (`flock`/`lake build <module>`, 3,864 jobs for the
closure), `check_port --force` **0 ok / 0 mismatch / 0 missing** on all three. The statements probe
(`lean/tmp/probe-af17-statements.lean`) states all four headlines verbatim and elaborates with **exactly
four `declaration uses 'sorry'` warnings**. It settled two things the brief now records:

- **Row 1's statement needs the adelic Borel space as a local instance** —
  `attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel`,
  which the pin registers at `Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean:11` and the port's
  own modules carry at `DetNormSlabFundamentalDomain.lean:358` and `PeterssonSlabPairing.lean:67`. Without
  it the statement does not elaborate (`synthInstanceFailed: MeasurableSpace (AdelicGL2 (𝓞 K) K)`); with
  it, its text is untouched — an `attribute` is not part of a signature.
- The probe needs the **union of the wrappers' opens** (`NumberField.AdelicBox`, `NumberField.AdelicHaar`,
  `AutomorphicForm.SmoothCusp`, and `open scoped ComplexConjugate` for row 4's `adelicBox`,
  `adelicAddHaar`, `IsHeckeCosetEigenfunctionAt` and `conj`).

The §2.1 decision is written into the order: import the set's one substitution
(`continuous_archEntries`, public and byte-identical) and write the rest. The headline-naming rule of
FR-0135 is an explicit instruction, and the gates ask for both checker readings (54 pin-public, 103 at the
dropped surface) and for `#print axioms` at the pin-qualified names.

### 5.1 The landing (2026-11-02)

**Files.** `RightTranslateAdjoint.lean` 63 (skeleton) → **479** (37 declarations: 36 `private` + the
headline); `RightConvDerivatives.lean` 71 → **750** (48: rows 2 and 3, all public);
`RightConvStructurePreservation.lean` 65 → **339** (18: 17 `private` + the headline);
`spec/AutomorphicFormSetAF17Consumer.lean` (215, new). **103 declarations** — the worklist's 103 exactly,
the two pin `solution`s merged into their headlines.

**Gates.** `check_port --force` **1 / 48 / 1 = 50 ok** at the pin's visibility and **37 / 48 / 18 = 103**
at the dropped-`private` reading, `0 mismatch / 0 missing / 0 own / 0 kw` at both — so every declaration in
the set, public and private alike, is a pin statement. `#print axioms` on all four headlines at their
pin-qualified names `[propext, Classical.choice, Quot.sound]`; the statements probe exactly four `sorry`
warnings; the consumer **0 errors**; own builds green (3,713 / 3,742 / 3,615 jobs, silent); `dedup
--within` **0 clusters** in all three modules; `move_dead --dry-run` **0 dead**. Zero warnings anywhere,
no `sorry`/`admit`/`axiom`/`native_decide`, no `import Mathlib`.

**Plan against actual.** Lines written **1,369** (order A 416, order B 679, order C 274) against
`port_plan`'s 1,326 net — **+3.2 %**. Declarations **103** against the worklist's 103. Checker: 50 and 103.

**Four imports were needed and are accepted**, each the port home of a lemma the pin's own `S_` file
imports: order A `NumberTheory/AdelicHaar/MulRightInvariant` (the right-invariance of `adelicGLHaar`, pin
`:5`); order B `Adelic/ArchDerivRightConvComplex` (pin `:7`) and `Adelic/ArchCasimirComplex` (pin `:11–12`,
the `𝔰𝔩₂(ℂ)` bracket table); order C `Adelic/TestFnTop` (pin `:6`, continuity and compact support of a
factorizable test function). No skeleton import was removed.

**One `set_option` was kept, and it is the pin's.** Four `set_option linter.unusedSectionVars false in`
in order B (`continuous_eA`, `continuous_eA_symm`, `N_add_smul`, `archEntries_unipotent_mul`) carry the
pin's own file-wide suppression (pin `:17`): those declarations do not *use* `[NumberField K]`, but Lean
includes the instance in the signature, and `omit` would drop it and mis-transcribe the statement. Every
other temptation was converted rather than suppressed — the `haveI`/`letI` walls became `have`/`let` (no
`haveILetI` option anywhere in the set), the unused `simp` arguments were trimmed, and the deprecated
`if_pos`/`if_neg` became `ite_eq_left`/`ite_eq_right`. Two adaptations also worth recording: `MS`/`eA`/`Ent`
are `local notation` (the pin's own device, pin `:24–26`) rather than `abbrev`s — declaring them would have
pushed the dropped reading past the pin's 103 — and `nA`'s pair is ascribed `id (… : AdeleRing …)` because
the port's `AdeleRing` is a `def` of a product and `rw [← unipotentGL2_add]` re-checks at implicit
transparency; the statement's text is unaffected and the checker matches it.

**Two instruments were wrong before the code was.** The brief's "54 at the pin's visibility" counted the
pin's public *surface* for order B (34 + 18 + 1 + 1) instead of the 48 declarations written; measured, it
is **50**. And the manager's first surface reading of order C came out **16** because the `sed` stripped
`private theorem|def|lemma` but not `private noncomputable def` — two declarations (`sliceFn`, `slice`)
stayed private and looked like a checker blind spot. Both are corrected in this brief, and the second is
**FR-0136**.

**The re-read is exact, and the four readied rows are the predicted ones.**

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 842 / 346,331 | **838 / 344,897** | −4 / −1,434 ✓ (the four rows' silo, exact) |
| `needed [literal]` | 855 / 349,806 | **851 / 348,372** | −4 / −1,434 ✓ |
| frontier F | 1,573 / 781,035 | **1,577 / 782,469** | +4 / +1,434 ✓ |
| ready rows, all namespaces | 61 / 16,494 | **61 / 16,105** | 4 out, 4 in: −389 silo (= −1,434 + 1,045) |
| ready rows, `AutomorphicForm` | 31 / 10,260 | **31 / 9,871** | −389 silo, same count |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 | — |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |
| `--selfcheck` | PASS (1,392 / 1,573) | **PASS** (1,396 `Thm_` sources, 1,577 declared names) | — |

**Four rows readied / 1,045 silo**, at exactly the forecast sizes:
`adjoint_rightConv_weightedPairing_of_isLsXiFunction` (661, 4 premises, 3/12),
`CuspidalSpectrum.exists_isLift_rightTranslate` (217, 2, 7/9),
`CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule` (112, 3, **20/23**) and
`archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex` (55, 3, 1/2). The
column's ready shelf kept its count (31) while losing 389 silo, and for the first time in five sets it
holds a row whose *consumers* number twenty.

## 6. Risk register

1. **Row 1 is an `MemLp` + Fubini argument, not algebra**: two `MemLp` conjuncts and one integral identity,
   with the twist `|det x|^-σ` and the factor `|det y|^σ`. The pin's proof goes through the change of
   variables `x ↦ x y⁻¹` on the fundamental domain and the character's growth law; the port's
   `IsLsXiFunction` API and `adelicGLHaar` are the ingredients, and the *fundamental domain* hypothesis
   `hFD` is used, not decoration.
2. **Row 2's statement is three conjuncts and 360 lines**: the `HasDerivAt` at `0` of a one-parameter
   family through `unipotentGL2 (ringEquiv_mixedSpace.symm (t • v), 0)`, the factorizability of the
   derivative, and its linearity in the direction. The mixed-space `ringEquiv_mixedSpace.symm` and its
   `t • v` spelling must be the pin's, or the statement hashes differently (FR-0123).
3. **Row 3 has six premises and is a flat public surface**: the archimedean smoothness of `x` and of its
   first and second `archDerivAtComplex` derivatives are hypotheses; the conclusion adds the same
   smoothness for `rightConv x f` and the two Casimir commutations. `CommConvC41` → `ComplexCasimirComm`
   is a namespace rename only.
4. **Row 4's support hypothesis** `hfs` (the test function vanishes only on the positive part of the level
   subgroup) is what makes the Hecke-eigen property survive; its conclusion is a four-way `∧` whose first
   conjunct is an `@IsCuspidalFn` with its measures spelled out (`@`-application with `_` holes). Copy the
   wrapper's text exactly.
5. **50 declarations are pin-public**: a mis-transcription in a helper is visible at the pin reading, which
   is the good case; the dropped-`private` reading adds the other 53 (order A's 36 and order C's 17) for
   103 in all. Record both, and cross-check the dropped reading against `dedup --within`'s declaration
   count (FR-0136).
6. **No `set_option`**, no top-level `letI` in the four statements, no `import Mathlib`.

## 7. What this set does not do

- **It does not take the Weyl pair** (2,640, measured return zero, deferred for the fifth consecutive
  pass), **nor the indicator row** (1,043, return zero), **nor the `SmoothCuspRealizationAt` trio**
  (1,407, return zero), **nor the isotypic/cuspidal-spectrum block** (925, return zero), **nor the
  `weylInv` pair** (577, return zero). Those five blocks are 6,592 silo — 64 % of the AF ready shelf — and
  none of them opens work; taking one is a decision to land bulk, and a scoping pass should say that
  plainly rather than dress it as progress.
- **It does not take the Hecke/Petersson tail** (947 silo in seven rows), which readies one 23-line row at
  project leverage 31 — cheap, and the natural companion of order C, but a different subject (the Hecke
  coset sums and the Petersson integral).
- **It does not take the four rows it readies.** They are 1,045 silo and they are **AF18's subject**:
  `adjoint_rightConv_weightedPairing_of_isLsXiFunction` (661) is the right-convolution half of order A's
  statement, and the two `rightTranslate`/`isLift`/`cuspMemberSubmodule` rows (217 / 112 / 55) are the
  `CuspidalSpectrum` API that consumes both halves. Taking them here would double the dispatch for no
  economy — they cannot be transcribed before this set exists.
- **It does not take the `diagOne` family** (2,098 in four rows), still blocked on the unported
  `TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` and the two `LanglandsTunnell`
  rows, nor the `su(2)` string (681 + 755).
- **The 4 withheld rows / 831 remain** the prunable complex-analytic subject.
- **No `Def_` node, no promotion, no migration**; three new modules, all cascade-free.

## Appendix A — the shelf, every row accounted for

### The ready block — **31 rows / 10,260 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | **SET-AF17** |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | 2 | 1/2 | **SET-AF17** |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred (§7) |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | 321 | 6 | 1/1 | **SET-AF17** |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 2 | 2/11 | **SET-AF17** |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred (§7) |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred (§7) |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred (§7) |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred (§7) |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred (§7) |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7) |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | deferred (§7) |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred (§7) |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | deferred (§7) |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | deferred (§7) |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred (§7) |

of which **4 rows / 1,434 silo** are this set's.

### The leaves block — **56 rows / 11,461 silo**

| leaf | silo | lev | disposition |
|---|---:|---:|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 3/4 | deferred (§7) |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred (§7) |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred (§7) |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred (§7) |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 1/3 | deferred (§7) |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 2/15 | deferred (§7) |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 2/7 | deferred (§7) |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | deferred (§7) |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred (§7) |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | deferred (§7) |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | deferred (§7) |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred (§7) |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred (§7) |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred (§7) |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred (§7) |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | deferred (§7) |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred (§7) |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred (§7) |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred (§7) |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 1/1 | deferred (§7) |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 1/1 | deferred (§7) |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | deferred (§7) |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | deferred (§7) |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | deferred (§7) |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | deferred (§7) |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | deferred (§7) |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | deferred (§7) |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 1/14 | deferred (§7) |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | deferred (§7) |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred (§7) |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | deferred (§7) |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 1/1 | deferred (§7) |
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 2/2 | deferred (§7) |
| `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 2/4 | deferred (§7) |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | 3/22 | deferred (§7) |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | 3/8 | deferred (§7) |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | deferred (§7) |
| `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 1/1 | deferred (§7) |
| `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 2/3 | deferred (§7) |
| `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | 2/14 | deferred (§7) |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 2/2 | deferred (§7) |
| `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 1/2 | deferred (§7) |
| `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | 5/18 | deferred (§7) |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | deferred (§7) |
| `IsKfSmooth.finite_smul_image_of_isCompact` | 40 | 3/4 | deferred (§7) |
| `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | deferred (§7) |
| `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | deferred (§7) |
| `exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 1/1 | deferred (§7) |
| `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 1/1 | deferred (§7) |
| `constantTerm_add` | 13 | 1/2 | deferred (§7) |
| `constantTerm_smul` | 11 | 1/1 | deferred (§7) |

of which **0 rows / 0 silo** are this set's.

## Appendix B — the per-row worklist

Generated by `build/af-worklist.py`. **4 of the 8 "imported" lines are the one real substitution (§2.1);
the other 4 are the second copy of the same lemma, which the import covers.**

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 397 | 0 | 397 | 37 |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 368 | 8 | 360 | 30 |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | 288 | 0 | 288 | 18 |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 272 | 0 | 272 | 18 |
| **4 rows** | **1325** | **8** | **1317** | **103** |

### `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` (order A)

397 declaration lines, 0 imported, **397 to write** in 37 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 57 | 378 | theorem |
| `integrand_central` | 40 | 321 | theorem |
| `setIntegral_translate` | 35 | 222 | theorem |
| `memLp_translate` | 34 | 276 | theorem |
| `fd_pair` | 20 | 202 | theorem |
| `integrableOn_sq_central` | 19 | 257 | theorem |
| `exists_ideleNorm_eq` | 17 | 87 | theorem |
| `integrand_shift` | 17 | 361 | theorem |
| `exists_completion_norm_eq` | 13 | 74 | theorem |
| `smulInvariant_restrict` | 12 | 124 | theorem |
| `integrand_Γ` | 11 | 310 | theorem |
| `countable_Γ` | 10 | 139 | theorem |
| `preimage_slab_eq` | 9 | 163 | theorem |
| `fd_preimage` | 8 | 149 | theorem |
| `normDet_global` | 7 | 67 | theorem |
| `slab_Γ_stable` | 7 | 114 | theorem |
| `normDet_mul` | 5 | 47 | theorem |
| `ideleNorm_one'` | 5 | 52 | theorem |
| `ideleNorm_inv'` | 5 | 57 | theorem |
| `normDet_central` | 5 | 62 | theorem |
| `Γ_smul_eq` | 5 | 109 | theorem |
| `central_comm` | 5 | 172 | theorem |
| `comm_left` | 5 | 181 | theorem |
| `preimage_right_eq` | 5 | 186 | theorem |
| `preimage_left_eq` | 5 | 191 | theorem |
| `Γ` | 4 | 37 | abbrev |
| `comm_right` | 4 | 177 | theorem |
| `slab` | 3 | 29 | def |
| `wt` | 3 | 32 | def |
| `slab_measurable` | 3 | 104 | theorem |
| `countable_K` | 3 | 136 | theorem |
| `mp_mul_right` | 3 | 157 | theorem |
| `mp_mul_left` | 3 | 160 | theorem |
| `emb_right` | 3 | 196 | theorem |
| `emb_left` | 3 | 199 | theorem |
| `μ` | 2 | 35 | abbrev |
| `Γ_smul` | 2 | 107 | theorem |

### `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` (order B)

368 declaration lines, 8 imported, **360 to write** in 30 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 84 | 267 | theorem |
| `solution` | 41 | 351 | theorem |
| `Φv_eq_zero` | 31 | 213 | theorem |
| `continuous_eA_symm` | 29 | 77 | theorem |
| `archEntries_unipotent_mul` | 23 | 150 | theorem |
| `continuous_Lf` | 15 | 252 | theorem |
| `hasDerivAt_curve` | 13 | 184 | theorem |
| `continuous_eA` | 12 | 65 | theorem |
| `continuous_unipotentGL2` | 12 | 106 | theorem |
| `nA_zero` | 9 | 37 | theorem |
| `glFin_nA` | 8 | 49 | theorem |
| `glArch_nA` | 8 | 57 | theorem |
| `hasCompactSupport_Φv` | 8 | 244 | theorem |
| `nA_add` | 7 | 30 | theorem |
| `N_add_smul` | 7 | 127 | theorem |
| `NL` | 6 | 142 | def |
| `curve_eq` | 5 | 179 | theorem |
| `deriv_curve` | 5 | 197 | theorem |
| `contDiff_Φv` | 5 | 208 | theorem |
| `N_smul` | 4 | 134 | theorem |
| `N_neg` | 4 | 138 | theorem |
| `Lf` | 4 | 175 | def |
| `Lf_zero` | 4 | 204 | theorem |
| `nA_inv` | 3 | 46 | theorem |
| `continuous_nA` | 3 | 118 | theorem |
| `nA` | 2 | 28 | def |
| `N` | 2 | 125 | def |
| `NL_apply` | 2 | 148 | theorem |
| `E` | 2 | 173 | abbrev |
| `Φv` | 2 | 202 | def |

### `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` (order B)

288 declaration lines, 0 imported, **288 to write** in 18 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 136 | 171 | theorem |
| `casimirBar_apply_eq_sum` | 25 | 79 | theorem |
| `casimir_apply_eq_sum` | 21 | 58 | theorem |
| `solution` | 16 | 307 | theorem |
| `rightConv_sum_left` | 15 | 127 | theorem |
| `rightConv_sum_right` | 13 | 114 | theorem |
| `isFactorizableTestFn_Lf` | 12 | 145 | theorem |
| `integrable_integrand` | 10 | 104 | theorem |
| `conv_smooth_and_deriv` | 6 | 157 | theorem |
| `archDerivAtComplex_sub_smul` | 5 | 48 | theorem |
| `archDerivAtComplex_add_smul` | 5 | 53 | theorem |
| `continuous_conv` | 5 | 163 | theorem |
| `word` | 4 | 35 | def |
| `wordR` | 4 | 39 | def |
| `coef` | 3 | 43 | def |
| `Lf` | 3 | 142 | def |
| `reg` | 3 | 168 | theorem |
| `sgn` | 2 | 46 | def |

### `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` (order C)

272 declaration lines, 0 imported, **272 to write** in 18 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 86 | 206 | theorem |
| `integral_integral_eq_zero` | 44 | 162 | theorem |
| `integralCLM` | 20 | 107 | def |
| `integrand_hecke` | 19 | 88 | theorem |
| `apply_mul_mul_eq` | 15 | 51 | theorem |
| `integrand_level` | 14 | 74 | theorem |
| `integralCLM_apply` | 12 | 127 | theorem |
| `hasCompactSupport_slice` | 11 | 151 | theorem |
| `eq_of_glArch_eq_of_glFin_eq` | 9 | 20 | theorem |
| `glArch_eq_one_of_mem_doubleCoset` | 9 | 42 | theorem |
| `apply_mul_eq` | 8 | 66 | theorem |
| `mul_comm_of_glFin_eq_one_of_glArch_eq_one` | 5 | 29 | theorem |
| `glArch_eq_one_of_mem` | 4 | 34 | theorem |
| `glArch_heckeGen` | 4 | 38 | theorem |
| `sliceFn` | 3 | 139 | def |
| `slice` | 3 | 142 | def |
| `slice_apply` | 3 | 145 | theorem |
| `continuous_slice` | 3 | 148 | theorem |

## Appendix C — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af17-scope.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction \
  --nodes AutomorphicForm.hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear \
  --nodes AutomorphicForm.archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex \
  --nodes AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset \
  --json build/af17-advise.json
python3 port_plan.py --json build/af17-advise.json     # 1,434 raw / 1,330 decl / 4 in port / 1,326 net
python3 build/af-worklist.py rightTranslate_adjoint_weightedPairing_of_isLsXiFunction \
  hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear \
  archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex \
  isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
python3 build/af14-forecast.py \
  AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction \
  AutomorphicForm.hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear \
  AutomorphicForm.archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex \
  AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset   # §0.3
python3 build/af17-shelf-appendix.py                                                  # Appendix A
cd ../../lean
ROWS="<the four Theorems/ wrappers>"
for pin in Def_NumberField_TateGlobalZeta Def_AutomorphicForm_RightConvolution Def_AutomorphicForm_AdelicLsXi \
  Def_AutomorphicForm_ConstantTerm Def_AutomorphicForm_FactorizableTestFn Def_AutomorphicForm_ProductionPinsGeneral \
  Def_AutomorphicForm_CuspidalConstituent Def_AutomorphicForm_ArchDerivCasimirComplex \
  Def_AutomorphicForm_CentreCutSiegelSet Def_AutomorphicForm_SmoothCuspRealization Def_NumberField_AdelicBox; do
  python3 spec/gate_scan.py --pin Definitions/$pin.lean --rows $ROWS
done
```

`--rows` takes a **list** in one flag; repeating it silently keeps only the last (AF13's finding, re-hit
at every pass since).

**Forecast on landing** (§0.3): `needed` **842 / 346,331 → 838 / 344,897**, literal
**855 / 349,806 → 851 / 348,372**, frontier **1,573 / 781,035 → 1,577 / 782,469**, ready
**61 / 16,494 → 61 / 16,105**, leaves untouched, and **four rows readied / 1,045 silo**. The re-read must
confirm every figure — and, unlike the last two sets, it must confirm four *new* rows on the shelf, of
which one is 661 lines and one carries twenty in-cone consumers.
