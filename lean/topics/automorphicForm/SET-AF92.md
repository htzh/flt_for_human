# SET-AF92 — the L²/archHeight bounds, Whittaker positivity, and the adelic tail

**Status: LANDED (2026-11-20).** The fourth cut of the session, and the
one that empties the AF subject's ready block: the twelve rows SET-AF91 readied. **12 rows / 6,331
silo** in five orders and six new modules. No definition gate (every pin's `Definitions/` import is
ported).

| # | order | rows | silo | module | wire |
|---|---|---|---:|---|---:|
| A | the L² bound through a Siegel cover | 1 | 1,942 | `AutomorphicForm/Adelic/LsXiL2Bound.lean` (new) | 1 |
| B | the `exists_forall` L² bound through a cover | 1 | 1,945 | `AutomorphicForm/Adelic/LsXiL2BoundExists.lean` (new) | 1 |
| C | the L² bound through a fundamental domain | 1 | 1,413 | `AutomorphicForm/Adelic/LsXiL2FundamentalDomain.lean` (new) | 1 |
| D | Whittaker positivity and the unfolding identity | 2 | 477 | `AutomorphicForm/Adelic/WhittakerPositivity.lean` (new) | 9 |
| E | the adelic trace/measure tail and the production-pins tail | 8 | 554 | `AutomorphicForm/Adelic/AdelicTraceTail.lean`, `AutomorphicForm/Adelic/ProductionPinsTail.lean` (new) | 2 + 8 |

**A/B/C are not flattened-public pins.** Each of the three 1.4–1.9k-line pins declares its entire
engine **`private`** and one public `solution`: 134 / 134 / 101 declarations, of which 1 / 1 / 1 is
public. So each order's real work is the private engine at the pin's names plus the row proof; the
`scaffold_audit` wire is 1 and is complete at the scaffold, `check_port` reads 1 `ok`, and the
acceptance test is the proof, the silence and the axioms — not a declaration count. The same holds
for the two `AdelicTraceTail` rows. D and the `ProductionPinsTail` module are ordinary flattened
pins (9 and 8 wire publics).

**A and B are near-duplicate pins** (133 common declarations, 132 identical statement hashes; the
two rows differ, and each pin has one unique private helper, `square_mass_le` vs
`square_mass_le_uniform`). The port mirrors the pin: each module transcribes its own **private**
engine, so the duplication stays private and invisible to `check_port` — the pin's own shape, not a
port-once candidate, because a `private` engine cannot be imported.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af92_read.json
```

| figure | before (AF91 landing) | after this set's scaffolds | corrected (`--port` ×2, §7) |
|---|---:|---:|---:|
| `needed [F terminal]` | 466 / 228,886 | **456 / 222,580** | **454 / 222,555** |
| ready rows | 19 / 8,275 | **16 / 7,921** | **15 / 8,732** |
| leaves | 74 / 21,398 | **74 / 21,398** | 74 / 21,398 |
| withheld (FR-0044 guard) | 3 | 3 | 3 |

**Seven rows become ready, 5,952 silo** — the weight-one lift's analysis, which the L² bounds and
the fundamental-domain row unlock together:

| row readied | silo | by |
|---|---:|---|
| `LanglandsTunnell.isCuspidalFn_weightOneLift` | 1,831 | C (the fundamental-domain L² bound) |
| `LanglandsTunnell.isHeckeCosetEigenfunctionAt_weightOneLift` | 1,753 | A/B |
| `LanglandsTunnell.weightOneLift_centralScalar_mul` | 1,134 | A/B |
| `DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift` | 472 | A/B |
| `LanglandsTunnell.isKfSmooth_weightOneLift` | 438 | A/B |
| `AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le` | 216 | D |
| `NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const` | 108 | E (the idèle measure row) |

The plain read keeps the two `AutomorphicForm.IsCuspidalFn.add`/`.smul` rows on the ready shelf even
though this set ports them (25 silo): the frontier's name tier **rejects short generic last names**
(`add`, `smul`, `mul`, …) to avoid false credits, so a ported row with such a name can never leave
the shelf. §7 records the correction and `--port` reproduces it.

## 1. The cut

| # | row | silo | wire | pin shape |
|---|---|---|---:|---:|---|
| A1 | `AutomorphicForm.setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre` | 1,942 | 1 | 134 decls, 133 private |
| B1 | `AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre` | 1,945 | 1 | 134, 133 private |
| C1 | `AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain` | 1,413 | 1 | 101, 100 private |
| D1 | `AutomorphicForm.exists_whittakerCoefficient_one_ne_zero` | 253 | 9 | 16 |
| D2 | `AutomorphicForm.integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj` | 224 | | 8 |
| E1 | `NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace` | 154 | 2 | 14 |
| E2 | `NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top` | 149 | | 7 |
| E3 | `AutomorphicForm.exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le` | 91 | 8 | 2 |
| E4 | `AutomorphicForm.ext_of_invariant_of_forall_glFin_eq_one_rat` | 72 | | 7 |
| E5 | `AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat` | 63 | | 2 |
| E6 | `AutomorphicForm.IsCuspidalFn.add` | 14 | | 1 |
| E7 | `AutomorphicForm.IsCuspidalFn.smul` | 11 | | 1 |

**The five stories.**

* **A/B/C** are one family: the L² mass of a continuous `LsXi` function over a
  unipotent-and-compact translate of the adelic box, bounded by a power of the archimedean height
  times the L² mass over a covering Siegel window (A), a universal `∃ T₁ A M` for every such
  function (B), or over a fundamental domain of the norm slice (C). A and B are the pin's own
  duplication; C replaces the cover by a fundamental domain and brings the norm-slice measure.
* **D** is the Whittaker coefficient's positivity at `1` (the Bessel input) and the unfolding
  identity `∫ φ · conj ψ = ∑' wc · conj wc`.
* **E** is the tail: the local standard character as the trace character, the finite Haar measure of
  a norm slice, the ample-window `ncard` bound, the invariance/extension lemma on rational points,
  the production-pins `U_mul` lemma, and the cuspidal closure under `+` and `·`.

## 2. The homes and the manager's layer

| module | home / direction | manager's work |
|---|---|---|
| `AutomorphicForm/Adelic/LsXiL2Bound.lean` | new, above `LsXi`, `LsXiCharacter`, `Siegel/Covering`, the `WindowedSiegel` set modules, `ConstantTerm`, AF91 `LatticeCounting`, AF90 `AdelicHeight/Compactness`, `AdelicDiscreteness`, `TateGlobal/Defs` | row statement + wire; 134-private engine is the worker's step 1 |
| `AutomorphicForm/Adelic/LsXiL2BoundExists.lean` | same direction; its own pin's engine | same |
| `AutomorphicForm/Adelic/LsXiL2FundamentalDomain.lean` | same, plus `FnTwist`, `AdelicVolume`, `TateGlobal` | row statement + wire + the `glBorel` local instance |
| `AutomorphicForm/Adelic/WhittakerPositivity.lean` | new, above `WhittakerCoefficient`, AF91 `WhittakerSum`, `BesselInequality`, `AdelicBox`, `GlobalAddChar/Circle`, AF90 `IntegralAdeles` | two row statements; 9-public target |
| `AutomorphicForm/Adelic/AdelicTraceTail.lean` | new, above `AdelicTraceFin`, `CompletionBaseChange`, `StandardLocalConstantsAt`, `IdeleProductMeasure`, `IdeleClass/Vocab`, `TateGlobal/Defs`, AF91 `FundamentalDomain`, `TateGlobalContinuousIdeleNorm` | two row statements; wire 2, complete at the scaffold (proofs only) |
| `AutomorphicForm/Adelic/ProductionPinsTail.lean` | new, above `CentreCutSiegelSetAmple`, `LsXi`, AF91 `AmpleFiniteness`, `ProductionPinsCompact`, `AdelicDock/LocalEmbedding`, `DeltaLift`, AF91 `IsotypicVanishing`, `ConstantTerm` | five row statements; 8-public target |

All six scaffolds elaborate and their rows check (`1 / 1 / 1 / 2 / 2 / 5` `ok` at scaffolding); no
hub is edited and the five orders touch disjoint files (E's two files are one order).

**Two statement corrections the manager already made.** The `IsCuspidalFn.add`/`.smul` rows are
stated in the pin's unqualified text inside a nested `namespace IsCuspidalFn` (the wrapper's
qualified spelling does not hash to the pin); and the `glBorel`/`ideleBorel` local instances the
wrappers carry are re-attached in C and E1. Both are why the scaffold reads 5 ok and 2 ok rather
than 3/0 and 0.

## 3. The orders

Orders in `lean/tmp/af92/WO.md` (untracked, like the earlier sets' order files), five orders,
disjoint files, five dispatches in parallel.

## 4. The forecast

The scaffolds are the measurement point: after them `needed` is **456 / 222,580** plain and
**454 / 222,555** with the two generic-name rows credited; ready **16 / 7,921**, leaves
**74 / 21,398**. The set's return is the seven readied rows of §0 (**5,952 silo**).

## 5. The gates (per order)

As SET-AF89–AF91 §5, unchanged, with one emphasis: for A/B/C and E1 the `scaffold_audit` wire is 1
or 2 and complete at the scaffold, so the gates that bite are the row proof, the module silence, the
axioms, `dedup` and `move_dead` — and the private engine must be transcribed at the pin's
statements even though `check_port`'s summary counts only the public row.

## 6. Risks

| # | risk | mitigation |
|---|---|---|
| 1 | A/B/C are the largest private-engine transcriptions in the session (100–134 declarations, 1.4–1.9k lines each) | transcribe the pin in its own order (window, region, centre, mass, the slab decomposition, the L² comparison); the proofs replay |
| 2 | A and B are near-duplicates (132 identical statements) and two agents will do nearly the same work | accepted: the pin duplicates them privately, and a private engine cannot be shared across modules |
| 3 | D's `exists_whittakerCoefficient_one_ne_zero` is the Bessel positivity input | its premise is AF91's `hasSum_whittakerCoefficient`; the scaffold imports `BesselInequality` and `WhittakerSum` |
| 4 | E's rows are eight small declarations across two modules and two namespaces | one order, two files; the two `constantTerm` rows (AF91) are imported, not re-proved |
| 5 | the `add`/`smul` rows will stay on the shelf after landing (§0) | recorded; the corrected read uses `--port` on both |

## 7. The landing (2026-11-20)

All five orders landed with no `sorry`, no heartbeat floor, no linter option, and no hub or existing
module edited. **6 new modules, 6,575 lines, 425 declaration commands (17 public + 408 private).**

| module | rows | lines | decls (pub/priv) | checker | audit | dedup | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|
| `AutomorphicForm/Adelic/LsXiL2Bound.lean` | A1 | **2,000** | 134 (1/133) | **1 ok / 0 / 0** | complete (1 wire, 0 imported) | 1 (pin's own) | 125,000 / 62,500 |
| `AutomorphicForm/Adelic/LsXiL2BoundExists.lean` | B1 | **2,000** | 134 (1/133) | **1 ok / 0 / 0** | complete | 1 (pin's own) | 160,000 / 80,000 |
| `AutomorphicForm/Adelic/LsXiL2FundamentalDomain.lean` | C1 | **1,497** | 101 (1/100) | **1 ok / 0 / 0** | complete | **0** | 40,000 / 20,000 |
| `AutomorphicForm/Adelic/WhittakerPositivity.lean` | D1–D2 | **429** | 19 (4/15) | **4 ok / 0 / 0** | complete | **0** | 10,000 / 5,000 |
| `AutomorphicForm/Adelic/AdelicTraceTail.lean` | E1–E2 | **363** | 23 (2/21) | **2 ok / 0 / 0** | complete | 2 (pins' own) | 6,250 / 3,125 |
| `AutomorphicForm/Adelic/ProductionPinsTail.lean` | E3–E7 | **286** | 14 (8/6) | **8 ok / 0 / 0** | complete | **0** | 6,250 / 3,125 |
| | **12** | **+6,575** | **425 (17/408)** | **17 ok, 0 mismatch, 0 missing, 0 own** | 6 complete | 4 pin-own | |

`move_dead` reads `0 declarations, 0 lines` on all six; every row and every probed engine is on
`[propext, Classical.choice, Quot.sound]`; the six modules build one at a time under the lock.

**The private-engine pins.** A and B are each the pin's 134-declaration engine transcribed whole
(133 private), with 0 statement-hash differences against their pins (verified with
`statement_db.parse_file`, because `check_port` skips private declarations — FR-0242); C is the same
at 101. The rows sit at the end of their modules (FR-0239) with statements byte-identical.

**Consumers** — one per order that has a non-trivial interface: `spec/AutomorphicFormSetAF92DConsumer.lean`
(the unfolding identity at `φ₁ = φ₂` gives `∫ ‖φ‖² = ∑' ‖wc‖²`, through `Complex.mul_conj` /
`normSq_eq_norm_sq`) and `spec/AutomorphicFormSetAF92EConsumer.lean` (`IsCuspidalFn.add` + `.smul` on
`c·f₁ + f₂`). A/B/C's rows are already their own consumer-facing `∃ … ∀` interface and need no
separate zone.

### The decisions of the landing

1. **The pin's private engines are transcribed per module, not shared.** A and B share 132 identical
   statements and C shares 70; all are `private` in the pins and unimportable, so each module carries
   its own engine — the pin's own duplication. `dedup --within` is module-scoped and clean; a
   cross-module dedup would show the block twice, as the pins themselves do.
2. **`check_port`'s `1 ok` is not the engine gate** (FR-0242). The name/statement diff against the
   pin is the measurement for a private-engine module; A/B/C report 0 differences.
3. **The two generic-name rows** (`IsCuspidalFn.add`/`.smul`) are ported and checker-green but cannot
   leave the shelf (FR-0240); the corrected read uses `--port` on both.
4. **FR-0241 fixed after the wave**: `spec/lean_parser.py`'s `strip_line_comments` now blanks the
   comment with spaces instead of deleting it, so `namespace_events` offsets are offsets in the text
   passed to it. `statement_db.py selftest` passes (122 declarations, 6 files, 16 assertions), the
   corpus was rebuilt (718,874 declarations), and the six AF92 modules re-check unchanged. The
   pre-existing `--`-comment misattributions elsewhere in the corpus (full names, not statement
   hashes) are now corrected on the next parse.

### The set's numbers

| figure | before (AF91) | after scaffolds | **after landing (plain)** | **corrected (`--port` ×2)** |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 466 / 228,886 | 456 / 222,580 | **456 / 222,580** | **454 / 222,555** |
| ready rows | 19 / 8,275 | 16 / 7,921 | **16 / 7,921** | **15 / 8,732** |
| leaves | 74 / 21,398 | 74 / 21,398 | **74 / 21,398** | 74 / 21,398 |
| withheld | 3 | 3 | **3** | 3 |

The landing read equals the scaffold read. The set's return is the seven readied rows of §0
(**5,952 silo**, the weight-one lift's analysis), and the corrected read adds a new 836-silo row
(`LanglandsTunnell.exists_mem_finset_inf_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot_of_mem_sup`)
that the two generic-name rows' credit readies.

### Frictions this set produced

* **FR-0241** — `namespace_events` offsets were computed on the line-comment-stripped text; fixed
  (length-preserving blanking), selftest and corpus rebuild green.
* **FR-0242** — `check_port` skips private port declarations, so a private engine's verification is
  the elaboration + proof + axioms + a `statement_db.parse_file` diff, not the checker's `N ok`.
* **FR-0229 recurred at five sites** — `WindowedSiegel/WindowVanishing` (A, B), `LatticeCounting`
  (E1, E2), plus the C and D imports; all recorded.
* **FR-0239 recurred** — every row that follows its engine moved to the module end (A, B, C, D, E).
* **FR-0231/FR-0235 recurred** — `prod_le_prod`→`prod_le_prod₀` (A, B, C), `ENNReal.le_tsum`'s index,
  `secondCountableTopology_restrictedProduct`, the `if_pos`/`if_neg`/`Set.mem_setOf_eq` renames, and
  the `haveI`/`letI` spelling.
