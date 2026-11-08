# SET-AF35 — the Satake bound at level one, and its `a² ≠ b·(N+2+N⁻¹)` form

**Status: scoped 2026-11-08, three orders (two in parallel, one capstone behind them)** — §5 is the
forecast, §6 the landing record (to be appended). Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the read
SET-AF34 left. It is the **thirty-fifth** `AutomorphicForm`/`LanglandsTunnell`-serving set.

**3 rows / 1,780 silo / 1,556 net priced (`port_plan`)** — the first row of the pair being the row
SET-AF34 readied (`satake_…`, 1,187, leverage 1/2).

| # | row | silo | lev | prem | what it says |
|---|---|---:|---:|---:|---|
| **A** | `AutomorphicForm.a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2/4 | 2 | a sesquilinear form covariant of weight `s` on the right-translate span forces `a·conj b = N^(1−s)·conj a` and `‖b‖ = N^(1−s)`; at `s = 1`, `‖b‖ = 1` |
| **B** | `LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet` | 1,187 | **1/2** | 8 | given `‖b v‖ = 1` off the level and the exceptional set, both Satake roots satisfy `‖α‖, ‖β‖ < √N`, and `a v² ≠ b v·(N+2+N⁻¹)` |
| **C** | `AutomorphicForm.SmoothCuspRealizationAt.a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet` | 125 | — | 7 | the headline: over a centre-cut cover, a genuine realization satisfies `a² ≠ b·(N+2+N⁻¹)` at every place off the level and the exceptional set |

The set is a **chain**, and that is its story: A produces the unitary input B consumes, C supplies that
input from the Petersson pairing and reads B at `s = 1`. C is not on the ready shelf because its two
unported premises are A and B — it is the third row of the story, one edge behind them (the
`SET-10`-style capstone, and here it is the *point* of the set: the level-one Ramanujan inequality).

## 0. The read

The read SET-AF34's landing left (`needed` **759 / 317,413**, `--selfcheck` PASS):

| figure | value |
|---|---:|
| `needed [F terminal]` | 759 / 317,413 |
| `needed [literal]` | 771 / 320,878 |
| frontier F | 1,657 / 809,963 |
| ready rows | 59 / 13,881 (AF 30 / 6,555; `LanglandsTunnell` 4 / 1,720) |
| leaves | 203 / 52,512 (`LanglandsTunnell` 18 / 5,597) |
| `AutomorphicForm` demand | 269 / 117,257 |
| `LanglandsTunnell` demand | 37 / 16,932 |
| withheld (FR-0044) | 4 / 831 |

**The premise audit, by hand** (the FR-0156 lesson: a last name is not a statement). All premises of
A, B and C are port declarations at the right statement, and each name is unique in the tree except
`NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow`, which has exactly two declarations — the
`RatIdele` ℚ case and the `NumberField.TateGlobal` general case the pin node names; the general one is
the premise. C's two "missing" premises are A and B by construction.

| premise | port home |
|---|---|
| `AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain` | `AutomorphicForm/Adelic/PeterssonSlabPairing.lean` |
| `AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc` | `AutomorphicForm/Adelic/DetNormSlabFundamentalDomain.lean` |
| `AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | `Cusp/GenuineRealization.lean` (SET-AF34 B) |
| `NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow` | `NumberTheory/NumberField/TateGlobal/NormExponent.lean` |
| `NumberField.TateGlobal.continuous_ideleNorm_det` | `NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean` |
| `NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult` | `AutomorphicForm/Adelic/IdeleNormDetGlue.lean` |
| `AutomorphicForm.ideleNorm_det_globalPoints` | `AutomorphicForm/Adelic/IdeleNormDet.lean` |
| `AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | `Cusp/LevelOneObstruction.lean` (SET-AF34 C) |
| `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen` (A's) | `RepTheory/LocalLanglands/HeckeCosetSystem.lean` |
| `NumberField.TateGlobal.ideleNorm_uniformizerIdele` (A's) | `NumberTheory/NumberField/TateGlobal/IdeleNormValues.lean` |

**The definition gate: none.** `port_advise --with-defs` closes over
`Def_AutomorphicForm_{ArithCuspRealization,IsotypicCuspSpace,ProductionPinsGeneral}`,
`Def_NumberField_{AdelicBox,TateGlobalZeta}` and — through the imports of the pin's capstone file —
`Def_LanglandsTunnell_RankinSelbergEuler` and `Def_NarrowRayClassGroup`. The first five are ported; the
last two are **not**, but neither is used: 0 occurrences of `rsEulerPoly`/`inducedEulerPoly`/`primeFibre`/
`rsDatum`/`narrowRay*`/`raySymbol`/`coprimeToModulus` in the three pin files (the capstone carries only
their `import` lines). Recorded, not a gate.

## 1. The cut

**One story: the Satake parameters of a genuine weight-one cusp realization are strictly inside the
critical circle, hence `a² ≠ b·(N+2+N⁻¹)`.** The three rows are a chain (A → B ← from the pairing → C),
and B is the largest single row the AF/LT shelf has carried since AF33.

| step | rows | silo | net | home |
|---|---|---:|---:|---|
| A | 468 | 468 | ~470 | **new** `Cusp/SatakeParameters.lean` |
| B | 1,187 | 1,187 | ~1,090 | **new** `Cusp/SatakeBound.lean` |
| C | 125 | 125 | ~120 | **new** `Cusp/SatakeConsequence.lean`, above A and B |
| | **3** | **1,780** | **~1,680** | 3 modules, 6 wire lines |

## 2. The price

`port_advise --nodes` on the three, then `port_plan`:

| figure | value |
|---|---:|
| raw `S_` lines | 1,780 |
| declaration lines | 1,687 |
| — duplicate copies | 17 |
| — boilerplate | 93 |
| distinct declaration groups | 106 |
| already in the port (vetted, tier 1) | 114 |
| **net new math lines** | **1,556** |

13 trusted substitutions, 0 suspect. Per row: A 37 declarations, B 68, C 2.

## 3. Homes

| order | module | the port modules the proof consumes |
|---|---|---|
| **35A** | `AutomorphicForm/Adelic/Cusp/SatakeParameters.lean` | `ProductionPinsGeneral` (it is above `Cusp/ArithRealization` → `Cusp/SmoothRealization`), `TateGlobal/IdeleNormValues`, `RepTheory/LocalLanglands/HeckeCosetSystem` |
| **35B** | `AutomorphicForm/Adelic/Cusp/SatakeBound.lean` | `PeterssonSlabPairing`, `DetNormSlabFundamentalDomain`, `Cusp/GenuineRealization`, `Cusp/LevelOneObstruction`, `IdeleNormDet`, `IdeleNormDetGlue`, `TateGlobal/NormExponent`, `TateGlobalContinuousIdeleNorm`, `Siegel/Covering` |
| **35C** | `AutomorphicForm/Adelic/Cusp/SatakeConsequence.lean` | `Cusp/SatakeParameters` (A), `Cusp/SatakeBound` (B), `Cusp/RealizationTwist` (the `‖det‖^t` twist C uses), `PeterssonSlabPairing`, `DetNormSlabFundamentalDomain` |

All three are new modules with no in-tree importers at creation. 35A and 35B are independent and
disjoint; 35C imports both, so it is dispatched when they are green (its statement is green now).

## 4. Orders and gates

`lean/tmp/WORKORDER-AF35A-satake-parameters.md`, `…-AF35B-satake-bound.md`,
`…-AF35C-satake-consequence.md`. The standard gates: `check_port --force` at 0 mismatch / 0 missing with
the surface gate run, axioms clean on the headline, the module's own build under `flock`/`timeout` and
silence, `dedup`/`move_dead`, and a `spec/` consumer zone with a real composition.

## 5. Forecast

Every line column from the silo.

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 759 / 317,413 | **756 / 315,633** |
| `needed [literal]` | 771 / 320,878 | **768 / 319,098** |
| frontier F | 1,657 / 809,963 | **1,660 / 811,743** |
| ready rows | 59 / 13,881 | **57 / 12,226** (A and B out; C was never on the shelf) |
| leaves | 203 / 52,512 | 203 / 52,512 |
| `AutomorphicForm` demand | 269 / 117,257 | **267 / 116,664** |
| `LanglandsTunnell` demand | 37 / 16,932 | **36 / 15,745** |
| `AutomorphicForm` ready | 30 / 6,555 | **29 / 6,087** |
| `LanglandsTunnell` ready | 4 / 1,720 | **3 / 533** |
| rows readied | — | see the landing |

## 6. The landing (2026-11-08)

Three orders, three modules, all gates green. A and B ran in parallel; C followed them.

| order | module | lines | declarations | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **35A** | `Cusp/SatakeParameters.lean` | 449 | 33 (1 public headline, 32 `private`; 4 helpers imported) | **1 ok** | 3,811 jobs, silent | clean |
| **35B** | `Cusp/SatakeBound.lean` | 1,223 | 68 (`WP` + 3 public lemmas + headline public, 63 `private`) | **5 ok** | 4,096 jobs, silent | clean |
| **35C** | `Cusp/SatakeConsequence.lean` | 126 | 1 | **1 ok** | 4,106 jobs, silent | clean |

The set-level probe `lean/tmp/af3536-axioms.lean` prints `[propext, Classical.choice, Quot.sound]` for all
six headlines of this set and SET-AF36, the derived ones included.

Consumers: `spec/AutomorphicFormSetAF35AConsumer.lean` (190 lines, 3 zones),
`spec/LanglandsTunnellSetAF35BConsumer.lean` (267, 3 zones),
`spec/AutomorphicFormSetAF35CConsumer.lean` (129, 4 zones) — **0 errors** each, each a real composition.

**What the set consumed**: 3 rows / 1,780 silo in **1,798 written lines** (449 + 1,223 + 126) — the first
set of the column whose written lines are *more* than its silo, because B's pin file is 1,187 lines and its
port is 1,223: a genuine transcription, not a composition. A reused 4 of the pin's 37 declarations from
`HeckeCosetSeam` and `IdeleNormValues`; B reused none (all 68 declarations are its own, 63 of them
`private` exactly as in the pin); C is the 125-line assembly, written in 71 lines of proof. No
promotion, no migration, no definition layer, no legacy touch, no tree build.

### 6.1 Deviations held for review

1. **The capstone derives its input, it does not assume it.** C's pin proof takes the unitary input
   `‖b v‖ = 1` from the Petersson pairing (`a_mul_conj_b_…` at `s = 1`) and then reads B off the
   `‖det‖^t`-twist at `t = (1-s)/2`; the `Real.rpow` cancellation `(N^{-t})² · N^{1-s} = N⁰` went through
   exactly as the pin's, with one vacuous `show` dropped (pin `:91–:93`).
2. **A re-transcribes two 3-line trivialities** (`centralScalar_mul_comm`, `det_heckeGen`) rather than
   importing `Cusp/GenuineRealization.lean` (which drags `HeckeCharacter.FiniteOrder` and `LsXiCharacter`)
   or `Cusp/RealizationTwist.lean` (which drags four modules) for them. Both are pin-copied private
   preludes; the trade is recorded, not silent.
3. **B's five mechanical drifts**: `Set.mem_setOf_eq → Set.mem_ofPred_eq` (four sites), one `convert`
   reshape for `linter.unnecessarySeqFocus`, one explicit `F` dropped, one `omit` for an unused section
   variable, `haveI → have` for Prop-valued instances (five sites), and two no-op `have`s for the frozen
   headline's unused `hc`/`hd₁`. Statements frozen throughout; all 68 declarations matched their exact pin
   line numbers under the surface gate.
4. **B keeps two pin declarations that are dead in the pin as well** (`levelPrimes`,
   `not_dvd_level_of_not_mem_levelPrimes`, pin `:950–:954`): `move_dead` reports them, the port keeps them
   as pin declarations rather than inventing a home for them.
5. **C's `hs'`**: the pin's `first | exact hs x | simpa using hs x` is a `have hs' := hs` in the port — the
   port's `PeterssonSlabPairing` binder already has the `⟨x, mem_top x⟩` shape, and the fallback trips the
   unreachable-tactic linter (zero-warning gate).

### 6.2 The re-read

The two sets of the wave landed together; the read is taken with the *next* wave's scaffold names
un-ported (FR-0157), so it prices only what is sorry-free:

```bash
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport AutomorphicForm.isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow \
  --unport AutomorphicForm.apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply \
  --unport AutomorphicForm.apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply \
  --unport CuspForm.exists_degeneracy_gamma1_hasNebentypus \
  --unport CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd \
  --unport CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div \
  --unport CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
```

| figure | before | forecast | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 759 / 317,413 | 753 / 313,678 | **753 / 313,678** ✓ |
| `needed [literal]` | 771 / 320,878 | 765 / 317,143 | **765 / 317,143** ✓ |
| frontier F | 1,657 / 809,963 | 1,663 / 813,698 | **1,663 / 813,698** ✓ |
| ready rows | 59 / 13,881 | 57 / 12,226 | **59 / 12,916** |
| leaves | 203 / 52,512 | 200 / 50,557 | **200 / 50,557** ✓ |
| `AutomorphicForm` demand | 269 / 117,257 | 267 / 116,664 | **267 / 116,664** ✓ |
| `LanglandsTunnell` demand | 37 / 16,932 | 33 / 13,790 | **33 / 13,790** ✓ |

**The one miss, and it is the sibling set's**: the ready block did not shrink by two rows — it kept its
size because SET-AF36's ODE engine **readied two rows**, `LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth`
(361) and `LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth`
(329), which cite the ODE leaves. The shelf diff is exact: A and B left the ready block (−1,655), those two
entered (+690), 59 − 2 + 2 = 59 and 13,881 − 1,655 + 690 = 12,916.

**Rows this set readied: none.** `centralChar_eq_of_agreesAwayFromFinite` was SET-AF34's, and nothing cites
the capstone yet — the rows that will consume the Satake bound
(`a_sq_ne_b_mul`'s own consumers) come after the next level of the lift.

## 7. What this set does not do

- **The `b`-side of the bound outside the unitary case.** B takes `‖b v‖ = 1` as a hypothesis; the set
  supplies it only through a *covariant self-pairing* (A at `s = 1`). A realization without such a `P`
  does not get the bound here.
- **The rest of the `SmoothCuspRealizationAt` tail** (`centralChar_eq_of_agreesAwayFromFinite` 113 is
  ready but not cut; `exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero`
  635 and `unramified_package_rightConv_sum_translate` 621 need the Hecke-coset/Whittaker machinery).
- **The Whittaker ODE engine** — the growth/linear-dependence leaves at the head of the leaves shelf —
  is SET-AF36's, cut in the same wave.
- **No definition layer, no promotion, no migration, no legacy touch, no tree build.**
