# SET-AF19 — the cusp subcarrier as a module for the right action, and the idèle norm at trivial finite part

**Status: LANDED 2026-11-07** — the manager's lane plus one dispatch of three orders, all gates green; **§5.1 records the landing and the re-read**, exact on every figure against §8's forecast, and the five predicted rows are the five that became ready. Read off the
D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF18 left. It is the **nineteenth** `AutomorphicForm`-serving set, and it is the third and last
set of the right-action story: AF17 ported right translation's adjoint and right convolution's
derivatives, AF18 convolution's adjoint and what convolution preserves, and this one makes the two
right actions **operators on the carrier and its cusp subcarrier** — averaging over a compact
subgroup, the convolution norm bound, the subcarrier maps — plus the 63-line leaf that has the
largest return on the whole shelf.

The set is **8 rows / 1,560 silo**, **1,357 declaration lines of which ~1,266 are new** (91 lines are
the prelude the pin copies into its two averaging files), in **19 declarations** — in **three orders
over two new modules and one insertion**.

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| A — averaging cusp lifts over a compact subgroup | 2 | 973 | 875 | new `Adelic/Cusp/SpectrumIntegration.lean` |
| B — right convolution on the cusp subcarrier | 4 | 442 | 366 | new `Adelic/Cusp/SpectrumConvAction.lean` |
| C — the idèle norm at trivial finite part | 2 | 145 | 116 | insertion into `NumberField/TateGlobal/IdeleNormValues.lean` |
| | **8** | **1,560** | **1,357** | three orders, three workers |

The work orders are `lean/tmp/WORKORDER-AF19A-averaging-cusp-lifts.md`,
`…-AF19B-conv-on-subcarrier.md` and `…-AF19C-idele-norm-snd-one.md` (tmp is not published).

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af19.json
python3 frontier.py --selfcheck
```

| figure | value (AF18's landing) | SET-AF18 §5.1 (at its landing) |
|---|---:|---:|
| `needed [F terminal]` | **826 / 343,413** | 826 / 343,413 |
| `needed [literal]` | 838 / 346,878 | 838 / 346,878 |
| frontier F | **1,590 / 783,963** | 1,590 / 783,963 |
| ready rows, all namespaces | **62 / 17,281** | 62 / 17,281 |
| ready rows, `AutomorphicForm` | **33 / 11,079** | 33 / 11,079 |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (1,409 `Thm_` sources, 1,590 names) | PASS |
| correction needed | none | none |

The read is the same read AF18 closed on, and **the instrument is now honest**: AF18 repaired the
three false ported markers it met (`NumberField.AdeleRing.secondCountableTopology`,
`IsCuspidalFn.rightTranslate` and its prerequisite `constantTerm_rightTranslate`), so this scoping
needs no `--unport` correction for the first time since SET 7. That is the measurement that lets the
shelf be trusted as it stands.

## 1. Why this block

Two candidates were on the shelf, and the choice is the recipe's "what does the landing buy".

| candidate | rows | silo | rows readied | silo readied |
|---|---:|---:|---:|---:|
| **the two readied carrier rows + the idèle-norm leaf (this set)** | 8 | 1,560 | **+5** | **+3,447** |
| the Hecke-coset averaging pair (`exists_integral_rightConv_eq_rightConv` + the Borel–Fubini row) | 2 | 943 | 0 | 0 |
| the Hecke/Petersson tail | 7 | 947 | +1 | +23 |
| the five bulk blocks (the Weyl pair, the indicator row, the `SmoothCuspRealizationAt` trio, the isotypic block, the `weylInv` pair) | 15 | 6,592 | 0 | 0 |
| the `SmoothCuspRealizationAt`/`sesqForm` rows alone | 4 | 2,355 | 0 | 0 |

- **The 63-line leaf is the single best buy on the shelf.** `NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one`
  (63 silo, 11 in-cone / 73 project consumers) readies **five rows / 3,330 silo**, and they are the
  `diagOne` family AF17, AF18 and AF19 each had to defer: the diagOne Whittaker formula (913), the
  flat/nonneg archimedean test factor (905), and the two `CuspidalConstituent` diagOne rows
  (716 / 714) — plus `exists_ideleNorm_eq_and_snd_eq_one` (82, **3 / 51**), which is this set's
  second order-C row. Measured: `silo readied ÷ silo spent = 23`.
- **The six carrier rows are the story AF18 opened and readied.** They are the `CuspidalSpectrum` API
  for the right action: the two averaging rows (which the pin proves twice, once for a compact open
  `U` and once for the archimedean row-isometry product — one engine, two headlines), the
  `toCarrier` norm bound for a convolution, and the three subcarrier maps. Their landing readies
  `exists_isLift_rightConv` (199, **11/13**), the lift of right convolution as an operator on the
  carrier — the natural centrepiece of AF20.
- **The two averaging rows are a port-once case**, which is the recipe's "the pin's own duplication is
  the story": the two `S_` files open with the *same seven declarations* (lines 30–115 in both), ~91
  lines the port writes once and publicly at the pin's names.

## 2. The rows

| row (`AutomorphicForm.` dropped) | silo | work | decls | prem | lev | what it states |
|---|---:|---:|---:|---:|---:|---|
| `CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact` | 510 | **461** | 7 | 3 | 1/1 | averaging cusp lifts over a compact open `U ≤ finiteAdelicGL2Subgroup`: `∫ u, c u • S u (toCuspSubcarrier φ) = toCuspSubcarrier (∫ u, c u * φ (· * u))`, the average again a cusp member |
| `CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate` | 463 | **414** | 6 | 3 | 1/1 | the same for the archimedean row-isometry product through `adelicArchGLIncl ∘ ι` |
| `CuspidalSpectrum.exists_norm_toCarrier_rightConv_le` | 253 | **233** | 1 | 4 | 1/1 | a norm bound `‖toCarrier (rightConv φ g)‖ ≤ C ‖toCarrier φ‖` with both `MemLp` conjuncts produced |
| `CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule` | 70 | **49** | 1 | 6 | **10/13** | convolution of a cusp member by a factorisable `f` is a cusp member |
| `CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv` | 53 | **36** | 1 | 2 | **7/7** | a lift `T` of `φ ↦ rightConv φ f` preserves the cusp subcarrier |
| `CuspidalSpectrum.map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv` | 66 | **48** | 1 | 3 | 1/1 | … and lands in the level-`N` subcarrier when `f` is bi-invariant under `(fdPins F Φ₀).U N` |
| `NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` | 63 | **50** | 3 | 1 | 1/1 | at trivial finite part `ideleNorm a = ∏ w, ‖a.1 w‖ ^ w.mult` |
| `NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one` | 82 | **66** | 5 | 1 | **3/51** | every `r > 0` is `ideleNorm z` for some idèle `z` with trivial finite part |
| | **1,560** | **1,357** | **25 pin / 19 written** | | |

`exists_ideleNorm_eq_and_snd_eq_one` is one edge behind `ideleNorm_eq_prod_norm_…` and is taken with
it (SET 10's precedent); the pin's own proof consumes the first row.

**The premise audit, by hand.** Every premise of every row is in the port at the right statement,
checked against its `Theorems/` wrapper:

| premise | port home |
|---|---|
| `CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule` (both averaging rows) | `Adelic/Cusp/SpectrumTranslation.lean` (SET-AF18 order B) |
| `isCompact_rowIsometrySubgroup_detOne` | `Adelic/MaximalCompactFactors.lean` |
| `NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo` | `NumberTheory/AdelicLevel/Countability.lean` (SET-AF18 §3.1) |
| `adjoint_rightConv_weightedPairing_of_isLsXiFunction` (norm bound, cusp preservation) | `Adelic/RightConvAdjoint.lean` (SET-AF18 order A) |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | `Adelic/RightTranslateAdjoint.lean` (SET-AF17) |
| `isCuspidalFn_rightConv`, `isKfSmooth_rightConv` | `Adelic/RightConvPreservation.lean` (SET-AF18 order C) |
| `continuous_rightConv_of_continuous_of_hasCompactSupport` | `Adelic/RightConvRegularity.lean` (SET-AF18 §3.2 promotion) |
| `exists_hasModulus_of_isAutomorphicFnAt_of_continuous` | `Adelic/Cusp/SpectrumCarrierAPI.lean` |
| `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` | `Adelic/RightConvNeZero.lean`'s cluster |
| `ideleNorm_det_eq_prod_archDetNorm_pow_mult` (order C) | `NumberTheory/NumberField/TateGlobal/…` |
| `continuous_ideleNorm` (order C) | `NumberTheory/NumberField/TateGlobal/ContinuousIdeleNorm.lean` |

**The definition gate: none.** Every `Def_` module in the eight wrappers' closure is ported, and all
eight statements elaborate today (§4) — that is the measurement, not a claim.

## 3. The price

`port_advise` / `port_plan` over the eight rows:

* **substitute** (import, do not re-prove): four pin declarations —
  `continuous_adelicArchGLIncl'` → `AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl`
  (byte-identical) and `eq_of_glArch_eq_of_glFin_eq` → `AutomorphicForm.gl_ext`
  (`Adelic/MaximalCompactFactors.lean`, binder spelling only), each appearing in both averaging files;
  21 lines of the slice.
* **port once**: the averaging pair's **shared prelude** — `continuous_iota`,
  `commute_of_mem_finiteAdelicGL2Subgroup`, `eLpNorm_two_pow_two`, `secondCountableTopology_KK`,
  `lintegral_sq_le` (+ the finite file's `isKfSmooth_integral_mul_apply_mul`) — 91 duplicate lines the
  `port_plan` budget removes. `secondCountableTopology_KK` is also already in the port
  (`ArchApproxIdentity/ArchInfra.lean:118`), so it joins the substitute list.
* **generalise**: no same-name pair inside the set. The pin's `KK` abbrev is a compressed name and is
  not carried (order A's §4.1): where a public statement needs the type it is written out, with an
  `own:` marker row.
* **drags**: the two averaging headlines are the only pin-public declarations of their files that are
  not prelude; every order-B row is a single public declaration; order C's rows carry 4 and 5
  declarations, of which the pin's are 2 public matrix facts (`map_diagOne`, `det_diagOne`) and 4
  `private` helpers (`archIdele` and its three companions), the `private` ones staying `private`.

**Budget**: raw 1,560 → declaration lines 1,397 → 91 deduplicated by porting the prelude once → 1,306
once-cost → 21 already in the port → **1,285 net new math lines**; the worklist's per-row "to write"
sums to 1,357 *before* removing the 91-line duplicate (≈1,266), which is the same number to 1.5 %.

## 4. Ground prep (manager's lane — landed before the cut)

| file | lines | wires | status |
|---|---:|---:|---|
| `Adelic/Cusp/SpectrumIntegration.lean` (new) | 122 | 4 | elaborates, **2 `sorry` warnings** (order A's headlines) |
| `Adelic/Cusp/SpectrumConvAction.lean` (new) | 111 | 8 | elaborates, **4 `sorry` warnings** |
| `NumberField/TateGlobal/IdeleNormValues.lean` (insertion) | 98 → 124 | +4 | elaborates, **2 `sorry` warnings**; the two landed headlines untouched |

`check_port --force` reads **2 / 4 / 4 ok, 0 mismatch, 0 missing, 0 own** — the eight statements are
the pin's before a line of proof exists. All three modules build green with only their `sorry`
warnings.

The imports were settled here: order A needs `MaximalCompactFactors`, `TestFnNearIdentity`,
`AdelicLevel/Projections` and `AdelicLevel/Countability`; order B needs `RightConvAdjoint`,
`RightConvPreservation`, `RightConvRegularity`, `CarrierPins`; order C needs
`AdelicLevel/HeckeGen` (for `diagOne`), which the worker adds and reports (§4.3 of its order).

## 5. The cut

**Three orders, two new modules and one insertion, three workers.**

1. **Order A** (2 rows, 973 silo): `Adelic/Cusp/SpectrumIntegration.lean`. The shared prelude is
   written **once, publicly, at the pin's names**, and the two headlines after it. The pin's own
   `set_option synthInstance.maxHeartbeats 400000 / maxHeartbeats 1600000` above its `solution` is
   **not** transcribed: the port's rule is that a declaration which does not fit the low cap is an
   instance-inference defect to diagnose, never a bump.
2. **Order B** (4 rows, 442 silo): `Adelic/Cusp/SpectrumConvAction.lean`. Row 1 is the pairing
   argument (`C = sqrt (N1 * N2)` from AF18's adjointness row at `u = v = φ`); rows 2–4 are the
   three-way conjunct chase and two closure arguments, and use AF18's four preservation rows.
3. **Order C** (2 rows, 145 silo): an insertion into the landed, checker-green
   `TateGlobal/IdeleNormValues.lean`, whose subject ("the values of the idèle norm") is exactly this.
   Its 63-line row is the shelf's best buy; the pin's `RS11DIL` namespace label is dropped.

**Disjoint files, disjoint pin sources**: A and B share the `Cusp/` directory but no file and no pin
source; C is in `NumberField/`. All three are safe concurrently (only the build lock is shared).

Gates are the recipe's §6 plus this set's three: no `set_option` of any kind; the statement texts are
frozen (all eight already read `ok`); one consumer file per order
(`spec/AutomorphicFormSetAF19{A,B}Consumer.lean`, `spec/TateGlobalIdeleNormConsumer.lean`).

### 5.1 The landing (2026-11-07)

**Files.** `Adelic/Cusp/SpectrumIntegration.lean` 122 (skeleton) → **1,031** (7 declarations: the
shared prelude written once, 5 declarations, 128 lines, against the pin's 2 × 86 = 172, plus the two
headlines at 363 and 418); `Adelic/Cusp/SpectrumConvAction.lean` 111 → **473** (4, all public);
`NumberField/TateGlobal/IdeleNormValues.lean` 98 → **225** (the two landed headlines untouched, +8
declarations); three consumers — `spec/AutomorphicFormSetAF19AConsumer.lean` (185), `…B…` (84),
`spec/TateGlobalIdeleNormConsumer.lean` (52). **19 declarations** (15 public, 4 `private`), not the
worklist's 25: the two averaging files share 6 prelude declarations, which the worklist counts once
per file.

| order | rows | plan (worklist) | written | decls | module |
|---|---:|---:|---:|---:|---|
| A | 2 | 875 | **909** (+3.9 %) | 7 | `SpectrumIntegration.lean` 1,031 (prelude 128 + headlines 781) |
| B | 4 | 366 | **367** (+0.3 %) | 4 | `SpectrumConvAction.lean` 473 |
| C | 2 | 116 | **101** (−12.9 %) | 8 | `IdeleNormValues.lean` 225 |
| | **8** | **1,357** | **1,377** (+1.5 %) | **19** | three modules |

**Gates** (all re-run by the manager on the landed tree):

1. `check_port --force` per module: **5 ok + 2 own** (A), **4 ok** (B), **6 ok** (C) — **15 ok, 0
   mismatch, 0 missing, 2 own, 0 kw**. The two `own:` rows are A's, both recorded in
   `spec/decl_markers.tsv` with their reasons (§ below).
2. `#print axioms` on all eight headlines at their pin-qualified names →
   `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
3. Three module builds green and **silent** (`flock`/`timeout`; 4,105 / 3,879 / 3,668 jobs); the edit
   loop silent on all three; **no `set_option` anywhere** — including the pin's
   `set_option synthInstance.maxHeartbeats 400000 in set_option maxHeartbeats 1600000 in` above the
   finite averaging headline, which was **not transcribed and not needed**: the declaration fits
   `-DmaxHeartbeats=200000` at the first try, so §6's risk 1 did not materialise and there is no
   instance-inference defect to diagnose.
4. `dedup --within`: 7 / 4 / 14 declarations, **0 duplicate clusters**, 0 removable lines.
   `move_dead --dry-run`: **0 dead** in all three (order C's two `diagOne` helpers are public and
   therefore kept, as the pin has them public).
5. Three consumers, **0 errors / 0 warnings** each, no `#check`, no `sorry`.

**The re-read is exact against §8's forecast.**

| figure | before | after | Δ | forecast |
|---|---:|---:|---:|---|
| `needed [F terminal]` | 826 / 343,413 | **818 / 341,853** | −8 / −1,560 | −8 / −1,560 ✓ |
| `needed [literal]` | 838 / 346,878 | **830 / 345,318** | −8 / −1,560 | −8 / −1,560 ✓ |
| frontier F | 1,590 / 783,963 | **1,598 / 785,523** | +8 / +1,560 | +8 / +1,560 ✓ |
| ready rows | 62 / 17,281 | **60 / 19,250** | 7 out, 5 in: +1,969 | +1,969 ✓ |
| leaves | 225 / 57,500 | 225 / 57,500 | — | — ✓ |
| `--selfcheck` | PASS (1,409 / 1,590) | **PASS** (1,417 sources / 1,598 names) | — | — |

**Rows readied: the predicted five** — 913, 905, 716, 714 (the `diagOne` family) and 199
(`exists_isLift_rightConv`, 11/13). AF's ready shelf is now **32 rows / 13,111 silo**, of which AF20's
subject is the `diagOne` family, 3,248.

**Deviations, by class.**

* **One pin statement is FALSE on this mathlib, and it is recorded as such.** The pin's
  `eLpNorm_two_pow_two` (its `S_` file `:76`) has no measurability hypothesis; at mathlib v4.34
  `MemLp f p μ := eLpNorm f p μ < ∞` and `eLpNorm := ⊤` off the a.e. strongly measurable functions, so
  the identity fails for a non-a.e.-strongly-measurable `φ`. The port carries
  `{φ} (hφ : AEStronglyMeasurable φ ν)` — discharged by every pin use (continuity, or
  `Lp.aestronglyMeasurable`) — with an `own:` row. This is the set's one statement-level drift with
  the pin, and it is a mathlib change, not a transcription slip.
* **`KK` not carried** (`continuous_iota`), second `own:` row. The other two `KK` prelude rows were
  *imported*: `secondCountableTopology_KK` → `ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀`,
  and `continuous_adelicArchGLIncl'`/`eq_of_glArch_eq_of_glFin_eq` → `TestFnNearIdentity`/`gl_ext`.
* **One route change, forced by the port's import direction.** Order C's row 1 is proved by the
  finite-`finprod` collapse rather than the pin's determinant route: the pin's
  `ideleNorm_det_eq_prod_archDetNorm_pow_mult` lives in `AutomorphicForm/Adelic/IdeleNormDetGlue.lean`,
  and `NumberField/TateGlobal/Defs.lean`'s header fixes the rule that the `NumberField` tree does not
  import `AutomorphicForm`. Same statement, different proof (one v4.34 wrinkle: the finite factor's
  norm is not syntactically `1`, so the collapse is stated as a `have` before rewriting).
* **v4.34 proof-level drift** (statements untouched): `MemLp` is a `def`, not a structure, so the
  pin's `⟨hmeas, hsq⟩` constructions become the bare `< ⊤` closed by `lt_of_le_of_ne le_top`, and
  `hψ.1` becomes `hψ.aestronglyMeasurable`; `MemLp.mul'` → `MemLp.fun_mul` (swapped arguments);
  `eLpNorm_eq_lintegral_rpow_enorm` → `…_toReal`; `continuous_unipotentGL2_adele` →
  `continuous_unipotentGL2`; `Topology.IsEmbedding.subtypeVal.secondCountableTopology` for `↥U`; every
  Prop-class `haveI`/`letI` → `have`/`let`; three pin `haveI` walls that the module headers already
  carry as `attribute [local instance]` dropped (each of the remaining ones ablation-verified
  load-bearing by order B).
* **One order defect, corrected by a consumer.** Order A's §6 suggested reading the archimedean
  headline at `ι := 1`; that is inadmissible — `archComponent` is a monoid hom, so `hι` at `1` forces
  `κ w = 1` for every `κ` (the consumer states the obstruction as `iota_one_forces_trivial`). The
  consumer reads the row at `ArchInfra.inclArch` instead.
* **One mathematical finding worth recording**: the two averaging headlines are one argument under
  five substitutions, *except* in the `IsKfSmooth` half — the finite side conjugates a compact
  `U ≤ finiteAdelicGL2Subgroup F` into `K_f` (the tube lemma), while the archimedean side uses that
  `adelicArchGLIncl (ι κ)` **centralises** `K_f`. That is exactly where the two groups stop being
  interchangeable, and it is why `isKfSmooth_integral_mul_apply_mul` is needed by the finite headline
  only.

## 6. Risk register

1. **Order A's finite headline is the pin's one maxHeartbeats site** (`400000`/`1600000`). The port
   forbids the override, so this is where the set can stall: the diagnosis ladder is the playbook's
   §3.5 (name the expensive type once and bind the instance by `have`; the `isKfSmooth` prelude lemma's
   `generalized_tube_lemma` step is the likely cost). If it cannot be made to fit, that is a report,
   not a bump.
2. **The two averaging statements are long and the `∃ h : (fun x => ∫ …) ∈ cuspMemberSubmodule …`
   shape is load-bearing** — the membership is a binder used on the conclusion's right-hand side. The
   statements are frozen, so a mis-copied one is impossible; a proof that reorders the existential is
   not.
3. **The `KK` abbrev** (order A): only `continuous_iota` should need the type written out. If the
   worker needs an `own:` row, it says which and why — one row, not five.
4. **Order C's second row is one edge behind the first** and its pin proof uses `RS11DIL`'s four
   private helpers; the `archIdele` `Units` structure has two field proofs (`val_inv`, `inv_val`)
   that must be the pin's.
5. **`toCuspSubcarrier`'s injectivity and `cuspSubcarrier` being a closure** are the two facts rows 3
   and 4 hinge on; both are in the port's `Cusp/SpectrumSubrep.lean` API.
6. **The pin's `attribute [-instance]`/`[-simp]` walls** are not port content; no worker transcribes
   one, and a misbehaving `simp` is resolved locally.

## 7. What this set does not do

- **It does not take the Hecke-coset averaging pair** (`exists_integral_rightConv_eq_rightConv` 514,
  `exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` 429): readied by
  AF18's promotion, measured return zero, and a different subject (the coset averaging engine and the
  adèlic Borel–Fubini fact).
- **It does not take the Hecke/Petersson tail** (7 rows / 947, return +23).
- **It does not take the five bulk blocks** (15 rows / 6,592, return zero) nor the `sesqForm` pair
  (468) nor the `weylInv` pair (577) nor the `su2` string (681 + 755) nor the `diagOne` family
  itself — **that family is what this set readies and is AF20's subject** (4 rows / 3,248).
- **The 4 withheld rows / 831** remain the prunable complex-analytic subject.
- **No `Def_` node, no migration, no legacy module**; two new modules, one insertion into a written
  module.

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af19.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes <each of the eight rows> --json build/af19-advise.json
python3 port_plan.py --json build/af19-advise.json
python3 build/af-worklist.py CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact \
  CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate \
  CuspidalSpectrum_exists_norm_toCarrier_rightConv_le CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule \
  CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv \
  CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv > build/af19-worklist.md
python3 build/af-worklist.py --prefix S_NumberField_ \
  TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one \
  TateGlobal_exists_ideleNorm_eq_and_snd_eq_one >> build/af19-worklist.md
```

**The forecast** (the three skeletons carry all eight headlines, so the frontier reads the set as
ported; the delta is the read with them minus the read without):

| figure | before | after | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 826 / 343,413 | **818 / 341,853** | −8 / −1,560 (the set's silo, exact) |
| `needed [literal]` | 838 / 346,878 | **830 / 345,318** | −8 / −1,560 |
| frontier F | 1,590 / 783,963 | **1,598 / 785,523** | +8 / +1,560 |
| ready rows | 62 / 17,281 | **60 / 19,250** | 7 out, 5 in: +1,969 (= −1,478 + 3,447) |
| leaves | 225 / 57,500 | 225 / 57,500 | — |

**Rows readied (5 / 3,447 silo):**

| row | silo | prem | lev | what it is |
|---|---:|---:|---:|---|
| `exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt` | 913 | 1 | 1/1 | the `diagOne` Whittaker formula (order C's payback) |
| `exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat` | 905 | 1 | **4/7** | the flat, nonnegative, `conj`-invariant archimedean test factor |
| `CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent` | 716 | 2 | 2/2 | the `diagOne` coefficient sum, `‖·‖ = 1` form |
| `CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent` | 714 | 2 | 1/2 | … general form |
| `CuspidalSpectrum.exists_isLift_rightConv` | 199 | 4 | **11/13** | right convolution as a bounded operator on the carrier (order B's payback) |

The first four are the `diagOne` family (3,248 silo) and are **AF20's subject**, already cut; the
fifth is the lift of the convolution action, the natural companion of AF18's translation lift.

**The landing section (§5.1 of the recipe) is filled at review**: files and lines per order, the
checker counts at both visibility readings, the axioms blocks, `dedup`/`move_dead`, the consumer error
counts, and the exact re-read against this forecast.

## Appendix A — the AF shelf, every row accounted for

### The ready block — **33 rows / 11,079 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `exists_integral_rightConv_eq_rightConv` | 514 | 3 | 2/3 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact` | 510 | 3 | 1/1 | **SET-AF19 order A** |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate` | 463 | 3 | 1/1 | **SET-AF19 order A** |
| `exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` | 429 | 3 | 1/1 | deferred (§7) |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_norm_toCarrier_rightConv_le` | 253 | 4 | 1/1 | **SET-AF19 order B** |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7, Hecke/Petersson) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7, Hecke/Petersson) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7, Hecke/Petersson) |
| `CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule` | 70 | 6 | 10/13 | **SET-AF19 order B** |
| `CuspidalSpectrum.map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv` | 66 | 3 | 1/1 | **SET-AF19 order B** |
| `NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` | 63 | 1 | 1/1 | **SET-AF19 order C** |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred |
| `CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv` | 53 | 2 | 7/7 | **SET-AF19 order B** |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | deferred |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred |

One more of this set's rows is one edge behind the block and is taken with it:
`NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one` (82).

### The leaves block — **56 rows / 11,461 silo** (unchanged since SET-AF17)

Quoted whole in SET-AF17's Appendix A; no leaf enters this set. The largest are
`su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` (755),
`CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` (646),
`exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` (587),
`exists_sum_prod_mul_of_rightTranslatesSpanFinite` (576).

## Appendix B — the per-row worklist

`build/af19-worklist.md` has the declaration-level detail.

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact` | 485 | 24 | 461 | 7 |
| `CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate` | 438 | 24 | 414 | 6 |
| `CuspidalSpectrum_exists_norm_toCarrier_rightConv_le` | 233 | 0 | 233 | 1 |
| `CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule` | 49 | 0 | 49 | 1 |
| `CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv` | 48 | 0 | 48 | 1 |
| `CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv` | 36 | 0 | 36 | 1 |
| `TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` | 50 | 0 | 50 | 3 |
| `TateGlobal_exists_ideleNorm_eq_and_snd_eq_one` | 66 | 0 | 66 | 5 |
| **8 rows** | **1,405** | **48** | **1,357** | **25** (`19` written) |

The 91-line difference between this table (1,405) and `port_plan`'s raw slice (1,560) is the pin's
duplicated prelude between the two averaging files plus the p2m scaffolding; the 24 "imported" lines
per averaging row are the two substitutions.

The `decls` counts are the pin's declarations in the slice, and for order B and C they are what is
written: order B is four single-declaration files, order C's 3 + 5 are `map_diagOne`/`det_diagOne` plus
the headline, and `archIdele` + 3 helpers plus the headline. For order A the table counts the shared
prelude **twice** (7 + 6); the landing wrote it once, 5 declarations — 6 of the pin's 13 declarations
are the same text in both files, so the 25 is 19 written (15 public, 4 `private`).
