# `lean/logs/mc-port.md` — the ModularCurve Hecke-layer port, measured

The running record of the effort that closes the remaining 82-node cone of
`ModularCurve.heckeOperatorsCommuteBar` (blueprint:
[../topics/PORTING-MC.md](../topics/PORTING-MC.md)). One section per set/topic,
with the measured costs and the friction. FLT is pinned at
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib at `v4.34.0`.

## §0 Baseline (2026-09-23, before SET-M1)

| check | result |
|---|---|
| `lake build` | green (last recorded: 4,054 jobs, 0 warnings, no `sorry`) |
| `spec/check_flt_statements.py` | **802 identical (53 promoted), 0 mismatched, 0 missing**, 14 own-proof |
| target cone | 225 nodes / 42,099 raw / 30,559 content |
| ported | 143 nodes / 31,530 raw / 22,980 content |
| **remaining** | **82 nodes / 10,569 raw / 7,579 content** |
| definition modules needed | 13, ≈1,713 pin lines |

The remaining 82 are all `ModularCurve.*` theorem nodes; the `AlgebraicCurve`
slice (65 nodes) and the `Polynomial.*` engine are ported, as is the
*automorphic* Hecke face (which is disjoint — see coverage §9).

## §1 Recon — the measured cone, the groups, and the redundancy

### 1.1 The 82 nodes by topic group

`raw` = the whole `S_` file; `content` = after dropping imports, `attribute`
lines, namespace/`section`/`variable` lines, `p2m_*` lines, comments and blanks.

| group | nodes | raw | content | topic |
|---|---|---|---|---|
| M1 Hecke correspondence vocabulary | 0 (defs) | — | — | m1 |
| M2 exchange reduction | 4 | 111 | 68 | m12 |
| M3 cusp/`q`-adic vocabulary | 0 (defs) + 11 bookkeeping | 177 | 78 | m2, m5 |
| M4 Laurent glue + relative degree | 12 | 1,402 | 1,061 | m7 |
| M5 Φ datum + degree tail | 14 | 1,465 | 950 | m6, m8 |
| M6 roof generation + diagonal degree | 2 | 1,181 | 859 | m9 |
| M7 modular-unit `q`-expansion | 9 | 1,677 | 1,282 | m3 |
| M8 Fricke invariance + field inclusion | 8 | 3,030 | 2,307 | m4 |
| M9 cusp dichotomy, Fricke automorphisms, cusp bookkeeping | 17 | 1,072 | 650 | m5 |
| M10 tower integrality/finiteness | 13 | 447 | 301 | m10 |
| M11 principal divisors | 2 | 82 | 38 | m11 |
| capstone | 1 | 112 | 63 | human |
| **total** | **82** | **10,569** | **7,579** | |

### 1.2 The 13 definition modules

`wc -l` of the pin files: `HeckeOperator` 191, `DegeneracyTower` 138,
`HeckeOperatorTotal` 65, `HeckeModule` 122, `HeckeInputsAll` 20,
`ArithmeticGalois` 140, `GeometricBaseChange` 227, `QAdicPlace` 380,
`CuspidalClass` 55, `AtkinLehner` 107, `ModularUnit` 185, `JqCoeff` 83
(+ `Def_HeckeGalois_EichlerShimura:14–16` for `HeckeAlg`/`heckeGen`).

### 1.3 The measured redundancy

1. **The Fricke/inclusion prelude — a 651-content-line 3-way copy (the effort's
   largest).** `S_ModularCurve_{mem_modularFunctionField,isIntegral_adjoin_jq}_of_hasSum_of_gamma0_invariant.lean`
   and `S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean`
   share lines 50–861 / 50–861 / 53–863. The first two differ by **12 lines**
   (all `p2m_*` strings plus the final `solution`); the third's prelude differs
   from the first's by **2 lines**. Content: 651 lines × 3 = 1,953, written once.
   The pin's `RealL` block inside it (lines 262–417) is **already ported** as
   `ModularForms/Hauptmodul.lean:230`'s `RealL` + closure.
2. **The modular-unit `q`-expansion prelude — a 4-way copy.** The four
   `S_ModularCurve_hasSum_{,smul_}modularUnitSeries{_inv,}_qParam.lean` share
   lines 28–192 byte-identically. Pairwise `diff | grep -c '^[<>]'`: 87, 69, 108.
   The port writes it once (m3).
3. **The degree/roof prelude — a 3-way copy, already ported.** The
   `TS`/`conj`/`phiAtSeed`/`roots_prime_at_slot` block at the head of
   `relfinrank_qExpand_full`, `heckeRoof_adjoin_range_union_eq_top` and
   `finrankAlong_towerSubstBar_comp_heckeAlphaBar` is already public in
   `Defs/TS.lean`, `Defs/PhiAtSlot.lean`, `Defs/Cyclotomic.lean`,
   `Defs/Twist.lean` and `PhiSlotRoots.lean`; the port writes none of it.
4. **One-liners over the ported Φ_p effort (M5).** `exists_modularPolynomialData_evalSymm`
   is `exists_phiIrreducible_evalSymm` with `PhiIrreducible` dropped;
   `modularPolynomialFamily` is the universal form; `full_eq_of_prime` /
   `functionFieldGeneration_of_prime` should be the ported `gen_prime`;
   `ModularPolynomialData.isIntegral_jqN` is `aeval_jqN_toAdjoin`/`minpoly_jqN_eq`;
   `isIntegral_jqNModC_mul` is `phiAtSeed_jqN_eval_down`. **Verified by probe
   (2026-09-23, 4.8 s `lake env lean`):** the first two close by
   `obtain ⟨data, _, hsymm⟩ := exists_phiIrreducible_evalSymm ℓ; exact ⟨data, hsymm⟩`
   (with `have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩` inside the `ModularPolynomialFamily`
   lambda, since the Prop binds `[NeZero ℓ]` then `ℓ.Prime`). **But only five of
   the candidates are one-liners**; the `eval_jqNModC_{mul_eq_zero,of_mul_eq_zero}`
   pair is a ~30-line transcription (private `coeffMap_jqNModC`,
   `coeffMap_eval₂_jqNModC`, `eval₂_rat_of_data` over ported `coeffMap_qExpand`/
   `coeffMap_injective`, `data.eval_eq_zero`, `map_jqModC`, `qExpand_qExpand`),
   and `isIntegral_jqNModC_mul` rides on it. The topic order now says so.
5. **The Hecke-operator prelude — 4 private supply lemmas.** Two are ported
   (`Defs/Laurent.lean` `coeffMap_qExpand`, `coeffEmb_qExpand`); two
   (`laurentBaseChange_mono'`, `qExpand_mem_laurentBaseChange'`) are **not**, and
   — the organizational point — they are themselves remaining wrapper targets
   (`ModularCurve.laurentBaseChange_mono`,
   `ModularCurve.qExpand_mem_laurentBaseChange`, both in the M4 degree/glue
   group). The port writes them **public** in `Defs/HeckeOperator.lean` (m1) and
   `Defs/DegeneracyTower.lean` imports them instead of repeating the pin's
   `laurentBaseChange_mono''`; m7 imports rather than re-declares. One public
   home for a lemma the pin writes twice privately. *Verified by grep:
   `laurentBaseChange_mono` has 0 hits in `FLTForHuman/` before this.*
6. **Principal divisors (M11).** `hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull`
   (34) should be an application of the AC `hasPrincipalDivisors_of_transcendental`;
   `hasPrincipalDivisors_modularFunctionFieldBar` (4) follows with `hΦ`.
7. **Already-ported definition modules.** Of the 13 pin modules the remaining
   files import, `Def_ModularCurve_LaurentCoeff` is fully ported
   (`Defs/Laurent.lean`, a superset) and `Def_ModularCurve_PhiGen` essentially so
   (`Defs/Twist.lean` + `Defs/PhiGen.lean`). The 11 genuinely new ones are the
   six m1/m2 homes plus `ArithmeticGalois`, `CuspidalClass`, `JqCoeff`,
   `ModularUnit`, `QAdicPlace`.
8. **The `RatFunc` cusp model — a 160-content-line 2-way copy (m5/m8).**
   `S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar.lean` (163 content) and
   `S_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime.lean` (200 content) share
   their first **160 content lines** exactly (`difflib.SequenceMatcher`: one
   matching block of size 160, then the tails diverge). The block is the
   `RatFunc 𝕂` model of `modularFunctionFieldBar ℓ` (`jb`, `σa`, `jTr`, `φ`,
   `IsScalarTower`, `finite_ratFunc`, `finrank_le`, `isSeparable_ratFunc`,
   `restrict_eq_of_isCusp`, `e_infty`, `e_zero`, `eq_cuspInftyBar_or_eq_cuspZeroBar`,
   `le_finrank`, `finrank_tower_eq`). m5 writes it once; m8 imports it.

### 1.4 The dependency spine (group level), and the set plan

`m1` vocabulary → `m3` analytic series → `m4` Fricke/inclusion → `m6` Φ data →
`m5` cusp dichotomy/Fricke aut (which consumes `m6`'s
`nonempty_modularPolynomialData_of_squarefree`, `finrank_adjoin_jqNModC_le`,
`transcendental_jqModC`) → `m7` degree/glue → `m8` prime degree → `m9` roof →
`m10` integrality → `m12` exchange reduction → capstone, with `m11` principal
divisors hanging off `m6`/`m7`. `m2` is the vocabulary the analytic chain is
stated about.

**Sets:** SET-M1 = m1–m3 (running); SET-M2 = m4, m6, m5; SET-M3 = m7–m9;
SET-M4 = m10–m12; capstone = the human reviewer. The analytic fork (`m3`/`m4`)
is independent of the degree/Φ chain until `m5`, which is why SET-M1 could take
the vocabulary + `m3` while the rest is priced.

## §2 SET-M1 — the vocabulary and the analytic core (m1–m3)

**Status (2026-09-23): COMPLETE and reviewed (PASS).** Final: 14 modules, 2,794
lines; `lake build` 4,093 jobs green, 0 warnings, no `sorry`; checker
**1,022 identical (58 promoted), 0 mismatched, 0 missing**; consumer Zones A/B/G
at 0 errors/0 warnings. The review is the §Review of SET-M1 below; the measured
close is in §m1–§m3. **SET-M2 (m4, m6, m5) was dispatched next.**

| order | topic | object | prereq |
|---|---|---|---|
| 1 | [TOPIC-m1-hecke-vocabulary.md](../topics/hecke/TOPIC-m1-hecke-vocabulary.md) | HeckeOperator, DegeneracyTower, HeckeTotal, HeckeModule, ArithmeticGalois | AC + ported FFG/Φ |
| 2 | [TOPIC-m2-geometric-cusp-vocabulary.md](../topics/hecke/TOPIC-m2-geometric-cusp-vocabulary.md) | GeometricBaseChange, QAdicPlace, CuspidalClass, AtkinLehner, ModularUnit, JqCoeff | m1 |
| 3 | [TOPIC-m3-modular-unit-qexpansion.md](../topics/hecke/TOPIC-m3-modular-unit-qexpansion.md) | the 9 M7 nodes, one prelude | m2, ported `ModularForms/*` |

### §m1 — the Hecke correspondence vocabulary

**Static audit (manager, pre-review, 2026-09-23 16:26).** Five modules written:
`Defs/HeckeOperator.lean` 184 lines / 15 decls, `Defs/DegeneracyTower.lean` 142
/ 17, `Defs/HeckeTotal.lean` 73 / 6, `Defs/HeckeModule.lean` 162 / 18,
`Defs/ArithmeticGalois.lean` 119 / 9; `grep -c 'sorry\|admit'` = 0 in all five.
The two promoted prelude lemmas `laurentBaseChange_mono` and
`qExpand_mem_laurentBaseChange` match their wrappers verbatim (checked against
`Theorems/Thm_ModularCurve_{laurentBaseChange_mono,qExpand_mem_laurentBaseChange}.lean`).
m1 also delivered the out-of-cone payoff (`HeckeAlg`, `heckeGen`, `heckeEvalBar`,
`heckeModuleBar`) and the `ArithmeticGalois` `≃ₐ`-action. **`HeckeExchangeAt`'s
binder block is byte-identical to the pin's** (`Definitions/Def_ModularCurve_DegeneracyTower.lean`),
verified by diff — the effort's central contract is intact. Build and checker
numbers are filled by the review. **Interim (16:26, m1 + m2's
`GeometricBaseChange`/`JqCoeff` in the tree): checker 802 → 867 identical, 0
mismatched, 0 missing; no real `sorry`/`admit` anywhere** (the single grep hit is
a comment in `Spine.lean`). The manager's review harness is
`.recon/review-setm1.sh`. **Interim full build (16:31, after m2's `AtkinLehner`):
`lake build` = 4089 jobs, exit 0, no `sorry`**; the `#print axioms` lines in the
log are the source modules' own checks, all `[propext, Classical.choice,
Quot.sound]`.

**Measured close (m1).** Checker **816 → 867 declarations checked; 802 → 853
identical, 0 mismatched, 0 missing** (14 own-proof). The four supply lemmas:
`grep -c` 2 each for the pin's `coeffMap_qExpand'`/`coeffEmb_qExpand'`/
`laurentBaseChange_mono'`/`qExpand_mem_laurentBaseChange'`; the port dedups the
first two to `Defs/Laurent.lean`'s public `coeffMap_qExpand`/`coeffEmb_qExpand`
(1 each) and ports the second two **publicly once** (1 each) from their wrappers,
so `DegeneracyTower` imports `laurentBaseChange_mono` instead of repeating
`mono''`. The workspace rule forbids editing `Defs/Laurent.lean`, so they are
not moved there (deviation from the topic's suggested home, recorded).
`heckeAlphaBar_eq_towerInclBar` is `rfl`; `heckeBetaBar_eq_towerSubstBar` is the
pin's `AlgHom.ext ∘ Subtype.ext` (risk 4 did not bite). The `HeckeAlg` payoff is
**ported**, not deferred: `HeckeAlg`/`heckeGen` restated locally (3 lines) with
`Def_HeckeGalois_EichlerShimura.lean` registered as their source. m1's
`#print axioms` headlines are clean.

### §m2 — geometric base change, cusps, `q`-adic place, modular unit

**Static audit (manager, pre-review, 16:30, m2 complete).**
`GeometricBaseChange.lean` 241 lines / 28 decls, `QAdicPlace.lean` 396 / 36,
`CuspidalClass.lean` 69 / 11, `AtkinLehner.lean` 135 / 16,
`ModularUnit.lean` 199 / 30, `JqCoeff.lean` 96 / 11; **0 real `sorry`** in all
six. The predicted stalls (`baseChangeEquiv`/`geomAut`,
`qIntegersBar_isPrincipalIdealRing`, `irreducible_uniformizerBar`,
`IsMonicOfOrder`/`modularUnitSeries`) did not bite. Interim checker: **802 → 1011
identical (56 promoted), 0 mismatched, 0 missing** — the 11 new definition
modules' declarations verify by name against their `Definitions/Def_ModularCurve_*.lean`
sources. m3's analytic modules remain.

**Measured close (m2).** Checker **867 → 1,025 declarations checked; 853 →
1,011 identical, 0 mismatched, 0 missing.** The `geomAut`/`baseChangeEquiv`
instance goals: `IsDomain (L ⊗[ℚ] F₀)` (from injectivity), `IsField` (via
`TensorProduct.isField_of_isAlgebraic`) and `Algebra.IsAlgebraic ℚ L` (a
hypothesis of the field part); two v4.34 migrations were needed
(`Subfield.toIntermediateField'` → `Subalgebra.toIntermediateField'`;
`TensorProduct.induction_on` → `inductionOn`, no `zero` case).
`qIntegersBar_isPrincipalIdealRing` is the pin's route
(`IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization` +
`.toIsPrincipalIdealRing`; `uniformizerBar = j⁻¹`); `Set.mem_setOf_eq` →
`Set.mem_ofPred_eq`. All six files are ported whole; the one structural
restoration is the anonymous `SMul (F ≃ₐ[K] F) (Place K F)` (the AC port dropped
its home, `Def_AlgebraicCurve_DivisorClassGroup.lean:285`) in `AtkinLehner`; the
m1 `PicAction`/`JZero.torsionGaloisRep` stay deferred.

### §m3 — the modular-unit `q`-expansion core

**Measured close (m3).** Checker **1,025 → 1,036 declarations checked; 1,011 →
1,022 identical, 0 mismatched, 0 missing.** The 4-way prelude is lines 28–192
(165 lines) byte-identical; pairwise `diff | grep -c '^[<>]'`: 87, 69, 108 (the
blueprint's three pairs) and 149, 150, 68 (the rest — the brief's "all pairs
69–108" is wrong for two). The port writes it once (`grep -c` = 1 for `gfun`,
`theta`, `taylorCoeff`, `phiFun`, `psiFun`, `hasSum_single_mul_coe_iff`; the pin
has 1 in each of four files). `qParam_coeff_unique` **held the bare `F : ℍ → ℂ`
shape** (no `DFunLike` stall, no `maxHeartbeats` pressure; it builds in
seconds). The four headlines are the two public generic heads
`hasSum_modularUnit`/`hasSum_modularUnitInv` (1, 2) and their `S`-transport by
`discriminant_S_smul` (3, 4); the checker verifies the four wrappers directly and
the two generic heads by the dotted fallback (their `𝕢`/`ℍ` notation is
reproduced). `SpecialLinearGroup.map`'s coercion drift cost an explicit
`mapGL_conjSL` lemma in `Gamma0Cosets`. **SET-M1 totals:** 14 modules, 2,794
lines, `timeout 900 lake build` **4,093 jobs, 0 warnings, no `sorry`**, consumer
Zones A–B at **0 errors**.

### §Review of SET-M1

**Reviewed by the manager (2026-09-23 16:45). Verdict: PASS.** The set delivered
the Hecke vocabulary, the geometric/cusp/modular-unit vocabulary and the
modular-unit `q`-expansion core, with no `sorry` and no statement mismatch.

| check | independent result |
|---|---|
| modules | 14 (m1 5, m2 6, m3 3), 2,794 lines |
| `timeout 900 lake build` | **4,093 jobs, 0 warnings, exit 0** |
| `spec/check_flt_statements.py` | **1,022 identical (58 promoted), 0 mismatched, 0 missing**, 1,036 checked, 14 own-proof |
| `#print axioms` on `heckeSquareBar_commutes`, `hasSum_modularUnitSeries_qParam` | `[propext, Classical.choice, Quot.sound]` |
| `spec/ModularCurveHeckeConsumer.lean` Zones A/B/G | **0 errors, 0 warnings** (the manager removed one unused binder) |
| `HeckeExchangeAt` vs pin | **byte-identical** binder block |
| dedup | 4-way `hasSum` prelude written once; `laurentBaseChange_mono`/`qExpand_mem_laurentBaseChange` one public copy each; `TS`/slot prelude not re-declared |

**Accepted deviations.** (1) The two promoted prelude lemmas live in
`Defs/HeckeOperator.lean`, not `Defs/Laurent.lean`, because the workspace rule
forbids editing the latter; recorded, harmless. (2) The anonymous
`SMul (F ≃ₐ[K] F) (Place K F)` that AC had dropped is restored in
`AtkinLehner.lean` (via `SemilinearAut.ofAlgAut`); it is needed by
`frickeInvolutionBar • cuspInftyBar` and is a genuine AC gap worth a later
promotion to `AlgebraicCurve`'s `DivisorClassGroup`/`SemilinearAut`. (3) The m3
brief's "all pairs 69–108" was wrong for two of the six prelude diffs (149, 150,
68); the corrected numbers are in §m3. (4) The `ArithmeticGalois` `PicAction`
section and `JZero.torsionGaloisRep` are deferred (0 cone occurrences); they
need the dropped `SMul (SemilinearAut K F) (Pic0 K F)`.

**Friction carried forward** (also §Friction): `dif_pos`/`dif_neg` →
`dite_eq_left`/`dite_eq_right`; `if_pos` → `ite_eq_left`;
`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; `TensorProduct.induction_on` →
`inductionOn` (no `zero` case); `Subfield.toIntermediateField'` →
`Subalgebra.toIntermediateField'`; `SpecialLinearGroup.map` coercion drift cost
the private `mapGL_conjSL`.

**Consequences for SET-M2.** m4 imports `Analytic/{QParamUnique,ModularUnitQExpansion,Gamma0Cosets}.lean`,
`Defs/{ModularUnit,AtkinLehner,Jq}.lean` and `ModularForms/Hauptmodul.lean` — all
present. m6's five one-liners and the `eval_jqNModC_*` route were pre-verified by
the manager (`TOPIC-m6-phi-data.md`). m5 imports m4 and m6. The SET-M2 orders are
unchanged and dispatched next.

## §3 SET-M2, SET-M3, SET-M4 and the capstone — orders drafted

**SET-M2** ([../topics/hecke/SET-M2.md](../topics/hecke/SET-M2.md)): m4
(Fricke/inclusion core), m6 (Φ datum family), m5 (the `RatFunc` cusp model,
dichotomy, Fricke automorphisms, cusp bookkeeping, and the folded prime degree).
**SET-M3** ([../topics/hecke/SET-M3.md](../topics/hecke/SET-M3.md)): m7 (Laurent
glue + the two relative-degree theorems), m9 (roof generation + diagonal degree).
**SET-M4** ([../topics/hecke/SET-M4.md](../topics/hecke/SET-M4.md)): m10
(integrality/finiteness), m11 (principal divisors), m12 (the exchange
reduction). The capstone
([../topics/hecke/TOPIC-m13-capstone.md](../topics/hecke/TOPIC-m13-capstone.md))
is reserved for the reviewer.

All orders are written ahead of their dispatches and are finalized against the
landed modules at each review. The m5 order carries the m5/m8 `RatFunc` dedup
(160 content, §1.3 item 8); the m9 order carries the AC `finrankAlong`
promotion candidates; the m11 order tests the coverage report's "nearly a
corollary" prediction against AC's `hasPrincipalDivisors_adjoin_of_transcendental`.

## §4 SET-M2 — the Fricke/inclusion core and Φ data (partial, measured)

**Status (2026-09-23): 6 of 7 modules green; the m5 tail re-scoped to `m5b`.**

| topic | modules | lines | result |
|---|---|---|---|
| m4 | `Analytic/Gamma0InvariantCore`, `Analytic/FrickeInvariance` | 919 + 410 | the 651-content-line M8 prelude written **once**; first two headlines + four small targets; the third headline delivered in `FrickeAut` |
| m6 | `Degree/PhiData`, `Degree/PhiDegree` | 630 + 184 | the biresultant existence, the `jqNModC` tail, the prime generation facts, the degree tail |
| m5 (first half) | `Analytic/CuspBookkeeping`, `Analytic/FrickeAut` | 199 + 376 | the 11 cusp-bookkeeping nodes, the four Fricke-automorphism nodes, and the deferred m4 third headline |
| m5 (tail) | `Analytic/CuspDichotomy` | — | **blocked** on a kernel deterministic timeout; re-scoped to [TOPIC-m5b](../topics/hecke/TOPIC-m5b-cusp-dichotomy.md), dispatched |

**Independent verification at this point:** `lake build` **4,099 jobs, 0 warnings,
no `sorry`**; checker **1,166 identical (65 promoted), 0 mismatched, 0 missing**
(1,180 checked), up from SET-M1's 1,022; `FrickeAut` builds in **16 s**. The
manager fixed one binder mismatch the subagent left
(`exists_isFrickeAut_of_modularPolynomialData` now carries the wrapper's explicit
`{N} [NeZero N] (data)` binders) and registered the 15 landed m5 nodes plus
`FrickeAut`'s internal helpers in `SOURCES`/`PORT_FILES`.

**Dedup.** m4's 651-content-line prelude is written once (the pin's three copies
differ by 12 lines for the first two, 2 lines for the third's prelude). m5's
160-line `RatFunc` model is written once in `CuspDichotomy` — awaiting the `m5b`
build. m6's five one-liners and the `eval_jqNModC_*` route were pre-verified by
the manager and held.

### §m5b — the `CuspDichotomy` re-scope (m5's blocked tail)

**Measured close (m5b).** The blocked module is delivered as
`FLTForHuman/ModularCurve/Analytic/CuspDichotomy.lean` (363 lines), closing §4's
`m5 (tail)` row. It carries the pin's shared **160-content-line `RatFunc` model written
once** — `grep -c` in the port: `def jTr` 1, `def σa` 1, `def φ` 1, `theorem coe_jTr` /
`coe_φ` / `finrank_tower_eq` 1 each — against the pin's **two** copies
(`S_ModularCurve_{eq_cuspInftyBar_or_eq_cuspZeroBar,finrank_adjoin_jqNModC_eq_of_prime}.lean`,
`def jTr` 1 each). The two targets are short applications of that model
(`eq_cuspInftyBar_or_eq_cuspZeroBar`, `finrank_adjoin_jqNModC_eq_of_prime`); the third
(`modularFunctionFieldBar_eq_restrictScalars`) is `TwoCuspAux.bar_eq_restrictScalars`,
the carrier equality `mem_bar_iff` already uses, so the pin's `DivUSol` divisor route is
not re-ported. The 160-line saving priced in §1.3 item 8 is realised.

**The blocker was structural, not mathematical.** `TwoCuspAux.jTr`'s `Subtype` coercion
carried `(mem_bar_iff ℓ x).mpr x.2`, but the kernel cost was *not* the proof term: with
the membership proof replaced by an abstract variable it still timed out. What blows up
is any declaration whose kernel check forces a `Subtype.val` defeq between
`↥(𝕂⟮jqModC⟯⟮jqNModC ℓ⟯)` and `↥(modularFunctionFieldBar ℓ)` — two
`IntermediateField.adjoin` subtypes. Probes at 20 000 heartbeats: a plain `Equiv` and a
plain `RingHom` between the pair both time out, while `↥⊤ ≃+* ↥bar`, `↥T ≃+* ↥⊤` and
`Subtype p ≃+* Subtype q` for abstract `p q` are all cheap — only *both concrete
`adjoin`s* at once are expensive. **The winning route** keeps the concrete carriers out
of the reduction: a generic
`private def ifRE (S T : IntermediateField 𝕂 (LaurentSeries 𝕂)) (h : S = T) : ↥S ≃+* ↥T`
with `toFun x := ⟨↑x, h ▸ x.2⟩` / `invFun y := ⟨↑y, h.symm ▸ y.2⟩`, and
`private theorem ifRE_coe … := rfl` proved at the *abstract* `S, T, h`. Instantiating at
`(T.restrictScalars 𝕂) = bar` gives `jTr`, with `coe_jTr := by unfold jTr; exact ifRE_coe …`:
the kernel checks only the generic `rfl`, never the concrete carriers. A second
cross-`IntermediateField` `rfl` — in `φ_algebraMap`, comparing `↑(algebraMap 𝕂 K₁ k)`
with `↑(algebraMap 𝕂 bar k)` — became the `@[simp]`
`IntermediateField.coe_algebraMap_apply` on both sides (both reduce to the same ambient
`algebraMap`), and the `haveI` instance in `finite_ratFunc` became `have` (v4.34
`linter.style.haveILetI`).

**Measured.** `lake env lean …CuspDichotomy.lean` **15.9 s real / 30.2 s user** (from
3 m 09 s with a `(kernel) deterministic timeout`); `timeout 300 lake build
FLTForHuman.ModularCurve.Analytic.CuspDichotomy` **15 s, 0 warnings, 0 `sorry`**;
`timeout 900 lake build` **4,100 jobs, exit 0, 0 warnings**; consumer Zone E `[cusp]` at
**0 errors / 0 warnings** (the dichotomy, the two-cusp split, the prime degree and the
restrict-scalars identity at `ℓ = 2`). The three headlines print
`[propext, Classical.choice, Quot.sound]`.

**Bookkeeping.** `Analytic/CuspDichotomy.lean` is in `PORT_FILES`; the three `Thm_`
wrappers and the two pin `S_` files are in `SOURCES`; the checker reads **1,198
identical, 0 mismatched, 0 missing** (the SET-M2 first-half baseline was 1,166). No
`maxHeartbeats`/`maxRecDepth` change and no raised timeout anywhere.

### §Review of SET-M2

**Reviewed by the manager (2026-09-23 18:05). Verdict: PASS**, after the m5 tail
was re-scoped and re-dispatched (`m5b`). The set delivered the Fricke/inclusion
core, the Φ datum family, and the cusp/Fricke tail.

| check | independent result |
|---|---|
| modules | 7 (`Gamma0InvariantCore` 919, `FrickeInvariance` 410, `CuspBookkeeping` 199, `FrickeAut` 376, `CuspDichotomy` 337, `PhiData` 630, `PhiDegree` 184), 3,055 lines |
| `timeout 900 lake build` | **4,100 jobs, 0 warnings, exit 0, no `sorry`** |
| checker | **1,198 identical (67 promoted), 0 mismatched, 0 missing**, 1,212 checked |
| `#print axioms` ×3 on `CuspDichotomy` | `[propext, Classical.choice, Quot.sound]` |
| consumer Zones A–E, G | **0 errors, 0 warnings** (the manager added Zones C/D and fixed two proofs) |
| `CuspDichotomy.lean` build | **15–16 s** (was a 3 m 09 s `(kernel) deterministic timeout`) |
| dedup | m4's 651-content-line prelude once; m5's 160-line `RatFunc` model once; m6's five one-liners held |

**The blocker and its resolution.** The original m5 tail failed with a kernel
deterministic timeout. Isolation probes (m5b) showed the cost is **not** the
`mem_bar_iff` proof term but any kernel `Subtype.val` defeq between the two
concrete `IntermediateField.adjoin` carriers `↥(𝕂⟮jqModC⟯⟮jqNModC ℓ⟯)` and
`↥(modularFunctionFieldBar ℓ)`. The fix is a **generic** private
`ifRE (S T) (h : S = T) : ↥S ≃+* ↥T` with its coercion lemma `ifRE_coe := rfl`
proved at the abstract `S, T, h`; `jTr := ifRE …` then checks only the generic
`rfl`. No `maxHeartbeats`/`maxRecDepth`/timeout was raised.

**Accepted deviations.** (1) m4's third headline is delivered in `FrickeAut.lean`
(it is downstream of `exists_isFrickeAutFull`), not `FrickeInvariance.lean`.
(2) `CuspDichotomy` reuses `TwoCuspAux.bar_eq_restrictScalars` (the carrier
equality `mem_bar_iff` uses) rather than re-porting the pin's `DivUSol` divisor
argument. (3) The manager fixed one real binder mismatch left by the first
subagent (`exists_isFrickeAut_of_modularPolynomialData` now carries the wrapper's
explicit `{N} [NeZero N] (data)` binders) and completed the README rows and
consumer Zones C/D.

**Consequences for SET-M3.** m7 imports the m1/m2 vocabulary (the two promoted
lemmas are public in `Defs/HeckeOperator.lean`), `Defs/GeometricBaseChange`,
`Defs/QAdicPlace`, `Defs/JqCoeff`, and m6's degree modules; m9 imports m7 plus
m6's `isIntegral_jqNModC_mul` and the ported `AlgebraicCurve` exchange. The SET-M3
orders are unchanged and dispatched next.

## §5 SET-M3 — the Laurent glue, the relative degree, and the roof (m7, m9)

**Status (2026-09-23): green, 0 mismatched / 0 missing.** Run m7 → m9; build and
statement-check after each module. All the set's declarations are transcriptions
of the pin's `solution`/wrapper statements; no statement was weakened and no
heartbeat cap was raised.

| topic | modules | lines | public decls | build | checker |
|---|---|---|---|---|---|
| m7 (short) | `Degree/LaurentGlue.lean` | 176 | 8 | `lake build` 3 s | 1198 → **1206** |
| m7 (TransportDev) | `Degree/Relfinrank.lean` | 739 (both) | `relfinrank_laurentBaseChange` | `lake build` 8 s | **1207** |
| m7 (qExpand full) | `Degree/Relfinrank.lean` | — | `relfinrank_qExpand_full` | `lake build` 16 s | **1208** |
| m9 | `Degree/Roof.lean` | 411 | 2 | `lake build` **15 s** | **1210** |

`timeout 900 lake build` = **4,103 jobs, exit 0, 0 warnings, no `sorry`**
(baseline 4,100; the three new modules). `#print axioms` on all four headlines
returns `[propext, Classical.choice, Quot.sound]`. Consumer
`spec/ModularCurveHeckeConsumer.lean` = **0 errors / 0 warnings**, with the new
Zone I `[relfinrank]` (m7: `coeffEmb_jq`/`coeffEmb_jqN` at `L = ℂ`,
`relfinrank_qExpand_full` at `N = 1`, `ℓ = 2`) and Zone F `[roof]` (m9: the
`N = 1`, `ℓ = 2`, `ℓ' = 3`, `M = 6` square, with `data'` from
`exists_modularPolynomialData_evalSymm 3` and `hgenQ` from
`functionFieldGeneration 6`).

### §m7 — the Laurent/`coeffEmb` glue and the two relative-degree theorems

**The eight short nodes** are transcription; the only adaptations are the port's
own dedup: the pin re-proves `CharLRows.map_qExpand_aux` and
`CharLRows.coeffEmb_jq` inside both `coeffEmb_jq`/`coeffEmb_jqN`; the port uses
the public `coeffEmb_qExpand`/`coeffEmb_jq`, so `coeffEmb_jqN` is the one-liner
`rw [jqN, jqNModC, coeffEmb_qExpand, coeffEmb_jq]`. `order_qExpand`/
`order_coeffEmb` were already proved `private` in `Analytic/CuspBookkeeping.lean`
(m5, which could not import them yet); these are their promoted public homes.
`Set.mem_setOf_eq` is deprecated in v4.34 → `Set.mem_ofPred_eq` (the same drift
`QAdicPlace` recorded).

**The two real blocks.** (1) `relfinrank_laurentBaseChange`'s `TransportDev`
block. It is generic field theory: `K₀ = ℚ(t)`, `K = L(t)` (`t = coeffEmb L t`),
the two `extendScalars` fields, the ring maps `φ`/`ψ` on them, `mem_span_image`
(adjoin of an algebraic set = span), `mem_span_range`, `finite_and_finrank_le`
(`≤` via a spanning set), and the hard half `linearIndependent_ψ` (a common
denominator `d ∈ L[X]` turns a `K`-relation into a `K₀`-relation, then
`linearIndependent_pow_mul` + `linearIndependent_coeffEmb` and the minpoly degree
bound finish it). Where it bit: **two instance-search deterministic timeouts at
the default 20,000 heartbeats**, at `Algebra.IsIntegral ↥(K₀ t) ↥(E₀ …)` and
`Free ↥(K₀ t)/↥(K L t) ↥(E₀ …)/↥(E L …)`. Fixed by explicit
`have : Algebra.IsIntegral … := Algebra.IsIntegral.of_finite _ _` and
`have : Module.Free … := Module.Free.of_divisionRing …` locals — the port's
`Correspondence.lean`-style "make the instance explicit" route, **no cap raised**.
Two v4.34 style drifts also landed: `if_pos`/`if_neg` are deprecated
(`ite_eq_left`/`ite_eq_right`) and the two `letI`s were accepted as `let`
(the `linter.style.haveILetI` suggestion, and the `let` still registers for
typeclass search). The pin's `relfinrank_laurentBaseChange_full`,
`relfinrank_restrictScalars` and `relfinrank_full_prime` tail is omitted
(`full_prime` needs m5's `finrank_adjoin_jqNModC_eq_of_prime` and is not an M4
node; the target's `solution` is `relfinrank_eq` alone).

(2) `relfinrank_qExpand_full`'s new block: `g2_relfinrank_union_left`,
`g2_zeta_mod`/`g2_seed_eq`/`g2_y0_eq`/`g2_twist_fix`, and the two ~230-line
`finrank_adjoin_jq_of_subset_range_qExpand{,_of_mem}` heads. The route is the
cyclotomic slot product: a symmetric irreducible `data` from
`exists_phiIrreducible_evalSymm ℓ`, the root list `roots_prime_at_slot` at
`CyclotomicField ℓ ℚ`, the transitive `qTwistEquiv (cycUnit ℓ)` on the roots via
`Polynomial.irreducible_of_transitive_ringAut`, then `= ℓ+1` by minpoly; the
`_of_mem` variant peels the factor `(X - j(q^{ℓ²}))` to get `= ℓ`. Where it bit:
**nowhere** — the pin's `set_option maxHeartbeats` bumps are not needed, the two
`letI`s were accepted as `let`, and the whole 739-line module builds in 16 s. The
only new ingredients over the ported prelude are the `g2_*` glue and
`coeffEmb_injective` (imported from `Defs/Laurent.lean` instead of re-proved).

### §m9 — the roof generation and the diagonal degree

**The roof** (`heckeRoof_adjoin_range_union_eq_top`). After
`laurentBaseChange_adjoin_pair` (`laurentBaseChange L F_M^full =
L[jqModC, jqNModC L M]` for `hgenQ : FunctionFieldGeneration M`) the two new
field-theoretic steps are `mem_range_towerInclBar_iff` (the range of
`towerInclBar` is exactly the smaller `laurentBaseChange`) and the reduction to
`Algebra.adjoin E₂s {jqNModC L M} = ⊤`, where `E₂s = laurentBaseChange L
F^full_{Nℓ}`: `isIntegral_jqNModC_mul` (m6) makes `adjoin` an algebraic
`adjoin`, so `Algebra.adjoin = (IntermediateField.adjoin …).toSubalgebra`
(`adjoin_simple_toSubalgebra_of_isAlgebraic`), and the `Algebra.adjoin_induction`
case split sends `xM = jqNModC L M` to the `towerSubstBar` leg (via
`qExpand_qExpand` + `jqNModC_congr`) and `algebraMap` to the `towerInclBar` leg.

**The diagonal degree** (`finrankAlong_towerSubstBar_comp_heckeAlphaBar`). The
route is `finrankAlong_comp` → the `towerInclBar` leg is `finrankAlong_id`
(degree 1, through `finrankAlong_towerInclBar_of_eq`) → the `towerSubstBar` leg
is `finrankAlong_heckeBetaBar` (the `if ℓ ∣ A then ℓ else ℓ+1` value). The latter
is `finrankAlong_eq_relfinrank_fieldRange` + `fieldRange_heckeBetaBar` +
`relfinrank_laurentBaseChange`/`relfinrank_qExpand_full` +
`relfinrank_full_eq_dedekindPsi`, cancelling `dedekindPsi A` from the two towers.
Where it bit: the pin's `synthInstance.maxHeartbeats 3200000` and
`maxHeartbeats 6400000` bumps are **not needed** — the module builds under the
port's global `4000000` in 15 s, with the default instance budget.

**The three AC `finrankAlong` promotion candidates.** The port's
`AlgebraicCurve/Defs/Correspondence.lean` publishes only `finrankAlong` itself;
the pin defines these three `private` inside each of its two degree/roof `S_`
files (and copies them into the three AC `finrankAlong_*` `S_` files):
`finrankAlong_comp` (`finrankAlong K (χ.comp φ) = finrankAlong K φ *
finrankAlong K χ`, by `Module.finrank_mul_finrank`), `finrankAlong_id`
(`= 1`, by `Module.finrank_self`) and
`finrankAlong_eq_relfinrank_fieldRange`
(`finrankAlong K φ = relfinrank ((B.val.comp φ).fieldRange) B`, by
`Algebra.finrank_eq_of_equiv_equiv`). Written `private` in `Degree/Roof.lean`;
**recommend promoting all three to `AlgebraicCurve/Defs/Correspondence.lean`**
beside `finrankAlong` (they are generic, have no `ModularCurve` dependency, and
their wrappers are already registered in `SOURCES`).

### §Prelude drop, measured

`grep -c` for a *declaration* of each ported prelude name in the three new
modules is **0** for all fourteen names (`TS`, `conj`, `phiAtSeed`,
`roots_prime_at_slot`, `cycUnit`, `qTwistEquiv`, `qTwist_iota_of_pow_eq_one`,
`iota_jq`, `iota_jqN`, `conj_zero_eq`, `conj_succ_eq`, `coeffEmb_qExpand`,
`coeffMap_qExpand`, `coeffMap_TS`). The pin's copies are imported from
`Defs/TS.lean`, `Defs/PhiAtSlot.lean`, `Defs/Twist.lean`,
`Defs/Cyclotomic.lean`, `PhiSlotRoots.lean`, `PhiGenSplits.lean`. The pin's
`raw − prelude` for the three prelude-carrying files:

| pin file | raw | prelude (`def TS` → `phiAtSeed_iota_eval`) | new block ≈ |
|---|---|---|---|
| `S_ModularCurve_relfinrank_qExpand_full.lean` | 794 | 357 | 437 |
| `S_ModularCurve_heckeRoof_adjoin_range_union_eq_top.lean` | 571 | 356 | 215 |
| `S_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean` | 610 | 356 | 254 |

`S_ModularCurve_relfinrank_laurentBaseChange.lean` carries **no** `TS` prelude
(342 raw lines all `TransportDev`), and the six short-node pin files are
15–30 raw lines each.

### §SET-M4 hand-off

- **m10** (`HeckeInputs/Integrality.lean`) imports m7's `Degree/Relfinrank.lean`
  and `Degree/LaurentGlue.lean` (its `FiniteAlong`/integrality route uses the
  `relfinrank_qExpand_full`/`relfinrank_laurentBaseChange` pair) plus m6's
  `Degree/PhiData.lean` (`isIntegral_jqNModC_mul`,
  `eval_jqNModC_of_mul_eq_zero`) and m1's `Defs/{DegeneracyTower,HeckeOperator,
  HeckeTotal}.lean` (`towerInclBar`/`towerSubstBar`, the integrality predicates).
- **m11** (`PrincipalDivisors/ModularCurveBar.lean`) imports m7's
  `laurentBaseChange_modularFunctionField{,Full}` and AC's
  `Defs/PrincipalDivisors` API.
- **m12** (`HeckeExchange/Reduction.lean`) consumes the two m9 headlines exactly
  as binders: `heckeRoof_adjoin_range_union_eq_top L N ℓ ℓ' M hM hgenQ data'`
  (the `hgen`) and `finrankAlong_towerSubstBar_comp_heckeAlphaBar L N ℓ ℓ' M hM
  hne` (the `hLD`), together with m10's integrality predicates and AC's ported
  `pullbackAlong_pushforwardAlong_eq_…`.
- **Capstone** (`Capstone.lean`, human): needs `HeckeExchangeAt L N ℓ ℓ' M hM`
  (m1) and the two `HasPrincipalDivisors` instances on
  `laurentBaseChange L F^full_{Nℓ}`/`F^full_M` (m11), as in
  `Defs/DegeneracyTower.lean`'s `HeckeExchangeAt` binder list.
- **Promotion to AC**: the three `finrankAlong` helpers above are the only
  SET-M3 generic helpers that belong outside the `ModularCurve` namespace.

### §Review of SET-M3

**Reviewed by the manager (2026-09-23 18:36). Verdict: PASS.** The set delivered
the Laurent/`coeffEmb` glue, the two relative-degree theorems, the roof
generation and the diagonal degree.

| check | independent result |
|---|---|
| modules | 3 (`LaurentGlue` 176, `Relfinrank` 739, `Roof` 411), 1,326 lines |
| `timeout 900 lake build` | **4,103 jobs, 0 warnings, exit 0, no `sorry`** |
| checker | **1,210 identical (67 promoted), 0 mismatched, 0 missing**, 1,224 checked |
| `#print axioms` ×4 (`relfinrank_qExpand_full`, `relfinrank_laurentBaseChange`, `heckeRoof_adjoin_range_union_eq_top`, `finrankAlong_towerSubstBar_comp_heckeAlphaBar`) | `[propext, Classical.choice, Quot.sound]` |
| consumer (Zone F `[roof]` + the m7 zone) | **0 errors, 0 warnings** |
| dedup | `grep -c` = **0 declarations** of all fourteen ported prelude names; the pin's `raw − prelude` is ≈437/215/254 |

**Two structural wins.** (1) The pin's `set_option maxHeartbeats` bumps are
**not needed**: `relfinrank_qExpand_full` and `finrankAlong_towerSubstBar_comp_heckeAlphaBar`
build under the port's global 4,000,000 in ~15–16 s. (2) m7's two
instance-search deterministic timeouts (`Algebra.IsIntegral`/`Module.Free` in the
`TransportDev` block) were fixed by **explicit instance locals**
(`Algebra.IsIntegral.of_finite`, `Module.Free.of_divisionRing`) — the
`Correspondence.lean`-style route — not by raising the cap. Both are reusable
lessons (the explicit-instance one extends the playbook's §3.11 family).

**Promotion candidates.** The three generic `AlgebraicCurve` helpers the pin keeps
`private` (`finrankAlong_comp`, `finrankAlong_id`,
`finrankAlong_eq_relfinrank_fieldRange`) are `private` in `Degree/Roof.lean` and
are the one SET-M3 item that belongs outside `ModularCurve`. Promoting them to
`AlgebraicCurve/Defs/Correspondence.lean` beside `finrankAlong` is recommended
but not done (AC is a closed effort; the manager will decide or ask).

**Consequences for SET-M4.** m10 imports m6's degree modules and m7's degree
modules; m11 imports m7 (via `isIntegral_gens`) and AC's
`hasPrincipalDivisors_adjoin_of_transcendental`; m12 imports m1's vocabulary, m9's
roof, m10's integrality and the ported AC exchange. The SET-M4 orders are
unchanged and dispatched next.

## §6 SET-M4 — integrality, principal divisors, and the exchange reduction (m10, m11, m12)

**Status (2026-09-23): green, 0 mismatched / 0 missing.** Run m10 → m11 → m12;
build and statement-check after each module. All 19 declarations are
transcriptions of the pin's `solution`/wrapper statements; no statement was
weakened and no heartbeat cap was raised.

| topic | module | lines | public decls | build | checker |
|---|---|---|---|---|---|
| m10 | `HeckeInputs/Integrality.lean` | 393 | 13 | `lake build` **17 s** | 1210 → **1223** |
| m11 | `PrincipalDivisors/ModularCurveBar.lean` | 81 | 2 | `lake build` **4 s** | **1225** |
| m12 | `HeckeExchange/Reduction.lean` | 144 | 4 | `lake build` **16 s** | **1229** |

`timeout 180 lake build` = **4,106 jobs, exit 0, 0 warnings, no `sorry`**
(baseline 4,103; the three new modules). `#print axioms` on all
`finiteAlong_hecke{Alpha,Beta}Bar_of_modularPolynomialData`, the five tower nodes,
`hasPrincipalDivisors_{laurentBaseChange_modularFunctionFieldFull,modularFunctionFieldBar}`
and the four m12 reductions returns `[propext, Classical.choice, Quot.sound]`.
Consumer `spec/ModularCurveHeckeConsumer.lean` = **0 errors / 0 warnings**, with
the new Zone J `[inputs]` and Zone H `[reduction]`.

### §m10 — tower integrality/finiteness and the Hecke integrality predicates

**The `gens` set** is the pin's, transcribed `private`:
`gens L N = {x | ∃ (d) (_ : NeZero d), d ∣ N ∧ x = jqNModC L d}` — a `Set`
(`gens_finite` is `(Set.finite_Iic N).image` of the `if d = 0 then 0 else jqNModC L d`
indicator). `jqNModC_mem_bar` rewrites `coeffEmb_jqN` and `jqd_mem_full`.

**The two `FiniteAlong` routes.** `finiteAlong_heckeAlphaBar_of_modularPolynomialData`
(74 content) sets the along-algebra/module from the map's `toRingHom.toAlgebra`,
proves `IsIntegral` of every `S = {y | (y : LaurentSeries L) ∈ gens L (N * ℓ)}`
through the injective `valAlong` (`isIntegral_algHom_iff`), then
`hgen = laurentBaseChange_modularFunctionFieldFull` (m7) gives
`adjoin L (gens L (N * ℓ)) = ⊤`, `adjoin_eq_top_iff_of_isAlgebraic` converts the
`IntermediateField` adjoin to the `Algebra.adjoin`, and `fg_adjoin_of_finite`
closes `Module.Finite`. The generators' integrality splits by
`dvd_mul_prime_cases hℓ hdvd`: the `e ∣ N` branch is `isIntegral_algebraMap`, the
`e = d * ℓ` branch is m6's `isIntegral_jqNModC_mul` (which uses
`ModularPolynomialData.eval_jqNModC_mul_eq_zero`). `finiteAlong_heckeBetaBar_of_modularPolynomialData`
(116 content) replaces the generator integrality by
`isIntegralElem_heckeBetaBar_gens`, which uses m6's `eval_jqNModC_of_mul_eq_zero`
(the `hsymm` form) to build the integrality certificate
`data.Φ.map ev` for the `q ↦ q ^ ℓ` image, and the local `qExpand_jqNModC`.
Neither pin file needed a heartbeat bump; both elaborate under the project's
global `4000000`.

**The four `_of_prime` forms** are the general forms at
`exists_modularPolynomialData_evalSymm ℓ` (m6). The general
`hecke{Alpha,Beta}BarIntegral_of_modularPolynomialData` are the `FiniteAlong`
heads plus `Algebra.IsIntegral.of_finite`; all six build in a few seconds.

**The five tower nodes.** `towerInclBar_surjective_of_dvd_dvd` is the
antisymmetry composite (`towerInclBar_comp_towerInclBar` + `towerInclBar_self`).
`towerInclBar_isIntegral`/`towerInclBar_finiteAlong` are the pin's strong
induction on the quotient `k` (`N * k = M`): the `k = 1` case is
`RingHom.isIntegral_of_surjective`/`finiteAlong_of_surjective`, the step peels a
prime `p ∣ k` and composes `towerInclBar (N * k') p`,
`heckeAlphaBar (N * k') p` and `towerInclBar`. `towerSubstBar_isIntegral`/
`towerSubstBar_finiteAlong` are `heckeBetaBarIntegral_of_prime`/`finiteAlong_heckeBetaBar_of_prime`
composed with the `towerInclBar` legs (`RingHom.IsIntegral.trans`/`finiteAlong_comp`).
`finiteAlong_comp`/`finiteAlong_of_surjective` are AC's (`WeilExchange/Transport.lean`),
now imported by m10.

### §m11 — `HasPrincipalDivisors` for the modular function fields

**The prediction held.** The layer form is a **two-stage collapse onto AC's**
`AlgebraicCurve.hasPrincipalDivisors_adjoin_of_transcendental`, with no new
mathematics: after `rw [laurentBaseChange_modularFunctionFieldFull, ← insert_gens]`
the goal is literally `HasPrincipalDivisors L (adjoin L (insert (jqModC L) (gens L N)))`;
the instantiation is `K := L`, `x := jqModC L`, `hx := transcendental_jqModC L`
(m6), `T := gens L N` (the pin's `Finset` `{jqNModC L d | d ∣ N}`, transcribed
`private` with `mem_gens_iff`/`insert_gens`), and each `hT` obligation is m6's
`isIntegral_jqNModC_all_of_modularPolynomialFamily L hΦ d`. `CharZero L` comes from
`charZero_of_injective_algebraMap (algebraMap ℚ L).injective`.

**`hΦ`'s role, honestly.** `hΦ` is consumed *only* through
`isIntegral_jqNModC_all_of_modularPolynomialFamily` — the datum family is used
inductively (minFac peeling) exactly as m6 states it. No `data : ModularPolynomialData N`
is needed directly, and the pin's proof does not use more than the adjoin route
(the pin's `S_` file's `gens`/`mem_gens_iff`/`insert_gens` are the only extra
declarations, and they are the `Finset` packaging of the same generator set).

**Measured.** 81 port lines against the pin's 82 raw / 38 content; one of the two
module builds is 4 s. The `bar` form is the layer form at
`L = AlgebraicClosure ℚ` (`modularFunctionFieldBar N` is `abbrev`, so the
application is definitional); `CharZero (AlgebraicClosure ℚ)` is found by
instance search, so no explicit `PerfectField`/`CharZero` local is required.

### §m12 — the exchange reduction

**The two `heckeDivBar` nodes.** `heckeDivBar_heckeDivBar_of_heckeExchangeAt`
rewrites both `heckeDivBar`s and applies AC's
`Divisor.correspondence_correspondence` with
`φ = heckeBetaBar L N ℓ`, `ψ = heckeAlphaBar L N ℓ`,
`φ' = heckeBetaBar L N ℓ'`, `ψ' = heckeAlphaBar L N ℓ'`,
`u = towerInclBar L (dvd_of_eq_roof …).1`,
`u' = towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof …).2`; the `HeckeExchangeAt`
hypothesis `hex` is instantiated at `hβ hα' hu hu'`, and the two composite
integralities are `RingHom.IsIntegral.trans _ _ hβ' hu'`/`… hα hu`. The result is
the single roof `correspondence (towerSubstBar L N (ℓ*ℓ') h₁) (towerInclBar L h₂)`,
and `Divisor.correspondence_congr` identifies it with the two composites through
`towerSubstBar_comp_heckeBetaBar`/`towerInclBar_comp_heckeAlphaBar`.
`heckeDivBar_comm_of_heckeExchangeAt` runs that at `(ℓ, ℓ')` and `(ℓ', ℓ)` and
closes with `correspondence_congr (towerSubstBar_congr L (mul_comm ℓ ℓ') h₁ h₁') rfl`.

**The operator node.** `heckeOperatorBar_comm_of_heckeExchangeAt` splits on
`HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ` and `… ℓ'`; each junk branch is
`0 = 0` (`heckeOperatorAlong_of_not`), and the live branch
`obtain`s `hα hβ hFI hfin hN`, rewrites both `heckeOperatorAlong`s through
`heckeOperatorAlong_eq`, and descends to
`Pic0.correspondence_correspondence_comm` with the divisor identity
`fun D => heckeDivBar_comm_of_heckeExchangeAt … D`. The tower integrality the
node needs is m10's `towerInclBar_isIntegral`/`towerSubstBar_isIntegral` (the
pin's `S_` file does not pass m9's roof or the diagonal degree).
`heckeOperatorsCommuteBar_of_heckeExchangeAt` is the `Nat.Primes` bookkeeping:
`rintro ⟨ℓ, hℓ⟩ ⟨ℓ', hℓ'⟩`, `ℓ = ℓ'` is `rfl`, otherwise build `M = N * ℓ * ℓ'`,
turn `hℓ`/`hℓ'` into `Fact` instances, discharge the three
`HasPrincipalDivisors` instances from `hP`, and call the operator node with
`hex ℓ ℓ' _ rfl hne`/`hex ℓ' ℓ _ (by ring) (Ne.symm hne)`.

**The pin's pointwise rewrite does not survive the port.** In the junk branches
the pin's `apply LinearMap.ext; intro x; rw [heckeOperatorBar_apply]` fails:
after `intro x` Lean reports the goal `(heckeOperatorBar N ⟨ℓ, ⋯⟩) x = 0 x` is
not type-correct at implicit transparency, and `rw`'s keyed match tries to apply
`⟨ℓ, ⋯⟩ : {p // Nat.Prime p}` where `Nat.Primes` is expected. `Nat.Primes` is a
`def` (`rfl`-equal to the subtype), so this is the port's `Nat.Primes`/`JZero`
abbrev unfolding, not a mathematics change. The port proves the same `z` at the
bare linear-map shape instead: `show (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ).toIntLinearMap = 0; rw [heckeOperatorAlong_of_not h₁]; rfl`.
The statement is unchanged.

### §SET-M4 hand-off — the exact capstone binders

The capstone (`Capstone.lean`, human) needs:

- **`HeckeExchangeAt` (m1, `Defs/DegeneracyTower.lean`)**, verbatim
  `HeckeExchangeAt (L) (N ℓ ℓ' M : ℕ) [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M]
  (hM : M = N * ℓ * ℓ') : Prop`, a `∀` over the two `HasPrincipalDivisors`
  instances on `laurentBaseChange L (modularFunctionFieldFull (N * ℓ))`/
  `(modularFunctionFieldFull M)`, the four `IsIntegral` hypotheses
  `hβ : (heckeBetaBar L N ℓ).toRingHom.IsIntegral`,
  `hα' : (heckeAlphaBar L N ℓ').toRingHom.IsIntegral`,
  `hu : (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1).toRingHom.IsIntegral`,
  `hu' : (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).toRingHom.IsIntegral`,
  and `D : Divisor L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ')))`, with
  the conclusion the `β^* α_* = incl_* subst^*` identity.
- **The two `HasPrincipalDivisors` instances (m11)** are
  `hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull L hΦ (N * ℓ)`
  and `… L hΦ M` (the `bar` forms come from
  `hasPrincipalDivisors_modularFunctionFieldBar hΦ M`; `hΦ` is
  `modularPolynomialFamily`, unconditional).
- **The reduced assembly** is
  `heckeOperatorsCommuteBar_of_heckeExchangeAt N hP hex` with
  `hP : ∀ (M : ℕ) [NeZero M], HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M)`
  supplied by `fun M _ => hasPrincipalDivisors_modularFunctionFieldBar hΦ M`, and
  `hex : ∀ (ℓ ℓ' M : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M]
  (hM : M = N * ℓ * ℓ'), ℓ ≠ ℓ' → HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM`
  the output of `heckeExchangeAt_of_WEX` (which consumes m9's
  `heckeRoof_adjoin_range_union_eq_top` as its `hgen` and m9's
  `finrankAlong_towerSubstBar_comp_heckeAlphaBar` as its `hLD` — **not** the M2
  nodes of m12, whose proofs mention neither).
- **Consumer wire test.** Zone H's last example composes
  `heckeOperatorsCommuteBar_of_heckeExchangeAt 1 hP hex` and has type
  `HeckeOperatorsCommuteBar 1`.

**One reporting correction to the SET-M3 hand-off.** The §SET-M3 hand-off said
m12 "consumes `heckeRoof_adjoin_range_union_eq_top` (the `hgen`) and
`finrankAlong_towerSubstBar_comp_heckeAlphaBar` (the `hLD`)". The pin's four M2
`S_` files mention neither (checked with `grep -l`); those two are inputs of
`heckeExchangeAt_of_WEX`, i.e. the capstone. m12's real inputs are AC's
`Divisor.correspondence_correspondence`/`correspondence_congr`,
`Pic0.correspondence_correspondence_comm` and m10's tower integrality.

### §Review of SET-M4 and the capstone

**Reviewed by the manager (2026-09-23 19:00). Verdict: PASS, and the effort's
target is reached.** SET-M4 delivered m10–m12; the manager then wrote the
reserved capstone (`Capstone.lean`).

| check | independent result |
|---|---|
| SET-M4 modules | `HeckeInputs/Integrality` 393, `PrincipalDivisors/ModularCurveBar` 81, `HeckeExchange/Reduction` 144 lines, 0 `sorry` |
| capstone | `FLTForHuman/ModularCurve/Capstone.lean`, 178 lines, builds **first try in 13 s** |
| `timeout 180 lake build` | **4,107 jobs, 0 warnings, exit 0, no `sorry`** (Capstone built in 12 s) |
| checker | **1,237 identical (67 promoted), 0 mismatched, 0 missing**, 1,251 checked |
| `#print axioms ModularCurve.heckeOperatorsCommuteBar` | `[propext, Classical.choice, Quot.sound]` |
| consumer | Zones A–K at **0 errors, 0 warnings**; Zone K checks the unconditional target |
| **remaining cone** | **0 nodes / 0 raw / 0 content** (was 82 / 10,569 / 7,579 at the effort's start) |

**The two predictions held.** m11's "nearly a corollary" collapse onto AC's
`hasPrincipalDivisors_adjoin_of_transcendental` is measured at **81 port lines
against the pin's 82 raw / 38 content**, with `hΦ` consumed *only* through m6's
integrality lemma. And the capstone is pure assembly: `heckeExchangeAt_of_WEX`
applies the ported AC exchange to the roof square, and the three dischargers are
m11 + m6 (`hP`, `dataAll`) and m10 + AC (`hsepS`). No new mathematics was needed
at the top, which is the sharpest evidence that the slice cut was right.

**One correction the subagent caught.** The SET-M4 order claimed m12 consumes
m9's roof and diagonal degree; it does not — those are inputs of the capstone's
`heckeExchangeAt_of_WEX`. m12's real inputs are the AC exchange API and m10's
tower integrality. Recorded, no work lost.

**Capstone review instrument.** Because the capstone is assembly over m9–m12,
writing it was the final wire test: a wrong `HeckeExchangeAt` binder, a missing
tower integrality or a mis-stated roof would have failed to compile. It compiled
first try, so every upstream interface is intact.

## §Friction

- **`Defs/Laurent.lean` is off-limits, so the two generic supply lemmas live in
  `HeckeOperator`.** The topic suggested promoting `laurentBaseChange_mono`/
  `qExpand_mem_laurentBaseChange` beside `laurentBaseChange`; the workspace rule
  forbids editing `Defs/Laurent.lean`, and the manager confirmed they are wrapper
  targets, so they are public in `HeckeOperator` instead. Recorded, not worked
  around.
- **The AC `SMul (F ≃ₐ[K] F) (Place K F)` is missing.** `AtkinLehner`'s
  `frickeInvolution N • cuspInfty N` needs it; the AC port dropped the
  `DivisorClassGroup` block that defines it. Restored anonymously in
  `Defs/AtkinLehner.lean` via `SemilinearAut.ofAlgAut` (the one promoted helper).
  The `Pic0` half (`JZero.torsionGaloisRep`) stays deferred.
- **v4.34 `SpecialLinearGroup.map` coercion drift.** In `Gamma0Cosets`, `simp`
  no longer reduces `↑(mapGL ℝ (conjSL …))` to matrix entries, so the pin's
  one-line `heckeDiagMatrix_mul_mapGL` proof was replaced by an explicit
  `Matrix.GeneralLinearGroup.ext` + a `mapGL_conjSL` matrix lemma +
  `Matrix.map` `change`. Statement unchanged; cost ~half a round.
- **`HahnSeries.order` is otherwise stable.** The pin's `order_mul_of_ne_zero`
  hypothesis shape (`leadingCoeff * leadingCoeff ≠ 0`) already matches v4.34, so
  `QAdicPlace` was mostly assembly.
- **No `maxHeartbeats` touches, no timeouts.** The heaviest module build (with
  imports compiled) was ~6 s; the full build is seconds over the cached tree.

- **SET-M2 blocker — `CuspDichotomy.lean` kernel timeout (manager diagnosis,
  2026-09-23 17:30).** m5's last module does **not** elaborate: `lake build
  FLTForHuman.ModularCurve.Analytic.CuspDichotomy` exceeds 240 s (EXIT 124) and
  never writes an olean; `lake env lean` returns after **3 m 09 s (user 3 m 17 s)**
  with `(kernel) deterministic timeout` at `TwoCuspAux.coe_jTr` (and downstream
  `coe_φ`/`φ_algebraMap`), then cascading `unknown constant` errors. The cause is
  structural, not mathematical: `TwoCuspAux.jTr` is a `Subtype` ring equivalence
  whose `toFun` carries the proof `(mem_bar_iff ℓ x).mpr x.2`, and `mem_bar_iff`
  is proved through the subagent's shortcut `bar_eq_restrictScalars`
  (`full_eq_of_prime` + `laurentBaseChange_modularFunctionField_local` +
  `adjoin_simple_adjoin_simple`). The kernel cannot check `coe_jTr`'s
  definitional equality cheaply, because normalising `jTr` drags that heavy proof
  term. The file also carried a botched duplicated block at top level (former
  lines 324–356: `le_finrank`/`finrank_tower_eq` re-declared outside
  `TwoCuspAux` using its local `𝕂` notation and unqualified names) left by an
  in-place append; the manager removed it. The file is set aside as
  `Analytic/CuspDichotomy.lean.wip` so the tree stays green (full build 4,099
  jobs), it was never registered in `PORT_FILES`, and nothing imports it.
  **Re-scope**: a focused `TOPIC-m5b` re-dispatches it, restating `jTr`/`φ` so the
  kernel check is cheap (do **not** raise `maxHeartbeats`). The rest of SET-M2 is
  green: `Gamma0InvariantCore` 919, `FrickeInvariance` 410, `CuspBookkeeping` 199,
  `FrickeAut` 376, `PhiData` 630, `PhiDegree` 184 lines, checker 1,128 identical /
  0 mismatched / 0 missing.

- **Build-discipline lesson — CPU time is the discriminator.** The blocked module
  is a *real* blow-up: real 3 m 09 s with **user 3 m 17 s** and a kernel
  deterministic timeout. An earlier reading of the same file (real 4 m 34 s, user
  0.5 s, sys 1.3 s) was **lock/serialization contention** with another agent's
  build, not Lean compute — bisecting that reading would have been wasted work.
  Going forward: measure with `time`; high user CPU + timeout ⇒ bisect; ~0 CPU ⇒
  re-run when idle; never build concurrently with another agent.

- **Resolved (m5b) — the `CuspDichotomy` kernel timeout.** See §m5b. The original
  diagnosis named the `mem_bar_iff` proof as the drag; the deeper cause is the
  `Subtype.val` defeq between two concrete `IntermediateField.adjoin` carriers (it
  persists with the proof abstracted). The fix is the generic `ifRE`/`ifRE_coe` pair,
  so `jTr`'s coercion is a generic `rfl` and the kernel never normalises the carriers.
  Two secondary costs also went: the cross-`IntermediateField` `algebraMap` `rfl` in
  `φ_algebraMap` (now `IntermediateField.coe_algebraMap_apply`) and the v4.34
  `linter.style.haveILetI` (`haveI` → `have`). No cap was raised; the module builds
  in **15.9 s** and the full tree at **4,100 jobs, 0 warnings**. **Promoted to
  [porting-playbook.md](../porting-playbook.md) §3.11** as the second generic
  blow-up failure mode, together with the CPU-time blow-up/contention
  discriminator.

- **SET-M3 — instance *search* timeouts, not proof blow-ups (m7's
  `TransportDev`).** The one place m7 needed help was typeclass resolution at
  `Algebra.IsIntegral ↥(K₀ t) ↥(E₀ …)` and `Free ↥(K₀ t)/↥(K L t)
  ↥(E₀ …)/↥(E L …)`, each a `(deterministic) timeout … (20000)` at the default
  instance budget. The fix is an **explicit instance local**
  (`have : Algebra.IsIntegral … := Algebra.IsIntegral.of_finite _ _`,
  `have : Module.Free … := Module.Free.of_divisionRing …`), exactly the
  `Correspondence.lean` pattern. No `maxHeartbeats`/`synthInstance.maxHeartbeats`
  was touched. Distinguish this from a proof blow-up: the module still builds in
  8–16 s once the instances are named, so the cost was search, not compute.

- **SET-M3 — the pin's roof caps are dead weight.** The pin raises
  `maxHeartbeats 6400000` and `synthInstance.maxHeartbeats 3200000` around the
  roof and the diagonal degree. The port's `Degree/Roof.lean` builds under the
  project's global `maxHeartbeats 4000000` (and the default 20,000 instance
  budget) in **15 s**. The saving is the deduplicated prelude: the pin's
  `set_option` bumps were paying for its own 356-line inlined prelude, which the
  port imports.

- **v4.34 deprecations beyond `dif_pos`/`dif_neg`.** `if_pos`/`if_neg` are now
  deprecated in favour of `ite_eq_left`/`ite_eq_right` (the pin's
  `Finset.sum_ite_eq` step in `linearIndependent_pow_mul` and the two `by_cases`
  branches of `relfinrank_qExpand_full`); `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`
  recurred in `laurentBaseChange_modularFunctionFieldFull` (the same drift
  `QAdicPlace` recorded). `linter.style.haveILetI` also fired on the two algebraic
  `letI`s in the `finrank_adjoin_jq_*` heads; accepting `let` still registers the
  local for typeclass search, so the proofs are unchanged.

- **SET-M3 — a public/private twin is harmless to the checker.** `order_qExpand`
  and `order_coeffEmb` were proved `private` in `Analytic/CuspBookkeeping.lean`
  (m5, before m7 existed) and are now public in `Degree/LaurentGlue.lean`. The
  checker skips `private` port declarations, so the pair is not a mismatch; the
  private copies are the m5 record and the public ones are the wrapper targets.
  No module was edited to remove the private twins (the SET-M2 modules are
  frozen).

- **Build discipline tightened (manager, 2026-09-23 18:40).** The SET-M1–SET-M3
  work orders had loosened the playbook's original bounds to `timeout 240 lake env
  lean` / `300 lake build <module>` / `900 lake build`; a multi-minute build is
  never acceptable, even while experimenting. The canonical block in
  [porting-playbook.md](../porting-playbook.md) §3.11 now reads **60 / 90 / 180**,
  states **expect ≤ 30 s** and "past ~60 s is a blow-up to bisect", and the same
  numbers (and the CPU-time blow-up/contention discriminator) replace the loose
  ones in every `topics/**/*.md` work order, including the retired AC/FFG and the
  paused-face records. SET-M4 was dispatched with the tightened block.

- **SET-M4 — the port's `Nat.Primes` abbrev breaks a pointwise `rw` (m12).** The
  pin's `S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt` proves the junk
  branch by `apply LinearMap.ext; intro x; rw [heckeOperatorBar_apply]`. In the
  port the `rw` fails with "the target expression is not type-correct under the
  `implicit` transparency level": `Nat.Primes` is a `def` (not an `abbrev`), and
  after `intro x` the goal's `⟨ℓ, ⋯⟩` is re-elaborated as `{p // Nat.Prime p}`
  while `heckeOperatorBar` still expects `Nat.Primes`. The fix is shape-level, not
  a cap: state `z` at the bare linear map
  (`show (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ).toIntLinearMap = 0; rw [heckeOperatorAlong_of_not h₁]; rfl`).
  Statement unchanged; this is the third member of the family the playbook's
  §3.11 records (a `def`-vs-`abbrev` transparency mismatch inside a tactic), to be
  told apart from the `FunLike`/concrete-carrier blow-ups by the fact that it
  *fails fast* rather than timing out.
- **SET-M4 — the `haveI`/`letI` linter fires on the pin's instance walls.** m10's
  two `FiniteAlong` proofs carry the pin's `letI : Algebra …`/`letI : Module …`
  and `haveI : NeZero d`/`haveI : Fact p.Prime`; `linter.style.haveILetI` reports
  each (the values are propositions for the `haveI`s, and the `letI`s are in a
  proposition proof). Accepted `let`/`have` throughout, exactly as
  `Degree/Relfinrank.lean` did: the local still registers for typeclass search,
  and the proofs and statements are unchanged. Zero warnings.
- **SET-M4 — m10/m11 import AC's `WeilExchange/Transport.lean`.** The pin's
  `towerInclBar_isIntegral`/`finiteAlong` cite `AlgebraicCurve.finiteAlong_comp`/
  `finiteAlong_of_surjective`, which the AC port publishes in
  `WeilExchange/Transport.lean` (not in `Defs/Correspondence.lean`). The topic
  import list named `Defs/HeckeOperator` only; the two helpers are the real
  dependency, and adding the import is the whole cost.
- **SET-M4 — the SET-M3 hand-off over-attributed m12's inputs.** The §SET-M3
  hand-off (and TOPIC-m12 §Imports) said m12 consumes m9's roof and diagonal
  degree. The pin's four M2 `S_` files reference neither (`grep -l` is empty);
  those two are inputs of `heckeExchangeAt_of_WEX`, i.e. the capstone. m12's real
  inputs are the AC exchange API and m10's tower integrality. Recorded rather than
  worked around: no roof/diagonal import was added to `Reduction.lean`.
- **SET-M4 — the consumer zone letters collide with the plan.** `PORTING-MC.md`
  §7.2 planned Zone E `[inputs]`/Zone F `[reduction]`, and `SET-M4.md` §2 says
  Zone G `[inputs]`/Zone H `[reduction]`; but the consumer already used G for the
  `HeckeAlg` `[payoff]` and E/I/F for the m5b/m7/m9 zones. The new zones are
  therefore **J `[inputs]`** (m10/m11) and **H `[reduction]`** (m12), matching the
  SET-M4 name for the reduction and taking the next free letter for the inputs.
  The manager may re-letter in review; the content is what the wire test checks.
