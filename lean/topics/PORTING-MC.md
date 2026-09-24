# Blueprint: the `ModularCurve` Hecke layer for `ModularCurve.heckeOperatorsCommuteBar`

> **RETIRED (2026-09-23).** This blueprint is complete: SET-M1–SET-M4 landed and
> the reviewer's capstone `ModularCurve.heckeOperatorsCommuteBar` closed the
> effort. The remaining cone is **0 nodes / 0 raw / 0 content**; the checker reads
> **1,237 identical, 0 mismatched, 0 missing**; `lake build` is **4,107 jobs,
> 0 warnings, no `sorry`**; `#print axioms` on the target is
> `[propext, Classical.choice, Quot.sound]`. It is kept as the effort's planning
> record. The closing review is [mc-retrospective.md](mc-retrospective.md); the
> measured record is [../logs/mc-port.md](../logs/mc-port.md).

**Status (2026-09-23): effort complete.** This is the
fourth Lean port. It targets the **remaining 82 theorem nodes** of
`studies/hecke-commute-bar-coverage.md` — the `math/009` divisor-correspondence
Hecke face — plus the `ModularCurve` definition modules those nodes import. It is
opened now because the `AlgebraicCurve` port ([PORTING-AC.md](PORTING-AC.md),
retired) closed every *generic* input of the theorem, and because the
*automorphic* Hecke face ([PORTING-Hecke.md](PORTING-Hecke.md)) is paused with
its vocabulary (`heckeU`/`heckeT`, the `q`-coefficient layer) already ported and
reusable.

**Topics are coded `M`/`m` (`SET-M*`, `TOPIC-m*`) to keep them disjoint from the
paused automorphic face's `t`-numbered orders in [hecke/](hecke/).**

| set | topics | result |
|---|---|---|
| SET-M1 | m1–m3 | the Hecke vocabulary, the geometric/cusp/modular-unit vocabulary, the modular-unit `q`-expansion — **work orders written, not started** |
| later | m4–m12 | the Fricke/inclusion core, the degree theory, the Φ tail, the roof, integrality, principal divisors, the exchange reduction |
| capstone | `heckeExchangeAt_of_WEX` + `heckeOperatorsCommuteBar` | reserved for the human reviewer |

Companion records:

- [studies/hecke-commute-bar-coverage.md](../../studies/hecke-commute-bar-coverage.md) —
  the measured gap this blueprint closes (§§4–§6 are the scope).
- [studies/hecke-commute-bar-survey.md](../../studies/hecke-commute-bar-survey.md) —
  the mathematics: the two degeneracy maps, the roof square, the exchange, and
  §9's "what the note must not claim".
- [math/009-hecke-jacobian-commute.md](../../math/009-hecke-jacobian-commute.md) —
  the note this work serves.
- [PORTING-AC.md](PORTING-AC.md), [ac-retrospective.md](ac-retrospective.md) —
  the immediately preceding effort and its review; this blueprint inherits its
  verification machinery and its process wholesale.
- [porting-playbook.md](porting-playbook.md) — the reusable method.
- [hecke/SET-M1.md](hecke/SET-M1.md), [hecke/TOPIC-m*.md](hecke/) — the run brief
  and work orders; [../logs/mc-port.md](../logs/mc-port.md) — the measured record.

FLT line numbers and paths are against `anthropics/fermats-last-theorem@aa2d8b3`
(local clone `~/proj/fermats-last-theorem`); mathlib is the project's pinned
`v4.34.0`.

## 0. Scope

**The target is the whole remaining cone of `ModularCurve.heckeOperatorsCommuteBar`**
as measured in the coverage report: **82 theorem nodes / 10,569 raw / 7,579
content `S_` lines**, plus the **13`ModularCurve` definition modules** the proof
imports and the port does not yet carry (≈1,713 pin lines, §2.2). The cone is
the *divisor-correspondence* Hecke face: `heckeAlphaBar`/`heckeBetaBar`
(inclusion and `q ↦ q^ℓ`), the degeneracy tower
(`towerInclBar`/`towerSubstBar`), the roof square, `HeckeExchangeAt`, the
operators `heckeOperatorBar`, and the proposition `HeckeOperatorsCommuteBar`.

**What this port is not.**

| slice | status |
|---|---|
| the automorphic slash face (`heckeU`/`heckeT`, invariance, eigenforms, lattice) | ported by the paused [PORTING-Hecke.md](PORTING-Hecke.md); **not** part of this cone |
| `Module.Finite ℤ (heckeAlgebra N k S)`, `HasIntegralStructure` | out of scope (coverage §9; `TOPIC-t10-finite-algebra.md` §7) |
| the mod-`p`/Galois-representation tower, Eichler–Shimura, `CurveModel` | out of scope; nothing here imports them |
| Γ₁/Nebentypus/Γ_H/Atkin–Lehner *levels* beyond what the cone names | deferred, as in the paused effort's SET 5 |

**What it buys.** With this port, every input of `ModularCurve.heckeOperatorsCommuteBar`
is a ported theorem: the divisor exchange (`AlgebraicCurve`), the function-field
generation (FFG), the modular polynomial family (`Φ_p`), principal divisors, and
the roof generation/degree facts. The headline becomes unconditional, and the
`HeckeAlg`-module structure of `JZero N` (math/009 §7) becomes statable.

## 1. Organization for math clarity

The rules of [PORTING-FFG §1](PORTING-FFG.md) and playbook §7.1–§7.2 govern.
The MC-specific statements:

- **Namespace `ModularCurve`**, matching FLT and the existing port, so the
  checker's name map stays mechanical. The one exception is the generic
  `qParam`-uniqueness engine, which is namespace-free in the pin and stays so.
- **A module is a mathematical role.** The pin's `Def_ModularCurve_X0` (348) is
  already split (`Defs/Laurent`, `Defs/Jq`, `Defs/Fields`, `Defs/Polynomial`);
  this effort splits `Def_ModularCurve_HeckeOperator` (191) into the operator
  block, keeps `DegeneracyTower` (138) whole, and writes the geometric base
  change (`Def_ModularCurve_GeometricBaseChange`, 227) whole. The split is §6.
- **Adopt the port's vocabulary as the interface from the first declaration.**
  `heckeAlphaBar = towerInclBar L (dvd_mul_right N ℓ)`, `heckeBetaBar =
  towerSubstBar L N ℓ dvd_rfl`; `towerSubstBar = towerInclBar ∘ heckeBetaBar`;
  `JZero = Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`. These are
  definitional identities the pin proves by `rfl`; keep them `rfl` so the port's
  `rfl` bridges survive.
- **Drop the pin's scaffolding, not its mathematics.** `p2m_*`, the
  `attribute [-instance]`/`[-simp]` walls and the generated `rowMain`/`solution`
  pair are never written (§4.2 of PORTING-AC). Statements come from the
  `Theorems/` wrappers.
- **A shared prelude gets one public home.** The pin repeats two large blocks
  this effort would otherwise pay three or four times: the `TS`/`conj`/
  `phiAtSeed`/`roots_prime_at_slot` prelude (already ported once in
  `Defs/TS.lean`/`Defs/PhiAtSlot.lean`/`PhiSlotRoots.lean`) and the
  modular-unit `q`-expansion prelude (four copies). §§4.1–4.3 measure both.
- **Count before dropping.** Every pin declaration left out gets a `grep -c`
  count in the topic order and the log, as FFG/AC do.

## 2. The measured cone

Regenerate with §9.1.

### 2.1 The 82 theorem nodes, by topic group

`raw` is the whole `S_` file; `content` excludes imports, `attribute` lines,
namespace/`section`/`variable` lines, `p2m_*` lines, comments and blanks.

| group | nodes | raw | content | topic |
|---|---|---|---|---|
| **M1** Hecke correspondence vocabulary | 0 (defs) | — | — | m1 |
| **M2** exchange reduction | 4 | 111 | 68 | m-mid |
| **M3** cusp/`q`-adic vocabulary | 0 (defs) + 11 bookkeeping | 177 | 78 | m2, m-late |
| **M4** Laurent glue + relative degree | 12 | 1,402 | 1,061 | m-mid |
| **M5** Φ datum + degree tail | 14 | 1,465 | 950 | m-mid |
| **M6** roof generation + diagonal degree | 2 | 1,181 | 859 | m-late |
| **M7** modular-unit `q`-expansion | 9 | 1,677 | 1,282 | m3 |
| **M8** Fricke invariance + field inclusion | 8 | 3,030 | 2,307 | m-mid |
| **M9** cusp dichotomy, Fricke automorphisms, cusp bookkeeping | 17 | 1,072 | 650 | m-mid/m-late |
| **M10** tower integrality/finiteness | 13 | 447 | 301 | m-late |
| **M11** principal divisors | 2 | 82 | 38 | m-late |
| **capstone** | 1 | 112 | 63 | human |
| **total** | **82** | **10,569** | **7,579** | |

The exact partition is reproducible with §9.2. The two heaviest *developments*
are one story told in three files — the function-field degree/roof files
(`relfinrank_qExpand_full` 631, `heckeRoof_adjoin_range_union_eq_top` 418,
`finrankAlong_towerSubstBar_comp_heckeAlphaBar` 441) each re-derive the same
`TS`/conj/slot prelude — and the Fricke/inclusion core (M8) which the others
consume. §4 removes the duplication; the numbers above do not.

### 2.2 The 13 definition modules

None is imported by the coverage report's existing port; all are imported by the
remaining `S_` files. "Used by" counts how many remaining proof files import the
module (a lower bound on its cone relevance).

| module | lines | used by | home |
|---|---|---|---|
| `Def_ModularCurve_HeckeOperator` | 191 | 8 | `Defs/HeckeOperator.lean` |
| `Def_ModularCurve_DegeneracyTower` | 138 | 12 | `Defs/DegeneracyTower.lean` |
| `Def_ModularCurve_HeckeOperatorTotal` | 65 | — | `Defs/HeckeTotal.lean` |
| `Def_ModularCurve_HeckeModule` | 122 | 2 | `Defs/HeckeModule.lean` |
| `Def_ModularCurve_HeckeInputsAll` | 20 | — | `Defs/HeckeTotal.lean` |
| `Def_ModularCurve_ArithmeticGalois` | 140 | 2 | `Defs/ArithmeticGalois.lean` |
| `Def_ModularCurve_GeometricBaseChange` | 227 | 1 | `Defs/GeometricBaseChange.lean` |
| `Def_ModularCurve_QAdicPlace` | 380 | 3 | `Defs/QAdicPlace.lean` |
| `Def_ModularCurve_CuspidalClass` | 55 | 8 | `Defs/CuspidalClass.lean` |
| `Def_ModularCurve_AtkinLehner` | 107 | 10 | `Defs/AtkinLehner.lean` |
| `Def_ModularCurve_ModularUnit` | 185 | 10 | `Defs/ModularUnit.lean` |
| `Def_ModularCurve_JqCoeff` | 83 | 15 | `Defs/JqCoeff.lean` |
| `Def_ModularCurve_HeckeAlgebraDef` (`Def_HeckeGalois_EichlerShimura:14–16`) | 3 | — | `Defs/HeckeModule.lean` (optional payoff) |

`Def_ModularCurve_X0`, `Def_ModularCurve_LaurentCoeff`, `Def_ModularCurve_JqCoeff`
(coeff part) and `Def_ModularCurve_PhiGen` are already ported
(`Defs/{Laurent,Jq,Fields,PhiGen}.lean`); `Def_ModularCurve_ModularUnit`,
`Def_ModularCurve_AtkinLehner` and `Def_ModularCurve_ArithmeticGalois` are partly
out-of-cone API (`eisensteinNumerator`, `cuspZero`(Full), the Galois `≃ₐ`-action,
`JZero.torsionGaloisRep`) and are ported or deferred per topic.

### 2.3 The outbound interface tier

External indegree = citers *outside* the hecke closure. The reusable surface is
thin compared with AC's, and concentrated in the analytic/degree vocabulary:

| ext. | declaration | topic |
|---|---|---|
| 21 | `modularFunctionFieldBar` (the `bar` field itself) | m1 |
| 14 | `JZero` | m1 |
| 12 | `heckeOperatorBar` | m1 |
| 9 | `heckeAlphaBar` / `modularUnitSeries` | m1/m2 |
| 8 | `frickeInvolutionFull` | m2 |
| 7 | `qParam_coeff_unique` | m3 |
| 5 | `cuspInftyBar`, `qSeriesBar`, `heckeBetaBar` | m2/m1 |

(Measured with §9.3; the point is organizational — the vocabulary topics m1/m2
expose essentially the whole outbound surface before any heavy proof lands.)

## 3. The routes, and the mathlib seam

### 3.1 The dependency spine

After the vocabulary (m1/m2) the cone splits into three stories that rejoin at
the roof:

```
m1 vocabulary ─┬─> M2 exchange reduction ──> capstone (human)
               │
               ├─> M7 analytic series ─> M8 Fricke/inclusion ─┬─> M9 cusp dichotomy
               │                                             │        │
               │                                             └────────┴─> M4 degree/glue ─> M5 Φ tail
               │                                                                              │
               ├─> M10 integrality/finiteness <──────────────────────────────────────────────┘
               │
               └─> M11 principal divisors <── M5 + M4 + AC
                                                   │
                        M6 roof ───────────────────┘
```

The **analytic fork is real**: M7/M8 share nothing with M4/M5/M6 except the
vocabulary and the q-expansion machinery the port already has. This is the
scheduling freedom SET-M1 takes: do the vocabulary and the first analytic layer
first, while M4–M6's routes are priced off m1/m2's actual declarations.

### 3.2 The exchange reduction (M2)

`heckeDivBar_heckeDivBar_of_heckeExchangeAt` (10 content) and
`heckeDivBar_comm_of_heckeExchangeAt` (17) are bookkeeping: `HeckeExchangeAt`
moves the middle `β^*α_*` to `incl_* subst^*`, then `towerSubstBar_comp_heckeBetaBar`
(`qExpand_qExpand`) and `correspondence_congr` identify the two roofs.
`heckeOperatorBar_comm_of_heckeExchangeAt` (29) splits on `HeckeInputsAlong`
(junk branch `0 = 0`), rewrites through `heckeOperatorAlong_eq`, and applies the
ported `Pic0.correspondence_correspondence_comm`. These are *transcriptions
against a ported API*; their only real input is M10's tower integrality, which is
why they are scheduled after it.

### 3.3 The degree/roof theory (M4–M6)

- `relfinrank_qExpand_full` is the statement `[F_{Nℓ} : q^ℓ(F_N)] = if ℓ ∣ N then ℓ
  else ℓ+1`, proved through the cyclotomic slot product `roots_prime_at_slot` and
  `finrank_adjoin_jqN_eq_dedekindPsi` — **all ported** by the Φ_p effort.
- `heckeRoof_adjoin_range_union_eq_top` is the generation hypothesis: the roof's
  two legs generate the top field; its inputs are `FunctionFieldGeneration M`
  (FFG, ported) and `jqNModC`'s integrality (`isIntegral_jqNModC_mul`, M5).
- `finrankAlong_towerSubstBar_comp_heckeAlphaBar` is the diagonal-degree count
  `[F_M : F_{Nℓ'}] = ℓ`, via `relfinrank_qExpand_full`/`relfinrank_laurentBaseChange`.

The pin's three files each carry a ~370-raw-line private copy of the
`TS`/`conj`/`phiAtSeed`/`roots_prime_at_slot` prelude. The port writes it **once**
(it already did, in `Defs/TS.lean`/`Defs/PhiAtSlot.lean`/`PhiSlotRoots.lean`), so
these topics should be mostly assembly. This is the largest single reduction the
effort has (§4.1).

### 3.4 The analytic core (M7–M9)

The pin proves the four `hasSum_*modularUnitSeries*` statements in four ~300-line
files with a **byte-identical 165-line prelude** (§4.3): the eta product `gfun`,
its nonvanishing on the unit disc, `discriminant = qParam · gfun`, the theta
transport, Taylor coefficients, and the generic `hasSum_modularUnit` /
`hasSum_modularUnitInv`. The port writes that prelude once and derives all four
heads from the two generic ones.

`mem_modularFunctionField_of_hasSum_of_gamma0_invariant` (656),
`isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant` (656) and
`coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant` (913) are the cone's
substantive analysis: an `Γ₀(N)`-invariant function realized by a `qParam`
expansion lies in the modular function field, is integral over `ℚ[jq]`, and its
Fricke transform is the `N^12 · (unit)^{-1}` twist. mathlib has the
`ModularForm`/`qParam`/`Gamma0` vocabulary but none of these statements; the
predecessor (`ModularForms/QExpansionPrinciple.lean`, `Hauptmodul.lean`) already
did the level-one analogue once, so the route is known.

### 3.5 The Φ tail (M5)

`nonempty_modularPolynomialData_of_squarefree` (363) is the one real proof: for
squarefree `N > 1`, the biresultant of the prime data assembles a datum at `N`.
Everything else is a **one-liner over the ported Φ_p effort**:

- `exists_modularPolynomialData_evalSymm` = strip `PhiIrreducible` from the
  ported `exists_phiIrreducible_evalSymm`;
- `modularPolynomialFamily` = the same, universally;
- `full_eq_of_prime` / `functionFieldGeneration_of_prime` = the ported
  `gen_prime`/`Hall`;
- `ModularPolynomialData.isIntegral_jqN` = `aeval_jqN_toAdjoin`/`minpoly_jqN_eq`;
- `isIntegral_jqNModC_mul` = `phiAtSeed_jqN_eval_down`;
- `transcendental_jqModC`, `finiteDimensional_adjoin_jqNModC`,
  `finrank_adjoin_jqNModC_le` = the `toAdjoin`/`finrank_adjoin_jqN_eq` API;
- `finrank_adjoin_jqNModC_eq_of_prime` = `finrank_adjoin_jqN_eq_of_prime` after
  the M9 restrict-scalars identification.

The topic order must **verify each one-liner and record it**; a claim that two
statements are equal is tested by the checker, not assumed.

### 3.6 The mathlib seam, measured

Two seams, both already used by the port:

- **the modular-forms seam** — `ModularForm.discriminant`,
  `Function.Periodic.qParam`, `CongruenceSubgroup.Gamma0`, `ModularGroup.S/T`,
  `UpperHalfPlane.denom`, `Matrix.SpecialLinearGroup`, mathlib's
  `ModularForm.trace`/`eq_const_of_weight_zero` (the last two already consumed by
  the level-one analytic modules). No `EichlerShimura`, `Petersson`, `SturmBound`.
- **the function-field seam** — `IntermediateField.relfinrank`/`adjoin`/`map`,
  `Module.finrank`, `Transcendental`, `IsIntegral`, `CyclotomicField`,
  mathlib's resultant API (for `nonempty_..._of_squarefree`).

Nothing in the cone touches a scheme, `KaehlerDifferential`, `CurveModel`,
`ModularForm.sturm_bound`, or the Hecke algebra's finiteness. Import lists can
stay inside the modules the existing port already imports.

## 4. Deduplication, scaffolding, and the budget

### 4.1 The three-way degree/roof prelude — already written once

`relfinrank_qExpand_full`, `heckeRoof_adjoin_range_union_eq_top` and
`finrankAlong_towerSubstBar_comp_heckeAlphaBar` each inline the same private
block: `TS` + its coefficient lemmas, `qTwist_TS`, `qExpand_TS`, `iota_jqN`,
`iota_jq`, `conj_{zero,succ}_eq`, `qTwistEquiv`, `phiProd_conj_eq`,
`roots_phiProd_conj_{,_nodup}`, `cycUnit`, `roots_prime_at_slot{,_nodup,_roots_nodup}`,
`isRoot_prime_at_slot_iff`, `phiAtSeed` + its six structural lemmas. The Φ_p
effort already ported every one of these:

| already ported | where |
|---|---|
| `TS`, `TS_coeff_*`, `TS_ne_zero`, `TS_injective`, `qTwist_TS`, `qExpand_TS`, `iota_jqN`, `qTwist_TS_one_cycle`, `qExpand_qTwist_TS` | `Defs/TS.lean` |
| `iota_jq`, `conj_{zero,succ}_eq`, `phiProd_conj_eq`, `roots_phiProd_conj{,_nodup}`, `phiAtSeed*` | `Defs/PhiAtSlot.lean` |
| `prod_form_ne_zero`, `roots_prime_at_slot{,_nodup,_roots_nodup}`, `isRoot_prime_at_slot_iff` | `PhiSlotRoots.lean` |
| `exists_isPrimitiveRoot_cyclotomicField`, `cycUnit`, `isPrimitiveRoot_pow_div` | `Defs/Cyclotomic.lean` |
| `qTwist_iota_of_pow_eq_one`, `qTwistEquiv` | `Defs/Twist.lean` |
| `coeffMap_qExpand`, `coeffEmb_qExpand`, `coeffMap_TS` | `Defs/Laurent.lean`, `Defs/TS.lean` |

Measured: the prelude is ≈370 raw lines per file in three files. **The port
writes none of it.** The degree/roof topics are the port's assembly layer; their
work orders must `grep -c` the ported names and record the saving.

### 4.2 The modular-unit `q`-expansion prelude — a 4-way copy

`S_ModularCurve_hasSum_{,smul_}modularUnitSeries{_inv,}_qParam.lean`
(258/263/321/325 raw) share lines 28–192 **byte-identically**: `ratNRH`, `theta`,
`gfun`, `differentiableOn_gfun`, `gfun_ne_zero`,
`discriminant_eq_qParam_mul_gfun`, `hasSum_single_mul_coe_iff`,
`hasSum_theta_deltaSeries`, `qParam_heckeDiagMatrix_smul`,
`hasSum_theta_deltaSeriesN`, `theta_deltaSeriesN_ne_zero`,
`phiFun`/`psiFun` + differentiability, `taylorCoeff`, `hasSum_taylorCoeff`,
`hasSum_modularUnit`. Diff counts between pairs (`diff | grep -c '^[<>]'`):
87, 69, 108. The port writes the prelude **once** and keeps the two generic heads
(`hasSum_modularUnit`, `hasSum_modularUnitInv`) public; the four headline
statements become short derivations.

### 4.2b The Fricke/inclusion prelude — a 651-content-line 3-way copy

This is the effort's largest redundancy. The three M8 files

```
S_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant      (870 raw, 656 content)
S_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant          (870 raw, 656 content)
S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant   (1155 raw, 913 content)
```

share the block at lines 50–861 / 50–861 / 53–863: `interpPoly`, `conjPoly` and
their permutation/evaluation lemmas, `slotH`, `liftPerm`, `coeffMap_{qTwist,conj}`,
`zeta_*`, `qTwist_slotH`, `qTwist_conj`, `interpK`, `conjK`,
`exists_{interpK,conjK}_coeff_eq`, the `RealL` block, `realL_{one_of_realL_qExpand,
qExpand_of_realL_one}`, `expRoot`, `realL_twist`, `jt`/`jtN`, `cosetRep`,
`slotF`/`slotJ`, `realL_{fC,gC,slotH,jqC,conj}`, `interpFun`/`conjFun`,
`jtN_smul`, `slots_smul`, `{interpFun,conjFun}_smul`,
`mem_adjoin_of_{interpK,conjK}_coeff_eq`, `iota` + its lemmas, `dHat`,
`exists_sum_eq_mul_dHat`, `mem_modularFunctionField_of_data`,
`isIntegral_of_data`, `sigma`, `sigma_zeta`, `mem_modularFunctionField`,
`isIntegral_adjoin_jq`.

**The first two files differ by 12 lines, all `p2m_*` namespace strings plus the
final `solution`**; the third's prelude differs from the first's by **2 lines**.
The block is **651 content lines**, repeated three times: **≈1,302 content lines
never written**. The port writes it once in a shared module.

Two pieces are already ported and must be imported, not rewritten: the `RealL`
block (lines 262–417 of the pin) is `ModularForms/Hauptmodul.lean:230–`'s
`RealL` + its closure (the level-one effort promoted it for exactly this reason),
and `iota_jqN`/`qExpand_qTwist_TS` are in `Defs/TS.lean`/`Defs/Twist.lean`.

The third file's genuinely new content is `natDegree_interpPoly_lt`,
`realL_jtN_S`, `realL_sum_qExpand_mul_jq_pow`, `coeffMap_castC_injective`,
`embW`(+`_apply`,`_of_mem_adjoin`) and the 137-content `fricke_transport` — plus
`coe_frickeInvolutionFull_modularUnitSeries` (10). So M8's deduplicated content is
≈ 651 (prelude, once) + 137 + ≈50 = **≈840**, against the measured 2,307.

### 4.2c The `RatFunc` cusp model — a 160-content-line 2-way copy, and m8's fold

`S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar.lean` (236 raw, 163 content)
and `S_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime.lean` (275 raw, 200
content) share their first **160 content lines** exactly (`difflib`:
`SequenceMatcher` finds one matching block `a[0:160] ↔ b[0:160]`, nothing else).
The block is the `RatFunc 𝕂` model of `modularFunctionFieldBar ℓ`: `prime'`,
`dedekindPsi_prime`, `jb`, `coe_jb`, `bar_eq_restrictScalars`, `σa`, `coe_σa_X`,
`mem_bar_iff`, `jTr`, `coe_jTr`, `φ`, the `φ_*` compatibility lemmas,
`algRatFunc`, `isScalarTower_ratFunc`, `he_compat`, `finite_ratFunc`,
`finrank_le`, `isSeparable_ratFunc`, `restrict_eq_of_isCusp`, `e_infty`,
`e_zero`, `eq_cuspInftyBar_or_eq_cuspZeroBar`, `le_finrank`, `finrank_tower_eq`.

**Consequence for the cut:** the covered node
`finrank_adjoin_jqNModC_eq_of_prime` (200 content) is essentially the shared 160
plus a ~40-line tail. It is not a topic; it is the last section of **m5**. m5
writes the model once and both the dichotomy and the prime degree fall out.
`finrank_adjoin_jqNModC_eq_of_prime` does **not** feed m9 (the roof and the
diagonal degree use `relfinrank_qExpand_full`/`relfinrank_laurentBaseChange`,
not the `RatFunc` degree), so folding it into m5 costs SET-M3 nothing.

### 4.3 Scaffolding never written

Of the 10,569 raw `S_` lines, 2,990 (28%) are imports, `attribute` walls,
namespace/`section`/`variable` lines, `p2m_*` lines, comments and blanks (§9.1's
`raw − content`). None is ported. The `attribute [-simp]`/`[-instance]` walls are
disable-noise inherited from FLT's shared prelude.

### 4.4 The budget

| correction | content lines |
|---|---|
| 82-node structural sum | 7,579 |
| Fricke/inclusion prelude already written once (3 copies → 1, and the ported `RealL` block imported) | −≈1,302 |
| degree/roof prelude already ported (3 copies) | −≈900 |
| `RatFunc` cusp model (m5/m8, 2 copies → 1) | −160 |
| modular-unit prelude (4 copies → 1) | −≈120 |
| one-liners over the ported Φ_p effort (M5) | −≈200 |
| `hasPrincipalDivisors_*` as AC corollaries (M11) | −≈30 |
| **deduplicated theorem content** | **≈4,870** |
| 13 definition modules, raw (≈45% off-cone) | +≈950 |
| **structural total** | **≈5,800** |

At the AC effort's measured adaptation ratios (module lines ÷ content ≈ 1.0–1.3),
the port is **≈6k–7.6k written lines** — comparable to AC, with the analytic core
(M7–M9, now ≈3.7k dedup content) the least predictable piece. As in AC, the
budget unit is the **named shape risk**, not the line count (§8).

## 5. The topics

The cut is by mathematical object, one shared development per topic.
Prerequisites are real dependencies, not the pin's section order.

| topic | object | group | nodes | dedup content | ≈ port | prereq |
|---|---|---|---|---|---|---|
| **m1** | the Hecke correspondence vocabulary | M1 | defs | — | 500–650 | AC, ported FFG/Φ vocab |
| **m2** | geometric base change, cusps, `q`-adic place, modular unit | M3 | defs | — | 700–900 | m1, AC |
| **m3** | the modular-unit `q`-expansion core | M7 | 9 | 1,282 | 1,300–1,600 | m2 |
| **m4** | Fricke invariance and the field inclusion | M8 | 8 | ≈1,000 (2,307 raw group; §4.2b) | 1,000–1,300 | m3 |
| **m5** | the `RatFunc` cusp model, the cusp dichotomy, the Fricke automorphisms, and the prime degree | M9 (+ the M5 node `finrank_adjoin_jqNModC_eq_of_prime`) | 18 | 650 + 40 (m8 is a 40-line tail of m5's 160-line model, §4.2c) | 500–700 | m4, m6 |
| **m6** | the Φ datum family | M5 | 14 | 950 | 550–750 | m3 |
| **m7** | Laurent glue and the relative degree | M4 | 10 | 1,040 (2 nodes delivered early by m1) | 700–950 | m6 |
| **m9** | the roof generation and the diagonal degree | M6 | 2 | 859 | 550–750 | m7 |
| **m10** | tower integrality and finiteness | M10 | 13 | 301 | 350–450 | m6 |
| **m11** | principal divisors | M11 | 2 | 38 | 40–70 | m6, m7, AC |
| **m12** | the exchange reduction | M2 | 4 | 68 | 200–280 | m1, m9, m10 |
| **capstone** | `heckeExchangeAt_of_WEX` + `heckeOperatorsCommuteBar` | — | 1 | 63 | 130–180 | all; **human** |

The set boundaries are the manager's and are finalized after each review. The
planned sets, in dependency order, are:

- **SET-M1 = m1–m3** — the vocabulary plus the analytic core's first layer.
- **SET-M2 = m4, m6, m5** — the Fricke/inclusion core (m4), the Φ datum family
  (m6), then the cusp dichotomy, the Fricke automorphisms, the cusp bookkeeping
  and the prime degree (m5). The order matters:
  `eq_cuspInftyBar_or_eq_cuspZeroBar` and `modularFunctionFieldBar_eq_restrictScalars`
  (m5) consume `nonempty_modularPolynomialData_of_squarefree`,
  `finrank_adjoin_jqNModC_le` and `transcendental_jqModC` (m6).
- **SET-M3 = m7, m9** — the Laurent glue and the relative degree, then the roof
  generation and the diagonal degree.
- **SET-M4 = m10–m12** — tower integrality/finiteness, principal divisors, the
  exchange reduction.
- **capstone** — `heckeExchangeAt_of_WEX` + `heckeOperatorsCommuteBar`, by the
  human reviewer.

The order files: [SET-M1](hecke/SET-M1.md) (m1–m3, dispatched),
[SET-M2](hecke/SET-M2.md) (m4, m6, m5), [SET-M3](hecke/SET-M3.md) (m7, m9),
[SET-M4](hecke/SET-M4.md) (m10–m12), and
[TOPIC-m13-capstone.md](hecke/TOPIC-m13-capstone.md) (reserved). Each set's
orders are finalized against the modules that actually exist after the previous
review.

## 6. Module layout

One directory per theory, shared vocabulary in `Defs/`, per playbook §8.

```text
lean/FLTForHuman/ModularCurve/
  Defs/
    HeckeOperator.lean        -- m1: heckeAlphaBar/heckeBetaBar, integrality predicates,
                              --     heckeDivBar, heckePic0Bar, the transpose
    DegeneracyTower.lean      -- m1: towerInclBar, towerSubstBar, the square, HeckeExchangeAt
    HeckeTotal.lean           -- m1: HeckeInputsAlong, heckeOperatorAlong
    HeckeModule.lean          -- m1: heckeOperatorBar, HeckeOperatorsCommuteBar
                              --     (+ the HeckeAlg payoff, optional)
    ArithmeticGalois.lean     -- m1: modularFunctionFieldBar, JZero (the `bar` layer)
    GeometricBaseChange.lean  -- m2: baseChangeEquiv, geomAut
    QAdicPlace.lean           -- m2: qSeriesBar, qIntegersBar, qInftyPlaceBar, IsCusp
    CuspidalClass.lean        -- m2: frickeInvolutionBar, cuspZeroBar, cuspidalDivisor/Class
    AtkinLehner.lean          -- m2: IsFrickeAut(Full), frickeInvolution(Full),
                              --     order_coeffEmb_jq, cuspInftyBar
    ModularUnit.lean          -- m2: IsMonicOfOrder, deltaSeries(N), modularUnitSeries
    JqCoeff.lean              -- m2: jqModC/jqNModC, modularFunctionFieldC
  Analytic/
    QParamUnique.lean         -- m3: qParam_coeff_unique, laurent_qParam_coeff_unique
    ModularUnitQExpansion.lean-- m3: the shared prelude + the four hasSum heads
    Gamma0Cosets.lean         -- m3: exists_perm_gamma0_cosetReps,
                              --     exists_sl2_heckeDiagMatrix_smul_eq, discriminant_div_...
    FrickeInvariance.lean     -- m4: the three `of_hasSum_of_gamma0_invariant` heads,
                              --     isIntegral_adjoin_jq_modularUnitSeries, mem_modularFunctionField
    CuspDichotomy.lean        -- m5: eq_cuspInftyBar_or_eq_cuspZeroBar,
                              --     modularFunctionFieldBar_eq_restrictScalars
    FrickeAut.lean            -- m5: exists_isFrickeAut_of_modularPolynomialData, ...Full
    CuspBookkeeping.lean      -- m5: ord_cuspInftyBar/cuspZeroBar, isCusp_*
  Degree/
    PhiData.lean              -- m6: modularPolynomialFamily, of_squarefree, eval_jqNModC_*,
                              --     isIntegral_jqNModC_*, isIntegral_jqN
    PhiDegree.lean            -- m6/m8: transcendental_jqModC, finiteDimensional/finrank_adjoin_jqNModC*
    LaurentGlue.lean          -- m7: laurentBaseChange_*, coeffEmb_jq(N), order_*,
                              --     transcendental_jqN
    Relfinrank.lean           -- m7: relfinrank_laurentBaseChange, relfinrank_qExpand_full
    Roof.lean                 -- m9: heckeRoof_adjoin_range_union_eq_top,
                              --     finrankAlong_towerSubstBar_comp_heckeAlphaBar
  HeckeInputs/
    Integrality.lean          -- m10: tower*_isIntegral/finiteAlong, hecke*BarIntegral,
                              --      finiteAlong_hecke*
  PrincipalDivisors/
    ModularCurveBar.lean      -- m11: hasPrincipalDivisors_modularFunctionFieldBar(+Full)
  HeckeExchange/
    Reduction.lean            -- m12: heckeDivBar_heckeDivBar/comm, heckeOperatorBar_comm,
                              --      heckeOperatorsCommuteBar_of_heckeExchangeAt
lean/FLTForHuman/ModularCurve/HeckeCommuteBar.lean  -- the human's: heckeExchangeAt_of_WEX +
                                                    -- heckeOperatorsCommuteBar
lean/spec/ModularCurveHeckeConsumer.lean     -- the consumer; zones added per set
```

Directory and namespace differ on purpose, as everywhere else in the port: the
path is `...ModularCurve.Analytic.FrickeInvariance`, the declarations are
`ModularCurve.*`.

### 6.1 What is deliberately not cut

- **The out-of-cone API of the definition modules** — `eisensteinNumerator`, the
  Galois `≃ₐ`-action on `Pic0`, `JZero.torsionGaloisRep`, `cuspidalClass`,
  `heckeDivBarTranspose`/`heckePic0BarTranspose`, `cuspZero`(Full). Each is
  ported (or explicitly deferred) with a count, as AC's §6.1 did; they are the
  modular Hecke/Galois-rep and Riemann–Roch layers' API.
- **The pin's analytic argument structure.** The eta-product/Taylor route is
  transcribed as written where mathlib has no replacement; §3.4's route audit
  precedes any restatement.
- **Repo-wide prelude dedup.** The port writes the `TS`/slot and modular-unit
  preludes once *for its own cone*; deduplicating the whole FLT tree is separate.

## 7. Verification

The instruments are those FFG and AC built; nothing new is required.

### 7.1 The statement checker

`spec/check_flt_statements.py` currently reports **802 identical (53 promoted), 0
mismatched, 0 missing**. Each topic appends its `Theorems/Thm_ModularCurve_*.lean`
wrappers to `SOURCES` and each new module to `PORT_FILES`. Definition
declarations (m1/m2) have no wrappers and verify by name against their
`Definitions/Def_ModularCurve_*.lean` files, which are appended to `SOURCES`. The
existing conventions carry over:

- statements come from the `Theorems/` wrappers, binders included;
- the checker keys by last name and first occurrence wins, so a module whose
  declarations share a last name with the port's must be ordered deliberately;
- the pin's dot-notation statements (`ModularPolynomialData.eval_jqNModC_*`,
  `ModularPolynomialData.isIntegral_jqN`) are matched by the dotted fallback;
- anything the port *authors* rather than transcribes goes on the reasoned
  `OWN_PROOFS` list — this effort's list should stay short (the one-liners are
  still transcriptions of the pin's statement, just short proofs);
- **the wrappers for a `_of_prime` node and its `_of_modularPolynomialData`
  general form must both be listed**, since the checker compares statements, not
  proofs.

### 7.2 The consumer

`spec/ModularCurveHeckeConsumer.lean`, outside every library, error count as the
deliverable. Zones (added per set):

- **Zone A `[vocab]`** — m1/m2: `JZero`/`heckeOperatorBar` inhabited, the
  `heckeAlphaBar = towerInclBar` and `heckeBetaBar = towerSubstBar` `rfl`s,
  `HeckeExchangeAt` stated, `modularUnitSeries`/`qInftyPlaceBar` checked against
  the pin signatures.
- **Zone B `[analytic]`** — m3/m4: the four `hasSum` heads at `N = 2`, and
  `mem_modularFunctionField_of_hasSum_of_gamma0_invariant` instantiated.
- **Zone C `[degree]`** — m6–m8: `relfinrank_qExpand_full` at `ℓ = 2`, `N = 1`.
- **Zone D `[roof]`** — m9: `heckeRoof_adjoin_range_union_eq_top` on the concrete
  `N = 1` square.
- **Zone E `[inputs]`** — m10/m11: `HeckeInputsAlong` discharged for `N = 1`,
  `hasPrincipalDivisors_modularFunctionFieldBar` applied.
- **Zone F `[reduction]`** — m12: the three reductions composed, and
  `heckeOperatorsCommuteBar` in the capstone (the human's zone).
- **Zone G `[payoff]`** — the `HeckeAlg`-module structure, if m1 includes it.

### 7.3 Axioms, build discipline, definition of done

`#print axioms` on each topic's headlines must return only
`[propext, Classical.choice, Quot.sound]`. Every build runs under
`timeout 60 lake env lean <file>` / `timeout 90 lake build <module>` /
`timeout 180 lake build`, and **expects ≤ 30 s**: any build past ~60 s is a
blow-up to bisect, never a reason to raise `maxHeartbeats` or to wait (a
multi-minute build is never acceptable, even while experimenting). Tell a real
blow-up from lock contention by CPU time (`time`/`/usr/bin/time -v`: high user
CPU + timeout ⇒ bisect; ~0 CPU ⇒ re-run when idle, never build concurrently with
another agent). The lakefile sets 4,000,000 globally. Keep imports specific;
`Scratch*.lean` (gitignored) carries probes.

Definition of done (per topic): modules as named; statements verbatim from the
wrappers; `lake build` green with 0 warnings and no `sorry`/`admit`; `#print
axioms` clean; checker 0 mismatched / 0 missing; dedup demonstrated with
`grep -c`; `logs/mc-port.md` section; `README.md` rows.

## 8. Risks, in the order they will bite

1. **The Fricke/inclusion core (m4) is the one genuinely new analysis.** The
   three 656–913-line statements have no mathlib analogue; the level-one
   `Hauptmodul.lean` is the route template, but `Γ₀(N)`-invariance and the
   Fricke twist are new. Scout `mem_modularFunctionField_of_hasSum_of_gamma0_invariant`
   first, in `Scratch.lean`, before pricing m4.
2. **`nonempty_modularPolynomialData_of_squarefree`'s biresultant argument.** The
   pin's 363 content lines build the squarefree indicator, the fibre polynomial,
   the composite fibre, and a biresultant; mathlib's `Polynomial.resultant` API is
   the seam. Scout the coefficient comparison (`coeff_biResultant_*`) first.
3. **The `qParam`-uniqueness engine's analytic shape.** `qParam_coeff_unique`
   (121 content) is stated over `UpperHalfPlane → ℂ` with `HasSum` hypotheses; the
   port's `QExpansionPrinciple.lean` note records that mathlib's replacement for
   the pin's `coeff_unique` blew up on the bare function type, so the shape
   decision (bare `F : ℍ → ℂ` vs `ModularForm`) is the topic's route risk.
4. **Instance/defeq traps in the vocabulary.** `towerSubstBar` is
   `towerInclBar ∘ heckeBetaBar` by definition; `heckeBetaBar_eq_towerSubstBar`
   is a `Subtype.ext` rewrite, not `rfl`. Keep `heckeAlphaBar_eq_towerInclBar`
   and `heckeSquareBar_commutes` as the pin states them (`rfl`-level in FLT) and
   record any defeq adaptation.
5. **`geomAut`/`baseChangeEquiv` (m2).** The pin's `GeometricBaseChange` builds
   the tensor-product model `L ⊗[ℚ] F₀ ≃ₐ[L] laurentBaseChange L F₀`; the port
   has only `laurentBaseChange`. This is the AC0-style one-time shape decision of
   the effort — changing it later would redo `frickeInvolutionBar`.
6. **The degree/roof files' real content.** Once the prelude is imported, the
   remaining proof is the slot product and the `relfinrank` multiplicativity;
   verify by `grep -c` that none of the private prelude survives, then re-price.
7. **The `HeckeAlg` payoff is out of cone.** `heckeModuleBar`/`heckeEvalBar` need
   `HeckeAlg`/`heckeGen` from `Def_HeckeGalois_EichlerShimura`, which drags a
   large import cone. Keep it an optional tail; never let it block the target.
8. **The `_of_prime`/`_of_modularPolynomialData` duplication.** Several
   statements are stated twice (a general datum form and a prime form). Port both
   statements; prove the prime form from the general one where the pin does.

## 9. Reproduction recipes

### 9.1 Regenerate the remaining cone and the group totals

```bash
cd tools/deps && python3 - <<'PY'
import sys, re
from pathlib import Path
sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); FLT = Path.home() / 'proj' / 'fermats-last-theorem'
LEAN = Path('../../lean')
def closure(i):
    seen, stack = set(), [i]
    while stack:
        j = stack.pop()
        if j in seen: continue
        seen.add(j); stack.extend(d.cites(j))
    return seen
cl = closure(d.index['ModularCurve.heckeOperatorsCommuteBar'])
sc = re.compile(r'^\s*(import |attribute |namespace |end\b|open |p2m_open|p2m_export|p2m_alias|p2m_reactivate|section\b|variable\b|#|/-|--|\s*$)')
def raw(i):  return sum(1 for _ in open(FLT / f"P2M/Sol/S_{d.stem_of[i]}.lean", encoding='utf-8'))
def cont(i): return sum(1 for l in open(FLT / f"P2M/Sol/S_{d.stem_of[i]}.lean", encoding='utf-8') if not sc.match(l))
port = "\n".join(p.read_text(encoding='utf-8') for p in (LEAN / 'FLTForHuman').rglob('*.lean'))
src = re.search(r'SOURCES = \[(.*?)\n\]', (LEAN / 'spec/check_flt_statements.py').read_text(), re.S).group(1)
srcs = set(re.findall(r'"([^"]+)"', src))
def ported(q):
    if any(s.endswith('Thm_' + q.replace('.', '_') + '.lean') for s in srcs): return True
    return re.search(r'(?<![\w.])' + re.escape(q.rsplit('.', 1)[-1]) + r'(?![\w])', port) is not None
rem = [n for n in cl
       if not d.qual(n).startswith(('AlgebraicCurve.', 'Polynomial.'))
       and d.qual(n) not in ('MulAction.ncard_orbit_inter_orbit_mul_card', 'Subgroup.exists_eq_mul_of_index_inf_eq')
       and not ported(d.qual(n))]
print(f"closure {len(cl)} nodes; remaining {len(rem)} nodes, "
      f"{sum(raw(n) for n in rem)} raw, {sum(cont(n) for n in rem)} content")
PY
```

### 9.2 The definition-module need and the modular-unit duplication

```bash
cd ~/proj/fermats-last-theorem/Definitions && wc -l \
  Def_ModularCurve_{HeckeOperator,DegeneracyTower,HeckeOperatorTotal,HeckeModule,HeckeInputsAll,ArithmeticGalois,GeometricBaseChange,QAdicPlace,CuspidalClass,AtkinLehner,ModularUnit,JqCoeff}.lean
cd ../P2M/Sol
diff S_ModularCurve_hasSum_modularUnitSeries_qParam.lean \
     S_ModularCurve_hasSum_modularUnitSeries_inv_qParam.lean | grep -c '^[<>]'   # 87
```

### 9.3 The outbound interface tier

```bash
cd tools/deps && python3 - <<'PY'
import sys
sys.path.insert(0, '.')
from fltdata import FltData
d = FltData()
i = d.index['ModularCurve.heckeOperatorsCommuteBar']
def closure(i):
    seen, stack = set(), [i]
    while stack:
        j = stack.pop()
        if j in seen: continue
        seen.add(j); stack.extend(d.cites(j))
    return seen
cl = closure(i)
rows = [(sum(1 for j in d.cited_by[n] if j not in cl), d.qual(n)) for n in cl]
for ext, q in sorted(rows, reverse=True)[:12]:
    print(f"{ext:5d}  {q}")
PY
```

## 10. Open questions

- **How much of `Def_ModularCurve_HeckeModule` is in scope?** The cone needs only
  `heckeOperatorBar`/`HeckeOperatorsCommuteBar`. The `HeckeAlg` module structure
  (`heckeEvalBar`/`heckeModuleBar`) is the theorem's *payoff* (math/009 §7) but
  imports `Def_HeckeGalois_EichlerShimura`. Answered by m1: port the operator
  block first, leave the payoff an optional tail with a count.
- **Does the port need `AtkinLehner`'s `cuspZero`/`cuspZeroFull` at the rational
  level?** The cone uses only the `bar` forms (`cuspZeroBar`, `cuspInftyBar`,
  `frickeInvolutionBar`). The rational `cuspZero` is other consumers' API;
  port-or-defer is a per-declaration count in m2.
- **Is `nonempty_modularPolynomialData_of_squarefree` reachable from the ported
  Φ_p API, or does the biresultant argument need its own module?** m6's scout
  answers it; the pin's private `fibrePoly`/`resLift*` block is ~300 lines and
  may be irreducible.
- **Does `full_eq_of_prime` follow from the ported `gen_prime` by definitional
  unfolding alone?** The pin proves it by `FunctionFieldGeneration` unfolding;
  verify with `rfl`/`exact` before writing any proof.

## 11. Links

- [studies/hecke-commute-bar-coverage.md](../../studies/hecke-commute-bar-coverage.md) §4 — the measured slice table this blueprint refines.
- [studies/hecke-commute-bar-survey.md](../../studies/hecke-commute-bar-survey.md) §3–§8 — the mathematics.
- [PORTING-AC.md](PORTING-AC.md) §7 — the verification discipline inherited wholesale.
- [ac-retrospective.md](ac-retrospective.md) §6 — why sets are split on the fork, and why the capstone is a review instrument.
- [`Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean#L9) — the target statement.
- [`Definitions/Def_ModularCurve_DegeneracyTower.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean#L121) — `HeckeExchangeAt`.
- [`Definitions/Def_ModularCurve_HeckeOperator.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean#L136) — `heckeDivBar`/`heckePic0Bar`.
