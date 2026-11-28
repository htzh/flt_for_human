# SET-AF112 — the Whittaker summability story, the finite-adèle Fourier inversion, and two small consumers

**Status: landed (2026-11-27).** The next set of the AF column in the D–S cone, scoped
per [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. SET-AF111 left a ready shelf of **13 rows / 6,132 silo**; this set cuts **nine of
them, 4,797 silo**, in five orders: five new modules and two insertion sites.

| # | order | rows | silo | module(s) |
|---|---|---:|---:|---|
| A | Whittaker summability for archimedean-smooth vectors | 2 | 2,141 | `AutomorphicForm/Adelic/WhittakerSmoothSummability.lean` (new) |
| B | Whittaker summability of the Bruhat–Eisenstein series | 1 | 1,038 | `AutomorphicForm/Adelic/BruhatEisensteinWhittakerSummability.lean` (new), + 15 promotions |
| C | Fourier inversion on the finite adèles | 3 | 711 | `NumberTheory/AdelicFourier/FourierInversion.lean` (new), insertion into `…/PoissonNormalized.lean` |
| D | The local components of a global additive character | 1 | 440 | `AutomorphicForm/Adelic/AddCharLocalComponents.lean` (new) |
| E | The free-algebra lift of the differential correspondence, and the Tate point equation | 2 | 467 | `AlgebraicCurve/Differential/FreeAlgebraLift.lean` (new), insertion into `TateCurve/SeriesIdentities.lean` |
| **total** | | **9** | **4,797** | 5 new + 2 insertions + 15 promotions |

§0 the read; §1 the stories; §2 the scaffolds; §3 homes; §4 ground prep (the promotions); §5 what is
**not** cut, and why; §6 traps; §7 gates; §8 reproduce and the forecast; §9 what this set does not do.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf11.json
python3 frontier.py --selfcheck
```

The corrected read (the 20-name unport list of `lean/tmp/af108/unport_final.txt`, AF109's) is
**identical** on this shelf — none of the false ported markers touches an AF node — so there is one
set of figures, not two:

| figure | value |
|---|---:|
| `needed [F terminal]` | **214 / 136,028** |
| frontier (union) | 2,221 / 995,797 |
| ready rows, all namespaces | **13 / 6,132** |
| leaves, all namespaces | **5 / 13,761** |
| withheld by the FR-0044 guard | 6 / 1,970 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

**`--selfcheck` is INCONSISTENT**, with eight `source node not covered by the name scan` lines: the
live **MD-005** phi-family inventory (`ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq`,
`ModularCurve.{exists_phiIrreducible, exists_phiIrreducible_of_finrank_eq, phiIrreducible_all,
phiIrreducible_of_prime, isInftySide_cuspInftyBar}`) plus **MD-007**
(`ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0`) and
`WeierstrassCurve.Affine.ncard_fibSet`. No AF shelf row is affected; the phi family *is* the deferral
of §5.

**The AF ready shelf, quoted whole** (rank by silo; `prem` = graph premises, `lev` = leverage
cone/project):

| row (`AutomorphicForm.`/`NumberField.` prefix dropped where noted) | silo | prem | lev | what it is |
|---|---:|---:|---:|---|
| `WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j` | 1,133 | 20 | 1 / 5 | `j` of every cyclic quotient is a root of the modular polynomial |
| `AutomorphicForm.summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace` | 1,071 | 3 | 1 / 4 | the Whittaker coefficients are absolutely summable |
| `AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace` | 1,070 | 3 | 4 / 14 | … and individually integrable (same engine) |
| `AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary` | 1,038 | 5 | 1 / 1 | the same for the Bruhat–Eisenstein series |
| `AlgebraicCurve.Pic0.freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero` | 444 | 6 | 1 / 4 | a vanishing `Pic0` lift kills every regular differential |
| `AutomorphicForm.exists_localComponents_of_isGlobalAddChar` | 440 | 5 | 6 / 26 | a global character is a finite product of local ones |
| `NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq` | 394 | 6 | 1 / 1 | Fourier inversion on the finite adèles |
| `NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing` | 260 | 3 | 1 / 2 | its Schwartz-space property |
| `TateCurve.lineCoeff_eq_zero` | 142 | 3 | 1 / 1 | **not statable** (§5) |
| `NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet` | 57 | 1 | 1 / 1 | Poisson summation at an arbitrary Haar measure |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 2 | 1 / 3 | **false ready** (§5) |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1 | 1 / 6 | **def-layer gate** (§5) |
| `TateCurve.equation_pointX_pointY_of_defectCoeff_eq_zero` | 23 | 4 | 1 / 6 | the point lies on the curve when the defect vanishes |

**The leaves, quoted whole** (all five are definition-layer gates, none is cut):

| leaf | silo | its gate |
|---|---:|---|
| `M4aTorus.completedRayL_fe` | 12,126 | `Def_NumberField_CompletedRayL` (4), `_RayCharacterData` (10), `_EuclideanIdealLattice` (2), `_FrobeniusDensity_ClassGroupLSeries` (5), `Def_NarrowRayClassGroup` (63 absent of 67) |
| `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` | 684 | `Def_NumberField_CompletedRayL` (4), `_RayCharacterData` (10) |
| `TateCurve.point_mul_eq_add_of_norm_le_one` | 471 | `Def_TateCurve_TorsionParametrization` (42 of 43 absent) |
| `TateCurve.point_mul_eq_add_of_norm_eq_one` | 247 | same |
| `NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one` | 233 | `Def_LanglandsTunnell_NormClass` (9 absent) |

**The withheld block** (the FR-0044 guard: a proof that cites the pruned complex-analytic set) is six
rows / 1,970 — `ModularCurve.exists_bijective_heckeEquivariant…` (817), `moduleFinite_and_free_padicInt_`
`tateModule_jH` (327), **`Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero`
(322, the converse of order E's row)**, `moduleFinite_padicInt_tateModule_jOne` (283),
`Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` (126), `Pic0.finite_torsion_of_isAlgClosed_`
`of_charZero` (95). They are the prunable subject's work; order E ports only the direction whose proof
avoids it.

**The premise audit was run before the cut** (FR-0338): `lean/tmp/af112/premcheck.py` over all 13 rows
reads **5 problems** — one `MISSING` (`ModularPolynomialData.dvd_resultant_of_mul`, §5) and four
`SHADOW`. Three of the shadows are one premise, `norm_apply_eq_one_of_isGlobalAddChar`, whose port copy
in `NumberTheory/NumberField/GlobalAddChar/Circle.lean` is the pin's statement up to the notation
`𝔸` for `AdeleRing (𝓞 F) F` (its own `check_port` reads `6 ok / 0 mismatch`, so the shadow is the
premcheck normaliser, not the tree); the fourth is `exists_basis_gamma1_qCoeff_mem_range_ratCast`, the
known false-ready of §5. Every premise of the nine cut rows is `ported` otherwise.

## 1. The stories

### A — Whittaker summability for archimedean-smooth vectors (2,141)

`summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace` and
`whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace`: for a left-invariant,
`Kf`-smooth `φ` that is `ContDiff` of order `finrank ℚ K + 1` on the mixed space, the Whittaker
coefficients are summable (row 1) and integrable (row 2) in the coefficient index `α : K` at every `g`.
This is the archimedean half of the Whittaker theory: the pin's engine is the mixed-space dictionary
plus repeated integration by parts (forward differences) and the support/decay description of the
coefficient, ending in `summable_of_support_of_decay`.

**The two pins are one text**: their 1,071 and 1,070 `S_` lines differ only in the last ~15 lines (the
headline statements and their two-line proofs) — the other **75 declarations are byte-identical**
(`port_advise` §2 reports 74 shared names, ≈997 removable lines). So the order writes the engine
**once**, public at the pin's declaration names (the precedent is
`AutomorphicForm/Adelic/WhittakerTorusDecay.lean`), and both headlines sit on top.

### B — Whittaker summability of the Bruhat–Eisenstein series (1,038)

`summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary`: for `Re s > 1`, a unitary
pair `μ, ν` and an induced section `φ`, the Whittaker coefficients of
`E g = φ g + ∑' ξ, φ (w * u(ξ) * g)` are summable. The proof is the unfolding engine (`bruhatSeries`,
`jacquetIntegrand`, the coefficient identity) closed by **SET-AF111A's polynomial decay** of the
Weyl-unipotent integral and AF110's level splitting.

This is the shelf's cheapest large row, because the engine is already in the port **privately**:
`port_advise`'s *drags* block lists 53 helpers, of which **10 are public** already and **15 exist only
as `private` declarations** in three modules. Those 15 are promoted by the manager (§4); the order adds
the 31 genuinely new declarations (≈450 lines), 12 of them the pin's conjugation/`finAdele`/`infAdele`
dictionary.

### C — Fourier inversion on the finite adèles (711)

Two new rows and one insertion, one subject — the additive Fourier transform on
`FiniteAdeleRing (𝓞 F) F`:

* `fourierIntegral_fourierIntegral_finiteAdeleRing_eq` (394, 20 flat public declarations): the transform
  inverts on locally constant compactly supported functions, up to
  `|N (differentIdeal ℤ (𝓞 F))| · ν (integralFiniteAdeles)²` and `y ↦ -y`;
* `isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing` (260, 11): the transform
  preserves that Schwartz space;
* `tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet` (57, 1): the pure-tensor Poisson
  summation at an **arbitrary** Haar measure, with the factor `(μ (adelicBox F))⁻¹` explicit — the
  consumer of SET-AF111D's normalized row, and the insertion into `PoissonNormalized.lean` beside it.

All three are flat public surfaces: no private prelude, no engine split, pure transcription plus the
proof adaptations to the port's Fourier API.

### D — The local components of a global additive character (440)

`exists_localComponents_of_isGlobalAddChar`: every global additive character of the adèles is a finite
product of local characters, with levels `nψ` equal to the conductor exponents, a finite support, and
real/complex phases `θr`, `θc` at the infinite places. Fifteen private helpers (≈347 lines) — the
level/ball dictionary (`stdAddChar_mk_zero_eq_finprod_psiLocal`, `addCharLevel_spec`), the twisted
components, the archimedean frequencies — and one headline.

### E — The free-algebra lift, and the Tate point equation (467)

* `Pic0.freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero` (444, 32 flat public
  declarations): if the free-algebra lift of the `Pic0` correspondences vanishes, then the free-algebra
  lift of the differential correspondences kills every regular differential. It is the differential
  half of the base-change dictionary whose `Pic0` half is `Pic0/BaseChangeDescent.lean`, and it
  consumes SET-AF111C's geometric-cycle row.
* `TateCurve.equation_pointX_pointY_of_defectCoeff_eq_zero` (23, 1): vanishing defect coefficients put
  `(pointX, pointY)` on the curve — the companion of SET-AF111E's `equation_of_defectCoeff_eq_zero`,
  and the second half of the point-arithmetic layer's dictionary.

## 2. The scaffolds

Seven files are touched before any order starts: **five new** and **two insertions**. All seven
elaborate at the 200 k edit-loop cap with only their `sorry`s.

| order | module | new | scaffold `check_port` |
|---|---|---|---:|
| A | `AutomorphicForm/Adelic/WhittakerSmoothSummability.lean` | 2 | **2 ok** |
| B | `AutomorphicForm/Adelic/BruhatEisensteinWhittakerSummability.lean` | 1 | **1 ok** |
| C | `NumberTheory/AdelicFourier/FourierInversion.lean` | 2 | **2 ok** |
| C | `NumberTheory/AdelicFourier/PoissonNormalized.lean` (insert) | 1 | **2 ok** (1 before) |
| D | `AutomorphicForm/Adelic/AddCharLocalComponents.lean` | 1 | **1 ok** |
| E | `AlgebraicCurve/Differential/FreeAlgebraLift.lean` | 1 | **1 ok** |
| E | `TateCurve/SeriesIdentities.lean` (insert) | 1 | **18 ok** (17 before) |
| **total** | **7 files** | **9 rows** | **27 ok / 0 / 0 / 0 / 0** |

The scaffold headlines are the pin `Theorems/` wrapper statements verbatim, bodies `sorry`; the
scaffold files, the generator and the insertion script are `lean/tmp/af112/gen.py` and
`lean/tmp/af112/insert.py`. Each module header names its subject, its pin sources (`spec-pin:` rows)
and what it assumes from earlier modules; the measured landing tables go in when the set lands.

## 3. Homes

Each home is above every module that holds one of its premises, checked row by row against the port's
import closure; the subject decides the directory.

| row | premises' homes | why this home |
|---|---|---|
| A ×2 | `KfSmoothTensor`, `StdAddCharNormalization`, `GlobalAddChar/Circle` | `AutomorphicForm/Adelic/` is the Whittaker/mixed-space theory's directory, and no module is above all three premises plus `CarrierPins`/`WhittakerCoefficient` |
| B | `PolyDecay`, `TraceDual`, `NonzeroTrace`, `GlobalAddChar/Circle`, `WeylIntegrable/Assembly` | new, above `PolyDecay` and `EisensteinGeneral/Unfolding` (whose engine it imports) |
| C ×2 | `Transform`, `FiniteCoset`, `TraceDual`, `AdelicBox` | the Fourier directory itself; the pin's own subject is the Fourier transform of the finite adèles |
| C (57) | `PoissonNormalized` (its own premise) | inserted **beside** its premise, which is the module's subject |
| D | `StdAddCharNormalization`, `TateLocal/AddCharLevel{,Different}`, `StandardAddCharTrace`, `AdelicTraceFin` | `AutomorphicForm/Adelic/` is the additive-character theory's directory; the `LanglandsTunnell` modules are below it |
| E (444) | `Pic0/BaseChangeDescent`, `Differential/PushPull`, `ResidueTheorem/TraceSum`, `IsCurveOver/*`, `Canonical/HasCanonicalDivisor` | the differential half of the base-change dictionary; `Differential/` is where the correspondence's differential lives, and it is above every premise by import |
| E (23) | `SeriesIdentities` (its own premises' module) | inserted at the end of the module that holds the defect expansion |

## 4. Ground prep — the promotions for order B

The pin's Bruhat–Eisenstein `S_` file declares its engine `private`; the port already holds the same
names `private` in three modules. **Promoted to public by the manager** (a one-line edit each, at the
pin's names, so the row imports rather than re-proves them):

| module | promoted |
|---|---|
| `EisensteinGeneral/Unfolding.lean` | `bruhatSeries`, `jacquetIntegrand`, `integrable_jacquetIntegrand`, `integrand_eq`, `whittakerCoefficient_bruhatSeries_eq`, `whittakerCoefficient_productionPins_eq`, `integrable_tsum_of_lintegral`, `integral_eq_tsum_setIntegral_adelicBox`, `tsum_lintegral_adelicBox_translate_eq`, `integrableOn_adelicBox_translate`, `integrableOn_adelicBox_tsum_translate`, `setIntegral_adelicBox_tsum_translate_eq` (12) |
| `NumberTheory/AdelicFourier/Faithful.lean` | `valued_algebraMap_eq`, `exists_pow_subset_of_mem_nhds` (2) |
| `AutomorphicForm/Adelic/PolyDecay.lean` | `haarModulus`, `integrable_weyl_unipotent_mul` (2) |

`adelicWeyl_inv` is **not** promoted: the port already states it publicly as
`AutomorphicForm.WeylIntegrable.adelicWeyl_inv'` (a registered `pin:` rename). The three
`addChar_neg_algebraMap_mul_*` helpers and `principalEquiv` are already public in
`WhittakerSum.lean` / `BruhatEisenstein.lean`. The remaining 12 helpers
(`conjUnip`, `finAdele`, `infAdele`, `apply_mul_eq_of_mem_stabilizer`, `algebraMap_mul_finAdele`,
`algebraMap_mul_infAdele`, `continuous_conjUnip`, `conj_unipotentGL2_mem`, `conjUnip_zero`,
`continuous_finAdele`, `finAdele_zero`, `finAdele_fst`) are **absent or unimportable** and are order B's
own new work — measured on landing, `glArch_unipotentGL2` and `continuous_unipotentGL2` do exist in the
port but only `private`, and outside the module's import closure (`KfSmoothTensor.lean`,
`WhittakerSystem.lean`), so two of the twelve were transcribed rather than imported.

The promotion cost is three module rebuilds plus a `check_port` re-run on each — the checker's public
surface grows, its `ok` count with it, and no statement text moves. Measured after the edit:

| module | before | after |
|---|---:|---:|
| `EisensteinGeneral/Unfolding.lean` | 1 ok | **13 ok** |
| `NumberTheory/AdelicFourier/Faithful.lean` | 44 ok | **46 ok** |
| `AutomorphicForm/Adelic/PolyDecay.lean` | 1 ok | **3 ok** |

all three `0 mismatch / 0 missing`, and all three silent.

## 5. What is not cut, and why

* **`WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j` (1,133) —
  false ready.** One of its 20 premises, `ModularCurve.ModularPolynomialData.dvd_resultant_of_mul`
  (134 pin lines), has **no port declaration at all** (`premcheck` reads `MISSING`; `rg resultant`
  over `lean/FLTForHuman` is empty), and that premise's own premise
  `ModularCurve.phiIrreducible_all` is one of the MD-005 false ported markers. The row is the headline
  of the modular-polynomial root dictionary, so it is worth a set of its own: the deferred surface is
  `phiIrreducible_all` → `dvd_resultant_of_mul` → this row, registered in
  [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md).
* **`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36) — false ready.** Its premise
  `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` shadows (the port's copy is a different
  statement); registered in CARRY-FORWARD since SET-AF102. Not this column's work.
* **`ModularCurve.rep_tateModule_jOne_comm` (24) — definition-layer gate.**
  `Def_EllipticCurve_TateModule` is 89 declarations absent of 100 and `Def_ModularCurve_X1HeckeModule`
  14 of 42; a padic-Tate-module wave, not a row.
* **`TateCurve.lineCoeff_eq_zero` (142) — not statable.** `Def_TateCurve_QShift` (43 of 48 absent) and
  `Def_TateCurve_DefectLines` (128 of 128 absent) are a 176-declaration definition wave (this is
  SET-AF111's own finding; re-read, unchanged).
* **The five leaves** (§0 table): every one is a definition gate, the largest being
  `M4aTorus.completedRayL_fe` (12,126) whose five definition modules are almost entirely absent.
* **The withheld six** (§0): their proofs cite the pruned complex-analytic set; order E takes only the
  direction whose proof does not.

## 6. Traps for this set

1. **The Kf pair's engine is one text written twice** (74 shared names, ≈997 lines). Port it once and
   public; a second private copy is the pin's duplication, not a port decision.
2. **The two headlines' statements differ only in the conclusion**: the first is
   `∀ g, Summable (fun α => ‖…‖)`, the second is
   `(∀ α g, WhittakerCoefficientIntegrable …) ∧ ∀ g, Summable (fun α => …)`. Keep the wrapper's binder
   text verbatim — `K` is an *explicit* binder there (FR-0318's converse: a section-variable spelling
   would hash as the bare conclusion).
3. **`_`-prefixed binders in order B's statement** (`_hμ`, `_hν`, `_hψ`, `_hs`, `_hφ`, `_hφK`,
   `_hφf`, `_hφc`) are the pin's own names. Keep them: renaming a binder is a statement edit
   (the checker normalises bound names, but the port rule is that only a measured mismatch justifies a
   deviation).
4. **Order B's `let α`/`let E`**: the statement has two `let`s; transcribe them as written. The pin's
   `s.re > 1` is the strength the pin chose — do not weaken or strengthen it.
5. **`exp_neg_one_pow`** exists publicly only in its `WithZero.exp` spelling; if order B's proof needs
   the pin's private `exp` version, apply the public one at the same statement or re-spell it
   `private` locally and say so — do not duplicate a public name (FR-0274).
6. **Order C's `hψ_inf`** is a hypothesis of the pin's rows; do **not** discharge it with
   `exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar` in the statement. That
   normalization is what the *next* set's rows consume.
7. **`AdelicHaar`'s olean** was missing when this set's scaffolds were first elaborated; the tier-1
   build compiles it. Do not read a missing `.olean` as a missing declaration (FR-0033).
8. **Order D's wrapper carries enormous `attribute [-instance]` / `[-simp]` blocks.** They are the
   pin's own hygiene for its generated instances; do not transcribe them wholesale, and if one is
   needed for a `simp`/instance step, apply it locally (`set_option … in` or a scoped attribute) and
   record it.
9. **`TateCurve/SeriesIdentities.lean` is a 1,500-line module with an existing 17-row surface.**
   Order E appends one declaration at the end and adds its two `spec-pin:` lines; it must not reflow
   or re-elaborate anything else, and its build gate is the whole module.

## 7. Gates

Per order: `check_port` **0 mismatch / 0 missing** with every added declaration `ok`; the module's own
`lake build` under `flock`/`timeout` and silent but for its `sorry`s (removed); `#print axioms` on
every headline → `[propext, Classical.choice, Quot.sound]`; `dedup.py` / `move_dead.py`; a consumer
zone in `spec/` with a cross-module composition whose error count is the metric. No tree build.

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf11.json
python3 port_advise.py $(sed 's/^/--nodes /' ../../lean/tmp/af112/rows.txt | tr '\n' ' ') \
  --json build/af112_advise.json
```

With the nine rows treated as landed (`--port`, or read off the tree after the scaffolds), the ready
shelf was forecast at **12 rows / 6,351 silo**. Measured after the landing it is **11 rows / 6,204**: the
four rows of §5 stay, and **seven rows / 4,869 silo became ready because of this set** — the biggest is
`AutomorphicForm.whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family`
(2,695), the Euler-product identity that order B's summability row unblocks, followed by
`exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul` (995),
`exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein` (595),
`exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation` (211),
`fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace` (141),
`hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul` (130) and
`bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary` (102).

**The forecast's one miss, measured.** The pre-landing forecast counted
`NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace`
(147) as newly ready; in the post-landing read it is not on the shelf at all. `twin_scan --node` still
reads it **`new`** (unported), and the read is stable across two runs, so the row left the *demand*
rather than being ported: `needed` fell **214 / 136,028 → 202 / 130,951** — the set's own 4,797 lines plus
**280 lines of alternative-route nodes** the landing made unnecessary (this row and one more). That is
the one place where the forecast was optimistic; the shelf itself is the measured one.

## 9. What this set does not do

It does not touch the modular-polynomial root row (its missing premise is a separate port), the
padic-Tate-module rows, or any definition module; it does not promote anything outside the 15 names
of §4; and it writes no consumer of the next shelf — the Euler-product row (2,695) is the next set's
headline by size, and its premise audit is that set's first step.

## 10. The landing, measured

**Status: landed (2026-11-27).** Five orders, nine rows, five new modules and two insertion sites.

| order | module | lines | declarations | `check_port` | axioms |
|---|---|---:|---|---|---|
| A | `AutomorphicForm/Adelic/WhittakerSmoothSummability.lean` (new) | **1,206** | 75 public (73 engine + 2 headlines) | **75 ok** | clean |
| B | `AutomorphicForm/Adelic/BruhatEisensteinWhittakerSummability.lean` (new) | **689** | 1 public + 31 `private` | **1 ok** | clean |
| C | `NumberTheory/AdelicFourier/FourierInversion.lean` (new) | **713** | 25 public | **25 ok** | clean |
| C | `NumberTheory/AdelicFourier/PoissonNormalized.lean` (insertion) | 190 (from 112) | +1 public | **2 ok** | clean |
| D | `AutomorphicForm/Adelic/AddCharLocalComponents.lean` (new) | **534** | 1 public + 15 `private` | **1 ok** | clean |
| E | `AlgebraicCurve/Differential/FreeAlgebraLift.lean` (new) | **456** | 27 public | **27 ok** | clean |
| E | `TateCurve/SeriesIdentities.lean` (insertion) | 1,450 (from 1,429) | +1 public | **18 ok** | clean |
| — | promotions: `Unfolding` / `Faithful` / `PolyDecay` | 0 new | +12 / +2 / +2 public | **13 / 46 / 3 ok** | — |
| — | `spec/SetAF112Consumer.lean` (4 zones) | **152** | consumer, not wired | **silent** (exit 0) | — |

Every file is `0 mismatch / 0 missing / 0 own`, its own `lake build` exits 0 under `flock`, its edit loop
is silent at the 200 k cap, and `dedup` / `move_dead` read 0 clusters / 0 dead declarations per module.
The set-end tier-2 build of all ten modules: exit 0.

**The consumer zone** (`spec/SetAF112Consumer.lean`, four zones, no `#check`s): (1) order A's integrability
row implies its absolute-summability row (`Summable.norm`); (2) order B's hypothesis bundle feeds
SET-AF111A's polynomial-decay estimate (`1 < s.re` ⇒ `1/2 < s.re`), a cross-module composition of the
Bruhat–Eisenstein and `PolyDecay` rows; (3) order C's two rows compose to the four-fold inversion
`𝓕⁴ h = c² • h` on the locally constant compactly supported functions (the Schwartz row supplies the
hypotheses for the second inversion); (4) order E's row contrapositively: a regular differential the
differential lift does not kill certifies a non-vanishing `Pic0` lift.

**Plan vs actual.**

* **The gate text for two rows was a scaffold number, not a landing number.** Orders A and E were
  written with "1 ok" because the scaffold carried only the headline; the pin's surfaces are 77 and 32
  declarations, and the landings read **75 ok** and **27 ok** (the 73-row engine written once, public;
  E's 26 helpers public). Both are `0 mismatch / 0 missing`, so nothing is owed — the *size* was
  mis-stated, not the gate.
* **Order D dropped one pin declaration** (`addCharLevel_eq_of_ball`, pin `:177`–`:190`, 14 lines):
  it has no consumer anywhere in the pin either (`grep` over the whole pin tree finds only its own
  declaration) — the §2.3 residue, mechanically verified, recorded in the module header.
* **Order E's engine diff carries one `MISSING`** (`separableAlong_of_charZero`): a checker
  normalisation artefact, not a dropped row — the pin's `S_` text takes 3 binders from the section
  while its own `Theorems/` wrapper and the port copy spell 9, so `nhash` differs and positional
  `alpha_stmt` cannot bridge it. The module applies the port's public copy at the site. A one-line
  wrapper at the pin's spelling would make it `0 MISSING`; **declined**, because it would duplicate
  shared mathematics to satisfy an instrument.
* **Order A's engine is public at the pin's names**, twelve of them terse (`sl`, `ch`, `Sder`, `toLat`,
  `stepR`, `stepC`, `Harch`, …). Renaming them was considered and **declined**: the names occur inside
  the *statements* of a dozen further declarations, so a rename is a statement-text change that the
  checker resolves by reference, not a `pin:` row; the pin's own names are also the route readers
  arrive by, and the module header documents the layers.
* **Style linters**: order B carries one module-level `set_option linter.style.haveILetI false` and
  order E eight declaration-scoped ones; both are the pin's `haveI` instance walls, and both follow the
  precedent of `SmoothAutomorphicFn.lean` / `BaseChangeDescent.lean`.
* **One friction**: FR-0340 (a by-name visibility scan over-counts "already public"; `integrand_eq` is
  two theorems) — the promotion list needed a second pass (`Unfolding` 12 → 13 checked declarations).

**Post-landing read.** `needed [F terminal]` **214 / 136,028 → 202 / 130,951**; ready **11 / 6,204**;
leaves 5 / 13,761 and withheld 6 / 1,970 unchanged. Seven rows / 4,869 became ready (§8), the largest the
2,695-line Euler-product identity — the next set's headline by size.
