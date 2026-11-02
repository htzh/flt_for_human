# SET-AF1 — the cuspidal-spectrum carrier

**Status: landed 2026-11-02** (the definition layer by the manager, the eight headlines by
[WORKORDER-AF1-proofs.md](WORKORDER-AF1-proofs.md); §1.4–§1.5 record both halves and §8's table is
measured, not forecast). Scoped off the D–S shelf after SET 10 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). This is the
`AutomorphicForm` ready set as it now stands — **29 rows / 5,861 silo** on the corrected read (§0.2)
— and the cut is the one story most of it belongs to: the **cuspidal-spectrum carrier**, the 289-line
pin definition module `Def_AutomorphicForm_CuspidalSpectrumCarrier` that all seven rows cannot even
be *stated* without, and that
[CARRY-FORWARD.md](../../CARRY-FORWARD.md#def_automorphicform_cuspidalspectrumcarrier--the-carrier-definition-module-behind-the-deferred-centre-cut-slab-bound)
has owed since 2026-10-18.

The set is nine steps in four orders: **two definition modules (289 + 104 pin lines), one ground-prep
node (236 silo) and seven ready rows (739 silo)** — 1,368 pin lines, **≈1,020 net new math lines**,
five new modules, eighteen wire lines, no promotion, no migration, no marker, no tree build.

§0 the read and its state; §1 the cut; §2 what the rows say; §3 homes; §4 ground prep; §5 traps;
§6 gates; §7 calls; §8 reproduce and the forecast; §9 what this set does not do. Appendices A and B
name **every** `AutomorphicForm` row the set does not cut (23 ready + 91 leaves), with its reason.

No Lean was run while scoping; the read is `frontier.py`'s cached graph, the pricing
`port_advise`/`port_plan`, `twin_scan` statement-level, and the home check the port's own import
lines.

## 0. The read

### 0.1 The instrument's read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af1.json
python3 frontier.py --selfcheck
```

**`--selfcheck` PASS** (every `Thm_` source resolves; source tier covered by name tier; union is
sources | names; the frontier is inside the graph). It is a name-tier check, so it cannot see a
statement-level shadow — §0.2 finds one — but the extraction itself is consistent and has not changed
since SET 10.

| figure | value |
|---|---:|
| `needed [F terminal]` | 924 / 375,331 |
| `needed [literal]` | 937 / 378,806 |
| frontier F (union) | 1,491 / 752,035 |
| … of F, inside the cone | 1,166 / 603,367 |
| port cone / avoided R | 2,103 / 982,173 · 140 / 74,620 |
| ready rows, all namespaces | 61 / 11,434 |
| leaves, all namespaces | 262 / 64,874 |
| `AutomorphicForm` ready rows | **30 / 5,950** |
| `AutomorphicForm` leaves | 91 / 18,510 |
| `AutomorphicForm` demand | 420 / 173,110 |
| withheld by the FR-0044 guard | 4 / 831 (unchanged) |

**Read the delta, not the absolute.** SET 10's landing left `needed` at **937 / 379,736**; since then
the port has grown **13 nodes / 4,405 lines** (the MC wave and the Siegel-unit set, `git log`
`0f5039f..86041bf`). So every figure above is 4,405 lines lower than SET 10's, and none of that growth
is in this column.

**The withheld block, quoted whole** (unchanged since SET 6, all of it the prunable subject's):

| row | lines | blocking premise |
|---|---:|---|
| `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` | 327 | `AlgebraicCurve.Pic0.abelJacobiCard_genus` |
| `ModularCurve.moduleFinite_padicInt_tateModule_jOne` | 283 | `AlgebraicCurve.Pic0.abelJacobiCard_genus` |
| `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` | 126 | two `abelJacobiDiv`/`pathPeriodLattice` rows |
| `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` | 95 | `Pic0.natCard_torsion_prime_eq_pow_genus_complex` |

### 0.2 The correction — a ℚ-only shadow, and the one-command audit that finds it

The recipe's *read the shelf twice* rule fired, and not from a landing this time: the port holds
**`RatIdele.exists_norm_apply_eq_ideleNorm_rpow`** — the statement over `ℚ` —
at `NumberTheory/RatIdele/ClassCharNorm.lean:366`, and **not** the pin's general node
`NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow` (236 silo), which is the only premise of
the shelf row `AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous`
(89). The readiness test is last-name based (FR-0047), so the row reads `premises_unported = 0` and
`--selfcheck` is silent (it checks sources against names, not statements against names).

The statement-level verdict is one command per premise, and it is the whole audit:

```bash
python3 twin_scan.py --node NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow
#   236  relative   …  prelude 0/24  ~ RatIdele.exists_norm_apply_eq_ideleNorm_rpow
```

*relative* is the tool's word for "a port declaration with the same last name and a **different**
statement" — the SET 9 shadow (`Place.isRational_of_isAlgClosed` at the ℙ¹ statement), reached here
from the ℚ side. Applied to the cut's eleven premises, ten return `TWIN-public` and exactly one
returns `relative` (§0.3). **Proposal for the recipe §0** (recorded as FR-0092): the premise audit is
`twin_scan --node` on every premise of every cut row — one line and ~0.6 s each — and it is the only
cheap instrument that separates "ported" from "ported at a strictly weaker statement"; the `--unport`
read below then prices the correction.

```bash
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
  --unport NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow \
  --json > build/shelf-af1-corr.json
```

| figure | instrument | corrected (`--unport` the one shadow) |
|---|---:|---:|
| `needed [F terminal]` | 924 / 375,331 | **925 / 375,567** |
| `needed [literal]` | 937 / 378,806 | 938 / 379,042 |
| frontier F | 1,491 / 752,035 | 1,490 / 751,799 |
| ready rows, all namespaces | 61 / 11,434 | 61 / 11,581 |
| `AutomorphicForm` ready rows | 30 / 5,950 | **29 / 5,861** |
| `NumberField` demand | 108 / 35,026 | **109 / 35,262** |
| withheld | 4 / 831 | 4 / 831 |

The 89-row leaves the ready shelf (its proof cites an unported premise); the 236-line general node
**enters** it with both of its own premises ported (`NumberField.TateGlobal.compactSpace_normOneIdeleClass`
— the port's copy drops the `TateGlobal` namespace, statement identical — and
`NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one`, both `TWIN-public`). So the
correction costs the AF shelf one row and hands it a ready 236-line ground node with
**leverage 7 / 42** — the highest-leverage node in the cut. Every figure in §1 is from the corrected
read; the two sets of numbers are quoted side by side above because a delta between them means
nothing on different marker sets.

### 0.3 The premise audit, by hand, with the machine's verdict

All eleven distinct premise nodes of the nine steps, each checked by `twin_scan --node` (statement) and then
read against the port declaration (binder order), not by last name:

| premise | verdict | port home |
|---|---|---|
| `exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc` | TWIN-public | `AutomorphicForm/Adelic/DetNormSlabFundamentalDomain.lean:506` |
| `isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre` | TWIN-public | `AutomorphicForm/Adelic/DetNormSlab.lean:37` |
| `TateGlobal.continuous_ideleNorm_det` | TWIN-public | `NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean:37` |
| `TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq` | TWIN-public | `NumberTheory/NumberField/TateGlobalNormSection.lean:36` |
| `ideleNorm_det_globalPoints` | TWIN-public | `AutomorphicForm/Adelic/IdeleNormDet.lean:33` |
| `AdelicHaar.isMulRightInvariant_adelicGLHaar` | TWIN-public | `NumberTheory/AdelicHaar/MulRightInvariant.lean:334` |
| `exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple` | TWIN-public (two copies) | `AutomorphicForm/Adelic/Siegel/SlabCoveringTheorems.lean:41` (tier 1), `…/SlabCovering.lean:1080` (tier 3) |
| `TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc` | TWIN-public | `NumberTheory/NumberField/TateGlobalIdeleNormDet.lean:35` |
| **`TateGlobal.exists_norm_apply_eq_ideleNorm_rpow`** | **relative (ℚ-only)** | **absent — §0.2** |
| `TateGlobal.compactSpace_normOneIdeleClass` | TWIN-public | `NumberTheory/NumberField/TateGlobalCompactness.lean` |
| `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one` | TWIN-public (port name carries an `_impl` suffix, tier 3) | `NumberTheory/AdelicHaar/PlaceMeasure.lean` |

No other shadow: where the port renames across a namespace (`NumberField.compactSpace_normOneIdeleClass`
for `NumberField.TateGlobal.…`) the statement is the pin's, and where it keeps both copies
(`SlabCovering` / `SlabCoveringTheorems`) both check.

### 0.4 The definition layer — one module, and it is the gate

`port_advise --with-defs` over the seven rows returns **exactly three** pin `Def_` modules:
`CuspidalSpectrumCarrier` (41 declarations, **unported**), `CentreCutSiegelSetAmple` (11, ported) and
`FactorizableTestFn` (10, ported) — of which **36 declarations / ≈280 lines** are already in the port
by statement (33 byte-identical): `substitute`, not new work.

So the gate is one module, and the rows' *statement vocabulary* is complete, which is the FR-0049
check done by hand:

| vocabulary the seven statements name | port home |
|---|---|
| `CoversModCentre` | `AutomorphicForm/Adelic/Siegel/Covering.lean` |
| `centreCutSiegelSet`, `centreCutSiegelSetAmple` | `…/WindowedSiegel/CentreCutSet.lean`, `…/WindowedSiegel/CentreCutSiegelSetAmple.lean` |
| `cuspKFiniteSubmodule`, `levelInvariantSubmodule` | `…/Cusp/Constituent.lean` |
| `isotypicCuspSubmodule`, `IsArchBiFinite` | `…/IsotypicCuspSpace.lean` |
| `IsLsXiFunction`, `HeckeEigensystem` | `…/LsXi.lean`, `…/HeckeEigensystem.lean` |
| `productionPinsOf`, `levelOne`, `finiteAdelicGL2Subgroup`, `heckeGen`, `adelicBox` | `…/CarrierPins.lean`, `NumberTheory/AdelicLevel/{Level,HeckeGen}.lean`, `…/SmoothAutomorphicFn.lean`, `NumberTheory/AdelicBox.lean` |
| **`IsSlabFundamentalDomain`, `Carrier`, `contMemberSubmodule`, `cuspMemberSubmodule`, `toCarrier`, `pairing`, `HasModulus`** | **absent — the gate** |

### 0.5 The AF shelf, quoted whole

**Ready rows, all 29 (corrected read), 5,861 silo.** The six cut rows that survive the correction
are marked **◀**; the seventh cut row (`CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous`,
89) is exactly the one §0.2 removed from this table, and it is cut from the instrument read instead —
which is why the set carries its premise B1.

| row (`AutomorphicForm.` dropped) | silo | prem | lev | family |
|---|---:|---:|---|---|
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1 / 2 | SmoothCuspRealizationAt |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1 / 1 | SmoothCuspRealizationAt |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4 / 10 | — |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1 / 1 | the finite-place half of the Weyl/Bruhat left-translation computation; ready today (its four `Def_` imports are all ported), but it belongs with its gated archimedean twin (360 above), not with the carrier |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14 / 63 | — |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1 / 1 | — |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1 / 1 | — |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2 / 2 | LocalIntertwining |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3 / 20 | — |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2 / 27 | — |
| `CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample` **◀** | 234 | 3 | 1 / 2 | CuspidalSpectrum |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1 / 1 | SmoothCusp |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1 / 1 | — |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | 2 | 4 / 12 | — |
| `CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one` **◀** | 198 | 3 | 2 / 8 | CuspidalSpectrum |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5 / 8 | — |
| `finiteDimensional_span_translates_of_mem_archCutSubmodule` | 184 | 1 | 6 / 7 | — |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2 / 2 | — |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1 / 11 | — |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | 1 | 1 / 2 | SmoothCuspRealizationAt |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2 / 5 | — |
| `CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero` **◀** | 125 | 2 | 11 / 26 | CuspidalSpectrum |
| `isKfSmooth_rightConv` | 70 | 1 | 7 / 21 | — |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1 / 1 | CuspidalConstituent |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1 / 1 | — |
| `CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule` **◀** | 40 | 1 | 9 / 18 | CuspidalSpectrum |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2 / 3 | CuspidalConstituent |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1 / 6 | SiegelCovering |
| `CuspidalSpectrum.isotypicCuspSubmodule_le_cuspMemberSubmodule` **◀** | 29 | 1 | 2 / 3 | CuspidalSpectrum |
| `CuspidalSpectrum.exists_isSlabFundamentalDomain` **◀** | 24 | 1 | 6 / 14 | CuspidalSpectrum |

Every one of the 23 rows not marked is named with its reason in **Appendix A**; none of them is
silently dropped.

**The leaves block, all 91 rows / 18,510 silo** — 65 of them in the `AutomorphicForm` root
(13,728 silo), then `LocalIntertwining` 7 / 1,295, `CuspidalConstituent` 6 / 1,288,
`WindowedSiegel` 2 / 668, `CuspidalSpectrum` 2 / 379, `IsKfSmooth` 2 / 368,
`SmoothCuspRealizationAt` 2 / 280, `RankinSelberg` 2 / 207, and one each of
`IsFactorizableTestFn` 189, `IsUnitFactorizableAbove` 78, `IsIsotypicCuspFormAt` 30. The block is
**not cut and not priced** here — it is named row by row in **Appendix B** and deferred whole, as in
SET 3–10. Its shape is the same as ever: `M4aTorus`-scale outliers do not live here, but
`LocalIntertwining` and `CuspidalConstituent` hold the column's next two coherent clusters
(1,295 + 1,288 silo), and four leaves are the *successors* of this set's gates (§9).

## 1. The cut

### 1.1 The story

The carrier is the Hilbert-space object the whole cuspidal-spectrum development is stated over, and
the pin builds it in two tiny definition modules:

1. **`CuspidalSpectrumCarrier`** (289 pin lines / 41 declarations): the determinant-norm slab
   `detNormSlab α β`, the slab fundamental domain `IsSlabFundamentalDomain α β Φ₀` (positivity,
   `α < β`, containment, and `IsFundamentalDomain` of `GL₂(F)` in the slab under
   `(adelicGLHaar).restrict (detNormSlab α β)`), the production pins `fdPins Φ₀` with their nine
   `rfl` projections, the modulus predicate `HasModulus ξ σ`, the weight `weight σ` and the weighted
   measure `weightedMeasure Φ₀ σ`, the carrier `Carrier Φ₀ σ := Lp ℂ 2 (weightedMeasure Φ₀ σ)`, the
   three function submodules `memberSubmodule` (automorphic, `L²`), `contMemberSubmodule` (+
   continuous) and `cuspMemberSubmodule` (smooth cuspidal + continuous), the `MemLp` transfer
   `memLp_weightedMeasure_of_mem`, the linear map `toCarrier`, the weighted sesquilinear `pairing`,
   the cuspidal subcarriers `cuspSubcarrier` / `cuspLevelSubcarrier`, the lift `IsLift`, and `flat`.
2. **`CuspidalSpectrumSubrep`** (104 / 11): the subrepresentation datum over that carrier —
   `IsCuspLift` (a bounded operator that is the given function-level operator on the cuspidal
   subcarrier), `IsClosedCuspSubrep` (closed, and stable under right translation by the finite level
   group, by the archimedean row isometries, and by right convolution with factorizable arch-bi-finite
   test functions, each *through* an `IsCuspLift`), `IsIrreducibleCuspSubrep`, and their API
   (`IsClosedCuspSubrep.top`/`.bot`/`.inf` and the projections
   `IsIrreducibleCuspSubrep.isClosedCuspSubrep`/`.ne_bot`).

**What the gate unblocks, counted.** `Def_AutomorphicForm_CuspidalSpectrumCarrier` is imported by
**178** pin files — 107 `S_` files, their 70 `Theorems/` wrappers, and the subrep module itself — and
`Def_AutomorphicForm_CuspidalSpectrumSubrep` by 65 (35 `S_` + 30 wrappers). Those are not 178 rows
this set can write (a pin `import` is module-granular and many of those files use none of the
declarations), but they are the files that a landing of the gate makes *transcribable* one premise
wave at a time.

The seven ready rows are the carrier's first harvest: existence of a slab fundamental domain,
injectivity of `toCarrier`, existence of a modulus, the two submodule comparisons, right-translation
invariance of the weighted pairing by unit-norm elements, and the slab-integral bound that
CARRY-FORWARD has been holding since the centre-cut trio landed.

### 1.2 The steps

| step | node (`AutomorphicForm.` dropped) | pin lines | decls | net | prem | lev | gate |
|---|---|---:|---:|---:|---:|---|---|
| **A1** | `Def_AutomorphicForm_CuspidalSpectrumCarrier` | 289 | **41** | 263 | — | — | — |
| **A2** | `Def_AutomorphicForm_CuspidalSpectrumSubrep` | 104 | 11 | 80 | — | — | A1 |
| **B1** | `NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow` | 236 | 24 | 219 | 2 | 7 / 42 | — |
| **C1** ISLAB | `CuspidalSpectrum.exists_isSlabFundamentalDomain` | 24 | 1 | 6 | 1 | 6 / 14 | A1 |
| **C2** ISO | `CuspidalSpectrum.isotypicCuspSubmodule_le_cuspMemberSubmodule` | 29 | 1 | 14 | 1 | 2 / 3 | A1 |
| **C3** KFIN | `CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule` | 40 | 1 | 22 | 1 | 9 / 18 | A1 |
| **C4** TOCAR | `CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero` | 125 | 1 | 107 | 2 | 11 / 26 | A1 |
| **C5** HASMOD | `CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous` | 89 | 1 | 74 | 1 | 5 / 12 | A1, B1 |
| **D1** PAIR | `CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one` | 198 | 1 | 179 | 3 | 2 / 8 | A1 |
| **D2** SLAB | `CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample` | 234 | 17 | 61 | 3 | 1 / 2 | A1 |
| | **9 steps** | **1,368** | | **≈1,021** | | | |

**Pricing.** `port_advise` over the seven rows, then `port_plan`: **739 raw `S_` lines − 129
boilerplate = 610 declaration lines − 0 duplicate copies − 151 already in the port = 459 net new math
lines**. `--with-defs` adds the three pin `Def_` modules of §0.4; its 36 substitutions are **14** (the
`S_` file's shared slab prelude, ≈143 lines), **11 + 10** (the whole checked surface of
`CentreCutSiegelSetAmple` and `FactorizableTestFn`, both ported) and **1** (`detNormSlab`, the §4.2
false positive) — so of the three `Def_` modules only the carrier is work. The `net` column is measured
from the pin files: declaration text from the first declaration to the last, minus the substituted
lines (A1 263 of 289, A2 80 of 104, B1 219 of 236; the seven rows 606 − 143 = 463 declaration-text
lines, of which `port_plan` nets 459 after boilerplate attribution — the two figures are the same
number read two ways). Total **≈1,021**, of which the seven rows are only 459: the set is a
*definition* set with a theorem tail.

**The 459 is nearly all four rows.** SLAB's 235 pin lines contain 14 declarations / 143 lines that are
*already public in the port* — the CCF promotion put them in `PeterssonSlabPairing.lean` — so its
headline is a 12-line proof on top of `setLIntegral_fd_le_sum_mul` and `cover_of_forall`. ISLAB, ISO
and KFIN are one-line proofs once the gate exists. The weight is TOCAR (107), PAIR (179) and HASMOD
(74).

### 1.4 The landing — the definition layer, one manager session

The two gates were taken by the manager in one session, in the order the recipe asks for: wires and
header first, then the carrier, then its subrep sibling.

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---|---:|
| A1 | `Cusp/SpectrumCarrier.lean` (**+289**) | **41 ok** / 0 / 0 / 0 own | silent, **5.9 s**, zero warnings | clean on the five proof-carrying declarations |
| A2 | `Cusp/SpectrumSubrep.lean` (**+104**) | **11 ok** / 0 / 0 / 0 own | silent, **3.9 s**, zero warnings | clean |

Both were transcribed from the pin `Def_` files at the pin's names and statements, and both check
`41 ok` / `11 ok` on the **first** run — the only adaptations were the port import block (the pin's
two megafile stubs) and two linter silences the pin's own idiom forces (`linter.style.haveILetI` for
the `haveI`/`letI` walls, with the pin's precedent in `Adelic/AutomorphicFn.lean`).

**What the landing leaves**: 52 declarations of new public surface, 0 new imports in existing
modules, 0 markers, 0 promotions, 0 migrations, no new `Def_` module; `dedup.py --within` reports
**0 clusters** on both. `move_dead.py` reads the module as 0 declarations (the FR-0086 blindness —
`private`-heavy and definition-heavy modules are mis-read); a pin `Def_` transcription is exempt from
strict `move_dead` by the column's rules, and every one of the 41 is the pin's own surface.

**A consumer probe, and a repair found on the way.** `spec/AutomorphicFormSetAF1Consumer.lean` is new
(zones A/B: the slab fundamental domain at `(1,2)` from the centre-cut trio, the weighted-`L²`
transfer, `toCarrier`'s linearity, and `IsCuspLift` + `closed ⊓ closed`), 0 errors. The column's
existing probe `spec/AutomorphicFormConsumer.lean` was **already broken at HEAD** — 10
`unknownIdentifier` errors on the `Q09.*` / `Q09AIarch*` / `Q09AIarchG.*` names that the
token-removal commit renamed, never re-wired into the probe. It was repaired in the same touch
(`ArchApproxIdentity.isHaarMeasure_archHaarK`, `ArchInfra.muK`/`muK_univ`,
`ArchEntryBall.{matrixEntries,archEntries_eq,exists_approxIdentity}`,
`ArchApproxIdentity.{piRep,piRep_apply,contSubmodule,mem_contSubmodule}`) and is now **0 errors**. A
green checker on a module is not evidence that its consumer zone still typechecks; the probe must be
run with `lake env lean`, not assumed.

## 2. What the rows say

| order | who | steps | files touched | silo | why this order |
|---|---|---|---:|---:|---|
| **1** | manager (definition layer) | A1, A2 | `Cusp/SpectrumCarrier.lean`, `Cusp/SpectrumSubrep.lean` (both new) | 393 | nothing in the set can be *stated* before A1; A2 imports A1 |
| **2** | manager or worker | B1 | `NumberField/TateGlobal/NormExponent.lean` (new) | 236 | HASMOD's proof applies it; independent of A |
| **3** | worker | C1–C5 | `Cusp/SpectrumCarrierAPI.lean` (new) | 307 | needs 1 and 2 |
| **4** | worker | D1, D2 | `Cusp/SpectrumPairing.lean` (new) | 432 | needs 1 only |

**Disjointness.** Orders 3 and 4 write two different new modules and neither edits the other's; both
only *read* order 1's two modules, which are frozen on landing. So after order 1, orders 2 and 4 can
run concurrently and order 3 starts once order 2 lands. The build lock is the only shared resource —
and no order edits a hub: all five files are new, so every order's edit is cascade-free.

**Do not merge orders 3 and 4 into one module.** The API rows are stated over the carrier alone; the
two analytic rows import `Siegel/SlabCoveringTheorems` and the Haar-invariance module. One module
would make every future consumer of the carrier drag in the Siegel covering engine.

## 2. What the rows say

All seven are at the wrappers' binders, `F : Type` with `[Field F] [NumberField F]` and the
`(⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)` central subgroup spelled out; each `S_` file's `solution` is
the proof, and the wrapper is the statement authority.

* **A1 `CuspidalSpectrumCarrier` (289 / 41).** The definitions listed in §1.1 plus their API. Five of
  the 41 carry real proofs: `memberSubmodule`/`cuspMemberSubmodule`'s `zero_mem'`/`add_mem'`/`smul_mem'`
  (through `isAutomorphicFnAt_fdPins_iff` = `lsXiMemberAt_iff` at `Z = ⊤`), the `MemLp` transfer
  `memLp_weightedMeasure_of_mem` (the slab bound `α ≤ ‖det‖ ≤ β` gives `weight σ ≤ max (α^-σ) (β^-σ)`
  and `withDensity` monotonicity), the integrability of the constant-term integrand on the compact
  adelic box (`integrable_constantTermIntegrand_fdPins`), and `continuous_unipotentGL2_adele`.
  `toCarrier` is the `MemLp.toLp` of a member, `pairing` the weighted integral against `conj`.
* **A2 `CuspidalSpectrumSubrep` (104 / 11).** `IsCuspLift` and `IsClosedCuspSubrep` are the three
  invariance conditions (finite level, archimedean row isometries, right convolution by factorizable
  arch-bi-finite test functions) each mediated by a lift; `IsIrreducibleCuspSubrep` adds
  `M ≠ ⊥` and no proper closed sub-object; `IsClosedCuspSubrep.inf` is the only proof with content
  (a three-way `le_inf`).
* **B1 `exists_norm_apply_eq_ideleNorm_rpow` (236 / 24).** A continuous idèle-class character on
  `𝔸_K^×` has `‖μ x‖ = ‖x‖^σ` for a single `σ`. The pin's route: the modulus `x ↦ ‖μ x‖` is a
  continuous monoid homomorphism, trivial on principal idèles; on the **compact** quotient
  `normOneIdeles / principalIdeles` (`TateGlobal.compactSpace_normOneIdeleClass`) a continuous
  `ℝ`-valued homomorphism is bounded, hence trivial by the semigroup-power argument
  (`pow_unbounded_of_one_lt`); on the `ℝ_{>0}` direction it is forced by continuity of the additive
  logarithm `rayLog` to be `r ↦ r ^ rayLog 1`. The file is twenty-three private helpers (`expUnit`,
  `rayLog`, `apply_eq_rpow`, `modulus`, `ideleNormHom`, `apply_eq_one_of_mem_normOneIdeles`) plus the
  headline.
  The ℚ analogue in the port (`RatIdele.exists_norm_apply_eq_ideleNorm_rpow`) uses the `RatIdele`
  normalizer `ρ` instead and is **not** reusable — hence 0 of 24 in the port.
* **C1 ISLAB (24).** A slab fundamental domain exists: read
  `exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F 1 2` and take
  `α = 1, β = 2`; the pin's proof is three lines.
* **C2 ISO (29).** The isotypic cusp submodule of type `Ψ` (level `N`, exceptional set `S`) is
  contained in the carrier's cusp member submodule. One `Submodule.span_le` from
  `isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre` (the CCF
  landing) applied to a spanning cusp-smooth element: the covering `hcov` upgrades an automorphic
  function from the covering set to the slab fundamental domain `Φ₀`.
* **C3 KFIN (40).** The same for the whole cusp `K`-finite span `cuspKFiniteSubmodule`; identical
  proof, weaker hypothesis (`hcov` but no `S`, `Ψ`).
* **C4 TOCAR (125).** `toCarrier` is injective on continuous members. From `toCarrier φ = 0` get
  `φ =ᵐ 0` for the weighted measure on the slab (its density is strictly positive), hence `φ =ᵐ 0` on
  the slab `detNormSlab α β` itself, and left invariance plus countability of `GL₂(F)` propagates that
  to `φ =ᵐ 0` on the whole slab; then `φ` continuous and nonzero somewhere is translated *into* the
  slab by the continuous norm section `exists_continuous_monoidHom_ideleNorm_apply_eq`, contradiction.
* **C5 HASMOD (89).** An automorphic `φ ≠ 0` with `φ` continuous forces a modulus for its central
  character: read `φ (z · g₀) / φ g₀ = μ z` at a point `g₀` where `φ ≠ 0`, which makes `μ`
  multiplicative and continuous, gives `IsIdeleClassChar`, and applies **B1**. This is the row whose
  premise was the ℚ shadow of §0.2.
* **D1 PAIR (198).** `pairing (rightTranslate y φ) ψ = pairing φ (rightTranslate y⁻¹ ψ)` for
  `‖det y‖ = 1`, and both translates stay in `contMemberSubmodule`. Unimodularity of the restricted
  Haar measure on the slab (`isMulRightInvariant_adelicGLHaar`), the `SMulInvariantMeasure` of
  `μ.restrict (detNormSlab α β)` under `GL₂(F)`, and the central-character transformation of `φ`
  under the diagonal unit `det y`.
* **D2 SLAB (234).** *The carry-forward headline.* If the ample centre-cut Siegel sets cover `Φ₀` up
  to the centre, then the `L²` mass of any `IsLsXiFunction` on the slab is bounded by the mass on the
  covering, with the constant
  `∑ n ∈ N, ‖ξ n‖²` over the pin's central covering finset `N`. Proof: the covering theorem
  `exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple` supplies `N`, then
  the port's own `setLIntegral_fd_le_sum_mul` + `cover_of_forall` do the measure theory, and the
  central character's weights give the constant.

## 3. Homes — five new modules, no migration, no legacy question

**The "above all premises" search finds nothing.** Parsing the port's import graph (1,003 modules) and
asking which module dominates the cut's premise homes returns **no candidate at all**. For the two
consumer modules the ten premise homes are dominated at best **8 / 10**, by `DetNormSlab.lean` and
`MeasurableFundamentalDomainCover.lean` (both 0-importer); for the gate module its seven dependencies
are dominated at best **6 / 7**, by `Cusp/Constituent.lean` and a dozen others — they miss
`NumberTheory/NumberField/TateGlobal/Defs` or `NumberTheory/AdelicBox`, and the pin's own two `Def_`
imports (`CuspidalConstituent`, `TateGlobalZeta`) are *incomparable* in the port:
`Cusp/Constituent.lean` does not import `TateGlobal/Defs.lean`. That is expected: the pin's `Def_`
module imports two megafiles that the port split into `Cusp/Constituent` and
`NumberTheory/NumberField/TateGlobal/Defs` plus the five others its proofs name, so the ported module
must import the union. The homes are therefore all new modules, which also makes every edit
cascade-free.

| # | module (all new) | imports (beyond the gate) | holds |
|---|---|---|---|
| 1 | `FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumCarrier.lean` | `Cusp/Constituent`, `Adelic/CarrierPins`, `Adelic/AutomorphicFn`, `Adelic/SmoothAutomorphicFn`, `Adelic/ConstantTerm`, `NumberTheory/AdelicBox`, `NumberTheory/NumberField/TateGlobal/Defs` (+ `AdelicLevel/{Level,HeckeGen}`, `AdelicHaar/GeneralLinear` if not transitive) | A1 (41) |
| 2 | `FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumSubrep.lean` | 1, `Adelic/IsotypicCuspSpace` (`rowIsometryInclAt₀`), `Adelic/ArchWeightCharTransport` (`rowIsometrySubgroup₀`), `Adelic/RightConvolution`, `Adelic/FactorizableTestFn`, `Adelic/ArchType` | A2 (11) |
| 3 | `FLTForHuman/NumberTheory/NumberField/TateGlobal/NormExponent.lean` | `TateGlobal/Defs`, `TateGlobalCompactness`, `NumberField/IdeleClass/Vocab`, `AdelicHaar/PlaceMeasure` | B1 (24) |
| 4 | `FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumCarrierAPI.lean` | 1, 3, `Adelic/DetNormSlab`, `Adelic/DetNormSlabFundamentalDomain`, `NumberTheory/NumberField/TateGlobalContinuousIdeleNorm`, `…/TateGlobalNormSection` | C1–C5 (5) |
| 5 | `FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumPairing.lean` | 1, `Adelic/IdeleNormDet`, `NumberTheory/AdelicHaar/MulRightInvariant`, `Adelic/Siegel/SlabCoveringTheorems`, `NumberTheory/NumberField/TateGlobalIdeleNormDet` | D1, D2 (2) |

**Import-direction check.** Module 1 is above its seven dependencies by construction (nothing imports
it), and 2–5 are above 1. The one direction to *not* add blindly: if a worker finds an import missing
in module 1, it is an edge into the module from something `Cusp/Constituent` or `TateGlobal/Defs`
already dominates — i.e. already there — or a genuine cycle, which must be reported rather than
worked around (the recipe §4 failure mode that cost two worker rounds). In particular
`Cusp/SpectrumCarrier.lean` must **not** import `Cusp/SpectrumSubrep.lean`, and `SpectrumPairing.lean`
must not be imported by `SpectrumCarrierAPI.lean`: the four consumer orders must stay independent.

**Namespace.** Keep the pin's `AutomorphicForm.CuspidalSpectrum` (the checker's dotted fallback and
the pin fidelity both rely on it). No new `Def_` module is created: both gates transcribe existing pin
`Def_` files.

**No legacy module, no migration, no promotion.** None of the five is in
`spec/old_check_stmts.py`'s `PORT_FILES`; none of the gate's 52 declarations exists in the port under
any name (`detNormSlab`, `IsSlabFundamentalDomain`, `fdPins`, `HasModulus`, `weight`,
`weightedMeasure`, `Carrier`, `memberSubmodule`, `contMemberSubmodule`, `cuspMemberSubmodule`,
`toCarrier`, `pairing`, `cuspSubcarrier`, `cuspLevelSubcarrier`, `IsLift`, `flat`, `IsCuspLift`,
`IsClosedCuspSubrep`, `IsIrreducibleCuspSubrep`, `adelicMaximalCompact` — all grepped, all absent;
`IsLift`'s only homonym in the port is `NumberField.Extension.IsLift`, unrelated).

## 4. Ground prep (the manager's)

1. **Wires.** Eighteen `spec-pin:` lines in the five new headers: two per row for the seven rows and
   B1 (`Theorems/Thm_…` + `P2M/Sol/S_…   -- comparable copy`), and one per gate module
   (`Definitions/Def_AutomorphicForm_CuspidalSpectrumCarrier.lean`,
   `…/Def_AutomorphicForm_CuspidalSpectrumSubrep.lean`). Precedent: the 69 modules already wired to a
   pin `Def_` file, e.g. `RepTheory/LocalLanglands/HeckeCosetLocal.lean:28`.
2. **`decl_markers.tsv`: no rows.** Every declaration is at the pin's name in the pin's namespace. The
   one exception to watch is `detNormSlab`, which `port_advise` reports as a *substitute* of
   `AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet` — a **false positive** of the parser's
   type-only `def` match (both have bare type `ℝ → ℝ → Set (AdelicGL2 (𝓞 F) F)`); it is new
   mathematics, write it from the pin (the DC1 order hit the same false positive on five `def`s).
3. **`PORT_FILES`/`SOURCES`: do not append.** The frozen registry is grandfathered; the new modules
   are wired by their own `spec-pin:` lines. Verify each of the five paths is absent from
   `PORT_FILES` before writing.
4. **Consumer zone.** `spec/AutomorphicFormSetAF1Consumer.lean`, two zones with real compositions (no
   `#check`s): (i) `exists_isSlabFundamentalDomain` at `(α, β) = (1, 2)` composed with
   `toCarrier`/`pairing` on a `cuspMemberSubmodule` element, and the modulus from C5 applied to a
   concrete central character; (ii) the SLAB bound instantiated at the pin's own covering hypotheses
   `hd`/`hκ` and composed with `memLp_weightedMeasure_of_mem` to read the `L²` membership it implies.
   Its error count is the deliverable metric.
5. **After the landing.** `python3 spec/unwired_register.py --check` (expect no drift: both gate
   modules are wired to their own pin `Def_` files, so they are tier 1 and nothing new enters the
   tier-3 register — A2 simply has no consumer yet), `dedup.py` / `move_dead.py` on the five modules,
   and the shelf re-read of §8.

## 5. Per-step traps

**A1 (289 / 41).** (i) The pin's `attribute [local instance] NumberField.AdelicHaar.glBorel` and
`borelSpace_glBorel` must be carried or supplied as `haveI` at each use — the port has the same
instance in `AdelicHaar/GeneralLinear.lean`. (ii) `Integrable` in
`integrable_constantTermIntegrand_fdPins` is stated under `letI : MeasurableSpace (AdeleRing …) :=
(fdPins F Φ₀).nS`; keep the `show`/`letI` order, it is what makes `(fdPins F Φ₀).ν` unfold to
`ProbabilityTheory.cond` (spelled out in the proof body). (iii) `memLp_weightedMeasure_of_mem` needs
`Real.rpow_le_rpow_of_nonpos` for the `σ > 0` branch and `Real.rpow_le_rpow` for `σ ≤ 0`; check both
names at v4.34 before writing the `rcases`. (iv) `Carrier` is `Lp ℂ 2 (weightedMeasure F Φ₀ σ)` with a
`Measure` (not `IsFiniteMeasure`) — do not add a finiteness instance to make `Lp` elaborate; the pin
does not. (v) The nine `fdPins_*` `rfl` lemmas are `@[simp]` and one of them is
`fdPins_ν = @ProbabilityTheory.cond …`; if the port's `CarrierPins` field names drifted, the whole
block is a `rfl` cascade and must be fixed at the field names, not by `simp only`. (vi) The pin's
`structure IsSlabFundamentalDomain … : Prop` is a `Prop`-valued structure holding
`IsFundamentalDomain` data — keep the `Prop` and the `where`-style fields.

**A2 (104 / 11).** (i) Every hypothesis of `IsClosedCuspSubrep` quantifies over a *bounded operator
together with* its `IsCuspLift`, so a `∀ S, IsCuspLift … → M.map S ≤ M` — read the pin's binder order
before transcribing. (ii) `rowIsometrySubgroup₀ w.Completion` and `rowIsometryInclAt₀ F w k` live in
`ArchWeightCharTransport`/`IsotypicCuspSpace` (not in `RowIsometry.lean`); confirm before adding an
import. (iii) `IsClosedCuspSubrep.inf`'s three sub-proofs are `le_inf` of two `map_mono` chains — the
only place a `Submodule.map_mono` transposition can invert.

**B1 (236 / 24).** (i) Drop the pin's `attribute [-instance]` line: it names mathlib `v4.30` instances
mangled with `…_definitions` suffixes that do not exist at v4.34 (the precedent and the wording are
`NumberTheory/RatIdele/ClassCharNorm.lean`'s header). (ii) `map_real_smul` (real `ℝ≥0`-linearity of a
continuous additive hom) is mathlib; the pin uses it once in `apply_eq_rpow`. (iii)
`QuotientGroup.lift`, `QuotientGroup.isQuotientMap_mk`, `isCompact_range`, `MonoidHom.mem_range`,
`Subgroup.mem_subgroupOf` are the whole compactness argument — no port-side helper is needed. (iv)
`NumberField.TateGlobal.normOneIdeles` and `M4aHerbrand.principalIdeles` are ported
(`TateGlobal/Defs.lean`, `NumberField/IdeleClass/Vocab.lean`); the pin's `P` is their `subgroupOf`.
(v) The pin's `#print axioms` line follows the `solution`; transcribe the headline only.

**C1 (24).** The pin's `α = 1, β = 2`; `IsSlabFundamentalDomain.pos`/`lt` are then `one_pos`,
`one_lt_two`. `hS : S ⊆ detNormSlab F 1 2` comes from the premise's third component.

**C2/C3 (29 / 40).** One `Submodule.span_le` + the CCF headline; the *only* risk is the argument order
of `isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre`
(`F c u d₁ d₂ T hd hcov α β hΦ₀.pos Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ φ …`) — read the port
declaration, not the pin. C3's statement drops `N`, `S`, `Ψ` but keeps `hc`, `hd₁`, which the proof
does **not** use — keep them anyway (they are the wrapper's statement, which the checker diffs) and
put the module's `set_option linter.unusedVariables false in` on that one declaration. **Correction
from the landing**: the first draft of this §5 claimed an unused *explicit* hypothesis does not trip
that linter — at `v4.34.0` it does (measured on C3's `hc`/`hd₁` and D2's `hκ`), so the one-declaration
suppression is the fix, not an unnecessary caution. C3 also needs the pin's
saturation trick — `rintro φ ⟨hsat, hcont, -⟩`, then `have h := hsat 1` and `rightTranslate F 1 φ = φ`
by `funext x; simp [rightTranslate]` — to get the smooth-cusp condition at `1`.

**C4 (125).** (i) `push_neg` in the pin's `by_contra` block is the deprecated spelling: `push Not`
(FR-0036). (ii) Four `Countable` instances are built inline (`F`, `Matrix (Fin 2) (Fin 2) F`, `GL₂(F)`,
`Γ`) from `Module.finBasis ℚ F`; keep them `haveI`-local — a global `Countable F` would be wrong for a
general number field. (iii) `ae_withDensity_iff` needs the measurability of
`x ↦ ENNReal.ofReal (weight σ x)`; the pin proves it from `continuous_ideleNorm_det`. (iv)
`Measure.restrict_apply` + `isOpen_ne_fun hcont continuous_const` is how the null set becomes
measurable.

**C5 (89).** (i) The row needs **B1**; if order 2 has not landed, the proof has no route (the ℚ copy is
not an instance). (ii) `push_neg` → `push Not`. (iii) The `centralScalar` continuity is spelled through
`NumberField.AdelicVolume.centralScalar_val` + `Units.continuous_iff` (`continuous_pi … |>.matrix_diagonal`,
`Units.continuous_coe_inv`); the pin's `let μ := ξ.comp (Subgroup.topEquiv …).symm.toMonoidHom` is what
turns the `⊤`-subgroup character into an idèle character for B1.

**D1 (198).** (i) Install `haveI : BorelSpace (AdelicGL2 …) := borelSpace_glBorel …`,
`haveI := isHaarMeasure_adelicGLHaar …`, `haveI : (adelicGLHaar …).IsMulRightInvariant :=
NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F` — the third is the module's own premise and
its statement is `IsMulRightInvariant`, not `SMulInvariantMeasure`. (ii) The
`SMulInvariantMeasure` instance for `μ.restrict (detNormSlab α β)` is built by hand with `hset` and
`measure_preimage_mul`; it is the technical core of the row. (iii) `hS_mul` uses
`ideleNorm (det x) = 1 → x * z ∈ S ↔ x ∈ S`, which needs `ideleNorm_mul` and `ideleNorm_pos`.

**D2 (234).** (i) **Import the 14 declarations, do not re-prove them**: they are public in
`AutomorphicForm/Adelic/PeterssonSlabPairing.lean` (the CCF promotion) —
`setLIntegral_fd_le_sum_mul`, `cover_of_forall`, `setLIntegral_biUnion_translates_le`,
`smulInvariantMeasure_restrict`, `slab`, `μH`, `Γp`, `dn*`, `measurableSet_slab`,
`subtype_mul_mem_slab`, `smulInvariantMeasure_slab`, `preimage_subtype_mul_slab`,
`setLIntegral_fd_le_of_cover`. The two `FundamentalDomainSlab.*` copies differ from the pin's only in
binder spelling (`port_advise`'s *generalise* block: ratio 0.95–0.98) and the port has both spellings;
take the `PeterssonSlabPairing` one. (ii) The pin's 17 declarations collapse to one headline of ~12
lines: `exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple` gives `N`, the
constant is `∑ n ∈ N, ‖ξ n‖²`, and the `sum_congr`/`ofReal_pow`/`enorm_eq_nnnorm` finish. (iii) The
pin's `ENNReal.ofReal_sum_of_nonneg` needs the `positivity` discharge per term.

## 6. The gates, per order

As in SET 6–10 and the recipe §6, unchanged:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; the new declarations are
   `ok` (or a `pin:`/`own:` row in `spec/decl_markers.tsv`, which the manager writes — none expected).
   Expect A1 to check **41 ok**, A2 **11 ok**, B1 **1 ok** (the headline; the 23 private helpers are
   matched through the checker's pin-private fallback but do not enter the checked surface), and one
   `ok` per row.
2. `#print axioms` on all eight headlines plus the five proof-carrying declarations of A1 →
   `[propext, Classical.choice, Quot.sound]`.
3. Each module's own `lake build` under `flock`/`timeout`; **silent** (zero warnings); no tree build,
   no dependents. A `Replayed` line is not evidence that the `.olean` exists (FR-0033).
4. `dedup.py --within --module <module>`; `move_dead.py`. Expect no cluster: A1–A2 are definitions,
   and the seven rows are seven distinct statements (all `new` in `twin_scan`, no pair).
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; **no `set_option maxHeartbeats`** — none
   of the seven `S_` files sets one, and neither gate module does.
6. The consumer zone of §4.4: its **error count** is the metric, and it must fail if any of the five
   modules is deleted.

## 7. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. **the cut** | **the carrier story: A1+A2+B1+C1–C5+D1+D2 = 9 steps / 1,368 pin lines / ≈1,021 net**, four orders | the alternative on the shelf is the *no-Hecke-eigenvalue* pair (527 + 513, no definition gate) — a cleaner-looking 1,040-silo set, but it is one story of two big theorem proofs, it is the Langlands–Tunnell column's, and it leaves the carrier gate unbuilt — with it all six `CuspidalSpectrum` shelf rows and the 65-file subrep family |
| 2. **A2 (Subrep, 104)?** | **include** | it is the second half of the same gate, its 11 declarations are checkable against their own pin `Def_` file, and it is the prerequisite of **65** pin files (35 `S_` + 30 `Theorems/` wrappers, §9). Excluding it saves 104 lines and leaves the next wave still gated |
| 3. **B1 (236) or defer HASMOD?** | **include B1** | the corrected read makes it a *ready* node with leverage 7 / 42; deferring it would cut the set's highest-leverage row (C5, 5 / 12) and leave the shadow in the read, so the next scoping would re-find it |
| 4. **the homes** | **five new modules**, no migration, no legacy question | the import-graph search returns no existing module above the premises (§3), so a new module costs nothing and a "home" would be a cycle |
| 5. **the lanes** | **order 1 (A1, A2) → order 2 (B1) and order 4 (D1, D2) concurrently → order 3 (C1–C5)** | the definition layer is the manager's; `HASMOD` needs B1; the two analytic rows are independent of B1 but not of A1 |
| 6. **the SLAB row** | **include it** | it is the CARRY-FORWARD entry's headline (deferred 2026-10-18, "do not schedule the 234 off `--ready` until [the carrier] lands") and after the gate its headline is a 12-line proof on top of 143 pin lines that are already public in the port |

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af1.json   # §0.1
python3 frontier.py --selfcheck                                                                          # PASS
python3 twin_scan.py --node NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow                     # relative
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
  --unport NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow --json > build/shelf-af1-corr.json  # §0.2
python3 port_advise.py --with-defs --nodes <the seven rows> --json build/af1-defs.json                    # §1.2
python3 port_plan.py --json build/af1-defs.json                                                          # 459 net
python3 port_advise.py --target Definitions/Def_AutomorphicForm_CuspidalSpectrumCarrier.lean --json build/af1-gate.json
python3 port_advise.py --target Definitions/Def_AutomorphicForm_CuspidalSpectrumSubrep.lean  --json build/af1-subrep.json
python3 port_advise.py --target P2M/Sol/S_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow.lean --json build/af1-norm.json
python3 twin_scan.py --node <each of the seven rows>                                                      # new × 7
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumCarrier.lean            # after landing
```

**What the set consumes**: 9 steps / 1,368 pin lines — two definition modules (393), one ground node
(236), seven rows (739 → 459 net); **≈1,021 net new math lines**; five new modules; 18 wire lines; 0
imports added to existing modules, 0 promotions, 0 migrations, 0 markers, 0 tree builds.

**Measured, not forecast** (the recipe's §7 re-read, run after the landing; the "before" column is
the corrected read of §0.2, the "forecast" column what this brief predicted):

| figure | before | forecast | **measured** |
|---|---:|---:|---:|
| `needed [F terminal]` | 925 / 375,567 | 917 / 374,592 | **917 / 374,592** ✓ |
| frontier F | 1,490 / 751,799 | 1,498 / 752,774 | **1,498 / 752,774** ✓ |
| `AutomorphicForm` ready rows | 29 / 5,861 | 23 / 5,122 | **24 / 5,248** |
| `AutomorphicForm` demand | 420 / 173,110 | 413 / 172,371 | **413 / 172,371** ✓ |
| `NumberField` demand | 109 / 35,262 | 108 / 35,026 | **108 / 35,026** ✓ |
| the two gates in the port | absent | 52 declarations | **52, checker 41 + 11 `ok`** |
| `--selfcheck` | PASS | — | **PASS** (1,334 `Thm_` sources / 1,498 names) |

The ready shelf is one row off the forecast because **the set makes a row ready**: with B1 ported,
`AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` (**37 silo**, 1 premise,
leverage 3 / 8) joins the shelf — the recipe's third number. Nothing else entered, and the eight rows
the set consumed are the only ones that left.

**The subrep wave is not unlocked by promotions alone.** The gates' consumers in the leaf list are
either already ready (`finiteDimensional_span_translates_of_mem_archCutSubmodule` 184, which imports
the carrier and uses none of it) or blocked on other premises (`exists_isArchBiFinite_flat` 304,
`isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` 75). What the set *does*
change is that the 65 pin files importing `Def_AutomorphicForm_CuspidalSpectrumSubrep` are one
premise-wave from transcribable; §9 names them.

## 9. What this set does not do

- **The 23 `AutomorphicForm` ready rows it does not cut.** Each is named with its reason in
  Appendix A. **Four** of them are *definition-gated elsewhere*, by three unported modules the AF
  column still owes: `Def_AutomorphicForm_FnTwist` (104 → `rightTranslate_adjoint_weightedPairing…`
  433), `Def_UnramifiedWhittaker_HeckeRecursion` (55 → `heckeCosetSum_sum_rightConv_translate…` 138
  and `sum_whittakerCoefficient_mul_placeEmbed_…` 146, the second also needing
  `Def_AutomorphicForm_BoundedGenuineCuspRealization` 316), and that is all. **This list's original
  fourth entry was wrong**: `apply_weylInv_unipotent_mul_archSupportedAt…` (360) does **not** need
  `Def_AutomorphicForm_AdelicMaximalCompact` — its wrapper imports the module and neither the wrapper
  nor the `S_` file uses a single declaration of it (declaration-level grep: 0), the module-granular
  import the carry-forward register warns about. Its twin `apply_weylInv_unipotent_mul_localWeyl…`
  (217) shares the `WeylIntertwining`/`EtaFamily`/`InducedSection` closure, which *is* ported — so
  the pair is two ready rows, and the `adelicMaximalCompact` vocabulary is unported because the
  **leaves** need it, not this pair (SET-AF2 §0.3 makes the set).
- **The 91 `AutomorphicForm` leaves / 18,510 silo.** Named row by row in Appendix B, deferred whole.
  Its two coherent clusters — `LocalIntertwining` (7 / 1,295) and `CuspidalConstituent` (6 / 1,288) —
  are the column's next two candidate sets after this one.
- **The subrep wave (65 pin files).** `Def_AutomorphicForm_CuspidalSpectrumSubrep` is the import gate
  of **65** pin files — 35 `S_` files and their 30 `Theorems/` wrappers (`exists_isLift_rightConv`,
  `exists_commute_lift_*`,
  `isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_*`, the two `isCuspSubrep_…_map_subtype_comap_toCuspSubcarrier_*`,
  …). None of them is on the shelf today; A2 lands the gate so the wave can be scoped off a re-read
  instead of a hand-walk.
- **Anything behind the prunable complex-analytic subject.** The withheld 4 / 831 (§0.1) stay withheld
  (the RR column's phase 3).
- **The `AlgebraicCurve` regular-prolongation block and the MC column's genus row** — SET 10's
  hand-offs, untouched here.
- **No new `Def_` module, no promotion, no migration, no tree build.** The two gates are
  transcriptions of existing pin `Def_` files, wired to them.

## Appendix A — the 23 `AutomorphicForm` ready rows not cut

Grouped by subject, each with the reason it stays out.

**The no-Hecke-eigenvalue pair (1,040 silo, no definition gate) — the next theorem set.**

| row | silo | prem | lev | why not here |
|---|---:|---:|---|---|
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1 / 2 | one story of two theorem proofs (a cuspidal automorphic form has no right-translation eigenvalue at `heckeGen v` for `v ∤ level`); serves the Langlands–Tunnell Satake bound; a coherent set on its own, but 1,040 silo of *proof* — beyond a second dispatch here |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1 / 1 | the same statement under continuity instead of genuineness; same set |

**Definition-gated elsewhere (the column's other three definition waves).**

| row | silo | gate | why not here |
|---|---:|---|---|
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | `Def_AutomorphicForm_FnTwist` (104, unported) | adjointness of right translation for the weighted Petersson pairing; it is the *Petersson* story (with the 192 below), and its gate is `fnTwist`/`twistedCentralChar`, a different subject from the carrier |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | **none** — corrected by SET-AF2 §0.3: the wrapper *imports* `Def_AutomorphicForm_AdelicMaximalCompact` but neither it nor the `S_` file uses any of its declarations (declaration-level grep: 0), so the import is dead and the row was ready all along | the Weyl–Iwasawa left-translation computation at an archimedean supported section |

**Ready, but a different subject.**

| row | silo | prem | lev | why not here |
|---|---:|---:|---|---|
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1 / 1 | the finite-place half of the Weyl/Bruhat left-translation computation; ready today (its four `Def_` imports are all ported), but it belongs with its gated archimedean twin (360 above), not with the carrier |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14 / 63 | **global Iwasawa decomposition** `g = b·k` for `GL₂(𝔸_F)` — self-contained (premise `LocalGL2.iwasawa_decomposition` ported) and the column's highest-leverage row; a story of its own, and the natural first cut after this one if the Hecke pair is deferred |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1 / 1 | the adelic content/valuation computation feeding the class group; its closure is ported (`ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd`), no AF gate — number-theory-flavoured, not the carrier |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2 / 2 | `p`-adic local intertwining (the `LocalIntertwining` cluster of 7 leaves / 1,295 is its home); different subject |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3 / 20 | the Bruhat/Eisenstein constant term through `WeylIntertwining` (ported); the Eisenstein column's story, not the carrier's |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2 / 27 | the isotypic cut's membership lemma; it is the *isotypic* sibling of C2 and the natural successor of this set (it consumes the same submodules) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1 / 1 | the Hecke-coset seam's non-eigenfunction row (premise `exists_isHeckeCosetSystem_localRep_heckeGen`, ported); Hecke column |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | 2 | 4 / 12 | the Whittaker-coefficient normalisation; its own story |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5 / 8 | Petersson non-vanishing (with the 433 above); its own story |
| `finiteDimensional_span_translates_of_mem_archCutSubmodule` | 184 | 1 | 6 / 7 | the archimedean **cut**'s finite-dimensionality; imports the carrier module and uses **none** of its 41 declarations (declaration-level grep: only the `import` line), so it needs no gate — it is DC1's family, not the carrier's |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2 / 2 | right convolution by a level-spherical coset sum; the Hecke/level-spherical seam |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1 / 11 | the global fundamental domain without the determinant-norm restriction; a neighbour of C1 and the natural companion of the carrier *next* time |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | 1 | 1 / 2 | the Whittaker recursion; needs `Def_AutomorphicForm_BoundedGenuineCuspRealization` (316, unported) *and* `Def_UnramifiedWhittaker_HeckeRecursion` (55, unported) — a third definition wave, not this one |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2 / 5 | needs `Def_UnramifiedWhittaker_HeckeRecursion` (55, unported); the Hecke-recursion gate |
| `isKfSmooth_rightConv` | 70 | 1 | 7 / 21 | `K_f`-smoothness of right convolution (D5 family); cheap and self-contained, but a different subject |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1 / 1 | the constituent/arch-cut intersection; ATS family |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1 / 1 | test-function integrality (D4 family) |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2 / 3 | right convolution vs right translation with a conjugation; constituent family |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1 / 6 | the ℚ covering row; Siegel-covering family (its `ℝ`-general sibling is in the leaves) |

## Appendix B — the 91 `AutomorphicForm` leaves, 18,510 silo

Deferred whole; quoted so that the next scoping starts from a list, not from a memory. Names are
`AutomorphicForm.` dropped; silo in brackets.

**Root (65 rows / 13,728).**
`su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` 755 ·
`gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` 695 ·
`exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` 587 ·
`exists_sum_prod_mul_of_rightTranslatesSpanFinite` 576 · `exists_coversModCentre_centreCutSiegelSetAmple` 520 ·
`exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth` 506 ·
`finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule` 459 ·
`exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` 445 ·
`isFundamentalDomain_boxSheet_rationalTorusUnipotent` 440 · `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` 432 ·
`hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` 404 ·
`archDerivAtComplex_commutator_of_isArchSmoothAtComplex` 401 ·
`exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` 384 ·
`exists_isArchBiFinite_rightConv_comp_inv` 376 · `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` 347 ·
`not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` 346 · `isFundamentalDomain_boxSheet_rationalCentreUnipotent` 340 ·
`exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` 317 ·
`hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` 298 ·
`archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` 250 ·
`finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule` 222 · `archDerivAt_commutator_of_isArchSmoothAt` 208 ·
`integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` 196 ·
`exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` 192 ·
`flat_family_comp_mul_of_mem_adelicMaximalCompact` 185 · `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` 184 ·
`exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` 184 ·
`isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` 177 ·
`isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` 165 ·
`exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq` 158 · `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` 156 ·
`typeSubmodule_inf_typeSubmodule_eq_bot` 152 · `coversModCentre_of_le_of_lt_of_coversModCentre` 150 ·
`exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt` 145 · `constantTerm_adelicBox_unipotentGL2_mul` 144 ·
`coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` 136 · `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` 133 ·
`whittakerCoefficient_unipotentGL2_mul` 123 · `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` 119 ·
`apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` 117 · `exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty` 114 ·
`archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` 110 · `continuous_whittakerCoefficient` 108 ·
`existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` 108 ·
`apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` 107 ·
`isFactorizableTestFn_sum_mul_comp_mul_mul` 98 · `whittakerCoefficient_sum_smul_of_continuous` 86 ·
`exists_maximalCompactAway_subset_of_mem_nhds_one` 80 · `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` 78 ·
`isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` 71 · `exists_isRightEquivariant_comp_subtype_eq_of_injective` 70 ·
`exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` 69 ·
`existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` 65 · `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` 62 ·
`isLocallyConstant_iwasawaShellIndex_and_measurable` 62 · `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` 55 ·
`isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` 51 · `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` 46 ·
`isCompact_rowIsometrySubgroup_detOne` 43 · `continuous_unipotentGL2` 28 · `exists_iUnion_centreCutSiegelSet_mem_nhds` 25 ·
`eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` 23 · `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` 21 ·
`constantTerm_add` 13 · `constantTerm_smul` 11

**`LocalIntertwining` (7 / 1,295).**
`integral_one_add_sq_cpow_neg_eq_GammaReal_div` 362 · `integrable_complexAtom_and_integrable_moebiusShift` 219 ·
`integrable_realAtom_and_integrable_moebiusShift` 179 · `tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` 170 ·
`tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` 147 · `exists_bound_norm_integral_mixedSpace_archAtom_prod` 116 ·
`integral_one_add_norm_sq_cpow_neg_eq_pi_div` 102

**`CuspidalConstituent` (6 / 1,288).**
`exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` 646 · `exists_isFactorizableTestFn_isArchBiFinite_conj` 245 ·
`continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` 154 ·
`forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` 148 · `isCuspConstituent_productionPinsOf_mono` 62 ·
`eq_of_isCuspConstituent_of_exists_mem_ne_zero` 33

**`WindowedSiegel` (2 / 668).**
`exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` 386 ·
`isCompact_centreCutSiegelSet_inter_heightCap` 282

**`CuspidalSpectrum` (2 / 379) — this set's successors.**
`exists_isArchBiFinite_flat` 304 · `isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` 75.
The second genuinely uses the subrep gate (`IsClosedCuspSubrep` 1, `IsCuspLift` 1, `cuspSubcarrier` 11,
`toCuspSubcarrier` 6 — declaration-level grep of its `S_` file); the first only *imports*
`Def_AutomorphicForm_CuspidalSpectrumSubrep` and uses none of its declarations (the import-only pattern
of the arch-type-span leaf, §5 of CARRY-FORWARD). Both need further premises before they can be
stated.

**`IsKfSmooth` (2 / 368).** `exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` 328 · `finite_smul_image_of_isCompact` 40

**`SmoothCuspRealizationAt` (2 / 280).** `isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` 199 ·
`whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` 81

**`RankinSelberg` (2 / 207).** `whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` 141 ·
`section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` 66

**Singletons (3 / 297).** `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` 189 ·
`IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` 78 ·
`IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` 30
