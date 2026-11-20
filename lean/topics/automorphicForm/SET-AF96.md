# SET-AF96 — the conductor-datum definition layers, and the five rows behind them

**Status: IN FLIGHT (2026-11-20).** Two waves. Wave 1 is the **definition layer** that the `padicK1`
span family has needed since SET-AF95 wrote down the `AdelicSpan` carrier — `fixedSubmodule` and the
newvector conductor, the `p`-adic principal congruence subgroups `K(pⁿ)`, and the compactness of
`GL₂(ℤ_[p])` — plus two smaller gates (`LanglandsTunnell.ArchPlace`, `AutomorphicForm.iwasawaShellIndex`)
and the two rows behind them. Wave 2 is the three rows the `padicK1` gates unblock.

Cut: **8 rows / 2,082 silo**, plus **5 definition-layer modules / 987 pin lines** as gates.

| # | order | kind | rows | silo | module |
|---|---|---|---|---:|---|
| A | the `p`-adic congruence subgroups `K(pⁿ)` | definition layer | — | gate | `RepTheory/LocalNewvector/GL2CongruenceSubgroup.lean` (new) |
| B | the conductor datum and the compact integral subgroup | definition layer | — | gate | `NumberTheory/LocalNewvector/ConductorDatum.lean`, `RepTheory/LocalLanglands/IntegralSubgroupCompact.lean` (new) |
| C | the `padicK1` span and the conductor bound | rows | 2 | 647 | `NumberTheory/LocalNewvector/AdelicSpanConductor.lean` (new) |
| D | the factorization bound of the lift | row | 1 | 921 | `LanglandsTunnell/WeightOneLiftFactorizationBound.lean` (new) |
| E | the determinant companion of the central character | row | 1 | 74 | `LanglandsTunnell/WeightOneLiftCentralDet.lean` (new) |
| F | the archimedean zeta dictionary | def + rows | 2 | 332 | `LanglandsTunnell/TateLocal/ArchPlace.lean`, `LanglandsTunnell/TateLocalZetaComparison.lean` (new) |
| G | the Iwasawa shell index | def + rows | 2 | 108 | `AutomorphicForm/Adelic/IwasawaShellIndex.lean`, `AutomorphicForm/Adelic/IwasawaShellInvariance.lean` (new) |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af96_read.json
```

| figure | before (AF95 landing) | after this set's scaffolds |
|---|---:|---:|
| `needed [F terminal]` | 445 / 212,664 | **437 / 210,582** † |
| ready rows | 12 / 3,072 | **13 / 4,538** |
| leaves | 74 / 21,398 | **68 / 20,311** |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |

The delta is the eight cut rows exactly (−8 nodes / −2,082 lines).

† These are the figures the read produced on 2026-11-20. The front-end under-credited two rows
(`AutomorphicForm.IsCuspidalFn.add`/`.smul`) until FR-0264, so a read with the fixed tool subtracts
**2 nodes / 25 lines** from every figure in this section; the set's own delta is unaffected. **Three rows become ready,
2,461 silo**, all of them AF-subject: `DihedralWeightOne.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm`
(**1,096**, 9 premises), `DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm`
(**1,003**, 9 premises) and `AutomorphicForm.setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure`
(**362**, 6 premises — the Iwasawa shell gate is its statement's vocabulary). That is the AF subject's
next block, and it is why the shelf re-read, not a shelf memory, opens the next scoping.

Note the shape of the AF subject on this shelf: after this set the ready AF rows are those three plus
`AutomorphicForm.IsCuspidalFn.add`/`.smul` (14 + 11) and the `AutomorphicForm` measure-theory leaves;
the rest of the shelf is the other columns (`WeierstrassCurve` 1,296, `GaloisRep` 495,
`ModularCurve`, `AlgebraicCurve`, `NumberField`).

## 1. Why this set is definition work first

The `padicK1` span family has been on the shelf for two sets and could not be written. The reason is
not a missing theorem but a missing *vocabulary*, three times over, and it is the FR-0049 lesson
(`needed = 1` is a premise claim, not a statement claim):

* `Definitions/Def_RepTheory_GL2CongruenceSubgroup.lean` (531 lines / 29 declarations) declares
  `FLT.SmoothVectors.gl2CongruenceSubgroup p n` — the principal congruence subgroup of `GL₂(ℚ_[p])`
  defined by the norm bound `‖g − 1‖ ≤ p⁻ⁿ` — with its open/closed, monotone, normal and
  neighbourhood-basis lemmas. The port's `LocalNewvector.congruenceK1` is a *different* subgroup
  (the matrix-entry condition over `ℤ_[p]`); it is not a substitute, and the row
  `AdelicSpan.exists_mem_span_fixed_padicK1_…` is stated over `fixedSubmodule (padicK1 q a)`, whose
  proof opens by relating the two. **Nothing of the pin module was ported.**
* `Definitions/Def_LocalNewvector_ConductorDatum.lean` (114 lines / 15 declarations) declares
  `fixedSubmodule`, `HasNewvectorConductor`, `centralGL`, `IsCentralCharacterRep` and the
  `padicK0`/`padicK1`-vs-`integralSubgroup` seam. SET-AF95A transcribed two of them `private` into
  `AdelicSpan.lean` to close two statements; this set ports the file and the refactor deletes the
  transcriptions (`AdelicSpan` now imports them — see §5).
* `Definitions/Def_LocalLanglands_IntegralSubgroupCompact.lean` (40 lines / 5 declarations) is the
  compactness of `GL₂(ℤ_[p])` that the span row's `CompactSpace U` instance needs.

The other two gates are the *statement* vocabulary of the wave-1 rows: `LanglandsTunnell.ArchPlace`
(the additive characters and the real/complex zeta integrals the two `…_eq_localZeta` rows are
stated with) and `AutomorphicForm.iwasawaShellIndex` (the shell index of the two Iwasawa rows).

## 2. The homes

| module | direction | note |
|---|---|---|
| `RepTheory/LocalNewvector/GL2CongruenceSubgroup.lean` | above `RepTheory/SmoothVectors` only | the subject is the `p`-adic congruence subgroup of `GL₂`, next to the port's other `LocalNewvector` congruence module |
| `NumberTheory/LocalNewvector/ConductorDatum.lean` | above `RepTheory/LocalNewvector/CongruenceSubgroupK1`, `GL2CongruenceSubgroup`, `RepTheory/LocalLanglands/IntegralSubgroup` | fixed vectors of a `GL₂(ℚ_[p])`-representation — local representation theory, the `LocalNewvector` home |
| `RepTheory/LocalLanglands/IntegralSubgroupCompact.lean` | above `RepTheory/LocalLanglands/IntegralSubgroup` | it extends `FLT.SpectralSide`, whose port home is `IntegralSubgroupOpen.lean` in the same directory |
| `NumberTheory/LocalNewvector/AdelicSpanConductor.lean` | above `AdelicSpan`, `ConductorDatum`, `GL2CongruenceSubgroup`, `IntegralSubgroupCompact`, `AdelicLevel/Level`, `AdelicDock/LocalEmbedding` | the span of the lift and its conductor — the `LocalNewvector` subject |
| `LanglandsTunnell/WeightOneLiftFactorizationBound.lean` | above `WeightOneLiftLevel`/`…NebentypusExists`/`…QCoeffConverse`, `AdelicSpan`, `ConductorDatum` | the family's naming; the pin's engines are the three AF94/AF95 preludes' |
| `LanglandsTunnell/WeightOneLiftCentralDet.lean` | above `WeightOneLiftCentralScalar`, `RatIdele/UnitResidue` | the central character of the lift, with the idèle-class character |
| `LanglandsTunnell/TateLocal/ArchPlace.lean`, `…/TateLocalZetaComparison.lean` | above `LanglandsTunnell/TateLocalZeta` | the archimedean local data and the dictionary with `localZeta` |
| `AutomorphicForm/Adelic/IwasawaShellIndex.lean`, `…/IwasawaShellInvariance.lean` | above `AutomorphicForm/Adelic/Basic`, `ConstantTerm`, `AdelicLevel/Level`, `AdelicLevel/HeckeGen`, `AdelicHaar/GeneralLinear`, `UnipotentQuotient` | the shell index and its invariance — the adèlic `AutomorphicForm` subject |

## 3. The instruments

`port_advise --nodes <the eight rows> --json build/set_af96_advise.json`, then
`port_plan --json build/set_af96_advise.json`:

* **substitute — 20 declarations / ≈194 lines already in the port.** Sixteen of them are the
  factorization row's private engines: eleven are public in `WeightOneLiftLevel`/`WeightOneLiftQCoeffConverse`
  (`coe_finComponent`, `glEq_of_forall_finComponent_eq`, `commute_of_finComponent_eq_one`,
  `mapMatrix_injective`, `exists_glMap_eq`, `natGenerator_padicPlace`, `eq_padicPlace_natGenerator`,
  `padicPlace_injective`, `valued_natCast_eq_of_factorization_eq`, `idealBound_ratLevel_eq_of_factorization_eq`,
  `algebraMap_intCast_apply_padicPlace_eq`), four are the `fn` family and were `private` in
  `WeightOneLiftNebentypusExists`, and one is `repZ'` against the port's `repZ`. The remaining four
  are the two `distribHaarChar_*` lemmas of the zeta rows, which the port holds at
  `NumberField.TateGlobal.ArchMulHaar{C,R}eal` with a different binder spelling.
* **Promotions (manager, this set).** The four `fn` declarations and the five `DescentSupportA`
  engines were `private` in `WeightOneLiftNebentypusExists` and `WeightOneLiftQCoeffConverse`; they are
  now public at the pin's names, both modules re-read `17 ok` and `6 ok` on the checker, and the
  factorization module imports them instead of re-proving ≈194 lines. `WeightOneLiftNebentypusExists`
  `dedup`/`move_dead` unchanged.
* **drags.** `0 helpers` on the zeta rows and on `IsCuspidalFn.add`/`.smul` (flat public surface: no
  private prelude to expect); the factorization row's row-local block is *all* helpers, which is why
  it is its own order.

`port_plan` on the same eight rows: **raw 2,082 S_ lines → 1,631 net new math lines** — 155 lines of
duplicate copies (removable by porting once), 127 boilerplate, 169 already in the port (147 tier-1
diffed, 22 tier-3 registered). The 22% gap is the two promotions plus the shared zeta prelude
(`port_plan` prices the zeta pair at 149 once-lines against 332 silo); the definition layers are
outside that slice and are not in its 1,631.

## 4. The gates

As SET-AF89–AF95 §5, unchanged:

1. `spec/check_port.py --force <module>` → 0 mismatch / 0 missing / 0 own; every row `ok`.
   The scaffolds already read **102 ok / 0 / 0 / 0** across the six row modules and **56 ok / 0 / 0 / 0**
   across the three wave-1 definition modules.
2. `scaffold_audit` → **complete** (the definition-layer modules must, since their wire is exactly
   their own surface; the row modules read complete too, with the rows `FOLDED`).
3. The module's own `lake build` under `flock`/`timeout`, silent at the project cap
   (`maxHeartbeats = 4000000`) and under `-DmaxHeartbeats=8000` (heartbeat probe pair in the header).
4. `#print axioms` on every row and the largest engines → `[propext, Classical.choice, Quot.sound]`.
5. `dedup.py --within --module` → 0 clusters, or the pin's own pairs kept with the reason.
6. `move_dead.py … --dry-run` → 0 declarations / 0 lines, or a **reported, not deleted** dead
   declaration whose liveness is the port's resolution (the AF94C/AF95C rule).
7. A `spec/` consumer zone with a real cross-module composition (no `#check`s); error count is the
   deliverable metric.

**One build rule carries the wave** (FR-0254): no scaffold keeps a bare `import Mathlib` — on this box
the Mathlib closure is 6.1 GB against 7 GB of RAM, so it never caches and costs ≈100 s wall per
elaboration (~1 s of user CPU), transitively. Narrowing it to the modules a file uses took
`IntegralSubgroupCompact.lean` from >115 s to 42 s, and it is statement-neutral.

**Two hard rules carried in.** A `check_port` mismatch on a *statement* is a scaffold defect: report
it and keep the pin's own text (FR-0246). And the token `spec-pin` followed by a colon must never
appear in header prose (FR-0247) — the deferral is named without it.

## 5. The landing

| order | module | lines | decls | checker | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| A | `RepTheory/LocalNewvector/GL2CongruenceSubgroup.lean` | **788** | 36 (36 public) | **36 ok / 0 / 0** | clean (36 swept) | 0 | 0 / 0 | 8,000 / 4,000 |
| B | `NumberTheory/LocalNewvector/ConductorDatum.lean` | **253** | 15 (15) | **15 ok / 0 / 0** | clean (15) | 0 | 0 / 0 | 2,000 / 1,000 |
| B | `RepTheory/LocalLanglands/IntegralSubgroupCompact.lean` | **113** | 5 (5) | **5 ok / 0 / 0** | clean (5) | 0 | 0 / 0 | 1,000 / 500 |
| C | `NumberTheory/LocalNewvector/AdelicSpanConductor.lean` | **810** | 19 (19) | **19 ok / 0 / 0** | clean (19) | 0 | 0 / 0 | 25,000 / 12,500 |
| D | `LanglandsTunnell/WeightOneLiftFactorizationBound.lean` | **943** | 29 (15 public / 14 private) | **15 ok / 0 / 0** | clean (15) | 1 pin-own | 0 / 0 | 25,000 / 12,500 |
| E | `LanglandsTunnell/WeightOneLiftCentralDet.lean` | **161** | 3 (3) | **3 ok / 0 / 0** | clean (3) | 0 | 0 / 0 | 4,000 / 2,000 |
| F | `LanglandsTunnell/TateLocal/ArchPlace.lean` | **222** | 26 (26) | **26 ok / 0 / 0** | clean (26) | 0 | 0 / 0 | 1,000 / 500 |
| F | `LanglandsTunnell/TateLocalZetaComparison.lean` | **279** | 13 (13) | **13 ok / 0 / 0** | clean (13) | 2 pin-own | 0 / 0 | 1,000 / 500 |
| G | `AutomorphicForm/Adelic/IwasawaShellIndex.lean` | **448** | 23 (23) | **23 ok / 0 / 0** | clean (7 swept) | 0 | 0 / 0 | 5,000 / 2,500 |
| G | `AutomorphicForm/Adelic/IwasawaShellInvariance.lean` | **227** | 3 (3) | **3 ok / 0 / 0** | clean (3) | 0 | 0 / 0 | 5,000 / 2,500 |

**4,244 lines, 0 `sorry`, no linter option, no `haveI`/`letI`.** The manager re-read the checker over
all ten modules (**158 ok / 0 mismatch / 0 missing / 0 own**) and `#print axioms` over all eight rows
(`[propext, Classical.choice, Quot.sound]`) independently of the orders' reports; `scaffold_audit`
reads `complete` on all ten.

**The definition layer is open.** `gl2CongruenceSubgroup`, `fixedSubmodule`, `HasNewvectorConductor`,
`centralGL`, `IsCentralCharacterRep`, `isCompact_coe_integralSubgroup`, `LanglandsTunnell.ArchPlace` and
`AutomorphicForm.iwasawaShellIndex` are public, wired modules now; `AdelicSpan.lean` imports
`ConductorDatum` instead of carrying two `private` transcriptions (still `27 ok`), and the nine engines
of the factorization row are public in the two AF95 preludes (the promotion in §3).

**Three `spec/` consumer zones, each silent, no `#check`s:**

* `spec/LocalNewvectorSetAF96Consumer.lean` — the set's money composition: the conductor bound gives
  `c ≤ M.factorization q` with a nonzero `padicK1 q c`-fixed vector, the factorization row reads that
  vector as `M.factorization q ≤ c`, and `hasNewvectorConductor_unique` says the index is the only
  one — the conductor of the lift *is* the level's `q`-adic valuation.
* `spec/LanglandsTunnellSetAF96EConsumer.lean` — the two centre laws agree at the pin, and the
  eigenvalue is multiplicative across two places through `dirichletIdeleChar`'s `map_mul`.
* `spec/AutomorphicFormSetAF96Consumer.lean` — the shell index of a rational-centre-unipotent element
  times the Hecke generator at `v` is the index plus one; and the archimedean Gamma factors are ratios
  of *local* zeta functions.

**Four instrument findings, all in [frictions.md](../../logs/frictions.md):** FR-0252 (a row's
statement must be emitted from the pin `S_` file's `solution`, not from the `Theorems` wrapper — the
wrapper's unqualified names do not hash to the pin's, and the row reads `MISSING`); FR-0253
(an inline `@[simp] theorem` is not a declaration start for a chunk-based generator; read
`statement_db.parse_file` instead); FR-0254 (a bare `import Mathlib` costs ≈100 s wall per elaboration
here and poisons every importer — narrowed, the ten modules elaborate in 6–34 s); FR-0255 (narrowing
surfaces the deprecations the wall was hiding: `zero_le'` → `zero_le`, `if_pos`/`if_neg`, `haveI`); and
FR-0256 (`flock /tmp/…` is inert in this harness — each call gets a fresh `/tmp` — and a
`timeout`-killed `lake build` leaves the target's oleans *deleted*, which blocked two orders).

**One real defect the scaffold hid**, found by order C: the pin's `main` carries three
`haveI`/`letI` sites that no scaffold could see (the body was `sorry`); they are `have`/`let` now,
statement-neutrally. Order D likewise found the pin's own `private isUnit_entry_of_lowerLeft_mem` dead
in the pin and deferred it by line range rather than deleting it silently.

## 6. Not cut — named and deferred (FR-0040)

Ready rows left on the shelf (the other columns, and the AF tail):

* `WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two` (697),
  `WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero` (599),
  `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` (495),
  `NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const` (108),
  `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` (59),
  `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36),
  `ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion` (34),
  `ModularCurve.rep_tateModule_jOne_comm` (24), `AutomorphicForm.IsCuspidalFn.add` (14),
  `AutomorphicForm.IsCuspidalFn.smul` (11) — the last two are a 25-line AF tail, deferred to the next
  AF set (they are `IsCuspidal` space structure, a different story from the conductor).
* **Withheld** by the FR-0044 guard (a direct premise in the pruned set, so the pin proof cannot be
  transcribed): `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` (327),
  `ModularCurve.moduleFinite_padicInt_tateModule_jOne` (283),
  `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` (126),
  `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95). These are the prunable
  subject's work, not this column's.
* AF-subject leaves not cut (the next AF set's shelf):
  `LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers` (45, project fan-in 116),
  `…forall_eq_one_and_exists_ne_one_of_addCharLevel` (37, 100),
  `…tateFourier_indicator_setOf_valued_sub_le` (149, 21),
  `AutomorphicForm.isUnitFactorizableAbove…` (78), `existsUnique_bruhatRepresentative…` (65),
  `ModularForm.exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le` (195),
  `ModularForm.exists_levelOne_coe_eq_sum_slash` (156),
  `ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne` (94),
  `ModularForm.exists_levelOne_qExpansion_eq_map_int_constantCoeff_one` (62),
  `ModularForm.exists_coe_eq_of_levelOne` (22),
  `HaarQuotient.lintegral_density_mul_eq_one` (170, 39).
* The `NumberField.StandardAddChar.*` leaves (10, 60–70 lines each, project fan-in up to 59) are the
  additive-character supplements the Tate rows were proved against; they are the natural companion
  of the `TateLocal` leaves above, and are deferred whole.

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af96_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 445 / 212,664 | **437 / 210,582** † |
| ready rows | 12 / 3,072 | **13 / 4,538** |
| leaves | 74 / 21,398 | **68 / 20,311** |
| withheld | 4 / 831 | 4 / 831 |

The set consumed exactly its eight rows (−8 nodes / −2,082 lines); the landed read equals the
after-scaffold read, which is the check that the scaffolds' wires were read as ported from the start
and that no landing silently un-wired anything. The three rows that became ready because of the set
are §0's: the two lift rows (**1,096** and **1,003**) and the shell-measure row (**362**). The other
columns are untouched: `WeierstrassCurve` 1,296, `GaloisRep` 495, `ModularCurve`, `AlgebraicCurve`,
`NumberField`, `TateCurve`; the four withheld rows stay withheld (they are the pruned subject's work).

