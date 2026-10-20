# `kw` rectification

**Status:** rectified, checker-green and built. All 33 offending modules are wired
and renamed; `check_port --all` is `1815 ok, 0 mismatch, 0 missing, 4 own, 0 kw`
over 44 modules, and a targeted build of the 33 modules completed successfully
(no tree build). The residual `kw*`/`Kw*` names are gone from the port, the
checker's `norm` treats both forms (including middle `_kw`/`_Kw` tokens) as noise,
and the remaining work is documentation and a few post-processing naming choices.

This is the record of the sweep that produced the scope. It covers the three
generated-name families transcribed from the pinned FLT (`aa2d8b3`): the lower-case
`kw_` and `kwX` families, and the capital-`Kw` family, together with the modules,
consumers, documentation references and checker changes.

## 1. Why

FLT uses `kw`-prefixed names as collision tokens for its generated blocks. The
port transcribed a subset of them verbatim; they are not mathematics and should
not be part of the public API. They occur in three shapes:

* `kw_…` — the pin's promotion/collision convention (`kw_g₂_ofTau`, `kw_mlc_…`);
* `kwX…_…` — no underscore after `kw` (`kwF4R1V384a_…`, `kwTateRR3_…`, `kwHgfV352_…`);
* `Kw…` — the capital form (`KwD5BetweenCurves…`, `KwF4gRRTate`, `KwNo6Pin`,
  `KwVeluOrderTwo…`, `KwIsogenyEndDatum…`, `KwFunctionFieldTensor…`, …).

The statement checker's `norm` treats the lower-case forms as noise; the
rectification added the same erasure for the capital `Kw` prefix and a small
canonical-name map for the renames that deliberately leave the `norm` image. The
port-side name guard rejects residual names of both cases, and the legacy checker
no longer owns these modules.

## 2. Scope

The counts below are the pre-rename inventory (the generated names as they were
found); they are the record of the sweep, not the current declaration counts.

| family | declarations | public | private | modules |
|---|---:|---:|---:|---:|
| `kw_` | 433 | 339 | 94 | 22 |
| `kwX` | 112 | 84 | 28 | 14 |
| `kw*` total | **545** | 423 | 122 | **29** |
| `Kw` (genuine) | **373** | 356 | 17 | **25** |

The `kw*` batch is 29 modules; the `Kw` family adds 4 modules outside that batch.
The combined batch is 33 modules. The `Kw` family overlaps the 29: 21 of the 29
modules carry a `Kw` member (319 declarations, 20 namespaces); the other 8 are
`kw*`-only. The four extra modules carry 54 `Kw` declarations and three
namespaces.

The 29 `kw*` modules split by character:

* **15 `kw_`-only modules** — the plain strip is checker-safe (`norm` erases
  `kw_`; `stripped_source` matches the pin).
* **7 mixed `kw_`/`kwX` modules** — `RestrictAlong`, `LatticeIndex`,
  `PlaceCompletion`, `TraceCompat`, `KFamily`, `CompletionTraceSum`,
  `TranslationAlgEquiv`.
* **7 `kwX`-only modules** — `Agreement`, `CommFinite`, `ChainRule`, `Prelude`,
  `TraceCompletionCommute`, `TateResidueCurrency`, `P1/DivPow`.

The five `kw_`-only modules whose `kw_` tokens are meaningful (`OrderTwoMap`,
`PointEndSubring`, `Velu/Engine`, `CyclicQuotientJInjective`, `KCotrace`) are the
plain-strip pilot; `OrderTwoMap` and `PointEndSubring` also carry capital-`Kw`
names (`KwVelu…`, `KwIsogenyEndDatumOfNonzeroEnd`) for the `Kw` pass. The `velu*`, `pointEnd`, `restrictAlong`, `ord`,
`oddOrderSummingSet…`, `hnfPoint`, `dualEndData`, `datumKernelDegreeFace`,
`addXFun`/`addYFun`, `isSeparable`, `translateFF`, `phiTau`, `nsmul`, `degree`,
`exists`, `card`, `map`, `mem`, `not` names are real and stay.

The junk tokens erased by `norm` (`KW_JUNK_TOKENS`) are:

`surgehgf4`, `surge`, `hgf4`, `dcao`, `ffgc`, `fdn2`, `qephod`, `hend21`,
`hk5f`, `taseq`, `kqe`, `hID`, `pck`, `qtzz`, `hH2f`, `hH2`, `hfgkd`, `ktd`,
`cfe`, `hBC`, `hu5c`, `hKD`, `ipfd`, `HZZ`, `mlc`, `es`, `no6`, `iucz`,
`vdcoog`, `affod`, `vdc`.

Step labels are deliberately **not** in that list: `_s2`, `_s6`, `_s12`,
`_s17` (46 declarations in 6 modules) mark pin proof steps and are left alone,
as are the residual `WLightS*.S_…` and `M4a…` namespaces.

## 3. The 33 modules

Counts: `lines` and `public` are the module's lines and public declarations;
`kw_` is the public/private `kw_` count; `kwX` is the lower-case `kwX` count; `Kw`
is the capital family (namespaces plus capital-`Kw` declarations; it overlaps the
`kwX` names that live inside a `Kw` namespace). `wired` means the module has its
`spec-pin:` header and is checked by `check_port.py`; all 33 are out of the legacy
`PORT_FILES`.

| module | lines | public | `kw_` | `kwX` | `Kw` | status |
|---|---:|---:|---:|---:|---:|---|
| `WeierstrassCurve/IsogenyEndDatum/DualEndData.lean` | 3930 | 143 | 74/0 | 0 | 8 | wired |
| `WeierstrassCurve/Velu/RestrictAlong.lean` | 2169 | 100 | 43/1 | 6 | 1 | wired |
| `Elliptic/PeriodPair/LatticeIndex.lean` | 1250 | 63 | 43/0 | 2 | 3 | wired |
| `AlgebraicCurve/Tate/Agreement.lean` | 3177 | 96 | 0/0 | 30 | 91 | wired |
| `WeierstrassCurve/Velu/OddOrder.lean` | 647 | 30 | 28/0 | 0 | 0 | wired |
| `WeierstrassCurve/Isogeny/KernelBaseChange.lean` | 1420 | 35 | 27/0 | 0 | 3 | wired |
| `AlgebraicCurve/Defs/PlaceCompletion.lean` | 550 | 31 | 23/0 | 3 | 2 | wired |
| `AlgebraicCurve/Tate/TraceCompat.lean` | 2723 | 73 | 6/0 | 16 | 66 | wired |
| `Elliptic/PeriodPair/PrimCosetReps.lean` | 507 | 25 | 22/0 | 0 | 1 | wired |
| `WeierstrassCurve/Isogeny/KernelCyclicTransfer.lean` | 473 | 19 | 16/0 | 0 | 1 | wired |
| `Elliptic/PeriodPair/HoloLift.lean` | 932 | 20 | 15/0 | 0 | 4 | wired |
| `AlgebraicCurve/Tate/CommFinite.lean` | 721 | 48 | 0/0 | 14 | 45 | wired |
| `WeierstrassCurve/Isogeny/NatCard.lean` | 807 | 40 | 13/0 | 0 | 3 | wired |
| `WeierstrassCurve/IsogenyEndDatum/Engine.lean` | 2299 | 131 | 12/0 | 0 | 2 | wired |
| `AlgebraicCurve/ResidueTheorem/KFamily.lean` | 898 | 30 | 4/0 | 4 | 3 | wired |
| `WeierstrassCurve/Velu/MapEquation.lean` | 444 | 20 | 4/0 | 0 | 0 | wired |
| `WeierstrassCurve/IsogenyEndDatum/PointEndSubring.lean` | 417 | 23 | 3/0 | 0 | 1 | wired |
| `WeierstrassCurve/IsogenyEndDatum/RestrictAlongAdd.lean` | 2505 | 102 | 3/0 | 0 | 0 | wired |
| `AlgebraicCurve/Defs/TateResidueCurrency.lean` | 418 | 27 | 0/0 | 2 | 20 | wired |
| `AlgebraicCurve/P1/DivPow.lean` | 686 | 55 | 0/0 | 2 | 0 | wired |
| `AlgebraicCurve/Tate/ChainRule.lean` | 713 | 42 | 0/0 | 2 | 36 | wired |
| `AlgebraicCurve/Tate/Prelude.lean` | 423 | 21 | 0/0 | 2 | 21 | wired |
| `WeierstrassCurve/Velu/Engine.lean` | 2338 | 189 | 2/0 | 0 | 0 | wired |
| `AlgebraicCurve/ResidueTheorem/KCotrace.lean` | 761 | 42 | 1/0 | 0 | 0 | wired |
| `AlgebraicCurve/Tate/TraceCompletionCommute.lean` | 125 | 2 | 0/0 | 1 | 1 | wired |
| `AlgebraicCurve/Tate/CompletionTraceSum.lean` | 703 | 1 | 0/3 | 20 | 3 | wired |
| `WeierstrassCurve/IsogenyEndDatum/TranslationAlgEquiv.lean` | 1124 | 2 | 0/36 | 8 | 0 | wired |
| `WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` | 471 | 1 | 0/3 | 0 | 0 | wired |
| `WeierstrassCurve/Velu/OrderTwoMap.lean` | 1513 | 1 | 0/51 | 0 | 4 | wired |
| `AlgebraicCurve/LocalResidue/Instance.lean` | 1695 | 121 | 0 | 0 | 31 | wired |
| `WeierstrassCurve/Isogeny/IntermediateField.lean` | 1127 | 19 | 0 | 0 | 12 | wired |
| `WeierstrassCurve/Isogeny/BaseChange.lean` | 1169 | 73 | 0 | 0 | 6 | wired |
| `WeierstrassCurve/IsogenyEndDatum/Vocabulary.lean` | 644 | 6 | 0 | 0 | 5 | wired |

The four extra modules:

* `LocalResidue/Instance.lean` — `KwNo6Pin` (28 public) and `KwNo6Section`
  (3 public). The `Agreement` module has an empty `KwNo6Pin`/`KwNo6Section`
  namespace and uses the `Instance` `KwNo6Pin` names (`aCoeff`, `resStar`,
  `clearedHat`) unqualified; the namespace is shared by both modules, so the
  rename has to hit both and the `open`/empty-namespace lines.
* `Isogeny/IntermediateField.lean` — 12 capital-`Kw` declarations
  (`KwIotaCanonicalFinrank`, `KwIotaPinned…`, `KwIsogenyEndDatumSubfieldDescent`,
  `…''` variants, …); no exact external use was found.
* `Isogeny/BaseChange.lean` — 6 capital-`Kw` declarations
  (`KwFunctionFieldTensorIsDomainGeneral`, `…NoAC`,
  `KwIsogenyEndDatumBaseChangeAlongGeneral`, `…NoAC`,
  `KwTensorFracIotaFinrankSeamGeneral`, `…NoAC`); four are used by
  `spec/BaseChangeConsumer.lean`.
* `IsogenyEndDatum/Vocabulary.lean` — the private `KwNo3aHbadRiqsucrA1a`
  namespace (5 declarations, `no3ahbad_riqsucr_a1a_…`); internal.

## 4. `Kw` family detail

* 23 `Kw` namespaces in total: 20 in the 29 (nine empty; eleven non-empty) and
  three outside (`KwNo6Pin`, `KwNo6Section`, `KwNo3aHbadRiqsucrA1a`).
* 76 capital-`Kw` declaration last names: 57 in the 29 and 19 outside (18 genuine
  in `IntermediateField`/`BaseChange` plus the `ArchInfra` false positive).
* The genuine `Kw` family is 373 declarations: 319 in the 29 + 54 outside
  (31 `Instance`, 12 `IntermediateField`, 6 `BaseChange`, 5 `Vocabulary`).
* The 20 namespaces in the 29 hold 283 declarations; the 11 non-empty ones are
  `ModularCurve.KwF4gRRTate` (118), `KwF4gRRTate` (68), `KwTateRR3` (60),
  `KwF4R1V410a` (19), `KwF4R1V384a` (4), `KwNo6HrouteR` (4),
  `ModularCurve.KwF4R1V391a` (3), `KwOdaDHDR` (3), `KwF4R1V386a` (2),
  `ModularCurve.KwTateRR3` (1), `KwF4R1V394a` (1). The nine empty ones
  (`KwSmoothIrredRelDimConstantEngine`, `KwNo6HrouteS/V/Y/Z`,
  `KwNo6Pin`/`KwNo6Section` in `Agreement`, `KwF4R1V392a`,
  `KwF4R1V391a` in `Agreement`) can simply be dropped.

**False positives.** `AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean`
has `abbrev Kw (w : InfinitePlace F) : Type := rowIsometrySubgroup₀ w.Completion`
— a meaningful abbreviation, not a family name; `RepTheory/TypeReproducer.lean`
has a type variable `{Kw Kc G : Type*}`. Both are excluded. The family matcher
requires an uppercase/digit immediately after `Kw`, so the exact `Kw` is not
caught.

## 5. Consumers and documentation

Six `spec/` consumer files use the 29's capital-`Kw` API:

* `KernelBaseChangeConsumer.lean` — `KwD5BetweenCurvesHoloLift`,
  `…FFSeamBaseChange`, `…KerTransportAlongEmbed`;
* `KernelCyclicTransferConsumer.lean` — `KwD5BetweenCurvesPMOPConjKerEquiv`;
* `PeriodPairHoloLiftConsumer.lean` — `KwD5BetweenCurvesHoloLift`,
  `…LocallyHoloLift`, `…CocountableHoloLift`, `…CocountableAffineHoloCoords`,
  `…CocountableAffineHoloCoordsWeak`;
* `PeriodPairLatticeIndexConsumer.lean` — `KwD5BetweenCurvesIndexDual`,
  `…PointHomSublatticeCyclic`, `…KerQuotEquivBC`;
* `PeriodPairPrimCosetConsumer.lean` — `KwSublatticeQuotientZZTransport`;
* `BaseChangeConsumer.lean` — the four `BaseChange` names
  (`KwFunctionFieldTensorIsDomainGeneral`, `…NoAC`,
  `KwIsogenyEndDatumBaseChangeAlongGeneral`, `…NoAC`).

No consumer uses the 20 `Kw` namespaces by name; their only external references
are documentation. The `Agreement`/`Instance` `KwNo6Pin` coupling is the one
cross-module namespace dependency. The `IntermediateField` twelve and the
`Vocabulary` five have no exact external uses; two of the six `BaseChange` names
are unused outside their module.

Documentation references: 377 `Kw` token occurrences — 152 in
`lean/topics/velu`, 148 in `lean/topics/riemannRoch`, 52 in `lean/logs`,
22 in `math` (021, 022, 023) and 3 in `studies`. The `math/` notes are
user-facing; the topics/logs are work orders and audits. The pin's `Theorems/`
wrappers use the same names (for example
`ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers` and
`ModularCurve.KwNo6Pin.isLocalRing_completion`), so they are pin names, not
port-only inventions; the rename is port-side, and the checker's `Kw` statement
mapping belongs to the rename plan.

## 6. Checker state

The lower-case `norm` matcher (`spec/old_check_stmts.py`):

* `KW_PREFIX_RE` — `kw` + word characters + `_`, or a standalone `kwWord`;
* `KW_JUNK_TOKENS` — the generated segments above, erased repeatedly after the
  `kw_`/`kwX` prefix;
* step labels are not erased.

The capital name guard and its statement erasure:

* `KW_FAMILY_RE` — a `Kw` segment followed by an uppercase/digit, matching the
  `KwD5…`/`KwF4…`/`KwTate…`/`KwNo6…` namespaces and declarations; the exact
  `Kw` abbreviation is not matched. This remains the port-side **name policy**.
* `KW_GENERATED_RE` — the generated block token goes as a unit:
  `KwF4gRRTate` → `Tate`, `KwF4R1V384aCompletion…` → `Completion…`,
  `KwTateRR3Cohen…` → `Cohen…`, `KwNo6Pin` → `Pin`, `KwD5Between…` → `Between…`.
  A namespace that becomes empty (`KwF4R1V…`, `KwTateRR3`, `KwOdaDHDR`,
  `KwNo3a…`) disappears with its dot.
* `KW_FAMILY_PREFIX_RE` — the remaining generic `Kw` prefix for names that keep
  their suffix (`KwIsogenyEndDatum…` → `IsogenyEndDatum…`, `KwVelu…` → `Velu…`).
  The exact `Kw` abbreviation is untouched.
* `CANONICAL_NAMES` — the checker's rename map. The ambiguity fixes are not the
  `norm` image of the old name (`charFree` ×7, `proved` ×4, `map_eq` ×2,
  `axiomAnchor` ×3, `zero`/`some_of_mem`/`some_of_ne`, the `HZZ` family, the
  embedded `kwVelu…` names, `LocalResiduePin`/`Section`), so the map puts the port
  spelling back to the pin's normalised spelling before hashing. It is applied
  after the prefix erasures. This is a checker map, not an in-module marker.
* the selftest is 56 assertions, including the `kw*`, `Kw`, middle-token and
  canonical-map matchers.

The port-side guard (`spec/check_port.py`):

* every public or private declaration of a wired module is checked for
  `KW_PREFIX_RE` on its last name and `KW_FAMILY_RE` on its full name;
* a hit is reported `KW-NAME`, counted as `kw`, and fails the module; the `kw`
  count is in the module line, the cached summary, `--timestamps`, `--json`, the
  total, and the exit status;
* after the rename the 33 modules are `1590 ok, 0 mismatch, 0 missing, 4 own,
  0 kw`. `check_port --all` is `1815 ok, 0 mismatch, 0 missing, 4 own, 0 kw` over
  44 wired modules.
* the four `own` declarations are the port-own base-change helpers with no exact
  pin declaration: `ModularCurve.tensorUnit`, `tensorUnit_apply`,
  `bcTensorFracIotaFinrank` and `bcTensorFracIotaSeam`. They carry `-- own:`
  markers; they are tier 2, not diffed.

The legacy checker (`spec/old_check_stmts.py`):

* `PORT_FILES` is 584 modules: the 33 rectified modules are out; the `SOURCES`
  list is untouched.
* the full run after the removal was `8,881 statements identical (656 promoted,
  17 renamed), 0 mismatched, 0 missing, 37 own, 294 registered-unwired,
  9,212 port declarations checked` over 584 modules.
* the corpus was rebuilt (`spec/statement_db.py build`) after the `norm` change;
  the new checker and the register carry the new stamp.

The register (`spec/unwired_register.py`, generated, git-ignored) lists
**137 modules / 4,136 public declarations / 3,830 with a pin original**; the 33
rectified modules no longer appear, because their `spec-pin:` lines make them the
new checker's responsibility.

The hash: the corpus's `nhash` is still a 20-hex sha1 of the normalised
statement; the normalised text is not stored (the TSV's `signature` column is the
raw one). The decision is to keep the hash for now and revisit; a text tie-break
would need a stored `stmt` column or an on-demand re-parse.

## 7. The legacy removal and the coverage gap

The 33 offending modules are out of `PORT_FILES`, wired with `spec-pin:` headers,
and renamed. The temporary gap is closed: `check_port --all` reports no mismatch,
no missing statement and no residual `kw` name. The four `own` declarations are
the only declarations outside the pin diff, and each names its reason. The
register no longer lists the 33. The pilot `PointEndSubring` is green too: its
`KwIsogenyEndDatumOfNonzeroEnd` is now `IsogenyEndDatumOfNonzeroEnd`.

## 8. The rename as applied

The base rule is the `norm` image, then a small exception table.

* **`kw_` / `kwX`** — target = `norm(old)`: the `kw`/junk prefix is gone and the
  meaningful suffix stays (`kw_mlc_hrtCharP9_foo` → `hrtCharP9_foo`,
  `kwF4R1V384a_foo` → `foo`, `kwVeluPointMap` → `VeluPointMap`). This covers 545
  declarations; the checker needed no map for them because `norm` already erased
  the old spelling.
* **Ambiguity fixes** — the cases where the mechanical image is empty, duplicate or
  unhelpful:
  * `kw_HZZ`/`_index`/`_map_eq` → `sublatticeCoords`/`sublatticeCoords_index`/
    `sublatticeCoords_map_eq`;
  * the seven private `kwTISD…_charFree` → `tisdCharFree{α,β,γ,δ0,δ1,δ2,δY}`;
  * the three `…_axiomAnchor` → private `axiomAnchor_hBC`,
    `axiomAnchor_hfgkd_ktd`, `axiomAnchor_pck`;
  * the four `…_proved` → `pmopConjKerEquiv_proved`, `ffSeamBaseChange_proved`,
    `kerQuotEquivBC_proved`, `sublatticeQuotientZZTransport_proved`, and
    `…_proved_core` → `pmopConjKerEquiv_proved_core`;
  * the two `…_map_eq` → `kerQuotEquivBC_map_eq`, `sublatticeCoords_map_eq`;
  * `kwVeluPointMap_{zero,some_of_mem,some_of_ne}` →
    `VeluPointMap_{zero,some_of_mem,some_of_ne}`;
  * the embedded `kwVelu…` theorem names → `Velu…` spellings;
  * the colliding `kw_ffgc_adicValuation_algebraMap` →
    `adicValuation_algebraMap_ramificationIndex`;
  * the private/public collisions exposed by the build: `ModularCurve.scale` →
    `sublatticeIndex_scale`, `point_infinite` → `point_infinite_charFree` (the
    char-free NatCard theorem), `Δ_ne_zero_of_isElliptic` →
    `Δ_ne_zero_of_isElliptic_local`, `completionTraceSum_of_isSeparable` →
    `completionTraceSum_of_isSeparable_aux`, `hDDTerm` → `hDDTerm_velu`.
* **Checker map** — the ambiguity fixes are recorded in `CANONICAL_NAMES`, so a
  statement that mentions one of them puts the new spelling back to the pin's
  normalised spelling before hashing. This is the rename exemption the user chose
  over per-declaration markers.
* **`Kw`** — the generated capital token is removed as a unit, not just its `Kw`
  head: `KwF4gRRTate` → `Tate`, `KwF4R1V384aCompletion…` → `Completion…`,
  `KwTateRR3Cohen…` → `Cohen…`, `KwHgfV352Completion…` → `Completion…`,
  `KwD5BetweenCurves…` → `BetweenCurves…`, `KwDCAO…` → `…`. Namespaces whose
  generated token is the whole name (`KwF4R1V…`, `KwTateRR3`, `KwOdaDHDR`,
  `KwNo3a…`) are dropped and their declarations move to the parent; the shared
  `KwNo6Pin`/`KwNo6Section` become `LocalResiduePin`/`LocalResidueSection`, and
  `KwNo6Hroute*` becomes `Hroute*`. The generic `Kw` is dropped where the suffix
  is meaningful (`KwIsogenyEndDatum…` → `IsogenyEndDatum…`, `KwVelu…` → `Velu…`).
  The exact `Kw` abbreviation (`ArchInfra`) and the `RepTheory/TypeReproducer`
  variable are untouched.
* **Subfamily tokens** — `hH2c`/`hH2d`/`hH2e` were added to `KW_JUNK_TOKENS`
  (all `hH2a…z`), and the three HoloLift declarations lost the prefix. Their
  local hypotheses keep the names `hH2c`/`hH2d`/`hH2e`/`hH2f`: renaming them
  changed the checked statements, and the junk erasure already makes them match
  the pin.
* **Middle tokens** — `kw`/`Kw` after an underscore is a residual too. The 12
  `…_kwVelu…` theorem names and the 12 `Piece_KwVelu…` section names were
  renamed; `KW_PREFIX_RE`/`KW_FAMILY_RE` now also match after `_`, so a future
  middle token fails the guard.
* **Checker-invisible declarations** — the 17 `scoped`/`local instance`s that
  `DECL_RE` cannot see (e.g. `kwF4R1V410a_subsingletonHeightOneSpectrumDVR`,
  `kw_charZero_end_point`, `kwLatticeToAddSubgroupFree`) were renamed too.
* **Left alone** — step labels `_s2`/`_s6`/`_s12`/`_s17`, the
  `WLightS*.S_…`/`M4a…` namespaces, and the `s17` stubs (`pck_s17`, `hBC_s17`,
  `kerTransport_s17`), which are not `kw` names.

## 9. Work order

1. **Pilot green** — done: `KwIsogenyEndDatumOfNonzeroEnd` →
   `IsogenyEndDatumOfNonzeroEnd`; the pilot is green.
2. **Headers wired** — done: all 33 modules carry their `spec-pin:` lines.
3. **Lower-case pass** — done: the 545 `kw_`/`kwX` declarations, including the 17
   checker-invisible instances, are renamed.
4. **Capital `Kw` pass** — done: namespaces and declarations, with the checker
   map and the six `spec/` consumers updated.
5. **Consumers and docs** — the six `spec/` consumers are updated; the `math/`
   notes and the topics/logs still carry the old spellings and are the remaining
   documentation sweep.
6. **Close-out** — `PORT_FILES` 584, `check_port --all` green, the corpus rebuilt,
   the register current, the hash decision unchanged.

## 10. Risks and open items

* No tree build was run. A targeted build of the 33 modules (dependency closure)
  completed successfully, so the Lean name-resolution collisions the textual
  checker cannot see are covered for this batch.
* The generated capital block labels are gone. The remaining names are the
  meaningful suffixes (`Tate…`, `BetweenCurves…`, `HrouteR`, `LocalResiduePin`,
  `IsogenyEndDatum…`); a later post-processing pass can still give the public ones
  nicer names, with `CANONICAL_NAMES` extended in the same change.
* The rename was textual, so module docstrings that say `Pin <new name>` now cite
  the port spelling rather than the pin original. The documentation sweep should
  restore the pin name wherever the sentence is about provenance.
* The four `own` declarations are tier 2 and not diffed; they are the port-own
  base-change helpers with no exact pin declaration.
* `CANONICAL_NAMES` is part of the checker's definition of "the same statement";
  any later rename of one of its keys must update it in the same change.
* The `s17` stubs and the hash decision are untouched.
