# Mathlib-first substitution audit — the phase-3.1 residue instance (P3.1)

**Method:** `lean/porting-playbook.md` §2.2 (audit the route, mathlib first), after
the phase-1/2 templates [`AUDIT-mathlib.md`](AUDIT-mathlib.md) and
[`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Inventory:
[`tools/deps/build/p3_1_inventory.txt`](../../../tools/deps/build/p3_1_inventory.txt);
`port_advise` outputs
[`rt_completion_advise.txt`](../../../tools/deps/build/rt_completion_advise.txt) and
[`rt_instance_advise.txt`](../../../tools/deps/build/rt_instance_advise.txt)
(claims re-verified independently below).

Sources, in pin order:

- [`Definitions/Def_AlgebraicCurve_PlaceCompletion.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean) (529 ln, 33 inventoried +
  1 un-inventoried instance)
- [`Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean) (2,173 ln, 131 decls)
- the third-party dependency
  [`Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean) (564 ln, 39 decls)

**Class convention** (unchanged from phases 1–2). SUBSTITUTE = the port can import
an existing declaration instead of proving the row: an already-landed port lemma or
a mathlib constant whose *type* is the pin's, or a pin `def`/`abbrev`/instance whose
body is `rfl`-equal to a mathlib/port term. PROOF-INGREDIENT = the statement is
bespoke (it mentions pin vocabulary) but the proof is a short assembly of named
mathlib/port lemmas. BESPOKE = a definition/structure/class/`Prop` introducing new
vocabulary, or an instance with no mathlib/port counterpart; these are the recorded
negatives and the real work.

**Scratch evidence:** `lean/ScratchAuditP31.lean` (gitignored) — the
machine-checked record, compiled from `lean/` with

```
timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP31.lean
```

**final run clean, exit 0, 4.61 s wall** (104 lines of `#check` output; no errors or
warnings). Probes A1–A5 (InlineSpecific/RankOne), B1–B4 (V2 restrict/coefficient
block), C (AdicCompletion/Hensel/AdjoinRoot ledger), D1–D2 (V2 carrier and
`exists_sub_mem_adicCompletionIntegers` without PlaceCompletion/InlineSpecific) and
E (drift ledger) all elaborated.

## 1. Summary — class counts per file

| pin file | SUBSTITUTE | PROOF-INGREDIENT | BESPOKE | rows |
|---|---:|---:|---:|---:|
| `Def_AlgebraicCurve_PlaceCompletion` | 6 | 21 | 7 | 34 |
| `Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2` | 10 | 95 | 26 | 131 |
| **total** | **16** | **116** | **33** | **165** |

**Inventory correction.** `p3_1_inventory.txt` counts 33 declarations in
`PlaceCompletion`, but the file opens with an **anonymous global instance** at
pin line 9

```lean
instance {K L : Type*} [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L] :
    Algebra O L where …
```

(the tool drops unnamed instances, as phases 1–2 noted it drops `class` and
`instance`). It is audited as row `0` of §3.1 and is classed BESPOKE; it is the one
design hazard this phase surfaces. Hence 34 rows, not 33. The V2 inventory (131) is
complete, including its 3 `private` helpers.

**Headline.** Two facts dominate this phase:

1. The **only** thing (1) or (2) needs from the unported `InlineSpecific` prelude is
   its `Valuation.IsRankOneDiscrete` instance, and mathlib `v4.34.0` already supplies
   that instance (`NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV`).
   Every other InlineSpecific declaration is not needed by (1) or (2) at all. The
   pin imports the 564-line prelude for one instance that is a two-line copy of
   mathlib.
2. V2's dependency on `PlaceCompletion` is **vacuous at the name level**: no
   `kw_ffgc_*`, `kwHgfV352_*`, `adicCompletion`, `algebraMapKIntegers` or
   `KwF4gRRTate` name occurs anywhere in V2 (grep count 0 for each). V2 builds its
   own `lg37_completion v = AdicCompletion (maximalIdeal v.toValuationSubring)
   v.toValuationSubring` directly on mathlib. So the InlineSpecific disposition for
   (2) is subsumed by (1), and the port need not import `PlaceCompletion` in the V2
   module.

## 2. The InlineSpecific question — precise verdict

**Verdict in one paragraph.** Of the 39 declarations in
`Def_DedekindDomain_AdicValuation_InlineSpecific.lean`, exactly one is consumed by
(1) in effect — the `Valuation.IsRankOneDiscrete` instance for
`(Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)`, required for
`kw_ffgc_rankOne_adicCompletion` to elaborate. That instance is in mathlib
`v4.34.0` as `NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV`
(`Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean:102`, in the generic
Dedekind-domain/`IsFractionRing` context, no finiteness hypothesis), and probe A1
finds it by `inferInstance` for the port's `Place` — so the port imports that module
instead of porting InlineSpecific. The other 38 declarations are NOT-NEEDED-BY-(1)/(2):
none is named in either file (grep count 0 for every distinctive name, §2.2), and the
handful that (1) could conceivably have reached through instance search
(`IsDiscreteValuationRing` / `IsPrincipalIdealRing` / `Ring.DimensionLEOne` on
`v.adicCompletionIntegers`) are not reachable because (1) uses
`adicCompletionIntegers` only as a `ValuationSubring`, never as a DVR/PID, and (2)
never mentions `adicCompletion`/`adicCompletionIntegers` at all. Consequently the
work order's stop-early risk 1 does **not** fire, and the port owes no InlineSpecific
transcription.

### 2.1 Declaration-by-declaration disposition

`IN-MATHLIB` names the mathlib declaration; `NOT-NEEDED` means no occurrence in (1)
or (2) (by name or by instance search) and is additionally marked with a mathlib
analogue where one exists.

| InlineSpecific decl (line) | kind | verdict | note |
|---|---|---|---|
| private `SeparableSpace (v.adicCompletion K)` (22) | instance | NOT-NEEDED | `UniformSpace.Completion.induction_on` in v4.34.0 needs no `SeparableSpace`; no mathlib name |
| private `intValuation_eq_coe_neg_multiplicity` (26) | lemma | NOT-NEEDED | used only inside InlineSpecific (`exists_adicValued_mul_sub_le`) |
| private `IsLocalRing.maximalIdeal_le` (46) | lemma | NOT-NEEDED | used only by `Ring.DimensionLEOne` instance |
| private `ValuationSubring.subtype_inj` (57) | lemma | NOT-NEEDED | used only inside InlineSpecific |
| private `ValuationSubring.valued_eq_one_of_isUnit` (61) | lemma | NOT-NEEDED | idem |
| private `ValuationSubring.isUnit_of_valued_eq_one` (71) | lemma | NOT-NEEDED | idem |
| private `ValuationSubring.isUnit_iff_valued_eq_one` (81) | lemma | NOT-NEEDED | idem |
| `exists_ofAdd_natCast_of_le_one` (95) | lemma | NOT-NEEDED | only inside InlineSpecific |
| `exists_ofAdd_natCast_lt` (104) | lemma | NOT-NEEDED | only inside InlineSpecific |
| `ne_zero_of_some_le_intValuation` (118) | lemma | NOT-NEEDED | only inside InlineSpecific |
| `emultiplicity_eq_of_valuation_eq_ofAdd` (123) | lemma | NOT-NEEDED | only inside InlineSpecific |
| `exists_adicValued_mul_sub_le` (135) | lemma | NOT-NEEDED | only inside InlineSpecific |
| `exists_adicValued_sub_lt_of_adicValued_le_one` (167) | lemma | NOT-NEEDED | only inside InlineSpecific |
| `instance : Valuation.IsRankOneDiscrete vK` (215) | instance | **NEEDED-in-effect / IN-MATHLIB** | `NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV`; probe A1 |
| `closureAlgebraMapIntegers_eq_integers` (223) | theorem | NOT-NEEDED | consumed by `denseRange_of_integerAlgebraMap` / `exists_adicValued_sub_lt_of_adicCompletionInteger` only |
| `denseRange_of_integerAlgebraMap` (262) | theorem | NOT-NEEDED | idem |
| `exists_adicValued_sub_lt_of_adicCompletionInteger` (277) | theorem | NOT-NEEDED | PlaceCompletion uses the weaker `kwHgfV352_exists_sub_mem_adicCompletionIntegers`, which is mathlib-only (probe D2) |
| `completionIdeal` (299) | abbrev | NOT-NEEDED | term is mathlib `IsLocalRing.maximalIdeal (adicCompletionIntegers K v)` |
| `mem_completionIdeal_iff` (302) | lemma | NOT-NEEDED | mathlib `Valuation.mem_maximalIdeal_iff` |
| `algebraMap_completionIntegers` (306) | lemma | NOT-NEEDED | `rfl` (`algebraMap`-coercion) |
| `instance : (v.completionIdeal K).LiesOver v.asIdeal` (310) | instance | NOT-NEEDED | no mathlib `LiesOver` for the completion ideal |
| `ResidueFieldToCompletionResidueField` (318) | def | NOT-NEEDED | no mathlib name |
| `ResidueFieldEquivCompletionResidueField` (325) | def | NOT-NEEDED | no mathlib name |
| `inertiaDeg_asIdeal_completionIdeal` (345) | theorem | NOT-NEEDED | no mathlib name |
| `exists_forall_adicValued_sub_lt` (359) | theorem | NOT-NEEDED | no mathlib name |
| `adicCompletion.eq_mul_nonZeroDivisor_inv_adicCompletionIntegers` (392) | lemma | NOT-NEEDED | no mathlib name |
| `adicCompletion.eq_mul_pi_adicCompletionIntegers` (403) | lemma | NOT-NEEDED | no mathlib name |
| `adicCompletion.exists_uniformizer` (430) | theorem | NOT-NEEDED | mathlib has `intValuation_exists_uniformizer`/`valuation_exists_uniformizer`, not the completion form |
| `uniformizer_ne_zero` (438) | theorem | NOT-NEEDED | only inside InlineSpecific |
| `uniformizer_not_isUnit` (447) | theorem | NOT-NEEDED | only inside InlineSpecific |
| `eq_pow_uniformizer_mul_unit` (455) | theorem | NOT-NEEDED | only inside InlineSpecific |
| `maximalIdeal_eq_span_uniformizer` (474) | theorem | NOT-NEEDED | only inside InlineSpecific |
| `instance : Ring.DimensionLEOne (v.adicCompletionIntegers K)` (488) | instance | NOT-NEEDED | no mathlib instance for `adicCompletionIntegers` |
| `instance : IsPrincipalIdealRing (v.adicCompletionIntegers K)` (503) | instance | NOT-NEEDED | mathlib analogue `FinitePlace.lean:67` requires the extra `[Finite (A ⧸ v.asIdeal)]` |
| `instance : IsDiscreteValuationRing (v.adicCompletionIntegers K)` (513) | instance | NOT-NEEDED | mathlib analogue `FinitePlace.lean:75`, same extra hypothesis |
| `instance : IsDiscreteValuationRing (𝒪[v.adicCompletion K])` (522) | instance | NOT-NEEDED | `inferInstanceAs` restatement of the previous row |
| `mem_completionIdeal_pow` (525) | lemma | NOT-NEEDED | only inside InlineSpecific |
| `mem_completionIdeal_iff'` (555) | lemma | NOT-NEEDED | corollary of the above |
| `completionIdeal_ne_bot` (560) | lemma | NOT-NEEDED | only inside InlineSpecific |

### 2.2 Machine-checked evidence for the verdict

- **No name use.** Grep over both audit files gives 0 for each distinctive
  InlineSpecific name: `exists_ofAdd_natCast_of_le_one`, `exists_ofAdd_natCast_lt`,
  `emultiplicity_eq_of_valuation_eq_ofAdd`, `exists_adicValued_mul_sub_le`,
  `exists_adicValued_sub_lt_of_adicValued_le_one`,
  `closureAlgebraMapIntegers_eq_integers`, `denseRange_of_integerAlgebraMap`,
  `exists_adicValued_sub_lt_of_adicCompletionInteger`, `mem_completionIdeal_iff`,
  `algebraMap_completionIntegers`, `ResidueFieldToCompletionResidueField`,
  `ResidueFieldEquivCompletionResidueField`, `inertiaDeg_asIdeal_completionIdeal`,
  `exists_forall_adicValued_sub_lt`, `eq_mul_nonZeroDivisor_inv_adicCompletionIntegers`,
  `eq_mul_pi_adicCompletionIntegers`, `maximalIdeal_eq_span_uniformizer`,
  `eq_pow_uniformizer_mul_unit`, `mem_completionIdeal_pow`, `completionIdeal_ne_bot`,
  `completionIdeal`.
- **The instance is mathlib's** (probe A1): with only
  `Mathlib.NumberTheory.NumberField.Completion.FinitePlace` (no InlineSpecific),
  `example : (Valued.v : Valuation (V.heightOneSpectrum.adicCompletion F) ℤᵐ⁰).IsRankOneDiscrete := inferInstance`
  elaborates; the synth trace names
  `NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV`.
- **The consuming def elaborates** (probe A2): the exact body of
  `kw_ffgc_rankOne_adicCompletion`,
  `Valuation.IsRankOneDiscrete.rankOne _ (one_lt_two (α := ℝ≥0))`, closes.
  Note the task brief's "plain function" is slightly off: `rankOne` still carries
  an `[IsRankOneDiscrete v]` instance argument
  (`Mathlib/RingTheory/Valuation/Discrete/RankOne.lean:68`); the point is that
  mathlib now *provides that instance*, so the pin's copy is redundant.
- **PlaceCompletion's approximation lemma is mathlib-only** (probe D2): the
  statement of `kwHgfV352_exists_sub_mem_adicCompletionIntegers` (with
  `V.adicCompletion` unfolded) is proved from `denseRange_algebraMap`,
  `Valued.isOpen_valuationSubring`, `Homeomorph.addLeft` and
  `DenseRange.exists_mem_open` alone, so the InlineSpecific
  `exists_adicValued_sub_lt_of_adicCompletionInteger` (a different, stronger
  statement) is not on the path.
- **V2 never touches the completion integers** (probe D1/C): V2's carrier
  `AdicCompletion (maximalIdeal v.toValuationSubring) v.toValuationSubring` gets its
  `Algebra v.toValuationSubring` and `Algebra K` instances and its
  `IsScalarTower K v.toValuationSubring _` from mathlib plus the port's
  `Place`/`PushPull` instances, with no PlaceCompletion declaration.

## 3. Per-file tables

### 3.1 `Def_AlgebraicCurve_PlaceCompletion.lean` (34 rows)

| pin decl (line) | class | mathlib / port name | evidence |
|---|---|---|---|
| anonymous global `Algebra O L` instance (9) | **BESPOKE** | — | not in inventory; global instance on every `ValuationSubring`; probe B3/D1 show the port does not need it (mathlib `AdicCompletion` algebra + port `Place` suffice); keep-or-drop is a design decision, and keeping it invites a diamond with mathlib's `algebraMap` |
| `adicCompletion` (31) | **SUBSTITUTE** | mathlib `IsDedekindDomain.HeightOneSpectrum.adicCompletion` | `abbrev` body is the mathlib abbrev |
| `adicCompletionIntegers` (33) | **SUBSTITUTE** | mathlib `HeightOneSpectrum.adicCompletionIntegers` | idem, lands as a `ValuationSubring` (probe A3) |
| `kw_ffgc_adicValuation_algebraMap` (44) | PROOF-INGREDIENT | port `Place.ord_restrict`, `Place.ramificationIndex`; `WithZero.{log_zpow,exp_log}` | |
| `kw_ffgc_valued_withValMapAlgebraMap` (60) | PROOF-INGREDIENT | `WithVal.{map_apply,valued_toVal}`; previous lemma | |
| `kw_ffgc_uniformContinuous_withValMapAlgebraMap` (70) | PROOF-INGREDIENT | `HeightOneSpectrum.valuation_surjective`, `uniformContinuous_of_continuousAt_zero`, `Valued.hasBasis_nhds_zero`, `pow_le_pow_right_of_le_one'`; previous lemma | probe A4 |
| `kw_ffgc_adicCompletionComap` (114) | BESPOKE | `AdicCompletion.equiv`, `UniformSpace.Completion.mapRingHom` | new ring hom; no mathlib analogue |
| `kw_ffgc_continuous_adicCompletionComap` (122) | PROOF-INGREDIENT | `adicCompletion.continuous_ofCompletion`, `Completion.continuous_map`, `continuous_toCompletion` | |
| `kw_ffgc_adicCompletionComap_coe` (134) | PROOF-INGREDIENT | `adicCompletion.ext`, `Completion.mapRingHom_coe` | |
| `kw_ffgc_valued_adicCompletionComap` (146) | PROOF-INGREDIENT | `adicCompletion.ofCompletion_surjective`, `Completion.induction_on`, `valuedAdicCompletion_surjective`, `Valued.continuous_valuation_of_surjective` | |
| `kw_ffgc_adicCompletionComap_mem_integers` (188) | PROOF-INGREDIENT | `HeightOneSpectrum.mem_adicCompletionIntegers`, `pow_le_one'`; previous lemma | |
| `kw_ffgc_adicCompletionComapIntegers` (195) | BESPOKE | `RingHom.restrict` | new restricted hom |
| `kw_ffgc_adicCompletionComapIntegers_coe` (200) | PROOF-INGREDIENT | `rfl` | |
| `kw_ffgc_algebraMap_adicCompletionComap_eq` (230) | PROOF-INGREDIENT | `RingHom.toAlgebra`, `rfl` | |
| `kw_ffgc_isScalarTower_integersCompletionCompletion` (243) | PROOF-INGREDIENT | `IsScalarTower.of_algebraMap_eq` | |
| `kw_ffgc_isScalarTower_integersIntegersCompletion` (248) | PROOF-INGREDIENT | previous `_coe`, `IsScalarTower.of_algebraMap_eq` | |
| `kw_ffgc_rankOne_adicCompletion` (263) | **SUBSTITUTE** | mathlib `Valuation.IsRankOneDiscrete.rankOne` | one mathlib term; probe A2 |
| `kw_ffgc_absoluteValue` (280) | BESPOKE | `Valuation.norm_add_le`, `Real.rpow_*` | `AbsoluteValue` built by hand |
| `kw_ffgc_continuousSMul_adicCompletionComap` (307) | PROOF-INGREDIENT | `continuousSMul_of_algebraMap`; previous lemmas | |
| `kw_ffgc_adicCompletionComap_algebraMap_algebraMap` (335) | PROOF-INGREDIENT | `WithVal.toVal`, `kw_ffgc_adicCompletionComap_coe` | |
| `kw_ffgc_algebraMap_smul_algebraMap` (347) | PROOF-INGREDIENT | `Algebra.smul_def`, previous lemma | |
| `kw_ffgc_completionLinearCombination` (353) | BESPOKE | `Fintype.linearCombination` | new linear map |
| `kw_ffgc_denseRange_completionLinearCombination` (359) | PROOF-INGREDIENT | `HeightOneSpectrum.denseRange_algebraMap`, `Module.Basis.sum_repr` | |
| `kw_ffgc_finiteDimensional_adicCompletion` (370) | PROOF-INGREDIENT | `Module.Finite.of_surjective`, `Submodule.closed_of_finiteDimensional`, `Valued.toNontriviallyNormedField`, `Module.finBasis` | probe A4 |
| `kw_ffgc_completionTrace` (390) | **SUBSTITUTE** | mathlib `Algebra.trace` | `abbrev` body is the mathlib trace |
| `kw_ffgc_completionTraceF'` (394) | BESPOKE | `Algebra.trace`, `LinearMap.map_smul` | new linear map |
| `kwHgfV352_valued_algebraMap_adicCompletion` (422) | PROOF-INGREDIENT | `HeightOneSpectrum.valuedAdicCompletion_eq_valuation'`, `algebraMap_adicCompletion` | probe A4 |
| `mem_of_ord_nonneg_placeCompletionAux` (432, priv) | **SUBSTITUTE** | port `Place.mem_of_ord_nonneg` (`Defs/PushPull.lean:60`) | probe A5 |
| `ord_nonneg_of_mem_placeCompletionAux` (441, priv) | **SUBSTITUTE** | port `Place.ord_nonneg_of_mem` (`Defs/PushPull.lean:43`) | probe A5 |
| `kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff` (459) | PROOF-INGREDIENT | `HeightOneSpectrum.mem_adicCompletionIntegers`, `WithZero.log_le_iff_le_exp`, previous two | |
| `kwHgfV352_exists_sub_mem_adicCompletionIntegers` (477) | PROOF-INGREDIENT | `denseRange_algebraMap`, `Valued.isOpen_valuationSubring`, `Homeomorph.addLeft`, `DenseRange.exists_mem_open` | probe D2 (verbatim proof) |
| `algebraMap_K_mem_adicCompletionIntegers` (510) | PROOF-INGREDIENT | `IsScalarTower.algebraMap_apply`, previous `_iff` | |
| `algebraMapKIntegers` (515) | BESPOKE | `RingHom` structure | new ring hom |
| `instAlgebraKAdicCompletionIntegers` (522) | PROOF-INGREDIENT | `RingHom.toAlgebra` | |

### 3.2 `Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean` (131 rows)

V2 is five pin blocks; the block boundaries are the pin's own section breaks.

#### 3.2.1 Block 1 — `Place` pole/Laurent layer (68 rows, pin 19–790)

| pin decl (line) | class | mathlib / port name | evidence |
|---|---|---|---|
| `HasSeparableResidue.of_perfectField` (19) | PROOF-INGREDIENT | `Algebra.trace_ne_zero`; port `Place.FiniteResidue.finite` | instance of the port class |
| `HasSeparableResidue.of_perfectField_of_isCurveOver` (25) | PROOF-INGREDIENT | previous instance | one application (the 87-line inventory span is empty pin scaffolding at 29–111) |
| `finiteResidue_of_deg_pos` (112) | PROOF-INGREDIENT | `Module.finite_of_finrank_pos` | |
| `restrictSubringHom` (127) | **SUBSTITUTE** | port `Place.restrictInclusion` (`Defs/PushPull.lean:401`) | body `rfl`-equal, probe B1 |
| `instIsLocalHom_restrictSubringHom` (133) | **SUBSTITUTE** | port `Place.instIsLocalHomRestrictInclusion` | probe B3 |
| `residueFieldMapRestrict` (155) | **SUBSTITUTE** | port `Place.restrictResidueMap` (`Defs/PushPull.lean:429`) | `rfl`, probe B2 |
| `instAlgebra_restrictResidueField` (158) | **SUBSTITUTE** | port `Place.instAlgebraResidueFieldRestrictPushforward` | probe B3 |
| `algebraMap_residueField_residue` (161) | PROOF-INGREDIENT | port `Place.restrictResidueMap_residue`, `algebraMap_residueField_eq` | |
| `instIsScalarTower_restrictResidueField` (167) | **SUBSTITUTE** | port `Place.instIsScalarTowerResidueFieldRestrictPushforward` | probe B3 |
| `uniformizerSubring` (199) | **SUBSTITUTE** | port `Place.uniformizerSubring'` (`Canonical/HasCanonicalDivisor.lean:64`) | same `Classical.choose`, `rfl`, probe B4 |
| `coe_uniformizerSubring` (202) | PROOF-INGREDIENT | port `Place.uniformizer` (`Defs/CanonicalDivisor.lean:39`) | `rfl` after B4 |
| `irreducible_uniformizerSubring` (205) | PROOF-INGREDIENT | `IsDiscreteValuationRing.exists_irreducible … .choose_spec` | probe B4 |
| `ord_nonneg_of_mem` (208, priv) | **SUBSTITUTE** | port `Place.ord_nonneg_of_mem` | probe A5 |
| `mem_of_ord_nonneg` (223, priv) | **SUBSTITUTE** | port `Place.mem_of_ord_nonneg` | probe A5 |
| `mem_iff_ord_nonneg` (231, priv) | **SUBSTITUTE** | port `Place.mem_iff_ord_nonneg` | probe A5 |
| `uniformizerSubring_mem_maximalIdeal` (235) | PROOF-INGREDIENT | `IsLocalRing.mem_maximalIdeal`, `Irreducible.not_isUnit` | |
| `uniformizer_mem` (239) | PROOF-INGREDIENT | subtype property | |
| `simplePoleSubmodule` (242) | BESPOKE | `Submodule K F` | pin carrier |
| `mem_simplePoleSubmodule` (252) | PROOF-INGREDIENT | `Iff.rfl` | |
| `mem_simplePoleSubmodule_of_mem` (256) | PROOF-INGREDIENT | `mul_mem` | |
| `simplePoleMulUniformizer` (260) | BESPOKE | `LinearMap` structure | |
| `simplePoleResidueAux` (269) | BESPOKE | `Ideal.Quotient.mkₐ`, `LinearMap.comp` | |
| `simplePoleResidueAux_apply` (273) | PROOF-INGREDIENT | `rfl` | |
| `simplePoleResidueAux_eq_zero_of_mem` (276) | PROOF-INGREDIENT | `IsLocalRing.residue_eq_zero_iff`, `Ideal.mul_mem_right` | |
| `localResidueExtend` (285) | BESPOKE | `LinearMap.exists_extend` | choice |
| `localResidueExtend_apply_of_mem` (288) | PROOF-INGREDIENT | `Exists.choose_spec` | |
| `localResidueDataOfExtend` (293) | BESPOKE | port `Place.LocalResidueData` | |
| `instHasLocalResidue` (303) | PROOF-INGREDIENT | previous def | instance of port class |
| `gate_hasLocalResidue_uniformizer_inv` (308) | **SUBSTITUTE** | port `Place.gate_localResidue_uniformizer_inv` (`Defs/LocalResidue.lean:108`) | |
| `gate_uniformizer_inv_mem_simplePoleSubmodule` (312) | PROOF-INGREDIENT | port `Place.ord_inv`, `Place.ord_uniformizer` | |
| `poleSubmodule` (340) | BESPOKE | `Submodule K F` | |
| `mem_poleSubmodule` (350) | PROOF-INGREDIENT | `Iff.rfl` | |
| `uniformizer_pow_ne_zero` (354) | PROOF-INGREDIENT | `pow_ne_zero`, `Place.uniformizer_ne_zero` | |
| `ord_uniformizer_pow` (357) | PROOF-INGREDIENT | port `Place.ord_zpow`, `Place.ord_uniformizer` | |
| `coe_poleSubmodule_zero` (361) | PROOF-INGREDIENT | `Set.ext` | |
| `poleSubmodule_one` (365) | PROOF-INGREDIENT | `Submodule.ext` | |
| `mem_poleSubmodule_iff_ord` (369) | PROOF-INGREDIENT | port `Place.mem_iff_ord_nonneg`, `Place.ord_mul`, previous lemma | |
| `poleSubmodule_mono` (375) | PROOF-INGREDIENT | `Nat.cast_le`, `neg_le_neg`; previous lemma | |
| `iSup_poleSubmodule_eq_top` (383) | PROOF-INGREDIENT | `Submodule.mem_iSup_of_mem`, `Int.self_le_toNat` | |
| `poleMulUniformizerPow` (393) | BESPOKE | `LinearMap` structure | |
| `laurentTailCoeff` (402) | BESPOKE | `Ideal.Quotient.mkₐ`, `LinearMap.comp` | |
| `laurentTailCoeff_apply` (406) | PROOF-INGREDIENT | `rfl` | |
| `coe_mul_uniformizer_pow_inv_mem_poleSubmodule` (409) | PROOF-INGREDIENT | `mul_inv_cancel₀` | |
| `laurentTail_remainder_mem_poleSubmodule` (414) | PROOF-INGREDIENT | `Irreducible.maximalIdeal_eq`, `Ideal.mem_span_singleton`, `mul_left_cancel₀` | |
| `localResidueData_agree_on_simplePole` (441) | PROOF-INGREDIENT | `LocalResidueData.res_simplePole` | |
| `localResidueData_res_eq_simplePoleResidueAux` (445) | PROOF-INGREDIENT | `res_simplePole`, `simplePoleResidueAux_apply` | |
| `gate_poleSubmodule_strictMono` (451) | PROOF-INGREDIENT | `mul_inv_cancel₀`, `mem_poleSubmodule_iff_ord` | |
| `exists_mem_poleSubmodule` (478) | PROOF-INGREDIENT | `Int.self_le_toNat`; previous | |
| `laurentTailCoeff_coe_mul_uniformizer_pow_inv` (486) | PROOF-INGREDIENT | `mul_inv_cancel₀`, subtype extensionality | |
| `uniformizer_mul_uniformizer_sq_inv` (523) | PROOF-INGREDIENT | `mul_inv`, `mul_inv_cancel₀` | |
| `CanonicalLocalResidueDataK.res_algebraMap_mul_uniformizer_pow_inv` (533) | PROOF-INGREDIENT | `map_smul`, port `res_higherPoleMonomial` | |
| `CanonicalLocalResidueDataK.res_laurentRecK` (540) | PROOF-INGREDIENT | `map_sub`, previous lemma | |
| `uniformizer_pow_inv_mem_poleSubmodule_self` (565) | PROOF-INGREDIENT | `gate_poleSubmodule_strictMono` | |
| `higherPoleMonomial_sum_mem_poleSubmodule` (569) | PROOF-INGREDIENT | `Submodule.sum_mem`, `poleSubmodule_mono` | |
| `higherPoleMonomial_coeff_eq_zero_of_mem` (577) | PROOF-INGREDIENT | `Finset.induction_on_max`, `inv_smul_smul₀` | |
| `linearIndependent_higherPoleMonomial_mkQ` (607) | PROOF-INGREDIENT | `linearIndependent_iff'`, `Submodule.Quotient.mk_eq_zero`, previous lemma | |
| `higherPoleCorrectionAux` (617) | BESPOKE | `Basis.span`, `Module.Basis.constr` | |
| `higherPoleCorrection` (624) | BESPOKE | `LinearMap.exists_extend` | |
| `higherPoleCorrection_apply_of_mem` (627) | PROOF-INGREDIENT | `Submodule.Quotient.mk_eq_zero` | |
| `higherPoleCorrection_uniformizer_pow_inv` (633) | PROOF-INGREDIENT | `Basis.span_apply`, `Basis.constr_basis` | |
| `canonicalLocalResidueDataKOfExtend` (651) | BESPOKE | port `Place.CanonicalLocalResidueDataK` | |
| `instHasCanonicalLocalResidueK` (670) | PROOF-INGREDIENT | previous def | instance of port class |
| `canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj` (677) | PROOF-INGREDIENT | `Nat.rec` induction, `IsScalarTower.algebraMap_apply`, `IsLocalRing.ResidueField.algebraMap_eq` | |
| `CoefficientFieldSection` (724) | BESPOKE | structure | pin vocabulary |
| `CanonicalLocalResidueDataS` (730) | BESPOKE | structure extending port `LocalResidueData` | |
| `CanonicalLocalResidueDataS.res_laurentRecS` (740) | PROOF-INGREDIENT | `map_sub`, `res_higherPoleSectionMonomial` | |
| `canonicalLocalResidueDataS_agree_on_poleSubmodule` (746) | PROOF-INGREDIENT | same induction as `…_of_surj` | |
| `coefficientFieldSectionOfBijective` (769) | BESPOKE | `AlgEquiv.ofBijective`, `Algebra.ofId` | |

#### 3.2.2 Block 2 — `ModularCurve.Lg37` (4 rows, pin 944–975)

| pin decl (line) | class | mathlib / port name | evidence |
|---|---|---|---|
| `lg37_completion` (944) | BESPOKE | mathlib `AdicCompletion` | abbrev `AdicCompletion (maximalIdeal v.toValuationSubring) v.toValuationSubring`; no mathlib name, but the term is mathlib (probe D1) |
| `lg37_residueHat` (947) | BESPOKE | `AdicCompletion.evalOneₐ` | |
| `lg37_residueHat_algebraMap` (951) | PROOF-INGREDIENT | `rfl` | |
| `Lg37CompletionSection` (956) | BESPOKE | structure | pin vocabulary |

#### 3.2.3 Block 3 — the Hensel / adic-completion engine (27 rows, pin 998–1532)

| pin decl (line) | class | mathlib / port name | evidence |
|---|---|---|---|
| `mp72a102_t1_maximalIdealHat` (998) | BESPOKE | `Ideal.map` | abbrev |
| `mp72a102_t1_isScalarTower` (1003) | PROOF-INGREDIENT | `IsScalarTower.of_algebraMap_eq` | probe D1 |
| `mp72a102_t1_isAdicComplete_maximalIdealHat` (1007) | PROOF-INGREDIENT | `IsAdicComplete.map_algebraMap_iff`, `AdicCompletion.isAdicComplete`, `IsPrincipalIdealRing.principal`, `Submodule.IsPrincipal.fg` | probe C/E |
| `mp72a102_t1_henselianRing_completion` (1015) | PROOF-INGREDIENT | `IsAdicComplete.henselianRing` | probe C |
| `mp72a102_t1_maximalIdealHat_le_ker_residueHat` (1020) | PROOF-INGREDIENT | `Ideal.map_le_iff_le_comap`, `IsLocalRing.residue_eq_zero_iff` | |
| `mp72a102_t1_exists_completion_root_of_residue_root` (1026) | PROOF-INGREDIENT | `HenselianRing.is_henselian`, `IsLocalRing.residue_surjective`, `Polynomial.aeval_algebraMap_apply`, `Polynomial.Separable` | deepest row of the block (95 ln) |
| `mp72a102_t3_evalₐ_zero_depth` (1121) | PROOF-INGREDIENT | `Ideal.Quotient.subsingleton_iff`, `Subsingleton.elim` | |
| `mp72a102_t3_evalₐ_algebraMap` (1127) | PROOF-INGREDIENT | `AdicCompletion.algebraMap_apply`, `AdicCompletion.evalₐ_of` | probe C |
| `mp72a102_t3_evalₐ_factor` (1133) | PROOF-INGREDIENT | `AdicCompletion.mk_surjective`, `AdicCompletion.evalₐ_mk`, `AdicCompletion.Ideal.mk_eq_mk` | probes C/E |
| `mp72a102_t3_exists_rep_of_evalₐ_eq_zero` (1140) | PROOF-INGREDIENT | `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.factor_mk`, `Ideal.Quotient.eq_zero_iff_mem` | |
| `mp72a102_t3_evalₐ_succ_mul_eq_zero` (1149) | PROOF-INGREDIENT | `Ideal.mul_mem_mul`, `pow_succ'`; previous | |
| `mp72a102_t3_evalₐ_one_eq_zero_of_evalOneₐ` (1157) | PROOF-INGREDIENT | `AdicCompletion.factorₐ_evalₐ_one` | |
| `mp72a102_t3_evalDepth_add` (1171) | PROOF-INGREDIENT | `map_add` | |
| `mp72a102_t3_evalDepth_mul` (1178) | PROOF-INGREDIENT | `map_mul` | |
| `mp72a102_t3_residueHat_congr_of_depth_one` (1185) | PROOF-INGREDIENT | `AdicCompletion.factorₐ_evalₐ_one` | |
| `mp72a102_t3_evalDepth_one_eq_zero_of_residueHat` (1194) | PROOF-INGREDIENT | previous `t3_evalₐ_one_eq_zero_of_evalOneₐ` | |
| `mp72a102_t3_eq_uniformizer_mul_of_mem_maximalIdeal` (1199) | PROOF-INGREDIENT | `Irreducible.maximalIdeal_eq`, `Ideal.mem_span_singleton` | |
| `mp72a102_t3_exists_uniformizer_factor` (1205) | PROOF-INGREDIENT | `Ideal.Quotient.mk_surjective`, previous lemmas | |
| `mp72a102_t3_sigma_taylor_expansion` (1228) | PROOF-INGREDIENT | `Finset.sum_range_succ'`, `mp72a102_t3_*`, `ring` | 89 ln, all mathlib assembly |
| `mp72a102_t2_residueHat_algebraMap_base` (1317) | PROOF-INGREDIENT | `rfl`, `lg37_residueHat_algebraMap` | |
| `mp72a102_t2_residueHatAlgHom` (1326) | BESPOKE | `AlgHom` structure | |
| `residueFieldAdjoinRootEquiv` (1354) | BESPOKE | `IntermediateField.adjoinRootEquivAdjoin`, `IntermediateField.equivOfEq`, `topEquiv` | probe C |
| `residueFieldAdjoinRootEquiv_root` (1360) | PROOF-INGREDIENT | `adjoinRootEquivAdjoin_apply_root`, `AdjoinSimple.coe_gen` | |
| `sectionOfPrimitiveRoot` (1375) | BESPOKE | `AdjoinRoot.liftAlgHom` | |
| `mp72a103_t2_evalDepth_of_uniformizer_mul` (1428) | PROOF-INGREDIENT | `Irreducible.maximalIdeal_eq`, `Ideal.span_singleton_pow`, `mul_left_cancel₀` | |
| `mp72a103_t2_lift_eq_zero_of_depth_one` (1453) | PROOF-INGREDIENT | previous `t3_residueHat_congr_of_depth_one` | |
| `mp72a103_t2_taylor_coeff_eq_zero_of_depth` (1461) | PROOF-INGREDIENT | `Finset.sum_range_succ'`, `Finset.mul_sum` | 84 ln, all mathlib assembly |

#### 3.2.4 Block 4 — `ModularCurve.KwNo6Pin` (28 rows, pin 1545–2124)

| pin decl (line) | class | mathlib / port name | evidence |
|---|---|---|---|
| `maximalIdeal_fg` (1545) | PROOF-INGREDIENT | `IsNoetherian.noetherian` | |
| `isAdicComplete_map` (1549) | PROOF-INGREDIENT | previous `t1_isAdicComplete_…` | |
| `residueHat_surjective` (1556) | PROOF-INGREDIENT | `IsLocalRing.residue_surjective` | |
| `ker_residueHat` (1562) | PROOF-INGREDIENT | `AdicCompletion.factorₐ_evalₐ_one`, `Ideal.quotientEquivAlgOfEq`, `AdicCompletion.pow_smul_top_eq_ker_eval`, `Ideal.smul_top_eq_map` | probes C/E |
| `map_isMaximal` (1602) | PROOF-INGREDIENT | `RingHom.ker_isMaximal_of_surjective` | |
| `isLocalRing_completion` (1608) | PROOF-INGREDIENT | `isLocalRing_of_isAdicComplete_maximal` | |
| `ker_residueHat_eq_maximalIdeal` (1616) | PROOF-INGREDIENT | `IsLocalRing.eq_maximalIdeal`; previous | probe E |
| `hensel_unique` (1622) | PROOF-INGREDIENT | `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`, `Polynomial.Separable.aeval_derivative_ne_zero` | probe E |
| `section_unique` (1657) | PROOF-INGREDIENT | `Field.exists_primitive_element`, `Algebra.IsIntegral.isIntegral`, `Polynomial.aeval_algHom_apply`, `AdjoinRoot.algHom_ext` | probe C |
| `aCoeff` (1683) | BESPOKE | `Classical.choose` | |
| `aCoeff_section_indep` (1687) | PROOF-INGREDIENT | `Classical.choose_spec`, `Finset.sum_sub_distrib` | |
| `aCoeff_zero` (1739) | PROOF-INGREDIENT | `Finset.sum_range_one`, `sub_eq_zero` | |
| `aCoeff_add` (1751) | PROOF-INGREDIENT | `Finset.sum_add_distrib`, `mp72a102_t3_evalDepth_add` | |
| `aCoeff_smul` (1801) | PROOF-INGREDIENT | `map_smul`, `mp72a102_t3_evalDepth_mul` | |
| `aCoeff_shift` (1860) | PROOF-INGREDIENT | `Finset.sum_range_succ'`, `pow_succ` | |
| `aCoeff_shift_pow` (1930) | PROOF-INGREDIENT | induction, `pow_succ`; previous | |
| `aCoeff_one_eq_zero` (1947) | PROOF-INGREDIENT | `Finset.sum_eq_single`, `mp72a103_t2_taylor_coeff_eq_zero_of_depth` | |
| `clearPow_mem` (1990) | PROOF-INGREDIENT | port `Place.mem_iff_ord_nonneg`, `Place.ord_mul`, `Place.ord_uniformizer_pow` | |
| `clearedHat` (2000) | BESPOKE | def | |
| `resStar` (2005) | BESPOKE | def | |
| `aCoeff_clearedHat_of_le` (2009) | PROOF-INGREDIENT | `Nat.exists_eq_add_of_le`, `aCoeff_shift_pow` | |
| `resStar_add` (2024) | PROOF-INGREDIENT | `Finset.sum`-free `aCoeff_add`, `Subtype.ext`, `ring` | |
| `resStar_smul` (2040) | PROOF-INGREDIENT | `IsScalarTower.algebraMap_apply`, `aCoeff_smul` | |
| `resStarₗ` (2055) | BESPOKE | `LinearMap` structure | |
| `resStar_simplePole` (2061) | PROOF-INGREDIENT | `aCoeff_clearedHat_of_le`, `aCoeff_shift`, `aCoeff_zero` | |
| `resStar_of_mem` (2081) | PROOF-INGREDIENT | `IsLocalRing.residue_eq_zero_iff`, `Ideal.mul_mem_right` | |
| `resStar_higherPoleMonomial` (2089) | PROOF-INGREDIENT | `Place.ord_inv`, `Place.ord_uniformizer_pow`, `aCoeff_one_eq_zero` | |
| `canonicalLocalResidueDataKStar` (2110) | BESPOKE | port `Place.CanonicalLocalResidueDataK` | def |

#### 3.2.5 Block 5 — the unconditional instance (4 rows, pin 2137–2173)

| pin decl (line) | class | mathlib / port name | evidence |
|---|---|---|---|
| `completionSection_nonempty_generic` (2137) | PROOF-INGREDIENT | `Field.exists_primitive_element`, `minpoly.monic`, `Algebra.IsSeparable.isSeparable`, `mp72a102_t1_exists_completion_root_of_residue_root`, `sectionOfPrimitiveRoot` | |
| `instHasCanonicalLocalResidueKStar` (2149) | PROOF-INGREDIENT | `Place.FiniteResidue.finite`, `Algebra.IsAlgebraic.isSeparable_of_perfectField`, `canonicalLocalResidueDataKStar`, `Classical.choice` | the phase headline instance; statement `[IsCurveOver K F] [PerfectField K] : HasCanonicalLocalResidueKStar K F` |
| `localResidue_eq_resStar` (2158) | PROOF-INGREDIENT | `aCoeff_section_indep` | |
| `localResidue_eq_resStarₗ` (2168) | PROOF-INGREDIENT | `LinearMap.ext`; previous | |

## 4. Reuse wins, with probe evidence

All compile in `ScratchAuditP31.lean` (final run exit 0). The five most load-bearing:

1. **The `IsRankOneDiscrete` instance is mathlib's** (A1). The pin's `InlineSpecific`
   line 215 is a two-line copy of `FinitePlace.lean:102`; with
   `import Mathlib.NumberTheory.NumberField.Completion.FinitePlace` the port gets
   `NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV` for
   `(Valued.v : Valuation (V.adicCompletion) ℤᵐ⁰)` by `inferInstance`. This is the
   whole InlineSpecific dependency of phase 3.1.
2. **`kw_ffgc_rankOne_adicCompletion` is one mathlib term** (A2): the pin's body
   `Valuation.IsRankOneDiscrete.rankOne _ (one_lt_two (α := ℝ≥0))` elaborates
   verbatim.
3. **V2's `restrictSubringHom`/`residueFieldMapRestrict` block is the port's
   `restrictInclusion`/`restrictResidueMap` block** (B1/B2): both bodies are
   `rfl`-equal to the port definitions, and the three instances
   (`instIsLocalHom_restrictSubringHom`, `instAlgebra_restrictResidueField`,
   `instIsScalarTower_restrictResidueField`) are the port's instances (B3). Six V2
   rows become imports.
4. **V2's `uniformizerSubring` block is the port's `uniformizerSubring'`** (B4):
   same `Classical.choose`, `rfl`. `coe_uniformizerSubring` and
   `irreducible_uniformizerSubring` are then `rfl` and `choose_spec`.
5. **V2's three private ord helpers are the port's public PushPull lemmas**
   (A5): `ord_nonneg_of_mem`, `mem_of_ord_nonneg`, `mem_iff_ord_nonneg` already
   land at `Defs/PushPull.lean:43/60/69`, and `gate_hasLocalResidue_uniformizer_inv`
   equals `Defs/LocalResidue.lean:108`. (This corrects `rt_instance_advise.txt`,
   which reports `mem_of_ord_nonneg` as available only as a `private` local-residue
   helper: the public PushPull copy is the right home.)
6. **`lg37_completion`'s carrier algebras come from mathlib** (D1):
   `Algebra v.toValuationSubring (AdicCompletion …)`, `Algebra K (AdicCompletion …)`
   and `IsScalarTower K v.toValuationSubring (AdicCompletion …)` are all
   `inferInstance`/one-liners without the pin's global `Algebra O L` instance.
7. **`kwHgfV352_exists_sub_mem_adicCompletionIntegers` is mathlib-only** (D2): the
   pin's 12-line proof transcribes verbatim with no InlineSpecific name.
8. **`PlaceCompletion`'s abbreviations are mathlib abbreviations** (A3):
   `adicCompletion` and `adicCompletionIntegers` are `rfl`-aliases of the
   `HeightOneSpectrum` abbreviations, so those two rows (and
   `kw_ffgc_completionTrace` against `Algebra.trace`) cost no proof.

`port_advise`'s remaining claims were re-verified: the three `PlaceCompletion`
substitutions match, and the V2 substitutions match; the only correction is the
`mem_of_ord_nonneg` home (§4.5) and the `adicCompletion → CohCarrier.H1` false
positive recorded in the work order §3.

## 5. Route options

- **R1 — import the instance, delete the prelude.** The port should **not** port
  `InlineSpecific`. `PlaceCompletion.lean` imports
  `Mathlib.NumberTheory.NumberField.Completion.FinitePlace` and everything on the
  (1)/(2) path resolves. This turns the "≈2,600 written, no new mathematics" estimate
  into ≈2,600 with the only third-party blocker removed.
- **R2 — V2 need not import `PlaceCompletion`.** At the name level it does not (grep
  0 for every PlaceCompletion name), and D1 shows the carrier algebras are mathlib.
  Keeping the pin's import is harmless but adds a 530-line dependency that the
  statement checker will then require to be green first; the port may choose to drop
  it and let V2 depend on `Defs/{LocalResidue,PushPull,Place,IsCurveOver}` plus
  mathlib's `AdicCompletion`.
- **R3 — the global `Algebra O L` instance.** Transcribe or drop deliberately. It is
  a global instance on `ValuationSubring`, not a pin theorem, and is not needed by
  (1)/(2) (probe D1). If kept it can shadow/compete with mathlib's `AdicCompletion`
  algebra map; recommend a scoped/local instance or a documented drop.
- **R4 — the V2 Hensel engine is mathlib-shaped.** `lg37_completion` is
  `AdicCompletion`; `mp72a102_t1_*` are `IsAdicComplete`/`HenselianRing` and
  `AdicCompletion.evalₐ` facts. There is no shorter route than the pin's: the
  Taylor-coefficient vanishing (`mp72a103_t2_taylor_coeff_eq_zero_of_depth`) is the
  one genuinely assembled induction.
- **R5 — `exists_adicValued_sub_lt_of_adicCompletionInteger` is not the route.**
  PlaceCompletion only needs the weaker cofinal-approximation statement, proved by
  density + openness (D2). Do not port the InlineSpecific strengthening.

## 6. API drift (v4.34.0) — what the worker must change

| pin call / assumption | v4.34.0 status | worker action |
|---|---|---|
| `kw_ffgc_rankOne_adicCompletion` relies on `InlineSpecific`'s `IsRankOneDiscrete` | mathlib has `NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV` (`Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean:102`) | add `import Mathlib.NumberTheory.NumberField.Completion.FinitePlace`; drop InlineSpecific |
| `Valuation.IsRankOneDiscrete.rankOne _ (one_lt_two (α := ℝ≥0))` | present (`Mathlib/RingTheory/Valuation/Discrete/RankOne.lean:68`), still class-gated `[IsRankOneDiscrete v]` | no change (A2) |
| `AlgEquiv.coe_algHom` (V2:1681) | deprecated alias since 2026-05-05 (`Mathlib/Algebra/Algebra/Equiv.lean:202`) | rename to `AlgEquiv.coe_toAlgHom` |
| `AdicCompletion.isAdicComplete` (V2:1011) | takes `I.FG` explicitly (`Mathlib/RingTheory/AdicCompletion/Completeness.lean:184`) | pin already passes `(IsPrincipalIdealRing.principal …).fg` |
| `AdicCompletion.pow_smul_top_eq_ker_eval` (V2:1593) | takes `I.FG` (`Completeness.lean:154`) | pin passes `maximalIdeal_fg`; keep as is |
| `IsAdicComplete.henselianRing` (V2:1018) | present, module `Mathlib.RingTheory.Henselian` (`Henselian.lean:170`) | add the import (not `AdicCompletion`) |
| `eq_of_eval_eq_zero_of_not_isUnit_sub` (V2:1655) | `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`, `Mathlib/RingTheory/Henselian` (`Henselian.lean:266`) | `open IsLocalRing` (pin has it); add the import |
| `adjoinRootEquivAdjoin` (V2:1357) | full name `IntermediateField.adjoinRootEquivAdjoin`, `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:417` | `open IntermediateField` (pin has it); add the import |
| `AdicCompletion.Ideal.mk_eq_mk` (V2:1138) | present | none |
| `IsDiscreteValuationRing.irreducible_iff_uniformizer`, `Irreducible.maximalIdeal_eq` (V2:422, 1202, 1437) | present | none |
| `IsPrincipalIdealRing.principal … .fg` (V2:1012) | `IsPrincipalIdealRing.principal : (S : Ideal R) → Submodule.IsPrincipal S`; `Submodule.IsPrincipal.fg` present | none |
| `mathlib`-only names `evalₐ`/`evalOneₐ`/`factorₐ_evalₐ_one` | all in `Mathlib/RingTheory/AdicCompletion/Algebra.lean` | add the import; do not `import Mathlib` |

## 7. Recorded negatives

Confirmed against mathlib `v4.34.0`; phrased so the search is not repeated.

1. **No `genus`-style analogue issue here**, but no `Place`-level residue API:
   `resStar`, `aCoeff`, `Lg37CompletionSection`, `CoefficientFieldSection`,
   `CanonicalLocalResidueDataS`, `canonicalLocalResidueDataKStar` are all absent.
2. **No InlineSpecific names in mathlib.** `completionIdeal`,
   `ResidueFieldEquivCompletionResidueField`,
   `ResidueFieldToCompletionResidueField`, `inertiaDeg_asIdeal_completionIdeal`,
   `closureAlgebraMapIntegers_eq_integers`, `denseRange_of_integerAlgebraMap`,
   `exists_adicValued_sub_lt_of_adicCompletionInteger`,
   `exists_forall_adicValued_sub_lt`, `mem_completionIdeal_iff`,
   `eq_mul_pi_adicCompletionIntegers`,
   `eq_mul_nonZeroDivisor_inv_adicCompletionIntegers`,
   `exists_ofAdd_natCast_of_le_one`, `exists_ofAdd_natCast_lt`,
   `emultiplicity_eq_of_valuation_eq_ofAdd`, `exists_adicValued_mul_sub_le` are all
   absent from `Mathlib/` by name. None is on the (1)/(2) path.
3. **No `LiesOver` instance for the completion ideal** (`v.completionIdeal K` over
   `v.asIdeal`): mathlib's `LiesOver` API is for `HeightOneSpectrum`-over-
   `HeightOneSpectrum` only.
4. **No `Ring.DimensionLEOne (v.adicCompletionIntegers K)`** in mathlib.
5. **`IsPrincipalIdealRing`/`IsDiscreteValuationRing (v.adicCompletionIntegers K)`
   exist only with an extra hypothesis.** `FinitePlace.lean:67,75` prove them for
   `[Finite (A ⧸ v.asIdeal)]`; InlineSpecific's hypothesis-free versions are
   genuinely stronger and genuinely unported — but again not needed by (1)/(2).
6. **No completion-specific uniformizer statement.** Mathlib has
   `intValuation_exists_uniformizer` and `valuation_exists_uniformizer`; the
   `adicCompletion.exists_uniformizer` of InlineSpecific is absent.
7. **`port_advise`'s `adicCompletion → CohCarrier.H1` match is a false positive**
   (as the work order §3 already flags); `H1` is the pin's adelic index, unrelated.
8. **`port_advise`'s `mem_of_ord_nonneg` home is incomplete**: the public
   `Place.mem_of_ord_nonneg` is at `Defs/PushPull.lean:60`, not only the `private`
   `LocalResidue` helper.

## 8. What this changes for `WORKORDER-P3-1-residue-instance.md` §4

**Scope / measurement.**
- Row count for (1) is **34**, not 33: transcribe the anonymous global instance at
  pin line 9 or record its deliberate omission. Fix `p3_1_inventory.txt` to emit
  anonymous instances as well.
- V2's 131 rows are confirmed complete (3 `private` included).

**Discharged proofs (mark import-discharged; the statements still land).**
- `PlaceCompletion`: `adicCompletion`, `adicCompletionIntegers`,
  `kw_ffgc_rankOne_adicCompletion`, `kw_ffgc_completionTrace`,
  `mem_of_ord_nonneg_placeCompletionAux`, `ord_nonneg_of_mem_placeCompletionAux`.
- V2: `restrictSubringHom`, `instIsLocalHom_restrictSubringHom`,
  `residueFieldMapRestrict`, `instAlgebra_restrictResidueField`,
  `instIsScalarTower_restrictResidueField`, `uniformizerSubring`,
  `ord_nonneg_of_mem`, `mem_of_ord_nonneg`, `mem_iff_ord_nonneg`,
  `gate_hasLocalResidue_uniformizer_inv`.

**Imports the worker may use.**
- `PlaceCompletion.lean`: `Mathlib.NumberTheory.NumberField.Completion.FinitePlace`,
  `Mathlib.RingTheory.DedekindDomain.AdicValuation`,
  `Mathlib.Topology.Algebra.Valued.ValuationTopology` (valuation topology),
  `Mathlib.Topology.Algebra.Module.FiniteDimension` (`Submodule.closed_of_finiteDimensional`),
  plus `FLTForHuman.AlgebraicCurve.Defs.{Place, PushPull, Divisor}`; **no**
  `InlineSpecific`.
- V2: `Mathlib.RingTheory.AdicCompletion.{Algebra, Completeness}`,
  `Mathlib.RingTheory.Henselian`,
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`,
  `Mathlib.FieldTheory.PrimitiveElement`,
  plus `FLTForHuman.AlgebraicCurve.Defs.{LocalResidue, IsCurveOver, PushPull, Place}`.
  `PlaceCompletion` is not required at the name level; import it only if the
  manager wants the scoped algebra instances on `W.adicCompletion`.

**Stop-early risk 1 does not fire.** The required InlineSpecific declaration is in
mathlib; record the disposition in the set report and do not port the prelude.

**Stop-early risk 2** (port's `heightOneSpectrum`/`ramificationIndex`/`restrict`
API drift) was checked at the call sites used here: `Place.restrict`,
`Place.ord_restrict`, `Place.ramificationIndex`, `Place.ramificationIndex_pos`,
`Place.uniformizer`, `Place.ord_uniformizer`, `Place.ord_zpow`,
`Place.ord_unit_smul_zpow`, `Place.mem_iff_ord_nonneg`, `Place.FiniteResidue.finite`
all exist with the needed types; no drift found beyond the `AlgEquiv.coe_algHom`
rename.

**Checker wiring.** Unchanged from the work order §5 apart from the added mathlib
imports above; `instHasCanonicalLocalResidueKStar` still needs a real consumer
`example` (it is an `instance`, so `DECL_RE` parses it, but statement-only checking
would not exercise the term).

**Scratch evidence (removed at closeout).** `lean/ScratchAuditP31.lean` — `#check`
ledger plus probes A1–A5 (RankOne/InlineSpecific/port ord), B1–B4 (V2
restrict/coefficient substitutes), C (AdicCompletion/Hensel/AdjoinRoot names),
D1–D2 (V2 carrier and mathlib-only approximation), E (drift names). Command
`timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP31.lean`
from `lean/`, exit 0, 4.61 s. The file was deleted after the phase-3.1 whole-tree
build passed; the classifications above remain the record.

## 9. Appendix — module map for the named constants

Every non-BESPOKE row above cites a name; this is where `v4.34.0` declares it, so a
worker can add the narrow import rather than `import Mathlib`.

| name | module |
|---|---|
| `HeightOneSpectrum.{adicCompletion, adicCompletionIntegers}` | `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` |
| `HeightOneSpectrum.{valuation_surjective (405), valuedAdicCompletion_surjective (789), adicCompletion_valueGroup_eq (795), mem_adicCompletionIntegers (815), denseRange_algebraMap (886), valuedAdicCompletion_eq_valuation' (948)}` | `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` |
| `HeightOneSpectrum.{intValuation_exists_uniformizer (271), valuation_exists_uniformizer (396)}` | `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` |
| `Valuation.IsRankOneDiscrete.mk'` / `.generator*` | `Mathlib/RingTheory/Valuation/Discrete/Basic.lean` |
| `Valuation.IsRankOneDiscrete.rankOne` (68) | `Mathlib/RingTheory/Valuation/Discrete/RankOne.lean` |
| `NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV` (102) | `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean` |
| `IsPrincipalIdealRing` / `IsDiscreteValuationRing (adicCompletionIntegers)` (67, 75) | `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean` (with `[Finite (A ⧸ v.asIdeal)]`) |
| `Valued.toNontriviallyNormedField` (277) | `Mathlib/Topology/Algebra/Valued/NormedValued.lean` |
| `Valuation.norm_add_le` (126) | `Mathlib/Topology/Algebra/Valued/NormedValued.lean` |
| `Valued.isOpen_valuationSubring` (318) | `Mathlib/Topology/Algebra/Valued/ValuationTopology.lean` |
| `Submodule.closed_of_finiteDimensional` (531) | `Mathlib/Topology/Algebra/Module/FiniteDimension.lean` |
| `UniformSpace.Completion.{mapRingHom, mapRingHom_coe, induction_on, denseRange_coe, continuous_map}` | `Mathlib/Topology/UniformSpace/Completion.lean` |
| `AdicCompletion.{evalₐ, evalOneₐ, algebraMap_apply, evalₐ_of, evalₐ_mk, factorₐ_evalₐ_one}` | `Mathlib/RingTheory/AdicCompletion/Algebra.lean` |
| `AdicCompletion.{mk, mk_surjective, eval, Ideal.mk_eq_mk}` | `Mathlib/RingTheory/AdicCompletion/Basic.lean` |
| `AdicCompletion.{pow_smul_top_eq_ker_eval, isAdicComplete}` | `Mathlib/RingTheory/AdicCompletion/Completeness.lean` |
| `IsAdicComplete.{map_algebraMap_iff, henselianRing}` | `Mathlib/RingTheory/Henselian.lean` |
| `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub` (266) | `Mathlib/RingTheory/Henselian.lean` |
| `IsLocalRing.{residue_eq_zero_iff, residue_surjective, eq_maximalIdeal, mem_maximalIdeal}` | `Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`, `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` |
| `IntermediateField.adjoinRootEquivAdjoin` (417), `adjoinRootEquivAdjoin_apply_root` | `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean` |
| `Field.exists_primitive_element` | `Mathlib/FieldTheory/PrimitiveElement.lean` |
| `AlgEquiv.coe_toAlgHom` (`coe_algHom` deprecated, 202) | `Mathlib/Algebra/Algebra/Equiv.lean` |
| `AdjoinRoot.{liftAlgHom, algHom_ext, root}` | `Mathlib/RingTheory/AdjoinRoot.lean` |
| `IsDiscreteValuationRing.{exists_irreducible, eq_unit_mul_pow_irreducible, irreducible_iff_uniformizer}` | `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` |
| `Irreducible.maximalIdeal_eq` (98) | `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` |
| `IsNoetherian.noetherian` (63) | `Mathlib/RingTheory/Noetherian/Defs.lean` |
| `IsPrincipalIdealRing.principal`, `Submodule.IsPrincipal.fg` | `Mathlib/RingTheory/PrincipalIdealDomain.lean`, `Mathlib/LinearAlgebra/Submodule/Basic.lean` |
| `Basis.{span, span_apply}` / `Basis.constr_basis` | `Mathlib/LinearAlgebra/Basis/Basic.lean` / `Mathlib/LinearAlgebra/Basis/Defs.lean` (there is no `Basis/Span.lean` in v4.34.0 — corrected by the 3.1b-i worker) |
| `LinearMap.exists_extend` | `Mathlib/LinearAlgebra/Basis/VectorSpace.lean` |
| `Ideal.{quotientEquivAlgOfEq, smul_top_eq_map, map_le_iff_le_comap, Quotient.*}` | `Mathlib/RingTheory/Ideal/*` |
| `Polynomial.{aeval, aeval_def, aeval_algebraMap_apply, aeval_algHom_apply, derivative_map, eval_map}` | `Mathlib/Algebra/Polynomial/AlgebraMap.lean`, `Mathlib/Algebra/Polynomial/Derivative.lean` |

Port modules referred to above: `FLTForHuman/AlgebraicCurve/Defs/Place.lean`
(`Place`, `deg`, `FiniteResidue`, `ResidueField`, `ord*`),
`FLTForHuman/AlgebraicCurve/Defs/PushPull.lean` (`restrict`, `restrictInclusion`,
`restrictResidueMap`, `ramificationIndex`, the three ord lemmas),
`FLTForHuman/AlgebraicCurve/Defs/CanonicalDivisor.lean` (`uniformizer`, `dCoord`),
`FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean`
(`uniformizerSubring'`), `FLTForHuman/AlgebraicCurve/Defs/LocalResidue.lean`
(`LocalResidueData`, `CanonicalLocalResidueDataK`, `HasLocalResidue`,
`HasCanonicalLocalResidueK`, `HasCanonicalLocalResidueKStar`,
`HasSeparableResidue`, `gate_localResidue_uniformizer_inv`).
