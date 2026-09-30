# Mathlib-first substitution audit — the canonical-divisor construction (phase P2)

**Method:** `lean/porting-playbook.md` §2.2 (audit the route, mathlib first), after the
phase-1 template [`AUDIT-mathlib.md`](AUDIT-mathlib.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`, `lake-manifest.json` rev `5ed2965`). Inventory:
[`tools/deps/build/p2_inventory.txt`](../../../tools/deps/build/p2_inventory.txt).

Sources, in pin order:

- [`P2M/Sol/S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean) (64 ln)
- [`P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean) (63 ln)
- [`P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean) (1,723 ln)

**Class convention** (unchanged from phase 1). SUBSTITUTE = the port can import an
existing declaration instead of proving the row, either a mathlib constant or a
port-local lemma already landed in phase 1 / the refactor round. PROOF-INGREDIENT =
statement bespoke (must be written) but the proof is assembled from named
mathlib lemmas. BESPOKE = a definition/structure/instance object with no mathlib
analogue; the recorded negatives that are this phase's real work.

**Scratch evidence:** `lean/ScratchAuditP2.lean` (gitignored; **removed at the
phase-2 closeout**, so the classifications below are the retained record), compiled
from `lean/` with

```
flock /tmp/flt_for_human.lock timeout 120 lake env lean \
  -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP2.lean
```

final run clean (exit 0; only `haveI`/`letI` style warnings and one deprecation).
The `#check` ledger of every mathlib constant the pin reaches resolved in full; the
only failing probe was the deliberate negative in §5.6.

## 1. Summary — class counts per file

| pin file | SUBSTITUTE | PROOF-INGREDIENT | BESPOKE | rows |
|---|---:|---:|---:|---:|
| `S_KaehlerDifferential_span_D_eq_top_of_transcendental` | 0 | 2 | 0 | 2 |
| `S_KaehlerDifferential_D_ne_zero_of_transcendental` | 0 | 2 | 0 | 2 |
| `S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver` | 6 | 107 | 23 | 136 |
| **total** | **6** | **111** | **23** | **140** |

**Inventory correction.** `tools/deps/build/p2_inventory.txt` counts 134 declarations
(2 + 2 + 130), but the big file contains **six more**: the inventory tool omits
`instance` declarations (as phase 1 noted it omits `class`). They are
`instSMulCommClass_subring` (`:35`, private), `centerIdeal_isPrime` (`:451`),
`centerLocalizationSubalgebra_isLocalization` (`:593`),
`centerLocalizationSubalgebra_isDomain` (`:597`),
`centerLocalizationSubalgebra_isFractionRing` (`:608`),
`centerLocalizationValuationSubring_isDiscreteValuationRing` (`:638`). So the true row
count is **140**, and the transcription checklist must add these six from source.

The audit's headline negative is that the phase's objects are irreducible: the eleven
public model predicates/defs (`ValSubring*`, `IsAffineChart`, `ValSubringTwoAffineCharts`,
`transcendentalChart`, `HasSeparatingTranscendental`) plus eleven pin-private defs and
one private instance are BESPOKE. Conversely the Kähler half is *entirely* mathlib:
both headlines and their shared `exists_basis` prelude compile from mathlib imports
alone with the pin proof transcribed verbatim (§3, probes K1–K2).

## 2. Per-file tables

### 2.1 `S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean` (2 rows)

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `KaehlerDifferential.FF2.exists_basis` (private, `:22`) | PROOF-INGREDIENT | `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`, `KaehlerDifferential.polynomialEquiv`, `Module.Basis.singleton`/`map`/`baseChange`, `Algebra.FormallyEtale.{of_isLocalization,of_equiv,of_isSeparable,comp}`, `RatFunc.algEquivOfTranscendental`, `RatFunc.algEquivOfTranscendental_X` | Probe K1/K2 reproduce the body with pin imports removed; statement `∃ b : Module.Basis Unit F Ω[F⁄K], b () = D K F x` has no mathlib analogue |
| `solution` = headline `span_D_eq_top_of_transcendental` (`:57`) | PROOF-INGREDIENT | `Module.Basis.span_eq`, `Set.range_unique` | BESPOKE statement (no `KaehlerDifferential.span_singleton_D` in mathlib, §5.1); proof is 3 lines off `exists_basis`. Probe K1 |

### 2.2 `S_KaehlerDifferential_D_ne_zero_of_transcendental.lean` (2 rows)

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `KaehlerDifferential.FF2.exists_basis` (private, `:22`) | PROOF-INGREDIENT | identical to §2.1 | byte-identical to the §2.1 private helper |
| `solution` = headline `D_ne_zero_of_transcendental` (`:57`) | PROOF-INGREDIENT | `Module.Basis.ne_zero` | BESPOKE statement; proof is `simpa [hb] using b.ne_zero ()`. Probe K2 |

### 2.3 `S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean` — public declarations (72 rows)

Line numbers are pin lines. The five instances at the end are outside the inventory
(§1).

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `ValSubringKaehlerSpanTop` (`:52`) | BESPOKE | — | `Prop` over `Place`/`uniformizerSubring'`; no analogue |
| `ValSubringPolynomialFormallyUnramified` (`:154`) | BESPOKE | — | `Prop`, `Subsingleton Ω[O⁄K[X]]` under the pin's `polynomialAlgebra` |
| `valSubringKaehlerSpanTop_of_polynomialFormallyUnramified` (`:161`) | PROOF-INGREDIENT | private `span_D_uniformizer_eq_top_of_subsingleton` | one application |
| `ValSubringKaehlerFinite` (`:299`) | BESPOKE | — | `Prop`, `Module.Finite O Ω[O⁄K]` |
| `valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_isSeparable` (`:304`) | PROOF-INGREDIENT | `IsLocalRing.subsingleton_tensorProduct`, `Algebra.FormallyUnramified.{of_isSeparable,of_restrict_scalars,subsingleton_kaehlerDifferential}` | residue engine §2.4-G5 |
| `ValSubringEssFiniteType` (`:349`) | BESPOKE | — | `Prop`, `Algebra.EssFiniteType K O` |
| `ValSubringFiniteTypeModel` (`:352`) | BESPOKE | — | `Prop`, `∃ S₀ M, FiniteType K S₀ ∧ IsLocalization M O` |
| `valSubringKaehlerFinite_of_essFiniteType` (`:359`) | PROOF-INGREDIENT | `KaehlerDifferential.finite` | one line |
| `valSubringEssFiniteType_of_finiteTypeModel` (`:365`) | PROOF-INGREDIENT | `Algebra.essFiniteType_iff_exists_subalgebra` | |
| `valSubringEssFiniteType_iff_finiteTypeModel` (`:370`) | PROOF-INGREDIENT | `Algebra.essFiniteType_iff_exists_subalgebra` | both directions are that iff |
| `valSubringKaehlerFinite_of_finiteTypeModel` (`:378`) | PROOF-INGREDIENT | previous two | composition only |
| `eq_top_of_idealOfLE_eq_bot_s12` (`:398`) | PROOF-INGREDIENT | `ValuationSubring.ofPrime_idealOfLE`, `ValuationSubring.ofPrime_bot` | needs the pin's `ofPrime_congr_s12`; see §5.6 |
| `idealOfLE_ne_bot_of_ne_top_s12` (`:403`) | PROOF-INGREDIENT | contrapositive of the previous | |
| `eq_of_isDiscreteValuationRing_of_le_s12` (`:407`) | **SUBSTITUTE** | `ValuationSubring.eq_of_le_of_ne_top` | Probe V1; the pin's `[IsDiscreteValuationRing R]` is not needed by mathlib (its `[Ring.KrullDimLE 1 R]` comes from that instance) |
| `coe_modelInclusion` (`:439`) | PROOF-INGREDIENT | `rfl` over `Subring.inclusion` | pin-def projection |
| `ValSubringDedekindModel` (`:500`) | BESPOKE | — | `Prop` with the pin's `centerIdeal` localisation |
| `valSubringEssFiniteType_of_dedekindModel` (`:509`) | PROOF-INGREDIENT | `Algebra.EssFiniteType.of_isLocalization`, `Algebra.EssFiniteType.comp` | |
| `valSubringFiniteTypeModel_of_dedekindModel` (`:515`) | PROOF-INGREDIENT | `valSubringEssFiniteType_iff_finiteTypeModel` | |
| `coe_centerLocalizationValuationSubring` (`:634`) | PROOF-INGREDIENT | `rfl` | |
| `coe_centerLocalizationSubalgebra_eq` (`:654`) | PROOF-INGREDIENT | `ValuationSubring.eq_of_le_of_ne_top` (via private `centerLocalizationValuationSubring_eq`), `congrArg` | |
| `ValSubringDedekindFractionModel` (`:705`) | BESPOKE | — | `Prop`, finite-type Dedekind fraction model |
| `valSubringDedekindModel_of_dedekindFractionModel` (`:712`) | PROOF-INGREDIENT | private `isLocalization_centerIdeal_of_isDedekindDomain` | |
| `IsAffineChart` (`:783`) | BESPOKE | — | `Prop`; no mathlib `affine chart` on `Subalgebra K F` |
| `ValSubringTwoAffineCharts` (`:786`) | BESPOKE | — | `Prop` |
| `valSubringDedekindFractionModel_of_twoAffineCharts` (`:793`) | PROOF-INGREDIENT | `rcases` on the cover | |
| `valSubringDedekindModel_of_twoAffineCharts` (`:801`) | PROOF-INGREDIENT | previous two | |
| `gate_adjoin_subset_valuationSubring_of_mem` (`:837`) | PROOF-INGREDIENT | `Algebra.adjoin_le`, `Set.singleton_subset_iff` | |
| `transcendentalChart` (`:902`) | BESPOKE | `integralClosure`, `Subalgebra.restrictScalars` | definition is mathlib terms on a pin-new object |
| `coe_transcendentalChart` (`:905`) | PROOF-INGREDIENT | `rfl` | |
| `transcendentalChart_subset_valuationSubring_of_mem` (`:912`) | PROOF-INGREDIENT | private `integralClosure_subset_valuationSubring`, `gate_adjoin_...` | |
| `transcendentalChart_subset_or_inv_subset` (`:919`) | PROOF-INGREDIENT | `ValuationSubring.mem_or_inv_mem` | |
| `isScalarTower_integralClosure_subalgebra` (`:937`) | **SUBSTITUTE** | mathlib instance `IsScalarTower R' R S` for `S : Subalgebra R A` (`Algebra/Algebra/Subalgebra/Basic.lean:317`; also `:819`) | Probe S1: `inferInstance` closes it in v4.34.0 |
| `finiteType_integralClosure_of_moduleFinite` (`:942`) | PROOF-INGREDIENT | `Algebra.FiniteType.trans` | |
| `isDedekindDomain_integralClosure_adjoin` (`:952`) | PROOF-INGREDIENT | `integralClosure.isDedekindDomain` | |
| `isFractionRing_integralClosure_adjoin` (`:958`) | PROOF-INGREDIENT | `integralClosure.isFractionRing_of_finite_extension` | |
| `moduleFinite_integralClosure_adjoin` (`:963`) | PROOF-INGREDIENT | `IsIntegralClosure.finite` | |
| `finiteType_integralClosure_adjoin` (`:972`) | PROOF-INGREDIENT | `finiteType_integralClosure_of_moduleFinite`, `Algebra.FiniteType.adjoin_of_finite` | |
| `isAffineChart_restrictScalars_integralClosure` (`:978`) | PROOF-INGREDIENT | anonymous constructor | |
| `isAffineChart_transcendentalChart` (`:985`) | PROOF-INGREDIENT | previous four | 4 mathlib calls |
| `HasSeparatingTranscendental` (`:1000`) | BESPOKE | — | `Prop`; no analogue |
| `valSubringTwoAffineCharts_of_hasSeparatingTranscendental` (`:1007`) | PROOF-INGREDIENT | `isAffineChart_transcendentalChart`, `transcendentalChart_subset_or_inv_subset`, private `Transcendental.inv_s12` | |
| `valSubringDedekindModel_of_hasSeparatingTranscendental` (`:1016`) | PROOF-INGREDIENT | previous + `valSubringDedekindModel_of_twoAffineCharts` | |
| `IntermediateField.adjoin_simple_inv_s12` (`:1036`) | PROOF-INGREDIENT | `IntermediateField.adjoin_simple_le_iff`, `inv_mem`, `mem_adjoin_simple_self` | Probe T2; no `IntermediateField.adjoin_simple_inv` in mathlib (§5.5) |
| `IntermediateField.algebraMap_comp_equivOfEq_s12` (`:1043`) | PROOF-INGREDIENT | `IntermediateField.equivOfEq`, `RingHom.ext` | `ext x; rfl` |
| `IntermediateField.finiteDimensional_of_eq_s12` (`:1048`) | PROOF-INGREDIENT | `Module.Finite.of_equiv_equiv` | Probe T3; the previous lemma supplies the `algebraMap` compatibility |
| `IntermediateField.isSeparable_of_eq_s12` (`:1053`) | PROOF-INGREDIENT | `Algebra.IsSeparable.of_equiv_equiv` | Probe T4 |
| `IntermediateField.finiteDimensional_adjoin_inv_s12` (`:1058`) | PROOF-INGREDIENT | `finiteDimensional_of_eq_s12`, `adjoin_simple_inv_s12` | |
| `IntermediateField.isSeparable_adjoin_inv_s12` (`:1062`) | PROOF-INGREDIENT | `isSeparable_of_eq_s12`, `adjoin_simple_inv_s12` | |
| `Place.dCoordGenerates_of_valSubringKaehlerSpanTop` (`:1080`) | PROOF-INGREDIENT | `KaehlerDifferential.span_range_map_derivation_of_isLocalization`, `Submodule.map_span`, `Submodule.span_le_restrictScalars`, `Submodule.mem_map_of_mem`, private `kaehlerMap_subring_D_uniformizer` | |
| `isSeparable_residueField_forall_of_perfectField` (`:1134`) | PROOF-INGREDIENT | `Algebra.IsAlgebraic.of_finite`, `Algebra.IsAlgebraic.isSeparable_of_perfectField` | |
| `valSubringKaehlerSpanTop_of_kaehlerFinite_of_isSeparable` (`:1147`) | PROOF-INGREDIENT | previous two engines | |
| `Place.dCoordGenerates_of_valSubringKaehlerFinite_of_isSeparable` (`:1155`) | PROOF-INGREDIENT | previous + `dCoordGenerates_of_valSubringKaehlerSpanTop` | |
| `Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField` (`:1170`) | PROOF-INGREDIENT | previous + `isSeparable_residueField_forall_of_perfectField` | |
| `Place.dCoordGenerates_of_valSubringFiniteTypeModel_of_perfectField` (`:1196`) | PROOF-INGREDIENT | `valSubringKaehlerFinite_of_finiteTypeModel` + previous | |
| `Place.dCoordGenerates_of_valSubringDedekindModel_of_perfectField` (`:1204`) | PROOF-INGREDIENT | `valSubringFiniteTypeModel_of_dedekindModel` + previous | |
| `Place.dCoordGenerates_of_hasSeparatingTranscendental_of_perfectField` (`:1212`) | PROOF-INGREDIENT | `valSubringDedekindModel_of_hasSeparatingTranscendental` + previous | |
| `hasSeparatingTranscendental_of_isCurveOver_of_perfectField` (`:1220`) | PROOF-INGREDIENT | port `IsCurveOver.exists_separating_transcendental` (`IsCurveOver/SeparatingTranscendental.lean:138`), `IntermediateField.{finiteDimensional,isSeparable}_adjoin_inv_s12` | the port prerequisite is already landed |
| `valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField_s12` (`:1247`) | PROOF-INGREDIENT | the whole model chain above | pure composition, no new lemma |
| `exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver_s12` (`:1387`) | PROOF-INGREDIENT | private `exists_ord_eq_zero_D_eq_smul_D_s12` + `dCoordGenerates_...` | |
| `exists_mem_D_eq_smul_D_of_isCurveOver_s12` (`:1395`) | PROOF-INGREDIENT | private `exists_mem_D_eq_smul_dCoord_s12`, `exists_unit_D_eq_smul_dCoord_s12` | |
| `hasCanonicalDivisor_of_generator_finiteSupport_s12` (`:1432`) | PROOF-INGREDIENT | `Submodule.mem_span_singleton`, `Finsupp.onFinset`, `Finsupp.add_apply`, port `HasPrincipalDivisors.exists_divisor`, `Place.ordDifferential_smul` | the finite-support canonical-divisor assembly |
| `mem_span_D_adjoin_s12` (`:1501`) | PROOF-INGREDIENT | `KaehlerDifferential.span_range_derivation`, `Algebra.adjoin_singleton_eq_range_aeval`, `Derivation.map_aeval` | |
| `Place.eq_of_centerIdeal_eq_s12` (`:1577`) | PROOF-INGREDIENT | `ValuationSubring.eq_of_le_of_ne_top`, private `centerLocalizationValuationSubring_eq`, `div_mem_of_not_mem_centerIdeal` | the injectivity of `centerIdeal` |
| `adjoin_le_transcendentalChart_s12` (`:1592`) | PROOF-INGREDIENT | `mem_integralClosure_iff`, `isIntegral_algebraMap` | |
| `finite_ordDifferential_D_ne_zero_s12` (`:1601`) | PROOF-INGREDIENT | `differentIdeal_ne_bot`, `Ideal.finite_factors`, `not_dvd_differentIdeal_iff`, `Finite.of_injective`, `FractionRing.algEquiv`, `IsFractionRing.algEquiv_commutes`, `Algebra.IsSeparable.of_equiv_equiv`, `Module.IsTorsionFree` API, `IsPrincipalIdealRing.of_surjective` | deepest row: 95 lines, all mathlib assembly + `Place.eq_of_centerIdeal_eq_s12` |
| `hasCanonicalDivisor_of_isCurveOver_s12` (`:1696`) | PROOF-INGREDIENT | the two Kähler headlines, `hasCanonicalDivisor_of_generator_finiteSupport_s12`, `finite_ordDifferential_D_ne_zero_s12` | |
| `solution` (headline, `:1719`) | PROOF-INGREDIENT | `hasCanonicalDivisor_of_isCurveOver_s12` | one line |
| `centerIdeal_isPrime` (`:451`, `instance`) | PROOF-INGREDIENT | `Ideal.comap_isPrime` | not in the inventory |
| `centerLocalizationSubalgebra_isLocalization` (`:593`, `instance`) | PROOF-INGREDIENT | `Localization.subalgebra.isLocalization_ofField` | not in the inventory |
| `centerLocalizationSubalgebra_isDomain` (`:597`, `instance`) | PROOF-INGREDIENT | `inferInstanceAs` | not in the inventory |
| `centerLocalizationSubalgebra_isFractionRing` (`:608`, `instance`) | PROOF-INGREDIENT | `inferInstanceAs` | not in the inventory |
| `centerLocalizationValuationSubring_isDiscreteValuationRing` (`:638`, `instance`) | PROOF-INGREDIENT | private `centerLocalizationSubalgebra_isDiscreteValuationRing` | not in the inventory |

### 2.4 Private helpers, grouped by mathlib ingredient

All 64 private declarations (63 inventory rows + `instSMulCommClass_subring`). Each
group names the mathlib facts its proofs consume; the group's BESPOKE members are
definitions.

| group | private decls | class of the theorems | mathlib ingredients |
|---|---|---|---|
| G1 uniformizer aliases | `uniformizerSubring'` (`:31`), `uniformizerSubring''` (`:75`), `uniformizerSubring'''` (`:184`) | BESPOKE (defs) | `IsDiscreteValuationRing.exists_irreducible`; all three duplicate the port's `Place.uniformizer` (`Defs/CanonicalDivisor.lean:39`) |
| G2 Kähler map | `kaehlerMap_subring_D_uniformizer` (`:38`) | PROOF-INGREDIENT | `KaehlerDifferential.map_D` |
| G3 polynomial model | `polynomialAlgebra` (`:79`), `polynomialAlgebra_algebraMap_X` (`:83`), `polynomialIsScalarTower` (`:89`) | def BESPOKE; theorems PI | `Polynomial.aeval`, `aeval_X`, `Polynomial.algebraMap_eq`, `aeval_C`, `IsScalarTower.of_algebraMap_eq` |
| G4 cotangent engine | `range_mapBaseChange_le_span_D_uniformizer` (`:98`), `range_mapBaseChange_eq_top_of_subsingleton` (`:122`), `span_D_uniformizer_eq_top_of_subsingleton` (`:135`) | PROOF-INGREDIENT | `KaehlerDifferential.mapBaseChange_tmul`, `polynomialEquiv`/`polynomialEquiv_symm`, `map_D`, `range_mapBaseChange`, `LinearMap.ker_eq_top`, `Submodule.smul_mem`, `Submodule.mem_span_singleton_self`, `algebraMap_smul` |
| G5 residue engine | `irreducible_uniformizerSubring'''` (`:188`), `maximalIdeal_eq_span_uniformizer` (`:192`), `D_polynomialAlgebra_uniformizer` (`:197`), `ker_algebraMap_residueField_eq_span` (`:206`), `formallyUnramified_polynomial_residueField_of_isSeparable` (`:213`), `subsingleton_residueKaehler_of_isSeparable` (`:224`), `subsingleton_residueTensor_polynomialKaehler_of_isSeparable` (`:233`), `finite_polynomialKaehler_of_finite_kaehler` (`:269`), `subsingleton_polynomialKaehler_of_isSeparable_of_finite` (`:280`) | PROOF-INGREDIENT | `IsDiscreteValuationRing.irreducible_iff_uniformizer`, `Derivation.map_algebraMap`, `IsLocalRing.ResidueField.algebraMap_eq`, `IsLocalRing.ker_residue`, `Algebra.FormallyUnramified.{of_isSeparable,of_restrict_scalars,subsingleton_kaehlerDifferential}`, `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`, `kerCotangentToTensor_toCotangent`, `Ideal.toCotangent_surjective`, `Derivation.leibniz`, `TensorProduct.{tmul_add,tmul_smul,smul_tmul,zero_tmul}`, `KaehlerDifferential.map_surjective`, `Module.Finite.of_surjective`, `IsLocalRing.subsingleton_tensorProduct` |
| G6 EFT engine | `finite_kaehler_of_essFiniteType` (`:328`), `essFiniteType_of_exists_finiteType_isLocalization` (`:333`) | PROOF-INGREDIENT | `KaehlerDifferential.finite`, `Algebra.essFiniteType_iff_exists_subalgebra` |
| G7 center model | `modelInclusion` (`:435`), `modelAlgebra` (`:442`), `centerIdeal` (`:446`), `instSMulCommClass_subring` (`:35`), `isUnit_modelInclusion_of_not_mem_centerIdeal` (`:455`), `isUnit_modelInclusion_of_mem_primeCompl` (`:465`), `modelAlgebra_isScalarTower` (`:470`), `essFiniteType_of_finiteType_isLocalization_centerIdeal` (`:480`) | defs + instance BESPOKE; theorems PI | `Subring.inclusion`, `Subring.inclusion_injective`, `IsScalarTower.to_smulCommClass`, `Ideal.mem_comap`, `IsLocalRing.mem_maximalIdeal`, `mem_nonunits_iff`, `IsScalarTower.of_algebraMap_eq`, `Algebra.EssFiniteType.of_isLocalization`, `Algebra.EssFiniteType.comp` |
| G8 center localization | `inv_mem_of_not_mem_centerIdeal` (`:539`), `div_mem_of_not_mem_centerIdeal` (`:553`), `centerIdeal_ne_bot_of_isFractionRing` (`:560`), `centerLocalizationSubalgebra` (`:587`), `centerLocalizationSubalgebra_isDiscreteValuationRing` (`:601`), `centerLocalizationSubalgebra_subset` (`:612`), `centerLocalizationValuationSubring` (`:623`), `centerLocalizationValuationSubring_le` (`:643`), `centerLocalizationValuationSubring_eq` (`:648`), `mem_centerLocalizationSubalgebra_of_mem` (`:660`), `isLocalization_centerIdeal_of_isDedekindDomain` (`:666`) | defs BESPOKE; theorems PI | `IsFractionRing.div_surjective`, `ValuationSubring.toSubring_injective`, `nonZeroDivisors.ne_zero`, `Localization.subalgebra.ofField`, `Localization.subalgebra.isLocalization_ofField`, `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, `ValuationRing.isInteger_or_isInteger`, `ValuationSubring.eq_of_le_of_ne_top`, `isLocalization_iff`, `Ideal.zero_mem` |
| G9 integrally closed | `isIntegrallyClosed_toValuationSubring` (`:735`), `mem_valuationSubring_of_isIntegral` (`:739`), `modelAlgebra_isScalarTower_top` (`:749`), `mem_valuationSubring_of_isIntegral_subalgebra` (`:758`), `integralClosure_subset_valuationSubring` (`:767`) | **SUBSTITUTE** (`:735`); rest PI | mathlib instance `IsIntegrallyClosed V` (`RingTheory/Valuation/LocalSubring.lean:35,38`), `isIntegrallyClosed_iff`, `IsIntegral.tower_top`, `IsScalarTower.of_algebraMap_eq` |
| G10 adjoin ring properties | `ofPrime_congr_s12` (`:394`), `Transcendental.isPrincipalIdealRing_adjoin_s12` (`:860`), `Transcendental.isDedekindDomain_adjoin_s12` (`:867`), `Transcendental.isIntegrallyClosed_adjoin_s12` (`:873`), `Transcendental.isNoetherianRing_adjoin_s12` (`:879`), `Algebra.FiniteType.adjoin_singleton_s12` (`:885`), `Transcendental.inv_s12` (`:890`) | PROOF-INGREDIENT | `Polynomial.algEquivOfTranscendental`, `IsPrincipalIdealRing.of_surjective`, `IsPrincipalIdealRing.isDedekindDomain`, `Algebra.FiniteType.adjoin_of_finite`, `IsAlgebraic.inv_iff`; `ofPrime_congr_s12` is the pin's `subst`-workaround (§5.6) |
| G11 ord/D helpers | `ord_nonneg_of_mem_s12` (`:1265`), `mem_of_ord_nonneg_s12` (`:1281`), `ord_uniformizerSubring'_s12` (`:1290`), `dCoord_eq_D_uniformizerSubring'_s12` (`:1294`), `exists_mem_D_eq_smul_dCoord_s12` (`:1299`), `exists_unit_D_eq_smul_dCoord_s12` (`:1317`), `exists_ord_eq_zero_D_eq_smul_D_s12` (`:1373`) | first three **SUBSTITUTE** (port `Place.ord_nonneg_of_mem`, `Place.mem_of_ord_nonneg`, `Place.ord_uniformizer`); rest PI | `IsDiscreteValuationRing.{exists_irreducible,eq_unit_mul_pow_irreducible}`, `Submodule.mem_span_singleton`, `LinearMap.map_smul_of_tower`, `KaehlerDifferential.map_D`, `algebraMap_smul`, `Derivation.leibniz`, `smul_eq_zero`, `IsLocalRing.mem_maximalIdeal`, `Ideal.eq_top_iff_one`, `IsLocalRing.maximalIdeal.isMaximal` |
| G12 ramification helpers | `ordDifferential_D_eq_zero_of_span_eq_top_s12` (`:1452`), `span_D_eq_top_of_isUnramifiedAt_s12` (`:1523`) | PROOF-INGREDIENT | `Submodule.mem_span_singleton`, port `Place.differentialCoeff_unique`, `IsLocalization.algEquiv`, `Algebra.FormallyUnramified.of_equiv`, `.subsingleton_kaehlerDifferential`, `KaehlerDifferential.range_mapBaseChange`, `mapBaseChange_tmul`, `map_D`, `mem_span_D_adjoin_s12` |
| G13 toKSubalgebra | `toKSubalgebra` (`:824`), `coe_toKSubalgebra` (`:832`) | def BESPOKE; theorem PI | `rfl` |
| G14 residue separability | `Place.isSeparable_residueField_of_perfectField_of_finiteResidue` (`:1123`) | PROOF-INGREDIENT | `Algebra.IsAlgebraic.of_finite`, `Algebra.IsAlgebraic.isSeparable_of_perfectField`, port `Place.FiniteResidue.finite` |

## 3. Reuse wins, with probe evidence

All in `ScratchAuditP2.lean`, final run exit 0.

1. **The two Kähler headlines are mathlib-only.** Probes K1/K2 transcribe the pin's
   `exists_basis` with `P2M.Util`/`p2m_open` removed and discharge both wrappers:
   ```lean
   example … : Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) = ⊤
   example … : KaehlerDifferential.D K F x ≠ 0
   ```
   The only edit needed against v4.34.0 is `AlgEquiv.coe_algHom` →
   `AlgEquiv.coe_toAlgHom` (deprecation warning, not an error). No port vocabulary is
   needed for `KaehlerTranscendental.lean` beyond mathlib.
2. **`Place.eq_of_isDiscreteValuationRing_of_le_s12` is `ValuationSubring.eq_of_le_of_ne_top`**
   (probe V1):
   ```lean
   example (R S : ValuationSubring F) [IsDiscreteValuationRing R] (h : R ≤ S) (hS : S ≠ ⊤) : R = S :=
     ValuationSubring.eq_of_le_of_ne_top R h hS
   ```
   mathlib's version asks `[Ring.KrullDimLE 1 R]`, supplied by the
   `IsDiscreteValuationRing` instance; the pin's `IsDiscreteValuationRing` hypothesis
   is otherwise unused. This collapses the equality of valuation rings used by
   `Place.eq_of_centerIdeal_eq_s12`.
3. **`Place.isIntegrallyClosed_toValuationSubring` is a mathlib instance** (probe V2):
   `IsIntegrallyClosed V` and `IsIntegrallyClosed V.toSubring` are both
   `inferInstance` (`RingTheory/Valuation/LocalSubring.lean:35,38`).
4. **`isScalarTower_integralClosure_subalgebra` is a mathlib instance** (probe S1):
   `IsScalarTower K B ↥(integralClosure B F)` closes by `inferInstance`. The pin's
   explicit `IsScalarTower.of_algebraMap_eq` proof is unnecessary in v4.34.0.
5. **`IntermediateField.{finiteDimensional,isSeparable}_of_eq_s12` are the
   `…of_equiv_equiv` lemmas** (probes T3/T4), with
   `algebraMap_comp_equivOfEq_s12` as the compatibility hypothesis (`ext x; rfl`).
6. **`Algebra.FiniteType.adjoin_singleton_s12`** is
   `Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)` (probe T5).
7. **Already-landed port vocabulary removes three more rows** (no probe; source
   citations): `Place.ord_nonneg_of_mem` (`Defs/PushPull.lean:43`) ≡
   `ord_nonneg_of_mem_s12`; `Place.mem_of_ord_nonneg` (`Defs/PushPull.lean:60`) ≡
   `mem_of_ord_nonneg_s12`; `Place.ord_uniformizer` (`Defs/CanonicalDivisor.lean:42`) ≡
   `ord_uniformizerSubring'_s12`. The port's `Place`/`HasCanonicalDivisor` layer itself
   is phase-1 material and is not re-audited here (see `AUDIT-mathlib.md` §2.1–2.2,
   §5.4).

## 4. Route options — chains one mathlib fact could replace

* **R1 — the residue engine (pin `:206–288`).** `ValSubringPolynomialFormallyUnramified`
  from `ValSubringKaehlerFinite` + separable residue is proved through
  `ResidueField ⊗ Ω → Ω` exactness. After the SUBSTITUTE rows, the whole conclusion is
  `(IsLocalRing.subsingleton_tensorProduct).mp` of the residue-tensor vanishing, and
  the residue-tensor vanishing is
  `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential` at
  `K[X] → ResidueField` (from `of_isSeparable` + `of_restrict_scalars`). Keep the
  pin's nine private steps; they are already at this cost.
* **R2 — the valuation-subring comparison chain (`:394–416`, `:643–658`, `:1577–1590`).**
  `ValuationSubring.eq_of_le_of_ne_top` (reuse win 2) replaces
  `eq_of_isDiscreteValuationRing_of_le_s12` and is the last step of
  `centerLocalizationValuationSubring_eq` and `Place.eq_of_centerIdeal_eq_s12`. The
  surrounding `ofPrime`/`idealOfLE` reasoning (`:398–405`) must stay: mathlib's
  `ofPrime` cannot be rewritten under a changed prime ideal (§5.6).
* **R3 — the affine-chart engine (`:937–991`).** `transcendentalChart K t` is an
  `IsAffineChart` in four mathlib calls:
  `Algebra.FiniteType.adjoin_of_finite` + `Algebra.FiniteType.trans` (`:972`),
  `IsIntegralClosure.finite` (`:963`), `integralClosure.isDedekindDomain` (`:952`),
  `integralClosure.isFractionRing_of_finite_extension` (`:958`). The tower instance
  (`:937`) is free (reuse win 4). No bespoke mathematics remains in this block.
* **R4 — the `D`-generation engine (`:1080–1101`).**
  `Place.dCoordGenerates_of_valSubringKaehlerSpanTop` is one application of
  `KaehlerDifferential.span_range_map_derivation_of_isLocalization` plus
  `Submodule.map_span` and `Submodule.span_le_restrictScalars`; every downstream
  `dCoordGenerates_of_*` is composition. This is the port's only bridge from the
  generic Kähler span hypothesis to the port's `Place.DCoordGenerates`.
* **R5 — the finiteness of ramified places (`:1644–1694`).** After
  `hasSeparatingTranscendental_of_isCurveOver_of_perfectField` (port prerequisite) the
  set `{v | ordDifferential (D t) ≠ 0}` is the union of the poles of `t` and the
  pullback of `Ideal.finite_factors (differentIdeal_ne_bot)` along the injective map
  `v ↦ v.centerIdeal (transcendentalChart K t)`. Each piece is mathlib
  (`Finsupp.support.finite_toSet`, `Ideal.finite_factors`, `Finite.of_injective`); the
  only bespoke input is `Place.eq_of_centerIdeal_eq_s12` (injectivity of `centerIdeal`).
  The route cannot be shortened below this because no mathlib fact packages
  "ramified places of a finite separable extension are finite" in the pin's `Place`
  vocabulary.

## 5. Recorded negatives

Confirmed against mathlib `v4.34.0` (`grep -rIl` over `Mathlib/`); phrased so the
search is not repeated.

1. **No `KaehlerDifferential.D_ne_zero`, `D_eq_zero`, `span_singleton_D`** (nor any
   `D_ne_zero_of_transcendental`). The `D_eq_zero` hits are `Algebra/Homology`
   (`Homotopy`), unrelated. The two Kähler headlines are bespoke statements whose
   proofs are pure mathlib (§3.1).
2. **No `Place.fiberOver` in the pin's sense.** mathlib's `fiberOver`
   (`AlgebraicGeometry/Fiber.lean`) is the scheme-theoretic fiber of a morphism; it
   has nothing to do with the port's ramification counting. The pin's concept lives in
   `WeilExchange/FiberOverCount.lean` and is not a mathlib substitution.
3. **No `centerIdeal`, `ValSubring*` (any suffix), `transcendentalChart`,
   `HasSeparatingTranscendental`, `IsAffineChart`, `isUnramifiedAt_s12`** anywhere in
   mathlib. These ten public predicates/defs plus `transcendentalChart` are BESPOKE.
4. **No `ordDifferential`, `differentialCoeff`, `dCoord`, `DCoordGenerates`,
   `HasCanonicalDivisor`, `canonicalDivisor`** — reconfirms phase-1 §5.4 for the P2
   vocabulary. The `dCoord` hits are manifold chart coordinates.
5. **No `IntermediateField.adjoin_simple_inv`** (and no `Transcendental.inv`; only
   `Transcendental.linearIndependent_sub_inv` and the `IsAlgebraic.inv_iff` alias).
   `adjoin_simple_inv_s12` and `Transcendental.inv_s12` are bespoke statements built
   from `adjoin_simple_le_iff`/`inv_mem`/`mem_adjoin_simple_self` and
   `IsAlgebraic.inv_iff`.
6. **No `ValuationSubring.ofPrime_congr`; and the `idealOfLE = ⊥` rewrite under
   `ofPrime` is blocked.** Probe V1b (`rw [← ofPrime_idealOfLE, hbot, ofPrime_bot]`)
   fails with "motive is not type correct": `ofPrime` carries `[P.IsPrime]`, an
   instance depending on the ideal being rewritten. The pin's `ofPrime_congr_s12` is
   load-bearing, not cosmetic. Likewise `eq_top_of_idealOfLE_eq_bot_s12` /
   `idealOfLE_ne_bot_of_ne_top_s12` stay bespoke statements over that helper.
7. **No `Algebra.FiniteType.adjoin_singleton`**; only
   `Algebra.FiniteType.adjoin_of_finite`, which is what the pin calls at the singleton.
8. **No mathlib packaging of "finitely many ramified places"** in the pin's `Place`
   vocabulary (§4 R5): the finiteness assembly in `finite_ordDifferential_D_ne_zero_s12`
   is bespoke, and `IsUnramifiedAt` at the pin's `span_D_eq_top_of_isUnramifiedAt_s12`
   shape has no direct statement — only the `FormallyUnramified`/`Algebra.IsUnramifiedAt`
   API the proof uses.
9. **No mathlib `Place`/`ResidueField` separability instance.** `Algebra.IsSeparable K
   (ResidueField O)` needs `[PerfectField K]` and `[v.FiniteResidue]`; the pin's
   `Place.isSeparable_residueField_of_perfectField_of_finiteResidue` is the bespoke
   bridge (`Algebra.IsAlgebraic.of_finite` + `…isSeparable_of_perfectField`).
10. **`port_advise`'s "already present" matches on `def … : Prop` predicates remain
    false positives** (as in phase 1 §5.11); do not bank them.

## 6. What this changes for `WORKORDER-P2-canonical.md`

**Scope/measurement.**
- The row count is **140**, not 134: transcribe the six instances at pin lines 35, 451,
  593, 597, 608, 638. Fix `p2_inventory.txt` (the tool must also emit `instance`).
- The two Kähler modules can import **mathlib only**; no pin prelude is needed. The
  `letI`/`haveI` instance walls transcribe verbatim; change `AlgEquiv.coe_algHom` to
  `AlgEquiv.coe_toAlgHom` (v4.34.0 deprecation).

**Declarations whose proof the port does not owe** (mark import-discharged; the
statements still land for the checker):
- `Place.eq_of_isDiscreteValuationRing_of_le_s12` — `ValuationSubring.eq_of_le_of_ne_top`.
- `Place.isIntegrallyClosed_toValuationSubring` — mathlib instance.
- `isScalarTower_integralClosure_subalgebra` — mathlib instance.
- `Place.ord_nonneg_of_mem_s12` — port `Place.ord_nonneg_of_mem` (`Defs/PushPull.lean:43`).
- `Place.mem_of_ord_nonneg_s12` — port `Place.mem_of_ord_nonneg` (`Defs/PushPull.lean:60`).
- `Place.ord_uniformizerSubring'_s12` — port `Place.ord_uniformizer`
  (`Defs/CanonicalDivisor.lean:42`).

**Declarations to rewrite in one mathlib call** (keep the pin statements, drop the
bodies): `valSubringKaehlerFinite_of_essFiniteType`,
`valSubringEssFiniteType_of_finiteTypeModel`/`_iff_finiteTypeModel`,
`IntermediateField.finiteDimensional_of_eq_s12`/`isSeparable_of_eq_s12`,
`Algebra.FiniteType.adjoin_singleton_s12` (private), `gate_adjoin_subset_valuationSubring_of_mem`,
`adjoin_le_transcendentalChart_s12`, `isDedekindDomain_integralClosure_adjoin`,
`isFractionRing_integralClosure_adjoin`, `moduleFinite_integralClosure_adjoin`,
`finiteType_integralClosure_adjoin`, `isAffineChart_transcendentalChart`.

**Statements to re-examine before transcribing (design decisions).**
- `uniformizerSubring'`/`''`/`'''` (`:31`, `:75`, `:184`): three copies of the port's
  `Place.uniformizer`. Prefer importing `Place.uniformizer` and deleting the aliases;
  the `_s12` order/coordinate lemmas then match phase-1 names.
- `transcendentalChart` and `IsAffineChart`: keep the pin's `Subalgebra K F`-level
  interface (route R3 makes its properties cheap); do not re-express via mathlib's
  scheme-theoretic `fiberOver`.
- `ofPrime_congr_s12` + `eq_top_of_idealOfLE_eq_bot_s12` + `idealOfLE_ne_bot_of_ne_top_s12`:
  keep bespoke (negative 6); mathlib cannot rewrite under `ofPrime`.
- `finite_ordDifferential_D_ne_zero_s12`: keep the pin's two-set union proof (route
  R5); it is the one place the bespoke `centerIdeal` injectivity is consumed.

**No change:** the eleven BESPOKE public objects, all pin-private defs, the
`attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra`
at `:1599` needed by the different-ideal block, and the `p2m_*` scaffolding drop list.

**Boundary check.** The target's proof reaches only declarations of the three measured
`S_` files plus the port's already-landed
`IsCurveOver.exists_separating_transcendental` (`IsCurveOver/SeparatingTranscendental.lean:138`),
`HasPrincipalDivisors.exists_divisor`, `Place.{ord_nonneg_of_mem,mem_of_ord_nonneg,ord_uniformizer,differentialCoeff_unique,ordDifferential_smul}`
and `Place.FiniteResidue.finite` — all in `Defs/`/`IsCurveOver/`. No stop-early risk 1
(name/statement drift) was found: the `#check` ledger resolved every mathlib name the
pin reaches.

**Scratch evidence (probe file removed at the phase-2 closeout):**
`lean/ScratchAuditP2.lean` — `#check` ledger (all resolved) plus
probes K1, K2, V1, V2, S1, T1–T5; one deliberate failing probe V1b documented in §5.6.
Three `flock`/`timeout 120` compiles; final exit 0.
