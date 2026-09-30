# Mathlib-first substitution audit — the phase-3.2b ℙ¹ residue core, chunk 1 (P3.2b)

**Method:** `lean/porting-playbook.md` §2.2 (audit the route, mathlib first), after the
phase-1/2/3.1/3.2a templates [`AUDIT-mathlib.md`](AUDIT-mathlib.md),
[`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md),
[`AUDIT-mathlib-p3-1.md`](AUDIT-mathlib-p3-1.md) and
[`AUDIT-mathlib-p3-2a.md`](AUDIT-mathlib-p3-2a.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Measured inventory:
[`tools/deps/build/p32_master_inventory.txt`](../../../tools/deps/build/p32_master_inventory.txt)
(rows 0–144), with the pre-port advice in
[`tools/deps/build/p32_engine_advise.log`](../../../tools/deps/build/p32_engine_advise.log)
(§1) and its machine-readable twin
[`p32_engine_advise.json`](../../../tools/deps/build/p32_engine_advise.json).

Source, the single pin `S_` file (13,173 ln, 580 declarations):

- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean),
  rows 0–144 = pin lines 295–3387.

**Class convention** (unchanged from phases 1–3.2a). SUBSTITUTE = the port can import
an existing declaration instead of proving the row: an already-landed port lemma or a
mathlib constant whose *type* is the pin's, or a pin `def`/`abbrev`/instance whose body
is `rfl`-equal to a mathlib/port term. A statement that differs from the port copy only
by binder spelling (the checker's `binder_only` near-duplicate) is counted SUBSTITUTE
with that difference recorded. PROOF-INGREDIENT = the statement is bespoke (it mentions
pin vocabulary) but the proof is a short assembly of named mathlib/port lemmas.
BESPOKE = a definition/structure/class/`Prop` introducing new vocabulary, or an
instance with no mathlib/port counterpart; these are the recorded negatives and the real
work.

**Scratch evidence (two probes; both gitignored):**

```bash
cd lean
timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP32b.lean
timeout 200 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP32bPort.lean
```

- `ScratchAuditP32b.lean` — the **mathlib** probe. Narrow imports, no `import Mathlib`.
  **exit 0, 4.6 s wall**, 184 lines of `#check` output; seven deliberate
  deprecation-warning lines covering six distinct renames (`if_neg`/`if_pos`,
  `Ideal.inertiaDeg'`, `dif_pos`, `Set.mem_setOf_eq`, `Polynomial.degree_sub_lt`) and no
  other diagnostic. It compiles the pin's rows 0–5
  verbatim as `proto_*` (with the one-line `if_neg` → `ite_eq_right` / `if_pos` →
  `ite_eq_left` rename forced by v4.34.0), the row-7/23 valuation/log ledger, the
  DVR/PID route, the ramification/inertia signatures, the `AdicCompletion.evalₐ`
  ledger and the drift probes.
- `ScratchAuditP32bPort.lean` — the **already-ported** probe. Imports the landed port
  modules only. **exit 0, 3.6 s wall**, all `#check`s resolve, which is the
  by-probe verification of every SUBSTITUTE port name tabulated below.

Everything marked "probe A…/B…/C…/F/G" is a term or `#check` in those two files, with
this ledger: **A1–A5** the `proto_*` theorems for pin rows 0–5 (§A of
`ScratchAuditP32b.lean`); **B1–B5** the `Valuation`/`WithZero` examples (§B);
**F** the `AdicCompletion.{evalₐ, evalOneₐ, …}` `#check` block (§F); **G** the drift
`#check`s (§G, plus the integrality block §E); **C1–C10** the port `#check`s in
`ScratchAuditP32bPort.lean` (C1 rows 12–22, C2 rows 8–11, C3 rows 45–52, C4 rows
39/97/100/101, C5 the `PlaceDictionary` out-of-set bridges, C6 rows 36/95, C7 rows
88–89, C8 rows 90–94, C9 rows 107–109, C10 rows 140–144). Statement
identity against the port is the statement checker's, read through `port_advise`
(`p32_engine_advise.json`), so a substitution reported here is one the checker agrees
with; the trivial-`Prop` false positives are called out in §1.

## 1. Summary — class counts

| pin region (row range) | SUBSTITUTE | PROOF-INGREDIENT | BESPOKE | rows |
|---|---:|---:|---:|---:|
| trace prelude + `OrdDifferentialWellDefined` (0–7) | 0 | 7 | 1 | 8 |
| `lg37_*` / `Lg37CompletionSection` (8–11) | 4 | 0 | 0 | 4 |
| ord/valuation prelude (12–23) | 11 | 1 | 0 | 12 |
| ℙ¹ place dictionary (24–34) | 11 | 0 | 0 | 11 |
| cotangent + ℙ¹ generators (35–44) | 4 | 2 | 4 | 10 |
| `Mp72a102T1`/`T2` + local-residue engine (45–75) | 27 | 4 | 0 | 31 |
| placeInfty membership, generator spans, residue-iso (76–109) | 18 | 14 | 2 | 34 |
| pole/Laurent engine + `Mp72a102T3` (110–137) | 27 | 1 | 0 | 28 |
| tail: atom, log bound, `ord`/`log` bridges (138–144) | 6 | 1 | 0 | 7 |
| **total** | **108** | **30** | **7** | **145** |

**Headline.** Two thirds of the chunk is already paid for. 108 of 145 rows are
SUBSTITUTE — 96 importable port publics plus 12 port-private copies that must be
promoted or used in-file — and only 7 rows introduce new objects. The genuinely new
mathematics of chunk 1 is small and local: the power-basis trace prelude rows 0–5
(each a 1–5 line mathlib assembly; §11.1), the two `ord` additivity leaves rows 7/23
(the `-log ∘ adicValuation` normalization; §11.2), and the ℙ¹ generator/atom vocabulary
rows 40–43 and 79–80 (§11.3). Everything else on the path is an import.

**Correction 1 — the row count is 145, and the brief's content list crosses the
boundary.** Inventory rows 0–144 are 145 declarations at pin lines 295–3387. The
brief also names `ord_ofHeightOneSpectrum_of_span`, which is **row 145** (pin 3388,
span 11) and therefore belongs to chunk 3.2c, not 3.2b. Likewise two names the brief
lists as 3.2b content sit in the *same* pin file but in later chunks:
`ord_ofHeightOneSpectrum_eq_zero_of_notMem` is row 146 (pin 3399) and
`ord_placeInfty` is row 147 (pin 3411). Do not transcribe past line 3387.

**Correction 2 — the `Defs/PlaceDictionary.lean` bridges the brief names are
out-of-set.** `inertiaDeg_eq_inertiaDeg_fiberCenter` (pin 4038),
`surjective_residueOfCenter` (pin 3951) and `neg_log_valuation_fiberCenter_eq_ord`
(pin 3829) all sit past row 144. They are verified present by probe (`C5`) and are
relevant to 3.2c–e, but they are not consumed by any row 0–144 proof, so they add no
scope to this chunk.

**Correction 3 — `ValSubringKaehlerSpanTop` and `ValSubringPolynomialFormallyUnramified`
are real substitutes, not just false positives.** The brief calls the `def … : Prop`
matches against `EisensteinWeightOne.E1Chi3IsModular` false positives (44 copies in the
advise log). That is true for row 6 `OrdDifferentialWellDefined`, which exists nowhere
in the port — but rows 39 and 100 are genuinely carried at the pin statements in
`Canonical/HasCanonicalDivisor.lean:79` and `:166` (probe `C4`), so they are
SUBSTITUTE and the advise-log match must not be banked either way without the checker.

**Correction 4 — the "three ord lemmas" in `PushPull.lean` are a larger block.** The
brief's substitutes section names three; `PushPull.lean` actually carries six public
rows (12, 13, 14, 15, 17, 18) and five private rows (16, 19, 20, 21, 22) of this
chunk's ord prelude, plus the `ramificationIndex` and `inertiaDeg` definitions used by
the port's `Place`. Import the block, not the three.

**Correction 5 — the port renamed the ℙ¹ place.** Pin `p1PlaceInfty` is the port's
`AlgebraicCurve.RationalFunctionField.placeInfty` (`Defs/RatFuncPlaces.lean`), and pin
`p1PlaceInfty_toValuationSubring` is the port's `placeInfty_toValuationSubring`. Every
`p1PlaceInfty*` row below is a name translation, not a new statement.

## 2. Trace prelude + `OrdDifferentialWellDefined` (rows 0–7)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 0 | `coeff_minpolyDiv_dim_sub_one` (295) | PROOF-INGREDIENT | `minpolyDiv_monic` (`FieldTheory/Minpoly/MinpolyDiv.lean:110`), `natDegree_minpolyDiv` (`:182`), `PowerBasis.natDegree_minpoly` (`RingTheory/PowerBasis.lean:221`) | probe A1 compiles verbatim; `pb.isIntegral_gen` supplies the `IsIntegral` |
| 1 | `traceDual_eq_one_div_of_val_eq` (302) | PROOF-INGREDIENT | **`Module.Basis.traceDual_powerBasis_eq`** (`RingTheory/Trace/Basic.lean:610`), then row 0 | probe A2; the pin's two-line `rw` + row 0 |
| 2 | `trace_pow_div_aeval_derivative_minpoly_of_lt` (308) | PROOF-INGREDIENT | `Module.Basis.trace_mul_traceDual` (`Trace/Basic.lean:571`), `PowerBasis.basis_eq_pow` (`PowerBasis.lean:64`), row 1, `if_neg` | probe A3; `if_neg` deprecated → `ite_eq_right` |
| 3 | `trace_pow_div_aeval_derivative_minpoly_self` (321) | PROOF-INGREDIENT | idem + row 1, `if_pos` | probe A4; `if_pos` deprecated → `ite_eq_left` |
| 4 | `trace_root_pow_div_derivative_of_lt` (332) | PROOF-INGREDIENT | `AdjoinRoot.powerBasis` (`RingTheory/AdjoinRoot.lean:813`), `AdjoinRoot.minpoly_powerBasis_gen_of_monic` (`:828`), `AdjoinRoot.powerBasis_dim`/`_gen`, `Module.Finite.of_basis`, row 2 | probe A5; pin's `haveI` transcribes |
| 5 | `trace_root_pow_div_derivative_self` (345) | PROOF-INGREDIENT | idem + row 3 | probe A5 |
| 6 | `OrdDifferentialWellDefined` (406) | **BESPOKE** | — | new top-level `def … : Prop` over `Place.ord` and `KaehlerDifferential.D`; the advise-log match to `EisensteinWeightOne.E1Chi3IsModular` is a false positive; absent under `FLTForHuman/` |
| 7 | `_root_.AlgebraicCurve.Place.ord_add_eq_min` (478, priv) | PROOF-INGREDIENT | `Valuation.map_add_of_distinct_val` (`RingTheory/Valuation/Basic.lean:291`), `WithZero.log_le_log`, `WithZero.log` | probe B1/B2; pin-private, keep `private` |

## 3. The `lg37_*` / `Lg37CompletionSection` block (rows 8–11)

All four are public in the port at the pin statements
(`Defs/CanonicalLocalResidueInstanceV2.lean`, namespace `ModularCurve.Lg37`); probe
`C2`.

| row | pin decl (line) | class | port name |
|---:|---|---|---|
| 8 | `lg37_completion` (551) | SUBSTITUTE | `ModularCurve.Lg37.lg37_completion` |
| 9 | `lg37_residueHat` (554) | SUBSTITUTE | `ModularCurve.Lg37.lg37_residueHat` |
| 10 | `lg37_residueHat_algebraMap` (558) | SUBSTITUTE | `ModularCurve.Lg37.lg37_residueHat_algebraMap` |
| 11 | `Lg37CompletionSection` (563) | SUBSTITUTE | `ModularCurve.Lg37.Lg37CompletionSection` |

## 4. The ord / valuation prelude (rows 12–23)

`Defs/PushPull.lean` is the home: rows 12/13/14/15/17/18 are public there, rows
16/19/20/21/22 are `private` and must be promoted (or the consumer must live in that
module). `WeilDifferential.lean` and `PlaceEvaluationAlgebra.lean` carry second copies
of rows 12/13, which is the port's own dedup debt.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 12 | `_root_.AlgebraicCurve.Place.ord_nonneg_of_mem` (624, priv) | SUBSTITUTE | `AlgebraicCurve.Place.ord_nonneg_of_mem` (`PushPull.lean:43`) | probe C1; `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`, `ord_unit_smul_zpow` |
| 13 | `_root_.AlgebraicCurve.Place.mem_of_ord_nonneg` (640, priv) | SUBSTITUTE | `AlgebraicCurve.Place.mem_of_ord_nonneg` (`PushPull.lean:60`) | probe C1 |
| 14 | `_root_.AlgebraicCurve.Place.mem_iff_ord_nonneg` (649, priv) | SUBSTITUTE | `AlgebraicCurve.Place.mem_iff_ord_nonneg` (`PushPull.lean:69`) | probe C1; pin's `⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩` is the port body |
| 15 | `exists_ord_pos` (654) | SUBSTITUTE | `AlgebraicCurve.Place.exists_ord_pos` (`PushPull.lean:74`) | probe C1 |
| 16 | `_root_.AlgebraicCurve.Place.algebraMap_ne_zero` (668, priv) | SUBSTITUTE (promote) | `AlgebraicCurve.Place.algebraMap_ne_zero` (`PushPull.lean:84`, private) | probe C1 type; pin body is `simpa` |
| 17 | `_root_.AlgebraicCurve.Place.comap_algebraMap_ne_top` (674, priv) | SUBSTITUTE | `AlgebraicCurve.Place.comap_algebraMap_ne_top` (`PushPull.lean:88`) | probe C1; `ValuationSubring.mem_comap`, `ValuationSubring.mem_top`, `IsIntegrallyClosed.isIntegral_iff`, `IsIntegral.tower_top` |
| 18 | `mem_comap_iff_ord_nonneg` (695) | SUBSTITUTE | `AlgebraicCurve.Place.mem_comap_iff_ord_nonneg` (`PushPull.lean:107`) | probe C1 |
| 19 | `isUnit_mk_comap_iff` (703) | SUBSTITUTE (promote) | `AlgebraicCurve.Place.isUnit_mk_comap_iff` (`PushPull.lean:125`, private) | probe C1; `isUnit_iff_exists_inv`, `ord_mul`, `ord_inv` |
| 20 | `_root_.AlgebraicCurve.Place.exists_ord_algebraMap_pos` (728, priv) | SUBSTITUTE (promote) | `AlgebraicCurve.Place.exists_ord_algebraMap_pos` (`PushPull.lean:150`, private) | probe C1 |
| 21 | `ramificationIndex_set_nonempty` (745, priv) | SUBSTITUTE (promote) | `AlgebraicCurve.Place.ramificationIndex_set_nonempty` (`PushPull.lean:178`, private) | probe C1; `Int.toNat_of_nonneg` |
| 22 | `isPrincipalIdealRing_comap` (750) | SUBSTITUTE (promote) | `AlgebraicCurve.Place.isPrincipalIdealRing_comap` (`PushPull.lean:255`, private) | probe C1; DVR route: `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`, `toIsPrincipalIdealRing`, `ramificationIndex_dvd_ord` |
| 23 | `_root_.AlgebraicCurve.Place.ord_add_eq_left` (829, priv) | PROOF-INGREDIENT | `Valuation.map_add_of_distinct_val`, `WithZero.exp_le_exp`, `WithZero.exp_injective`, `WithZero.exp_log` | probe B3/B4/B5; pin-private, keep `private`; no port copy exists |

## 5. The ℙ¹ place dictionary (rows 24–34)

This block re-appears from phase 3.2a: the port already discharged it in
`Defs/RatFuncPlaces.lean`, `Defs/P1Dictionary.lean` and
`PrincipalDivisors/RatFuncDegree.lean`. Rows 26 and 28 are name translations.

| row | pin decl (line) | class | port name (module) |
|---:|---|---|---|
| 24 | `ord_finitePlace_ne_zero_iff` (929) | SUBSTITUTE | `RationalFunctionField.ord_finitePlace_ne_zero_iff` (`P1Dictionary.lean`) |
| 25 | `p1PlaceInfty` (946) | SUBSTITUTE | `RationalFunctionField.placeInfty` (`RatFuncPlaces.lean`) |
| 26 | `p1PlaceInfty_toValuationSubring` (959) | SUBSTITUTE | `RationalFunctionField.placeInfty_toValuationSubring` (`RatFuncPlaces.lean`) |
| 27 | `inftyValuation_isEquiv_adicValuation` (962) | SUBSTITUTE | `RationalFunctionField.inftyValuation_isEquiv_adicValuation` (`P1Dictionary.lean`) |
| 28 | `p1PlaceInfty_ne_ofHeightOneSpectrum` (966) | SUBSTITUTE | `RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum` (`RatFuncDegree.lean:78`) |
| 29 | `eq_ofHeightOneSpectrum_or_eq_placeInfty` (979) | SUBSTITUTE | `RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty` (`RatFuncDegree.lean:61`) |
| 30 | `subsingleton_setOf_forall_ne_ofHeightOneSpectrum` (989) | SUBSTITUTE | same name (`RatFuncDegree.lean`) |
| 31 | `finite_setOf_valuation_ne_one` (1000) | SUBSTITUTE | same name (`RatFuncDegree.lean`) |
| 32 | `finite_setOf_ord_ne_zero` (1019) | SUBSTITUTE | same name (`RatFuncDegree.lean`) |
| 33 | `exists_sub_algebraMap_intDegree_neg` (1047) | SUBSTITUTE | `RationalFunctionField.exists_sub_algebraMap_intDegree_neg` (`P1Dictionary.lean`) |
| 34 | `deg_placeInfty` (1098) | SUBSTITUTE | `RationalFunctionField.deg_placeInfty` (`P1Dictionary.lean`) |

## 6. Cotangent, ℙ¹ generators and `ValSubringKaehlerSpanTop` (rows 35–44)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 35 | `exists_smul_eq_of_ne_zero` (1158) | PROOF-INGREDIENT | port `Place.differentialCoeff_ne_zero`, `Place.differentialCoeff_smul_dCoord` (`Defs/Place.lean`); `smul_smul`, `inv_mul_cancel₀` | no port copy; pin proof is 8 lines |
| 36 | `_root_.AlgebraicCurve.Place.uniformizerSubring'` (1223, priv) | SUBSTITUTE | `AlgebraicCurve.Place.uniformizerSubring'` (`Defs/CanonicalDivisor.lean:46`) | probe C6 |
| 37 | `instSMulCommClass_subring` (1227, priv) | SUBSTITUTE (promote) | `AlgebraicCurve.Place`-scope `instSMulCommClass_subring` (`Canonical/HasCanonicalDivisor.lean:64`, private scoped) | body is `IsScalarTower.to_smulCommClass` |
| 38 | `_root_.AlgebraicCurve.Place.kaehlerMap_subring_D_uniformizer` (1230, priv) | SUBSTITUTE | same name (`Canonical/HasCanonicalDivisor.lean`) | `KaehlerDifferential.map_D`, `rfl` |
| 39 | `ValSubringKaehlerSpanTop` (1245) | SUBSTITUTE | `AlgebraicCurve.ValSubringKaehlerSpanTop` (`Canonical/HasCanonicalDivisor.lean:79`) | probe C4; advise-log `E1Chi3IsModular` match is the false-positive class |
| 40 | `principalAdele` (1302) | **BESPOKE** | — | new `def` into `adeleSpace` on `diagonalHom`/`diagonal_mem_adeleSpace` (`Defs/AdelicIndex.lean`, `RiemannRoch/Assembly.lean`) |
| 41 | `P1PolynomialGenerators` (1316) | **BESPOKE** | — | new `Set (RatFunc K)` def; no mathlib counterpart |
| 42 | `P1PrincipalPartGenerators` (1318) | **BESPOKE** | — | new `Set` def over `Polynomial.degree`/`Irreducible` |
| 43 | `P1PartialFractionGenerators` (1322) | **BESPOKE** | — | new `Set` def, `41 ∪ 42` |
| 44 | `gate_algebraMap_polynomial_mem_span_P1PolynomialGenerators` (1334) | PROOF-INGREDIENT | `Polynomial.sum_C_mul_X_pow_eq`, `Submodule.sum_mem`, `Submodule.subset_span`, `RatFunc.algebraMap_X`, `RatFunc.smul_eq_C_mul` | no port copy |

## 7. `Mp72a102T1`/`T2` and the local-residue engine (rows 45–75)

Every row except 53, 71 and 73–75 is landed verbatim; `Defs/CanonicalLocalResidueInstanceV2.lean`
is the home (namespaces `Mp72a102T1`, `Mp72a102T2`, `AlgebraicCurve.Place`), with row
53 in `Genus/Index.lean`.

| row | pin decl (line) | class | port name |
|---:|---|---|---|
| 45 | `mp72a102_t1_maximalIdealHat` (1388) | SUBSTITUTE | `Mp72a102T1.mp72a102_t1_maximalIdealHat` |
| 46 | `mp72a102_t1_isScalarTower` (1393) | SUBSTITUTE | `Mp72a102T1.mp72a102_t1_isScalarTower` |
| 47 | `mp72a102_t1_isAdicComplete_maximalIdealHat` (1397) | SUBSTITUTE | `Mp72a102T1.mp72a102_t1_isAdicComplete_maximalIdealHat` |
| 48 | `mp72a102_t1_henselianRing_completion` (1405) | SUBSTITUTE | `Mp72a102T1.mp72a102_t1_henselianRing_completion` |
| 49 | `mp72a102_t1_maximalIdealHat_le_ker_residueHat` (1410) | SUBSTITUTE | `Mp72a102T1.mp72a102_t1_maximalIdealHat_le_ker_residueHat` |
| 50 | `mp72a102_t1_exists_completion_root_of_residue_root` (1416) | SUBSTITUTE | `Mp72a102T1.mp72a102_t1_exists_completion_root_of_residue_root` |
| 51 | `mp72a102_t2_residueHat_algebraMap_base` (1535) | SUBSTITUTE | `Mp72a102T2.mp72a102_t2_residueHat_algebraMap_base` |
| 52 | `mp72a102_t2_residueHatAlgHom` (1544) | SUBSTITUTE | `Mp72a102T2.mp72a102_t2_residueHatAlgHom` |
| 53 | `mk_mem_maximalIdeal_iff` (1666) | SUBSTITUTE | `AlgebraicCurve.Place.mk_mem_maximalIdeal_iff` (`Genus/Index.lean`) |
| 54 | `uniformizerSubring` (1727) | SUBSTITUTE | `AlgebraicCurve.Place.uniformizerSubring` (`CanonicalLocalResidueInstanceV2.lean:98`) |
| 55 | `coe_uniformizerSubring` (1731) | SUBSTITUTE | `AlgebraicCurve.Place.coe_uniformizerSubring` (`:102`) |
| 56 | `irreducible_uniformizerSubring` (1733) | SUBSTITUTE | `…irreducible_uniformizerSubring` (`:104`) |
| 57 | `uniformizerSubring_mem_maximalIdeal` (1736) | SUBSTITUTE | `…uniformizerSubring_mem_maximalIdeal` |
| 58 | `uniformizer_mem` (1740) | SUBSTITUTE | `…uniformizer_mem` |
| 59 | `simplePoleSubmodule` (1743) | SUBSTITUTE | `…simplePoleSubmodule` |
| 60 | `mem_simplePoleSubmodule` (1754) | SUBSTITUTE | `…mem_simplePoleSubmodule` |
| 61 | `mem_simplePoleSubmodule_of_mem` (1757) | SUBSTITUTE | `…mem_simplePoleSubmodule_of_mem` |
| 62 | `simplePoleMulUniformizer` (1761) | SUBSTITUTE | `…simplePoleMulUniformizer` |
| 63 | `simplePoleResidueAux` (1770) | SUBSTITUTE | `…simplePoleResidueAux` |
| 64 | `simplePoleResidueAux_apply` (1774) | SUBSTITUTE | `…simplePoleResidueAux_apply` (`:145`) |
| 65 | `simplePoleResidueAux_eq_zero_of_mem` (1777) | SUBSTITUTE | `…simplePoleResidueAux_eq_zero_of_mem` |
| 66 | `localResidueExtend` (1786) | SUBSTITUTE | `…localResidueExtend` |
| 67 | `localResidueExtend_apply_of_mem` (1789) | SUBSTITUTE | `…localResidueExtend_apply_of_mem` |
| 68 | `localResidueDataOfExtend` (1794) | SUBSTITUTE | `…localResidueDataOfExtend` |
| 69 | `instHasLocalResidue` (1805) | SUBSTITUTE | `AlgebraicCurve.Place.instHasLocalResidue` (`:175`) |
| 70 | `gate_uniformizer_inv_mem_simplePoleSubmodule` (1812) | SUBSTITUTE | `AlgebraicCurve.gate_uniformizer_inv_mem_simplePoleSubmodule` |
| 71 | `…ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one` (1856, priv) | PROOF-INGREDIENT | port `CanonicalLocalResidueDataK.res_of_mem`, `.res_higherPoleMonomial` (`CanonicalLocalResidueInstanceV2.lean:167/345`), `Place.mem_of_ord_nonneg`, `Place.ord_zpow`, `Place.ord_uniformizer` | no port copy |
| 72 | `finiteResidue_of_deg_pos` (1906) | SUBSTITUTE | `AlgebraicCurve.Place.finiteResidue_of_deg_pos` |
| 73 | `instFiniteResidueOfHeightOneSpectrum` (1921) | PROOF-INGREDIENT | `exists_irreducible_span`, `Place.finiteResidue_of_deg_pos`, `deg_ofHeightOneSpectrum`, `Irreducible.natDegree_pos` | instance; no port copy |
| 74 | `instFiniteResiduePlaceInfty` (1928) | PROOF-INGREDIENT | `Place.finiteResidue_of_deg_pos`, `deg_placeInfty` | instance; no port copy |
| 75 | `instFiniteResidue` (1934) | PROOF-INGREDIENT | `eq_ofHeightOneSpectrum_or_eq_placeInfty`, rows 73/74 | instance; `IsCurveOver.instFiniteResidue` is a different statement |

## 8. placeInfty membership, generator spans, residue-field iso (rows 76–109)

Rows 90–94 are the **out-of-module** leaves the brief's "resolve locally `private`"
protocol anticipates: the port carries them `private` in
`PrincipalDivisors/Transcendence.lean` and `Defs/PlacesOverDVR.lean`. Rows 95–101 are
the Kaehler/formal-unramified block of `Canonical/HasCanonicalDivisor.lean`.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 76 | `algebraMap_polynomial_mem_of_ne_placeInfty'` (1995) | SUBSTITUTE | `RationalFunctionField.algebraMap_polynomial_mem_of_ne_placeInfty` (`Genus/Stichtenoth.lean:785`) | binder-only difference (`u ≠ placeInfty`; no prime on the name) |
| 77 | `pow_X_mem_of_ne_placeInfty` (2002) | PROOF-INGREDIENT | row 76, `map_pow`, `RatFunc.algebraMap_X` | no port copy |
| 78 | `pow_X_mul_mem_of_ne_placeInfty` (2009) | PROOF-INGREDIENT | row 77 + `mul_mem` | no port copy |
| 79 | `P1DifferentialCoeffRegularFinite` (2028) | **BESPOKE** | — | new `def … : Prop` over `Place.differentialCoeff` |
| 80 | `p1PrincipalPartAtom` (2047) | **BESPOKE** | — | new `abbrev` (a division term in `RatFunc K`) |
| 81 | `finitePlace_ne_placeInfty` (2056) | PROOF-INGREDIENT | port `placeInfty_ne_ofHeightOneSpectrum` (`RatFuncDegree.lean`) | no port copy |
| 82 | `ord_algebraMap_base` (2116) | PROOF-INGREDIENT | `Place.ord_nonneg_of_mem`, `map_inv₀`, `Place.ord_inv`, `omega` | no port copy |
| 83 | `exists_ord_finitePlace_eq_nsmul` (2135) | PROOF-INGREDIENT | `WfDvdMonoid.max_power_factor` (`RingTheory/UniqueFactorizationDomain/Multiplicity.lean:40`), `ord_mul`, `ord_zpow`, `zpow_natCast` | no port copy |
| 84 | `ord_finitePlace_dvd` (2154) | PROOF-INGREDIENT | row 83, `RatFunc.num_div_denom`, `Place.ord_inv`, `IsFractionRing.injective` | no port copy |
| 85 | `ord_finitePlace_self` (2168) | PROOF-INGREDIENT | `IsDiscreteValuationRing.exists_irreducible`, `Place.ord_coe_irreducible`, row 84, `Int.isUnit_iff`, `isUnit_of_dvd_one` | no port copy |
| 86 | `ord_placeInfty_eq_zero_of_intDegree_eq_zero` (2188) | PROOF-INGREDIENT | port `ord_placeInfty` (`P1Dictionary.lean`), `Place.ord_eq_zero_iff_adicValuation_eq_one`, `RatFunc.inftyValuation_of_nonzero` | no port copy |
| 87 | `ord_placeInfty_eq_intDegree_mul` (2195) | PROOF-INGREDIENT | port `ord_placeInfty`, `ord_mul`/`ord_zpow`, `RatFunc.intDegree_polynomial`, `RatFunc.intDegree_div` | no port copy |
| 88 | `ord_placeInfty_X` (2234) | SUBSTITUTE | `RationalFunctionField.ord_placeInfty_X` (`Genus/Stichtenoth.lean:780`) | probe C7 |
| 89 | `ord_placeInfty_algebraMap'` (2255) | SUBSTITUTE | `RationalFunctionField.ord_placeInfty_algebraMap` (`P1Dictionary.lean`) | probe C7; binder-only rename (`'` dropped) |
| 90 | `_root_.AlgebraicCurve.Place.aeval_mem` (2353, priv) | SUBSTITUTE (promote) | `AlgebraicCurve.aeval_mem` (`PrincipalDivisors/Transcendence.lean`, private) | probe C8 class |
| 91 | `_root_.AlgebraicCurve.Place.exists_coeff_ord_ne_zero` (2361, priv) | SUBSTITUTE (promote) | `AlgebraicCurve.exists_coeff_ord_ne_zero` (`Transcendence.lean`, private) | pin body: `minpoly.coeff_zero_ne_zero`, `Place.mem_of_eval_monic_eq_zero`, `P.X_mul_divX_add` |
| 92 | `chartHom` (2418, priv) | SUBSTITUTE (promote) | `AlgebraicCurve.Place.chartHom` (`Defs/PlacesOverDVR.lean`, private) | `RingHom.codRestrict` |
| 93 | `inv_algebraMap_mem` (2424, priv) | SUBSTITUTE (promote) | `AlgebraicCurve.Place.inv_algebraMap_mem` (`PlacesOverDVR.lean`, private) | `IsUnit` inversion |
| 94 | `finite_setOf_ord_ne_zero_of_finiteDimensional` (2457) | SUBSTITUTE (promote) | `AlgebraicCurve.finite_setOf_ord_ne_zero_of_finiteDimensional` (`Transcendence.lean`, private) | pin body: `Set.finite_Iio`, `Set.Finite.biUnion`, `Place.finite_setOf_restrict_eq` |
| 95 | `_root_.AlgebraicCurve.Place.uniformizerSubring''` (2509, priv) | SUBSTITUTE | `AlgebraicCurve.Place.uniformizerSubring''` (`Canonical/HasCanonicalDivisor.lean:96`) | probe C6 |
| 96 | `_root_.AlgebraicCurve.Place.polynomialAlgebra_algebraMap_X` (2517, priv) | SUBSTITUTE | same name (`HasCanonicalDivisor.lean:102`) | `aeval_X` |
| 97 | `_root_.AlgebraicCurve.Place.range_mapBaseChange_le_span_D_uniformizer` (2532, priv) | SUBSTITUTE | same name (`HasCanonicalDivisor.lean:115`) | probe C4 |
| 98 | `_root_.AlgebraicCurve.Place.range_mapBaseChange_eq_top_of_subsingleton` (2556, priv) | SUBSTITUTE | same name (`HasCanonicalDivisor.lean:138`) | `KaehlerDifferential.range_mapBaseChange` |
| 99 | `_root_.AlgebraicCurve.Place.span_D_uniformizer_eq_top_of_subsingleton` (2569, priv) | SUBSTITUTE | same name (`HasCanonicalDivisor.lean:150`) | `top_le_iff` |
| 100 | `ValSubringPolynomialFormallyUnramified` (2588) | SUBSTITUTE | `AlgebraicCurve.ValSubringPolynomialFormallyUnramified` (`HasCanonicalDivisor.lean:166`) | probe C4 |
| 101 | `valSubringKaehlerSpanTop_of_polynomialFormallyUnramified` (2595) | SUBSTITUTE | same name (`HasCanonicalDivisor.lean:173`) | probe C4 |
| 102 | `exists_monic_irreducible_factorization` (2647) | PROOF-INGREDIENT | `normalizedFactors`, `Polynomial.mem_normalizedFactors_iff` (`UniqueFactorizationDomain/NormalizedFactors.lean:230`), `irreducible_of_normalized_factor`, `prod_normalizedFactors_eq` (`:57`), `Finset.prod_multiset_count` | no port copy; pin's 29-line Finset assembly |
| 103 | `algebraMap_mem_span_P1PartialFractionGenerators` (2676) | PROOF-INGREDIENT | row 44, `Submodule.span_mono`, `Set.subset_union_left` | |
| 104 | `div_pow_mem_span_P1PartialFractionGenerators` (2681) | PROOF-INGREDIENT | `Submodule.subset_span` | |
| 105 | `ratFunc_mem_span_P1PartialFractionGenerators` (2688) | PROOF-INGREDIENT | `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` (`Algebra/Polynomial/PartialFractions.lean`), `RatFunc.monic_denom`, `Finset.prod_inv_distrib`, `RatFunc.num_div_denom`, `Submodule.sum_mem` | |
| 106 | `p1PartialFractionSpan_eq_top` (2723) | PROOF-INGREDIENT | `Submodule.eq_top_iff'` | |
| 107 | `residueFieldAdjoinRootEquiv` (2758) | SUBSTITUTE | `ModularCurve.KwNo6Section.residueFieldAdjoinRootEquiv` (`CanonicalLocalResidueInstanceV2.lean:913`) | probe C9; binder-only |
| 108 | `residueFieldAdjoinRootEquiv_root` (2764) | SUBSTITUTE | `ModularCurve.KwNo6Section.residueFieldAdjoinRootEquiv_root` (`:919`) | probe C9 |
| 109 | `sectionOfPrimitiveRoot` (2780) | SUBSTITUTE | `ModularCurve.KwNo6Section.sectionOfPrimitiveRoot` (`:933`) | probe C9 |

## 9. Pole/Laurent engine and `Mp72a102T3` (rows 110–137)

All 28 rows are landed verbatim in `Defs/CanonicalLocalResidueInstanceV2.lean`
(namespaces `AlgebraicCurve.Place`, `ModularCurve.Mp72a102T3`).

| row | pin decl (line) | class | port name |
|---:|---|---|---|
| 110 | `poleSubmodule` (2845) | SUBSTITUTE | `AlgebraicCurve.Place.poleSubmodule` |
| 111 | `mem_poleSubmodule` (2856) | SUBSTITUTE | `…mem_poleSubmodule` |
| 112 | `uniformizer_pow_ne_zero` (2859) | SUBSTITUTE | `…uniformizer_pow_ne_zero` |
| 113 | `ord_uniformizer_pow` (2862) | SUBSTITUTE | `…ord_uniformizer_pow` |
| 114 | `coe_poleSubmodule_zero` (2866) | SUBSTITUTE | `…coe_poleSubmodule_zero` |
| 115 | `poleSubmodule_one` (2871) | SUBSTITUTE | `…poleSubmodule_one` |
| 116 | `mem_poleSubmodule_iff_ord` (2874) | SUBSTITUTE | `…mem_poleSubmodule_iff_ord` |
| 117 | `poleSubmodule_mono` (2880) | SUBSTITUTE | `…poleSubmodule_mono` |
| 118 | `poleMulUniformizerPow` (2888) | SUBSTITUTE | `…poleMulUniformizerPow` |
| 119 | `laurentTailCoeff` (2897) | SUBSTITUTE | `…laurentTailCoeff` |
| 120 | `laurentTailCoeff_apply` (2901) | SUBSTITUTE | `…laurentTailCoeff_apply` (`:258`) |
| 121 | `laurentTail_remainder_mem_poleSubmodule` (2904) | SUBSTITUTE | `…laurentTail_remainder_mem_poleSubmodule` |
| 122 | `localResidueData_res_eq_simplePoleResidueAux` (2931) | SUBSTITUTE | `…localResidueData_res_eq_simplePoleResidueAux` |
| 123 | `gate_poleSubmodule_strictMono` (2938) | SUBSTITUTE | `AlgebraicCurve.gate_poleSubmodule_strictMono` |
| 124 | `gate_localResidueData_uniformizer_inv` (2948) | PROOF-INGREDIENT | port `Place.localResidueData_res_eq_simplePoleResidueAux`, `gate_uniformizer_inv_mem_simplePoleSubmodule`, `simplePoleResidueAux_apply`, `map_one` | no port copy |
| 125 | `mp72a102_t3_evalₐ_zero_depth` (2998) | SUBSTITUTE | `ModularCurve.Mp72a102T3.mp72a102_t3_evalₐ_zero_depth` |
| 126 | `mp72a102_t3_evalₐ_algebraMap` (3004) | SUBSTITUTE | `…evalₐ_algebraMap` |
| 127 | `mp72a102_t3_evalₐ_factor` (3010) | SUBSTITUTE | `…evalₐ_factor` |
| 128 | `mp72a102_t3_exists_rep_of_evalₐ_eq_zero` (3017) | SUBSTITUTE | `…exists_rep_of_evalₐ_eq_zero` |
| 129 | `mp72a102_t3_evalₐ_succ_mul_eq_zero` (3026) | SUBSTITUTE | `…evalₐ_succ_mul_eq_zero` |
| 130 | `mp72a102_t3_evalₐ_one_eq_zero_of_evalOneₐ` (3034) | SUBSTITUTE | `…evalₐ_one_eq_zero_of_evalOneₐ` |
| 131 | `mp72a102_t3_evalDepth_add` (3049) | SUBSTITUTE | `…evalDepth_add` |
| 132 | `mp72a102_t3_evalDepth_mul` (3056) | SUBSTITUTE | `…evalDepth_mul` |
| 133 | `mp72a102_t3_residueHat_congr_of_depth_one` (3063) | SUBSTITUTE | `…residueHat_congr_of_depth_one` |
| 134 | `mp72a102_t3_evalDepth_one_eq_zero_of_residueHat` (3072) | SUBSTITUTE | `…evalDepth_one_eq_zero_of_residueHat` |
| 135 | `mp72a102_t3_eq_uniformizer_mul_of_mem_maximalIdeal` (3077) | SUBSTITUTE | `…eq_uniformizer_mul_of_mem_maximalIdeal` |
| 136 | `mp72a102_t3_exists_uniformizer_factor` (3083) | SUBSTITUTE | `…exists_uniformizer_factor` |
| 137 | `mp72a102_t3_sigma_taylor_expansion` (3106) | SUBSTITUTE | `…sigma_taylor_expansion` |

## 10. Tail: atom, log bound, `ord`/`log` bridges (rows 138–144)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 138 | `p1PrincipalPartAtom_ne_zero` (3217) | PROOF-INGREDIENT | `map_ne_zero_iff`, `IsFractionRing.injective`, `pow_ne_zero`, `div_eq_zero_iff` | no port copy |
| 139 | `le_exp_neg_one_of_lt_one` (3306) | SUBSTITUTE | `AlgebraicCurve.le_exp_neg_one_of_lt_one` (`P1Dictionary.lean`) | `WithZero.exp_log`, `exp_lt_exp`, `exp_le_exp`, `omega` |
| 140 | `_root_.AlgebraicCurve.Place.isUnit_algebraMap` (3320, priv) | SUBSTITUTE (promote) | `AlgebraicCurve.Place.isUnit_algebraMap` (`P1Dictionary.lean`, private) | `isUnit_iff_ne_zero`, `IsUnit.map` |
| 141 | `_root_.AlgebraicCurve.Place.adicValuation_algebraMap` (3325, priv) | SUBSTITUTE | `AlgebraicCurve.Place.adicValuation_algebraMap` (`P1Dictionary.lean`) | probe C10 |
| 142 | `_root_.AlgebraicCurve.Place.ord_algebraMap` (3331, priv) | SUBSTITUTE | `AlgebraicCurve.Place.ord_algebraMap` (`Defs/Place.lean`) | probe C10; binder-only (port takes `v` explicitly) |
| 143 | `_root_.AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq` (3337, priv) | SUBSTITUTE | `AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq` (`Defs/Place.lean:302`) | probe C10; same statement, port public |
| 144 | `ord_ofHeightOneSpectrum_eq_neg_log` (3377) | SUBSTITUTE | `RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log` (`PrincipalDivisors/RatFuncDegree.lean:164`) | probe C10; bridge through `HeightOneSpectrum.intValuation_singleton` |

## 11. Reuse wins, with probe evidence

### 11.1 The trace prelude is `traceDual_powerBasis_eq` plus arithmetic

The whole power-basis prelude is one mathlib lemma and its specialisations. Probe A
compiles rows 0–5 verbatim against narrow imports:

```lean
theorem proto_traceDual_eq_one_div_of_val_eq (pb : PowerBasis K L) {j : Fin pb.dim}
    (hj : (j : ℕ) = pb.dim - 1) :
    pb.basis.traceDual j = 1 / aeval pb.gen (derivative (minpoly K pb.gen)) := by
  rw [Module.Basis.traceDual_powerBasis_eq]
  rw [hj, proto_coeff_minpolyDiv_dim_sub_one]
```

There is **no** single mathlib constant for row 0: `coeff_minpolyDiv_dim_sub_one` is
the three-step `natDegree_minpolyDiv` → `PowerBasis.natDegree_minpoly` →
`Monic.coeff_natDegree` argument, and it is worth landing as a helper because rows 1–3
consume it. Rows 4–5 are the `AdjoinRoot` specialisation and need the pin's
`haveI : FiniteDimensional F (AdjoinRoot g) := Module.Finite.of_basis …` (the
separable instance follows from `Fact (Irreducible g)` in `CharZero F`), which probe A5
confirms transcribes unchanged.

### 11.2 The two `ord` additivity leaves are `Valuation.map_add_of_distinct_val` plus `WithZero`

`Place.ord` is the port's `-log ∘ adicValuation` normalization
(`Defs/Place.lean:137`). Both rows 7 and 23 are the same three-step proof: translate
`ord` inequalities to `WithZero` inequalities with `log_le_log`/`exp_le_exp`, apply
`Valuation.map_add_of_distinct_val`, then `omega`. Probe B compiles the pieces:

```lean
example {f g : F'} (hf : f ≠ 0) (hg : g ≠ 0) (h : v f ≠ v g) :
    v (f + g) = max (v f) (v g) :=
  Valuation.map_add_of_distinct_val v h

example {a b : ℤᵐ⁰} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ≤ b) :
    WithZero.log a ≤ WithZero.log b :=
  (WithZero.log_le_log ha hb).mpr h
```

No port copy exists, so these are the chunk's first proof work; they are pin-`private`
and stay `private`.

### 11.3 The ℙ¹ generator/atom vocabulary is the only new-object block

Rows 40–43 (`principalAdele`, `P1PolynomialGenerators`,
`P1PrincipalPartGenerators`, `P1PartialFractionGenerators`), 79
(`P1DifferentialCoeffRegularFinite`), 80 (`p1PrincipalPartAtom`) and 6
(`OrdDifferentialWellDefined`) are the seven BESPOKE rows. Six are `def`/`abbrev`
shells over already-ported vocabulary (`adeleSpace`/`diagonalHom`,
`Place.differentialCoeff`, `Place.ord`, `KaehlerDifferential.D`); the only real proof
content around them is the partial-fraction span theorem chain rows 102–106, whose one
non-elementary input is mathlib's
`Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`
(`Mathlib/Algebra/Polynomial/PartialFractions.lean`).

### 11.4 The engine (rows 45–137) is mostly import-only

Rows 45–137 hold 72 SUBSTITUTE, 19 PROOF-INGREDIENT and 2 BESPOKE. The engine core
45–75 and 110–137 is import-only except rows 71, 73–75 and 124 (a private
`res_uniformizer_zpow` lemma, three `FiniteResidue` instances, and the
`gate_localResidueData_uniformizer_inv` law, all assembled from the port's own
`CanonicalLocalResidueDataK` API). Row 53 comes
from `Genus/Index.lean`; the local-residue and pole/Laurent blocks and the
`Mp72a102T1`/`T2`/`T3` calculus come from `Defs/CanonicalLocalResidueInstanceV2.lean`;
the Kaehler block rows 95–101 from `Canonical/HasCanonicalDivisor.lean`. The only
substantial new work inside 76–109 is the generator/atom leaf block 77–87 and the
partial-fraction span chain 102–106.

### 11.5 The brief's `PlaceDictionary` bridges are out-of-set

Probe C5 confirms `inertiaDeg_eq_inertiaDeg_fiberCenter`,
`surjective_residueOfCenter`, `neg_log_valuation_fiberCenter_eq_ord` and
`Place.ramificationIndex_eq_ramificationIdx_fiberCenter` exist in
`Defs/PlaceDictionary.lean`, but their pin lines (4038, 3951, 3829) are past row 144.
They are 3.2c–e material.

## 12. Route options

- **R1 — import `PushPull`, do not re-privatize the ord block.** Eleven of rows 12–22
  are already proved in `Defs/PushPull.lean`; five are `private` there. Promoting those
  five (or landing `P1ResidueCore` inside their reach) is one edit; a second
  transcription is ≈130 pin lines in this file alone for nothing.
- **R2 — treat `CanonicalLocalResidueInstanceV2` as the engine's public API.** Rows
  8–11, 45–70, 107–123 and 125–137 are 76 declarations landed by phase 3.1b-ii. The
  worker's module should import it and add only rows 71, 73–75, 124.
- **R3 — the `Mp72a102T3` block is already public at the pin names.** Rows 125–137 are
  an `AdicCompletion.evalₐ` calculus; do not re-derive it from
  `Mathlib.RingTheory.AdicCompletion.*` (the mathlib names exist — probe `F` — but the
  assembly is the port's).
- **R4 — the ℙ¹ dictionary rows 24–34 are not 3.2b work.** They are 3.2a's output; import
  `P1Dictionary`/`RatFuncDegree`/`RatFuncPlaces` and keep the pin statement names.
- **R5 — `ValSubringKaehlerSpanTop`/`ValSubringPolynomialFormallyUnramified` are
  substitutes.** Import them from `Canonical/HasCanonicalDivisor.lean`; do not re-add
  them because the advise log mis-matched them to `E1Chi3IsModular`.
- **R6 — the partial-fraction span chain is the one budget item.** Rows 102–106 are new
  and are the only place where the chunk needs a multi-step assembly
  (`normalizedFactors` + `PartialFractions`); everything around them is imports.
- **R7 — land the seven BESPOKE objects at the pin statements, no API around them.**
  Chunk 3.2c–e append to the same module; keep `OrdDifferentialWellDefined`,
  `P1DifferentialCoeffRegularFinite` and the generator sets exactly as the pin spells
  them so the later chunks can consume them.

## 13. API drift (v4.34.0) — what the worker must change

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `if_neg h` (row 2, pin 317) | deprecated → `ite_eq_right h` | rename; probe A3 compiles with the warning |
| `if_pos rfl` (row 3, pin 328) | deprecated → `ite_eq_left rfl` | rename; probe A4 |
| `Ideal.inertiaDeg'` (3.2c–e bridges, not rows 0–144) | deprecated → `Ideal.inertiaDeg` (`RingTheory/RamificationInertia/Inertia.lean`); warning on `#check` | prefer `Ideal.inertiaDeg`; the legacy def lives in `Mathlib/NumberTheory/RamificationInertia/Inertia.lean` |
| `Ideal.ramificationIdx'` | legacy def in `Mathlib/NumberTheory/RamificationInertia/Ramification.lean:71`; the new `Ideal.ramificationIdx` is `RingTheory/RamificationInertia/Ramification.lean:52` | unprimed names for new bridges; `Ideal.ramificationIdx'_*` lemma aliases are deprecated |
| `Polynomial.degree_sub_lt hdegeq hnum0 hlc` (row 33, pin 1094) | deprecated → `Polynomial.degree_sub_lt_left` (same signature) | rename if transcribed; the port already has row 33, so normally no edit |
| `dif_pos hf` | deprecated → `dite_eq_left hf` | global rename (3.2a already needed it) |
| `Set.mem_setOf_eq` (rows 31/32 pin proofs) | deprecated → `Set.mem_ofPred_eq` | rename if transcribed; port already has rows 31/32 |
| `Polynomial.multiplicity` / `Polynomial.emultiplicity` | **do not exist**; only root `multiplicity`/`emultiplicity` | no change: rows use `WfDvdMonoid.max_power_factor`, not `multiplicity` |

No other drift was found on rows 0–144. In particular
`Valuation.map_add_of_distinct_val`, `WithZero.{log_le_log, exp_log, exp_le_exp,
exp_injective, log_zpow}`, `IsDiscreteValuationRing.{exists_irreducible,
ofHasUnitMulPowIrreducibleFactorization, toIsPrincipalIdealRing}`,
`AdicCompletion.{evalₐ, evalOneₐ, evalₐ_of, evalₐ_mk, factorₐ_evalₐ_one, mk_surjective,
isAdicComplete}`, `AdicCompletion.Ideal.mk_eq_mk`,
`IsIntegrallyClosed.isIntegral_iff`, `ValuationSubring.{mem_comap, mem_top}`,
`IsFractionRing.injective`, `IsLocalRing.{residue_surjective, residue_eq_zero_iff,
residue_ne_zero_iff_isUnit, ResidueField.algebraMap_eq}`,
`Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`,
`RatFunc.monic_denom`, `IntermediateField.{adjoinRootEquivAdjoin, equivOfEq, topEquiv}`,
`AdjoinRoot.liftAlgHom` and the `IsDedekindDomain.HeightOneSpectrum.*` valuation API all
keep the pin's shapes (probe C/F/G).

## 14. Recorded negatives

Confirmed against mathlib `v4.34.0` and the port; phrased so the search is not repeated.

1. **No mathlib `Place.ord` and no `-log ∘ valuation` API.** The whole ord prelude is
   the port's `Place` vocabulary (`Defs/Place.lean:137`); mathlib supplies only
   `Valuation.map_add_of_distinct_val` and the `WithZero` log/exp lemmas. Do not look
   for an `ord_add_eq_min`/`ord_add_eq_left` in `Mathlib.RingTheory.Valuation.*`.
2. **No mathlib `IsPrincipalIdealRing`-of-comap and no ramification-index comap result.**
   Row 22 is bespoke: a DVR is *constructed* on the comap via
   `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization` and fed to
   `toIsPrincipalIdealRing`, using the port's `ramificationIndex_dvd_ord`.
3. **No single mathlib constant for `coeff_minpolyDiv_dim_sub_one`.** The ingredients
   are `minpolyDiv_monic`, `natDegree_minpolyDiv`, `PowerBasis.natDegree_minpoly`; the
   combination is the row.
4. **No mathlib declaration for `exists_monic_irreducible_factorization`.** Mathlib has
   `normalizedFactors`, `Polynomial.mem_normalizedFactors_iff`,
   `UniqueFactorizationMonoid.prod_normalizedFactors_eq` and
   `Finset.prod_multiset_count`; the Finset assembly is the row.
5. **No `Polynomial.multiplicity`/`Polynomial.emultiplicity`.** The root API is
   `Polynomial.rootMultiplicity` with `pow_rootMultiplicity_dvd`,
   `le_rootMultiplicity_iff`, `rootMultiplicity_pos`; root multiplicity is not on this
   chunk's path at all.
6. **No mathlib `OrdDifferentialWellDefined`, `P1DifferentialCoeffRegularFinite`,
   `P1PolynomialGenerators`, `P1PrincipalPartGenerators`,
   `P1PartialFractionGenerators`, `principalAdele` or `p1PrincipalPartAtom`.** These are
   the chunk's new vocabulary.
7. **No mathlib `ord_ofHeightOneSpectrum_eq_neg_log`.** The route is the port's
   `Place.ord_eq_neg_log_of_valuationSubring_eq` plus
   `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton` and
   `…valuation_of_algebraMap`.
8. **The advise-log trivial-`Prop` matches are not all false positives.** Row 6 is one,
   but rows 39/100 are real port declarations in `Canonical/HasCanonicalDivisor.lean`;
   check the port, not the log.
9. **`IsDiscreteValuationRing.{irreducible_iff_uniformizer, maximalIdeal_eq}` are
   needed, `addVal` is not.** Rows 83–85/124 use `exists_irreducible`,
   `ord_coe_irreducible` and `irreducible_uniformizerSubring.maximalIdeal_eq`;
   `IsDiscreteValuationRing.addVal` is off-path.
10. **`Valuation.valuationSubring_isDiscreteValuationRing` exists but is 3.2a's route**
    (the `placeInfty` construction), not a rows-0–144 dependency.

## 15. What this changes for `WORKORDER-P3-2b-p1core-1.md`

**Scope / measurement.**

- The chunk is **145 rows**, 108 SUBSTITUTE / 30 PROOF-INGREDIENT / 7 BESPOKE.
- `ord_ofHeightOneSpectrum_of_span` is **out of scope** (row 145, pin 3388); so are
  `ord_ofHeightOneSpectrum_eq_zero_of_notMem` (146) and `ord_placeInfty` (147).
- The `PlaceDictionary` bridges named in the order are 3.2c–e material (rows >144).

**Discharged proofs (mark import-discharged; the statements still land).**

- rows 8–11, 45–70, 107–123, 125–137 — import `Defs/CanonicalLocalResidueInstanceV2`;
- rows 12–22 — import `Defs/PushPull` (promote the five private names);
- rows 24–34, 88–89, 139–142, 144 — import `Defs/{P1Dictionary,RatFuncPlaces}` and
  `PrincipalDivisors/RatFuncDegree` / `Genus/Stichtenoth`;
- rows 36–39, 95–101 — import `Defs/CanonicalDivisor` + `Canonical/HasCanonicalDivisor`;
- rows 90–94 — promote `PrincipalDivisors/Transcendence` and `Defs/PlacesOverDVR`
  private copies (the order's "resolve locally `private`" protocol, here on the port's
  side);
- row 53 — import `Genus/Index`.

**New work, budgeted.**

- rows 0–5: six short mathlib assemblies (probe A).
- rows 7, 23: the two `ord` additivity leaves (probe B), pin-private.
- rows 40–43, 79–80: the new ℙ¹ vocabulary.
- rows 71, 73–75, 124: three instances and the `Gate` law from the port's
  `CanonicalLocalResidueDataK`.
- rows 76–78, 81–87, 102–106, 138: the membership/generator/atom leaf proofs.

**Imports the worker may use.** The port modules listed above plus, on the mathlib side,
`Mathlib.RingTheory.Trace.Basic`, `Mathlib.RingTheory.PowerBasis`,
`Mathlib.FieldTheory.Minpoly.MinpolyDiv`, `Mathlib.RingTheory.AdjoinRoot`,
`Mathlib.RingTheory.Valuation.Basic`, `Mathlib.RingTheory.Valuation.ValuationSubring`,
`Mathlib.RingTheory.Valuation.Discrete.Basic`,
`Mathlib.RingTheory.DiscreteValuationRing.Basic`,
`Mathlib.RingTheory.UniqueFactorizationDomain.{Multiplicity,NormalizedFactors}`,
`Mathlib.Algebra.Polynomial.PartialFractions`,
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`,
`Mathlib.NumberTheory.RamificationInertia.Valuation`,
`Mathlib.RingTheory.AdicCompletion.{Algebra,Completeness}`. Do **not** import
`Mathlib.RingTheory.RamificationInertia.*` for this chunk — the new
`Ideal.ramificationIdx`/`inertiaDeg` are 3.2c–e bridges.

**Checker wiring.** Append `P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`
(and its `Theorems/Thm_*` wrapper) to `SOURCES` **last**, and
`FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean` to `PORT_FILES`, per the order §5.

## 16. Appendix — module map for the named constants

| name | module |
|---|---|
| `Module.Basis.{traceDual, traceDual_powerBasis_eq, trace_mul_traceDual, trace_traceDual_mul}` | `Mathlib/RingTheory/Trace/Basic.lean` |
| `minpolyDiv`, `minpolyDiv_monic`, `natDegree_minpolyDiv`, `coeff_minpolyDiv`, `eval_minpolyDiv_self` | `Mathlib/FieldTheory/Minpoly/MinpolyDiv.lean` |
| `PowerBasis`, `PowerBasis.{basis, basis_eq_pow, dim, gen, natDegree_minpoly, isIntegral_gen}` | `Mathlib/RingTheory/PowerBasis.lean` |
| `AdjoinRoot.{powerBasis, powerBasis_gen, powerBasis_dim, minpoly_powerBasis_gen, minpoly_powerBasis_gen_of_monic, liftAlgHom, root}` | `Mathlib/RingTheory/AdjoinRoot.lean` |
| `Valuation.map_add_of_distinct_val` | `Mathlib/RingTheory/Valuation/Basic.lean` |
| `WithZero.{log, exp, log_le_log, exp_log, exp_le_exp, exp_lt_exp, exp_injective, log_zpow}` | `Mathlib/Algebra/GroupWithZero/WithZero.lean` |
| `ValuationSubring.{mem_comap, mem_top, comap}`, `Valuation.valuationSubring_isDiscreteValuationRing` | `Mathlib/RingTheory/Valuation/{ValuationSubring,Discrete/Basic}.lean` |
| `IsDiscreteValuationRing.{exists_irreducible, ofHasUnitMulPowIrreducibleFactorization, HasUnitMulPowIrreducibleFactorization, toIsPrincipalIdealRing, eq_unit_mul_pow_irreducible, irreducible_iff_uniformizer, maximalIdeal_eq}` | `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` |
| `IsIntegrallyClosed.isIntegral_iff` | `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean` |
| `IsFractionRing.injective` | `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure` / `Mathlib/RingTheory/Localization/*` (re-exported by `FieldTheory/RatFunc/*`) |
| `Ideal.ramificationIdx`, `Ideal.inertiaDeg`, `Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`, `Ideal.ramificationIdx_pos` | `Mathlib/RingTheory/RamificationInertia/{Ramification,Inertia}.lean` |
| `Ideal.ramificationIdx'`, `Ideal.inertiaDeg'` (legacy) | `Mathlib/NumberTheory/RamificationInertia/{Ramification,Inertia}.lean` |
| `AdicCompletion.{evalₐ, evalOneₐ, evalₐ_of, evalₐ_mk, factorₐ_evalₐ_one, mk_surjective, isAdicComplete}`, `AdicCompletion.Ideal.mk_eq_mk` | `Mathlib/RingTheory/AdicCompletion/{Algebra,Completeness,Basic}.lean` |
| `WfDvdMonoid.max_power_factor`, `multiplicity`, `multiplicity_eq_count_normalizedFactors` | `Mathlib/RingTheory/UniqueFactorizationDomain/Multiplicity.lean` |
| `normalizedFactors`, `prod_normalizedFactors_eq`, `mem_normalizedFactors_iff`, `Finset.prod_multiset_count` | `Mathlib/RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean` |
| `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` | `Mathlib/Algebra/Polynomial/PartialFractions.lean` |
| `Polynomial.{rootMultiplicity, pow_rootMultiplicity_dvd, le_rootMultiplicity_iff, rootMultiplicity_pos, degree_sub_lt_left}`, `Polynomial.{sum_C_mul_X_pow_eq, degree_mul, leadingCoeff_mul, degree_C, natDegree_lt_natDegree}` | `Mathlib/Algebra/Polynomial/*` |
| `RatFunc.{monic_denom, num_div_denom, num_ne_zero, denom_ne_zero, algebraMap_ne_zero, algebraMap_X, X_ne_zero, intDegree, intDegree_polynomial, intDegree_div, infinityValuation*}` | `Mathlib/FieldTheory/RatFunc/{Basic,AsPolynomial,Degree,Valuation}.lean` |
| `IsDedekindDomain.HeightOneSpectrum.{intValuation_singleton, valuation_of_algebraMap, valuation_eq_one_iff_notMem}` | `Mathlib/NumberTheory/RamificationInertia/Valuation.lean` |
| `IntermediateField.{adjoinRootEquivAdjoin, equivOfEq, topEquiv}`, `AdjoinSimple.coe_gen` | `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean` |
| `IsLocalRing.{residue, residue_surjective, residue_eq_zero_iff, residue_ne_zero_iff_isUnit, ResidueField.algebraMap_eq}` | `Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean` |
| `dite_eq_left`, `ite_eq_left`, `ite_eq_right` | core/`Init` (the v4.34 replacements of `dif_pos`, `if_pos`, `if_neg`) |
| `Set.mem_ofPred_eq` | core/`Init` (the v4.34 replacement of `Set.mem_setOf_eq`) |

Port declarations referred to above: `FLTForHuman/AlgebraicCurve/Defs/Place.lean`
(`ord`, `adicValuation`, `differentialCoeff*`, `ord_eq_neg_log_of_valuationSubring_eq`,
`ord_algebraMap`, `exists_unit_mul_zpow`, `ord_coe_irreducible`),
`…/Defs/PushPull.lean` (`ord_nonneg_of_mem`, `mem_of_ord_nonneg`, `mem_iff_ord_nonneg`,
`exists_ord_pos`, `algebraMap_ne_zero`, `comap_algebraMap_ne_top`,
`mem_comap_iff_ord_nonneg`, `isUnit_mk_comap_iff`, `exists_ord_algebraMap_pos`,
`ramificationIndex_set_nonempty`, `isPrincipalIdealRing_comap`, `ramificationIndex`,
`inertiaDeg`), `…/Defs/CanonicalLocalResidueInstanceV2.lean` (`ModularCurve.Lg37.*`,
`Mp72a102T1.*`, `Mp72a102T2.*`, `ModularCurve.Mp72a102T3.*`,
`ModularCurve.KwNo6Section.*`, `AlgebraicCurve.Place.{uniformizerSubring,
simplePoleSubmodule*, localResidue*, poleSubmodule*, laurentTail*,
localResidueData_res_eq_simplePoleResidueAux}`,
`AlgebraicCurve.gate_{uniformizer_inv_mem_simplePoleSubmodule,poleSubmodule_strictMono}`,
`AlgebraicCurve.Place.finiteResidue_of_deg_pos`),
`…/Canonical/HasCanonicalDivisor.lean` (`ValSubringKaehlerSpanTop`,
`ValSubringPolynomialFormallyUnramified`, `uniformizerSubring''`,
`polynomialAlgebra_algebraMap_X`, `range_mapBaseChange_*`, `span_D_uniformizer_*`,
`instSMulCommClass_subring`, `valSubringKaehlerSpanTop_of_polynomialFormallyUnramified`),
`…/Defs/CanonicalDivisor.lean` (`uniformizerSubring'`),
`…/Defs/P1Dictionary.lean` (`ord_finitePlace_ne_zero_iff`,
`inftyValuation_isEquiv_adicValuation`, `exists_sub_algebraMap_intDegree_neg`,
`deg_placeInfty`, `ord_placeInfty`, `ord_placeInfty_algebraMap`,
`isUnit_algebraMap`, `adicValuation_algebraMap`, `le_exp_neg_one_of_lt_one`),
`…/Defs/RatFuncPlaces.lean` (`placeInfty`, `placeInfty_toValuationSubring`),
`…/PrincipalDivisors/RatFuncDegree.lean` (`placeInfty_ne_ofHeightOneSpectrum`,
`eq_ofHeightOneSpectrum_or_eq_placeInfty`,
`subsingleton_setOf_forall_ne_ofHeightOneSpectrum`, `finite_setOf_valuation_ne_one`,
`finite_setOf_ord_ne_zero`, `ord_ofHeightOneSpectrum_eq_neg_log`),
`…/PrincipalDivisors/Transcendence.lean` (`aeval_mem`, `exists_coeff_ord_ne_zero`,
`finite_setOf_ord_ne_zero_of_finiteDimensional`),
`…/Defs/PlacesOverDVR.lean` (`chartHom`, `inv_algebraMap_mem`),
`…/Genus/Index.lean` (`mk_mem_maximalIdeal_iff`),
`…/Genus/Stichtenoth.lean` (`ord_placeInfty_X`,
`algebraMap_polynomial_mem_of_ne_placeInfty`),
`…/Defs/PlaceDictionary.lean` (the out-of-set 3.2c–e bridges), and
`…/Defs/AdelicIndex.lean` + `…/RiemannRoch/Assembly.lean` (`adeleSpace`,
`diagonalHom`, `diagonal_mem_adeleSpace`).

## 17. State at audit time

The phase-3.2b worker started before this note closed. No `P1ResidueCore.lean` existed
at audit time; the classifications above are the route record. The two outstanding
items to re-check against the landed module are (i) whether the five private
`PushPull.lean` names (rows 16, 19, 20, 21, 22) and the five private
`Transcendence`/`PlacesOverDVR` names (rows 90–94) are promoted or resolved in-module,
and (ii) whether rows 102–106 (the partial-fraction span chain) landed at the pin
statements, since they are the only multi-step new proofs in the chunk.
