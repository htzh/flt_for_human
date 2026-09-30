# Mathlib-first substitution audit — the phase-3.2c ℙ¹ residue core, chunk 2 (P3.2c)

**Method:** `lean/porting-playbook.md` §2.2 (audit the route, mathlib first), after the
phase-1/2/3.1/3.2a/3.2b templates [`AUDIT-mathlib.md`](AUDIT-mathlib.md),
[`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md),
[`AUDIT-mathlib-p3-1.md`](AUDIT-mathlib-p3-1.md),
[`AUDIT-mathlib-p3-2a.md`](AUDIT-mathlib-p3-2a.md) and
[`AUDIT-mathlib-p3-2b.md`](AUDIT-mathlib-p3-2b.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Measured inventory:
[`tools/deps/build/p32_master_inventory.txt`](../../../tools/deps/build/p32_master_inventory.txt)
(rows #145–#289), with the pre-port advice in
[`tools/deps/build/p32_engine_advise.log`](../../../tools/deps/build/p32_engine_advise.log)
and its machine-readable twin
[`p32_engine_advise.json`](../../../tools/deps/build/p32_engine_advise.json).

Source, the single pin `S_` file (13,173 ln, 580 declarations):

- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean),
  rows #145–#289 = pin lines 3388–6744 (145 rows).

**Class convention** (unchanged from phases 1–3.2b). SUBSTITUTE = the port can import
an existing declaration instead of proving the row: an already-landed port lemma or a
mathlib constant whose *type* is the pin's, or a pin `def`/`abbrev`/instance whose body
is `rfl`-equal to a mathlib/port term. A statement that differs from the port copy only
by binder spelling, a `p1PlaceInfty` → `placeInfty` name translation, or a dropped prime
on a pin-`private` name is counted SUBSTITUTE with that difference recorded.
PROOF-INGREDIENT = the statement is bespoke (it mentions pin vocabulary) but the proof is
a short assembly of named mathlib/port lemmas. BESPOKE = a definition/structure/class/
`Prop` introducing new vocabulary, or an instance with no mathlib/port counterpart; these
are the recorded negatives and the real work. Instances that assemble already-ported
vocabulary are counted PROOF-INGREDIENT, following 3.2b’s treatment of the
`FiniteResidue` instances (rows #73–#75 there).

**Scratch evidence:** `lean/ScratchAuditP32c.lean` (gitignored, 188 ln), compiled from
`lean/` with

```bash
timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP32c.lean
```

**final run clean, exit 0, 2.3–4.3 s wall** (466 lines of output; 114 `#check`s; no
errors; four warnings: the three deliberate deprecation probes and one unused-variable
linter note on a prototype binder). The probe ledger:

- **P** — the port-substitute `#check`s (§A–§F of the scratch): rows #145–#155, the
  chunk-1 vocabulary the new rows consume (`OrdDifferentialWellDefined`,
  `P1DifferentialCoeffRegularFinite`, `p1PrincipalPartAtom`, `p1PlaceInfty`,
  `Place.uniformizer_ne_zero`, `ord_placeInfty_X`), `Defs/PlaceDictionary.lean`,
  `Canonical/HasCanonicalDivisor.lean`, `Defs/CanonicalLocalResidueInstanceV2.lean`
  and `Genus/Index.lean`. All resolve; that is the by-probe verification of every
  SUBSTITUTE port name tabulated below.
- **M** — the mathlib `#check` ledger (§G): `Derivation.{leibniz_of_mul_eq_one,
  leibniz_div, leibniz_inv, map_algebraMap}`, `Polynomial.Separable`/`separable_def`,
  `Polynomial.dvd_derivative_iff`, `Polynomial.degree_derivative_lt`,
  `Polynomial.{wronskian, degree_wronskian_lt_add, natDegree_wronskian_lt_add,
  IsCoprime.wronskian_eq_zero_iff}`, `Polynomial.{divByMonic_eq_zero_iff,
  rootMultiplicity, rootMultiplicity_eq_multiplicity, pow_rootMultiplicity_dvd,
  le_rootMultiplicity_iff}`, `PerfectField.ofCharZero`,
  `Algebra.IsAlgebraic.isSeparable_of_perfectField`, `Ideal.{inertiaDeg,
  inertiaDeg_def, ramificationIdx, ramificationIdx_def, ramificationIdx_spec}`,
  `Finset.sum_fiberwise_of_maps_to`, `Algebra.norm_eq_prod_automorphisms`,
  `IsGalois.card_aut_eq_finrank`, `Algebra.finrank_eq_of_equiv_equiv`,
  `finrank_eq_one_iff_of_nonzero'`, and
  `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`.
- **D** — the deliberate deprecation probes (`Ideal.inertiaDeg'`,
  `Ideal.ramificationIdx'`, `Ideal.inertiaDeg'_algebraMap`), which are the only
  diagnostics.
- **H** — compile-checked prototypes: `[CharZero K] → PerfectField K` by
  `inferInstance` (row #187’s route); the pin’s `n'd − nd'` rewritten as
  `-Polynomial.wronskian n d` and closed by `Polynomial.natDegree_wronskian_lt_add`
  (row #271); and `hsep.isUnit_of_dvd'` dot-notation on the `Polynomial.Separable`
  `def` (row #218).

## 1. Summary — class counts

| block (rows) | SUBSTITUTE | PROOF-INGREDIENT | BESPOKE | rows |
|---|---:|---:|---:|---:|
| ℙ¹ ord / divisor / degree (#145–#156) | 11 | 1 | 0 | 12 |
| differential-coefficient prelude (#157–#163) | 0 | 7 | 0 | 7 |
| `PlaceDictionary` bridges (#164–#176) | 13 | 0 | 0 | 13 |
| Kaehler engine + char-0 closure (#177–#191) | 11 | 4 | 0 | 15 |
| pole / Laurent corrections + gate (#192–#203) | 11 | 1 | 0 | 12 |
| `ag9b15u` + `aCoeff` seed (#204–#211) | 4 | 4 | 0 | 8 |
| `dX`, derivatives, principal-part atoms (#212–#232) | 1 | 19 | 1 | 21 |
| `KaehlerRankOne` / `RamificationInertiaIdentity` / Galois (#233–#245) | 1 | 9 | 3 | 13 |
| coord-independence + `essFiniteType` (#246–#253) | 3 | 4 | 1 | 8 |
| `resStar` / `canonicalLocalResidueDataKStar` (#254–#270) | 17 | 0 | 0 | 17 |
| Wronskian / `ratFuncDXCoeff` / the capstone (#271–#289) | 0 | 18 | 1 | 19 |
| **total** | **72** | **67** | **6** | **145** |

**Headline.** Half of the chunk is already paid for and a third is short assembly:
72 of 145 rows are SUBSTITUTE, 67 are PROOF-INGREDIENT and only 6 introduce a new
object. The six BESPOKE rows are `dX` (#212), `KaehlerRankOne` (#233),
`RamificationInertiaIdentity` (#236), `principalDivisorOf` (#242),
`CanonicalLocalResidueKDifferentialCoordIndep` (#246) and `ratFuncDXCoeff` (#272) —
three `def … : Prop`, one `abbrev` (`dX`) and two plain `def`s (`principalDivisorOf`,
`ratFuncDXCoeff`). The genuinely new proof work is three
connected stories: the differential-coefficient prelude (#157–#163), the
`ag9b15u` normal-form block (#204–#207), and the `dX`/Wronskian/`ratFuncDXCoeff`
cone that culminates in the capstone `ordDifferentialWellDefined_ratFunc` (#285).
Three reuse wins dominate the route: `Defs/CanonicalLocalResidueInstanceV2.lean`
already carries 32 of the rows, `Canonical/HasCanonicalDivisor.lean` carries 14,
and mathlib’s `Polynomial.wronskian` block replaces the pin’s degree computation in
#271.

**Correction 1 — the brief’s substitutes list has two off-by-one names.**
`P1DifferentialCoeffUnitFinite` is **not** a chunk-1 / 3.2c declaration: the pin
defines it at line 6745, i.e. inventory row **#290**, the first row past the chunk
boundary. The chunk-1 and this chunk’s name is `P1DifferentialCoeffRegularFinite`
(pin line 2028 = row #79, port `Defs/P1ResidueCore.lean:437`), consumed here by
row #226. Do not let `UnitFinite` leak into this set. Likewise the brief’s
`exists_dXCoeff_*`/`exists_unit_dXCoeff_*` are rows #281–#283, all in-scope, while
`dX` is #212 and `ratFuncDXCoeff` is #272.

**Correction 2 — the brief’s "ℙ¹ `ord` leaves" are mostly phase-3.2a output.**
Rows #145–#155 (eleven of the twelve rows in that block) are already public in
`PrincipalDivisors/RatFuncDegree.lean` and `Defs/P1Dictionary.lean`. The pin’s
`p1PlaceInfty` is the port’s `placeInfty`, but `P1ResidueCore.lean:278` re-exports it
as `@[reducible] def p1PlaceInfty`, so the pin statements land verbatim. The one
genuinely new row in the block is #156 `instHasPrincipalDivisors`.

**Correction 3 — the `PlaceDictionary` bridges are in-set, and one is `private`.**
`neg_log_valuation_fiberCenter_eq_ord` (#165), `surjective_residueOfCenter` (#172)
and `inertiaDeg_eq_inertiaDeg_fiberCenter` (#176) are rows #164–#176, exactly as the
work order says (the 3.2b audit’s "out-of-set" note was against the 3.2b boundary).
All thirteen live in `Defs/PlaceDictionary.lean`; twelve are public and
`eq_ord_of_addHom_of_nonneg_iff` (#164) is `private` there
(`PlaceDictionary.lean:44`) and must be promoted or consumed in-file.

**Correction 4 — the fibre-count machinery already exists; `RamificationInertiaIdentity`
is only a re-shaping.** `AlgebraicCurve.FundamentalIdentity`
(`Defs/PushPull.lean:632`) already carries
`∀ v, ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.deg : ℤ) = (Module.finrank F F' : ℤ) * (v.deg : ℤ)`,
`SumRamificationInertia` (`:677`) the `inertiaDeg` form, and
`WeilExchange/FiberOverCount.lean:33` the proof of the latter. The pin’s
`RamificationInertiaIdentity` (#236) differs only by taking an arbitrary `Finset s`
with `(∀ w, w ∈ s ↔ w.restrict F = v)` instead of `v.fiber F'`; it is a thin wrapper,
not new mathematics. The same files supply `Place.ord_restrict` (`PushPull.lean:322`),
`deg_restrict_mul_inertiaDeg` (`:460`) and the Galois `ramificationIndex_smul` /
`inertiaDeg_smul` lemmas (`WeilExchange/GaloisRamification.lean:106/153`) that the
Galois block #238–#245 consumes.

**Correction 5 — the pin’s `KaehlerRankOne` duplicates the port’s `IsCurveOver`
field.** `IsCurveOver.kaehler_free_rank_one` (`Defs/IsCurveOver.lean:27`) is
`Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1`, verbatim the pin’s #233 `def`.
Row #234/#235 are then a two-line class construction.

**Correction 6 — row #245 is definitionally `Place.IsRational`.** The port’s
`Place.IsRational` (`Defs/PlaceEvaluation.lean:36`) is
`Function.Surjective (algebraMap K v.ResidueField)`, exactly the pin statement, and
`RationalFunctionField.isRational_of_deg_eq_one` (`P1Dictionary.lean:175`) plus
`deg_placeInfty` discharge it in one line.

## 2. The ℙ¹ ord / divisor / degree block (rows #145–#156)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 145 | `ord_ofHeightOneSpectrum_of_span` (3388) | SUBSTITUTE | `RationalFunctionField.ord_ofHeightOneSpectrum_of_span` (`RatFuncDegree.lean:176`) | probe P; `HeightOneSpectrum K[X]` = the port’s `IsDedekindDomain.HeightOneSpectrum (Polynomial K)` |
| 146 | `ord_ofHeightOneSpectrum_eq_zero_of_notMem` (3399) | SUBSTITUTE | `…ord_ofHeightOneSpectrum_eq_zero_of_notMem` (`P1Dictionary.lean:330`) | probe P; statement identical |
| 147 | `ord_placeInfty` (3411) | SUBSTITUTE | `…ord_placeInfty` (`P1Dictionary.lean:342`) | probe P; `p1PlaceInfty` → `placeInfty` translation |
| 148 | `ord_placeInfty_algebraMap` (3420) | SUBSTITUTE | `…ord_placeInfty_algebraMap` (`P1Dictionary.lean:347`) | probe P |
| 149 | `single_add_single_apply_eq_ord` (3431) | SUBSTITUTE | `…single_add_single_apply_eq_ord` (`P1Dictionary.lean:357`); the *general* `{vinf}` form is `private` at `RatFuncDegree.lean:303` | probe P; the pin’s `placeInfty`-specialised statement is the P1Dictionary copy |
| 150 | `degree_single_add_single` (3465) | SUBSTITUTE | `…degree_single_add_single` (`P1Dictionary.lean:391`); general private copy at `RatFuncDegree.lean:347` | probe P |
| 151 | `degree_eq_zero_of_forall_eq_ord_algebraMap` (3475) | SUBSTITUTE | `…degree_eq_zero_of_forall_eq_ord_algebraMap` (`RatFuncDegree.lean:360`) | probe P; statement identical (the port proof obtains an arbitrary `vinf` via `exists_forall_ne_ofHeightOneSpectrum` instead of using `placeInfty`) |
| 152 | `principalDivisor` (3518) | SUBSTITUTE | `…principalDivisor` (`P1Dictionary.lean:400`) | probe P; identical `def` body over `finite_setOf_ord_ne_zero` |
| 153 | `principalDivisor_apply` (3523) | SUBSTITUTE | `…principalDivisor_apply` (`P1Dictionary.lean:405`) | probe P; `rfl` |
| 154 | `degree_eq_zero_of_forall_eq_ord` (3526) | SUBSTITUTE | `…degree_eq_zero_of_forall_eq_ord` (`RatFuncDegree.lean:401`) | probe P; identical statement; the port builds `Dden` by `Finsupp.ofSupportFinite`, the pin by `principalDivisor` |
| 155 | `degree_principalDivisor` (3553) | SUBSTITUTE | `…degree_principalDivisor` (`P1Dictionary.lean:412`) | probe P; one call to row #154 |
| 156 | `instHasPrincipalDivisors` (3557) | PROOF-INGREDIENT | `HasPrincipalDivisors` (`Defs/Divisor.lean:63`) | **not in the port**; a three-field `scoped instance` assembled from #152/#155. Chunk 1 already consumes `[HasPrincipalDivisors K (RatFunc K)]` as a section variable (`P1ResidueCore.lean:345/435/452/461`), so this must land before any consumer that discharges the instance |

## 3. The differential-coefficient prelude (rows #157–#163)

No port copy exists for any of these seven; each is a short mathlib/port assembly.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 157 | `D_ratFuncX_eq_neg_X_sq_smul_D_inv` (3592) | PROOF-INGREDIENT | `Derivation.leibniz_of_mul_eq_one` (`RingTheory/Derivation/Basic.lean:479`), `mul_inv_cancel₀`, `RatFunc.X_ne_zero` | probe M; the pin’s body is the one call |
| 158 | `ord_placeInfty_X_inv` (3599) | PROOF-INGREDIENT | `Place.ord_inv`; `RationalFunctionField.ord_placeInfty_X` (`Genus/Stichtenoth.lean:780`) | probe P/M |
| 159 | `ord_placeInfty_X_pow` (3602) | PROOF-INGREDIENT | `zpow_natCast`, `Place.ord_zpow`, `ord_placeInfty_X` | probe M |
| 160 | `D_ratFuncX_inv_ne_zero` (3612) | PROOF-INGREDIENT | `OrdDifferentialWellDefined` (chunk 1, `P1ResidueCore.lean:120`), `Place.dCoord_ne_zero` | probe P |
| 161 | `differentialCoeff_placeInfty_D_X_eq` (3629) | PROOF-INGREDIENT | `Place.differentialCoeff_smul`, row #157 | probe P |
| 162 | `ord_differentialCoeff_placeInfty_D_X_inv_eq_zero` (3636) | PROOF-INGREDIENT | `Place.differentialCoeff_unique`, `OrdDifferentialWellDefined` | probe P |
| 163 | `ordDifferential_placeInfty_D_ratFuncX` (3655) | PROOF-INGREDIENT | `Place.{ordDifferential, ord_neg, ord_mul, differentialCoeff_ne_zero}`, rows #158/#159/#161/#162, `norm_num` | probe P |

## 4. The `PlaceDictionary` bridges (rows #164–#176)

All thirteen are landed in `Defs/PlaceDictionary.lean`; probe P verifies every name.
Row #167 and #176 keep the pin’s primed `Ideal` text under a reasoned
`set_option linter.deprecated false` (see §15).

| row | pin decl (line) | class | port name (line) |
|---:|---|---|---|
| 164 | `eq_ord_of_addHom_of_nonneg_iff` (3726) | SUBSTITUTE (promote) | `Place.eq_ord_of_addHom_of_nonneg_iff` (`:44`, **`private`**) |
| 165 | `neg_log_valuation_fiberCenter_eq_ord` (3829) | SUBSTITUTE | `Place.neg_log_valuation_fiberCenter_eq_ord` (`:127`) |
| 166 | `le_ord_iff_mem_pow_fiberCenter` (3871) | SUBSTITUTE | `Place.le_ord_iff_mem_pow_fiberCenter` (`:169`) |
| 167 | `ramificationIndex_eq_ramificationIdx_fiberCenter` (3894) | SUBSTITUTE | `Place.ramificationIndex_eq_ramificationIdx_fiberCenter` (`:192`) |
| 168 | `toValuationSubringOfRestrictEq` (3931) | SUBSTITUTE | `Place.toValuationSubringOfRestrictEq` (`:228`) |
| 169 | `residueOfCenter` (3936) | SUBSTITUTE | `Place.residueOfCenter` (`:240`) |
| 170 | `residueOfCenter_apply` (3941) | SUBSTITUTE | `Place.residueOfCenter_apply` (`:245`) |
| 171 | `ker_residueOfCenter` (3945) | SUBSTITUTE | `Place.ker_residueOfCenter` (`:249`) |
| 172 | `surjective_residueOfCenter` (3951) | SUBSTITUTE | `Place.surjective_residueOfCenter` (`:255`) |
| 173 | `residueFieldEquivQuotientCenter` (4020) | SUBSTITUTE | `Place.residueFieldEquivQuotientCenter` (`:324`) |
| 174 | `placeCongrEquiv` (4025) | SUBSTITUTE | `Place.placeCongrEquiv` (`:338`) |
| 175 | `restrictResidueFieldEquiv` (4034) | SUBSTITUTE | `Place.restrictResidueFieldEquiv` (`:351`) |
| 176 | `inertiaDeg_eq_inertiaDeg_fiberCenter` (4038) | SUBSTITUTE | `Place.inertiaDeg_eq_inertiaDeg_fiberCenter` (`:363`) |

## 5. The Kaehler engine and the char-0 closure (rows #177–#191)

Rows #177–#186 and #189 are public already in `Canonical/HasCanonicalDivisor.lean`
(the 3.2b audit promoted the pin-`private` names); probe P. Rows #187/#188/#190/#191
are the char-0 closures and are the only new work here.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 177 | `_root_.…Place.uniformizerSubring'''` (4118, priv) | SUBSTITUTE | `AlgebraicCurve.Place.uniformizerSubring'''` (`HasCanonicalDivisor.lean:188`) | probe P; the port is public, the pin `private` |
| 178 | `…irreducible_uniformizerSubring'''` (4122, priv) | SUBSTITUTE | `…irreducible_uniformizerSubring'''` (`:191`) | probe P |
| 179 | `…maximalIdeal_eq_span_uniformizer` (4126, priv) | SUBSTITUTE | `…maximalIdeal_eq_span_uniformizer` (`:194`) | `IsDiscreteValuationRing.irreducible_iff_uniformizer` |
| 180 | `…D_polynomialAlgebra_uniformizer` (4131, priv) | SUBSTITUTE | `…D_polynomialAlgebra_uniformizer` (`:198`) | `KaehlerDifferential.map_algebraMap` |
| 181 | `…ker_algebraMap_residueField_eq_span` (4140, priv) | SUBSTITUTE | `…ker_algebraMap_residueField_eq_span` (`:206`) | `IsLocalRing.ResidueField.algebraMap_eq`, `IsLocalRing.ker_residue` |
| 182 | `…formallyUnramified_polynomial_residueField_of_isSeparable` (4147, priv) | SUBSTITUTE | `…formallyUnramified_polynomial_residueField_of_isSeparable` (`:212`) | `Algebra.FormallyUnramified.{of_isSeparable, of_restrictScalars}` |
| 183 | `…subsingleton_residueKaehler_of_isSeparable` (4158, priv) | SUBSTITUTE | `…subsingleton_residueKaehler_of_isSeparable` (`:222`) | `FormallyUnramified.subsingleton_kaehlerDifferential` |
| 184 | `…subsingleton_residueTensor_polynomialKaehler_of_isSeparable` (4167, priv) | SUBSTITUTE | `…subsingleton_residueTensor_polynomialKaehler_of_isSeparable` (`:230`) | `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`, `Ideal.toCotangent_surjective` |
| 185 | `…finite_polynomialKaehler_of_finite_kaehler` (4203, priv) | SUBSTITUTE | `…finite_polynomialKaehler_of_finite_kaehler` (`:265`) | `Module.Finite.of_surjective`, `KaehlerDifferential.map_surjective` |
| 186 | `…subsingleton_polynomialKaehler_of_isSeparable_of_finite` (4214, priv) | SUBSTITUTE | `…subsingleton_polynomialKaehler_of_isSeparable_of_finite` (`:275`) | `IsLocalRing.subsingleton_tensorProduct` |
| 187 | `…isSeparable_residueField_of_charZero_of_finiteResidue` (4225, priv) | PROOF-INGREDIENT | `PerfectField.ofCharZero` (instance, `FieldTheory/Perfect.lean:306`), `Algebra.IsAlgebraic.isSeparable_of_perfectField` (instance, `:338`) | probe M/H: `[CharZero K] → PerfectField K` is `inferInstance`. The port’s `isSeparable_residueField_of_perfectField_of_finiteResidue` (`:1019`) and `isSeparable_residueField_forall_of_perfectField` (`:1030`) are the `[PerfectField K]` per-place / `∀ v` versions — a different hypothesis, **not** a statement substitute |
| 188 | `…subsingleton_polynomialKaehler_of_charZero_of_finite` (4234, priv) | PROOF-INGREDIENT | row #187 then row #186 | no port copy; two lines |
| 189 | `ValSubringKaehlerFinite` (4251) | SUBSTITUTE | `AlgebraicCurve.ValSubringKaehlerFinite` (`:291`) | probe P |
| 190 | `valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_charZero` (4256) | PROOF-INGREDIENT | `valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_isSeparable` (`:296`) | the port’s name takes `[∀ v, IsSeparable K (ResidueField …)]`; the pin’s `[CharZero K] [∀ v, v.FiniteResidue]` route is row #187 + the port lemma |
| 191 | `valSubringKaehlerSpanTop_of_kaehlerFinite_of_charZero` (4264) | PROOF-INGREDIENT | `valSubringKaehlerSpanTop_of_kaehlerFinite_of_isSeparable` (`:1042`) | one line from row #190; probe P verifies the separable copy |

## 6. Pole / Laurent corrections and the gate (rows #192–#203)

Rows #192–#196, #197–#200 and #201–#202 are import-only from
`Defs/CanonicalLocalResidueInstanceV2.lean`; all resolve by probe P. The block
`higherPoleCorrection'` was landed publicly there without the pin’s prime.

| row | pin decl (line) | class | port name (line) |
|---:|---|---|---|
| 192 | `exists_mem_poleSubmodule` (4322) | SUBSTITUTE | `AlgebraicCurve.Place.exists_mem_poleSubmodule` (`:317`) |
| 193 | `uniformizer_pow_inv_mem_poleSubmodule_self` (4378) | SUBSTITUTE | `…uniformizer_pow_inv_mem_poleSubmodule_self` (`:352`) |
| 194 | `higherPoleMonomial_sum_mem_poleSubmodule` (4382) | SUBSTITUTE | `…higherPoleMonomial_sum_mem_poleSubmodule` (`:356`) |
| 195 | `higherPoleMonomial_coeff_eq_zero_of_mem` (4390) | SUBSTITUTE | `…higherPoleMonomial_coeff_eq_zero_of_mem` (`:364`) |
| 196 | `linearIndependent_higherPoleMonomial_mkQ` (4420) | SUBSTITUTE | `…linearIndependent_higherPoleMonomial_mkQ` (`:394`) |
| 197 | `…higherPoleCorrectionAux'` (4430, priv) | SUBSTITUTE (rename) | `…higherPoleCorrectionAux` (`:404`, public, no prime) |
| 198 | `…higherPoleCorrection'` (4438, priv) | SUBSTITUTE (rename) | `…higherPoleCorrection` (`:411`) |
| 199 | `…higherPoleCorrection'_apply_of_mem` (4442, priv) | SUBSTITUTE (rename) | `…higherPoleCorrection_apply_of_mem` (`:414`) |
| 200 | `…higherPoleCorrection'_uniformizer_pow_inv` (4449, priv) | SUBSTITUTE (rename) | `…higherPoleCorrection_uniformizer_pow_inv` (`:420`) |
| 201 | `canonicalLocalResidueDataKOfExtend` (4468) | SUBSTITUTE | `…canonicalLocalResidueDataKOfExtend` (`:438`) |
| 202 | `CanonicalLocalResidueDataK.res_algebraMap_mul_uniformizer_pow_inv` (4544) | SUBSTITUTE | `AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_algebraMap_mul_uniformizer_pow_inv` (`:340`) |
| 203 | `gate_canonicalLocalResidueDataK_uniformizer_inv` (4554) | PROOF-INGREDIENT | `gate_localResidueData_uniformizer_inv` (`P1ResidueCore.lean:811`) | one line: `… v R.toLocalResidueData`; no port copy of the wrapper |

## 7. `ag9b15u` and the `aCoeff` seed (rows #204–#211)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 204 | `…MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero` (4592, priv) | PROOF-INGREDIENT | `IsLocalRing.residue_eq_zero_iff`, `IsLocalRing.mem_maximalIdeal`, `mem_nonunits_iff`, `Place.{ord_nonneg_of_mem, mem_of_ord_nonneg, ord_inv}` | **no `ag9b15u`/`MilneAvAg9b` anywhere in the port** (grep count 0); pin-`private`, keep `private` |
| 205 | `…ag9b15u_exists_unit_normal_form_of_surj` (4613, priv) | PROOF-INGREDIENT | row #204, `IsLocalRing.ResidueField.algebraMap_eq`, `IsScalarTower.algebraMap_apply`, `mul_inv_cancel₀` | new |
| 206 | `…ag9b15u_exists_K_truncation_of_mem_poleSubmodule` (4662, priv) | PROOF-INGREDIENT | `Place.{laurentTailCoeff, laurentTail_remainder_mem_poleSubmodule, coe_poleSubmodule_zero}`, `Finset.sum_range_succ` | new; induction on the pole depth |
| 207 | `…ag9b15u_differentialCoeff_D_unit_mul_uniformizer` (4703, priv) | PROOF-INGREDIENT | `Derivation.leibniz`, `Place.{differentialCoeff_unique, differentialCoeff_smul_dCoord}`, `add_smul`, `smul_smul` | new |
| 208 | `aCoeff` (4751) | SUBSTITUTE | `ModularCurve.KwNo6Pin.aCoeff` (`CanonicalLocalResidueInstanceV2.lean:1225`) | probe P; byte-identical body |
| 209 | `mp72a103_t2_evalDepth_of_uniformizer_mul` (4788) | SUBSTITUTE | `Mp72a103T2.mp72a103_t2_evalDepth_of_uniformizer_mul` (`:978`) | probe P |
| 210 | `mp72a103_t2_lift_eq_zero_of_depth_one` (4813) | SUBSTITUTE | `Mp72a103T2.mp72a103_t2_lift_eq_zero_of_depth_one` (`:1003`) | probe P |
| 211 | `mp72a103_t2_taylor_coeff_eq_zero_of_depth` (4821) | SUBSTITUTE | `Mp72a103T2.mp72a103_t2_taylor_coeff_eq_zero_of_depth` (`:1011`) | probe P |

## 8. `dX`, derivatives and the principal-part atoms (rows #212–#232)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 212 | `dX` (4933) | **BESPOKE** | — | new `abbrev dX : Ω[(RatFunc K)⁄K] := KaehlerDifferential.D K (RatFunc K) RatFunc.X`; no port copy (grep for the term under `FLTForHuman/` is empty) |
| 213 | `aeval_ratFuncX_eq_algebraMap` (4935) | PROOF-INGREDIENT | `aeval_algHom_apply`, `aeval_X_left_apply`, `RatFunc.algebraMap_X` | probe M |
| 214 | `D_algebraMap_polynomial` (4942) | PROOF-INGREDIENT | `Derivation.map_aeval` (`RingTheory/Derivation/Basic.lean:151`), row #213 | probe M |
| 215 | `denom_sq_smul_D_eq` (4948) | PROOF-INGREDIENT | `Derivation.leibniz_div` (`RingTheory/Derivation/Basic.lean:499`), `RatFunc.num_div_denom`, `RatFunc.denom_ne_zero`, `IsFractionRing.injective` | probe M |
| 216 | `span_dX_eq_top` (4966) | PROOF-INGREDIENT | `KaehlerDifferential.span_range_derivation` (`RingTheory/Kaehler/Basic.lean:220`), `Submodule.mem_span_singleton`, row #215 | probe M |
| 217 | `dX_ne_zero` (4981) | PROOF-INGREDIENT | row #216, `Submodule.span_zero_singleton`, `exists_ne` | no port copy |
| 218 | `not_dvd_derivative_of_sq_not_dvd` (4989) | PROOF-INGREDIENT | `Polynomial.Separable` (= `IsCoprime p p.derivative`, `FieldTheory/Separable.lean:44`), `IsCoprime.isUnit_of_dvd'` (`RingTheory/Coprime/Basic.lean:179`), `derivative_mul`, `dvd_sub` | probe M/H: `hsep.isUnit_of_dvd'` resolves by dot-notation unfolding the `def` |
| 219 | `not_dvd_derivative_of_ord_eq_one` (5005) | PROOF-INGREDIENT | row #218, `Place.ord_ofHeightOneSpectrum_ne_zero_iff`, `ord_ofHeightOneSpectrum_of_span`, `Place.{ord_mul, ord_zpow}`, `ord_nonneg_of_mem` | no port copy |
| 220 | `uniformizer_ne_zero'` (5047, priv) | SUBSTITUTE | `AlgebraicCurve.Place.uniformizer_ne_zero` (`Defs/CanonicalDivisor.lean:53`) | probe P |
| 221 | `ord_algebraMap_denom_uniformizer_eq_zero` (5050) | PROOF-INGREDIENT | `RatFunc.{num_div_denom, isCoprime_num_denom, num_ne_zero, denom_ne_zero}`, `Place.{ord_mul, ord_inv, ord_nonneg_of_mem, ord_uniformizer}` | no port copy; ~30 pin ln |
| 222 | `ord_algebraMap_num_uniformizer_eq_one` (5081) | PROOF-INGREDIENT | row #221 + `RatFunc.num_div_denom` | no port copy |
| 223 | `not_dvd_num'denom_sub_numdenom'` (5095) | PROOF-INGREDIENT | row #219/#221/#222, `dvd_add`, `dvd_sub`, `hp.prime.dvd_mul` | no port copy |
| 224 | `ord_differentialCoeff_dX_ofHeightOneSpectrum` (5134) | PROOF-INGREDIENT | row #215/#223, `Place.{dCoord, differentialCoeff_unique, ord_inv, ord_mul, ord_zpow}`, `div_eq_mul_inv` | no port copy |
| 225 | `differentialCoeff_dX_mem_ofHeightOneSpectrum` (5173) | PROOF-INGREDIENT | row #224, `Place.differentialCoeff_ne_zero`, `Place.mem_of_ord_nonneg`, row #217 | no port copy |
| 226 | `p1DifferentialCoeffRegularFinite_dX` (5193) | PROOF-INGREDIENT | `P1DifferentialCoeffRegularFinite` (chunk 1, `P1ResidueCore.lean:437`), row #225, `exists_irreducible_span`, `eq_ofHeightOneSpectrum_or_eq_placeInfty` | no port copy |
| 227 | `ord_ofHeightOneSpectrum_irreducible_eq_zero_of_ne` (5242) | PROOF-INGREDIENT | `Place.ord_ofHeightOneSpectrum_ne_zero_iff`, `PrincipalIdealRing.isMaximal_of_irreducible`, `HeightOneSpectrum.ext` | no port copy |
| 228 | `ord_algebraMap_irreducible_eq_zero_of_ne` (5256) | PROOF-INGREDIENT | row #227 + `eq_ofHeightOneSpectrum_or_eq_placeInfty` | no port copy |
| 229 | `inv_algebraMap_pow_mem_of_ne_finitePlace` (5265) | PROOF-INGREDIENT | row #228, `Place.{mem_of_ord_nonneg, ord_inv, ord_zpow}`, `zpow_natCast` | no port copy |
| 230 | `p1PrincipalPartAtom_mem_of_ne_finitePlace` (5275) | PROOF-INGREDIENT | row #229, `algebraMap_polynomial_mem_of_ne_placeInfty'` (chunk 1), `p1PrincipalPartAtom` (`P1ResidueCore.lean:454`) | no port copy |
| 231 | `ord_placeInfty_p1PrincipalPartAtom` (5293) | PROOF-INGREDIENT | `ord_placeInfty_algebraMap'` (`P1ResidueCore.lean:588`), `Place.{ord_mul, ord_inv, ord_zpow}`, `div_eq_mul_inv` | no port copy |
| 232 | `one_le_ord_placeInfty_p1PrincipalPartAtom` (5306) | PROOF-INGREDIENT | row #231, `Polynomial.natDegree_lt_natDegree`, `nlinarith` | no port copy |

## 9. `KaehlerRankOne`, `RamificationInertiaIdentity` and the Galois block (rows #233–#245)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 233 | `KaehlerRankOne` (5368) | **BESPOKE** | — | new `def : Prop`; the port’s `IsCurveOver.kaehler_free_rank_one` field (`Defs/IsCurveOver.lean:27`) is the same conjunction (Correction 5) |
| 234 | `IsCurveOver.of_finiteResidue_of_kaehlerRankOne` (5375) | PROOF-INGREDIENT | `IsCurveOver` (`Defs/IsCurveOver.lean:23`), `Place.FiniteResidue.finite`, row #233 | two-line class construction; no port copy |
| 235 | `isCurveOver_of_kaehlerRankOne` (5387) | PROOF-INGREDIENT | row #234 | one line; no port copy |
| 236 | `RamificationInertiaIdentity` (5427) | **BESPOKE** | — | new `def : Prop`; its content already exists as `AlgebraicCurve.FundamentalIdentity` (`Defs/PushPull.lean:632`) / `SumRamificationInertia` (`:677`) with `v.fiber F'` in place of the pin’s `Finset s` (Correction 4) |
| 237 | `Divisor.degree_eq_sum_support` (5447) | SUBSTITUTE | `AlgebraicCurve.Divisor.degree_eq_sum_support` (`Genus/Index.lean:45`) | probe P; identical statement |
| 238 | `degree_eq_finrank_mul_of_forall_eq_ord_algebraMap` (5452) | PROOF-INGREDIENT | `Finset.sum_fiberwise_of_maps_to` (`Algebra/BigOperators/…`), `Place.ord_restrict` (`PushPull.lean:322`), `Finset.{mul_sum, sum_filter, sum_congr}`, `Place.ramificationIndex_pos` | probe M; the pin’s 53-line assembly uses `H : RamificationInertiaIdentity` directly |
| 239 | `_root_.…Place.ord_prod` (5505, priv) | PROOF-INGREDIENT | `Finset.cons_induction`, `Place.ord_mul`, `Finset.prod_ne_zero_iff` | no port copy; pin-`private`, keep `private` |
| 240 | `sum_smul_apply_eq_ord_prod` (5520) | PROOF-INGREDIENT | row #239, `Place.ord_smul`, `AlgEquiv.restrictScalars`, `Finset.sum_apply'`, `smul_inv_smul` | no port copy |
| 241 | `degree_eq_zero_of_isGalois` (5534) | PROOF-INGREDIENT | `Algebra.norm_eq_prod_automorphisms` (`RingTheory/Norm/Transitivity.lean:277`), `Algebra.norm_ne_zero_iff`, `IsGalois.card_aut_eq_finrank`, `HasPrincipalDivisors.exists_divisor`, `Finset.{sum_const, card_univ}`, `nsmul_eq_mul` | probe M; 59 pin ln, all named lemmas |
| 242 | `principalDivisorOf` (5593) | **BESPOKE** | — | new `def`; consumes `finite_setOf_ord_ne_zero_of_finiteDimensional` (p3-2b row #94, `PrincipalDivisors/Transcendence.lean`) |
| 243 | `degree_eq_zero_of_forall_eq_ord_of_isGalois` (5597) | PROOF-INGREDIENT | row #241 | one line |
| 244 | `hasPrincipalDivisors_of_isGalois` (5603) | PROOF-INGREDIENT | rows #242/#243, `HasPrincipalDivisors` (`Defs/Divisor.lean:63`) | new instance assembly; no port copy |
| 245 | `surjective_algebraMap_residueField_placeInfty` (5654) | PROOF-INGREDIENT | `Place.IsRational` (`Defs/PlaceEvaluation.lean:36`, defeq the statement), `RationalFunctionField.isRational_of_deg_eq_one` (`P1Dictionary.lean:175`), `deg_placeInfty`, `finrank_eq_one_iff_of_nonzero'` (`LinearAlgebra/FiniteDimensional/Basic.lean:602`) | probe M; one line (Correction 6) |

## 10. Coordinate independence and `essFiniteType` (rows #246–#253)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 246 | `CanonicalLocalResidueKDifferentialCoordIndep` (5670) | **BESPOKE** | — | new `def : Prop` over `CanonicalLocalResidueDataK.res` and `Place.differentialCoeff`; no port copy |
| 247 | `ratFuncX_inv_pow_inv` (5693) | PROOF-INGREDIENT | `inv_pow`, `inv_inv` | no port copy; two lines |
| 248 | `X_pow_mul_differentialCoeff_D_X_eq_neg` (5697) | PROOF-INGREDIENT | row #247, row #161, `ring` | no port copy |
| 249 | `canonicalLocalResidueDataK_res_X_pow_mul_D_X_of_coordIndep` (5714) | PROOF-INGREDIENT | rows #248/#158, `CanonicalLocalResidueDataK.res` (chunk 1), `map_neg` | no port copy |
| 250 | `canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow_of_coordIndep` (5724) | PROOF-INGREDIENT | row #249, `diagonalHom_apply` (`Defs/AdelicIndex.lean`) | no port copy |
| 251 | `_root_.…Place.finite_kaehler_of_essFiniteType` (5786, priv) | SUBSTITUTE | `AlgebraicCurve.Place.finite_kaehler_of_essFiniteType` (`HasCanonicalDivisor.lean:314`) | probe P; body is `KaehlerDifferential.finite` |
| 252 | `ValSubringEssFiniteType` (5799) | SUBSTITUTE | `AlgebraicCurve.ValSubringEssFiniteType` (`:331`) | probe P |
| 253 | `valSubringKaehlerFinite_of_essFiniteType` (5804) | SUBSTITUTE | `AlgebraicCurve.valSubringKaehlerFinite_of_essFiniteType` (`:341`) | probe P |

## 11. `resStar` and `canonicalLocalResidueDataKStar` (rows #254–#270)

All seventeen are import-only from `Defs/CanonicalLocalResidueInstanceV2.lean`,
namespace `ModularCurve.KwNo6Pin`; probe P. Spot-checked statement-identical
(`aCoeff` `:1225`, `resStarₗ` `:1584`, `resStar_simplePole` `:1590`,
`canonicalLocalResidueDataKStar` `:1639`).

| row | pin decl (line) | port name (line) |
|---:|---|---|
| 254 | `aCoeff_zero` (5856) | `ModularCurve.KwNo6Pin.aCoeff_zero` (`:1268`) |
| 255 | `aCoeff_add` (5868) | `…aCoeff_add` (`:1280`) |
| 256 | `aCoeff_smul` (5918) | `…aCoeff_smul` (`:1330`) |
| 257 | `aCoeff_shift` (5977) | `…aCoeff_shift` (`:1389`) |
| 258 | `aCoeff_shift_pow` (6047) | `…aCoeff_shift_pow` (`:1459`) |
| 259 | `aCoeff_one_eq_zero` (6064) | `…aCoeff_one_eq_zero` (`:1476`) |
| 260 | `clearPow_mem` (6107) | `…clearPow_mem` (`:1519`) |
| 261 | `clearedHat` (6117) | `…clearedHat` (`:1529`) |
| 262 | `resStar` (6122) | `…resStar` (`:1534`) |
| 263 | `aCoeff_clearedHat_of_le` (6126) | `…aCoeff_clearedHat_of_le` (`:1538`) |
| 264 | `resStar_add` (6141) | `…resStar_add` (`:1553`) |
| 265 | `resStar_smul` (6157) | `…resStar_smul` (`:1569`) |
| 266 | `resStarₗ` (6172) | `…resStarₗ` (`:1584`) |
| 267 | `resStar_simplePole` (6178) | `…resStar_simplePole` (`:1590`) |
| 268 | `resStar_of_mem` (6198) | `…resStar_of_mem` (`:1610`) |
| 269 | `resStar_higherPoleMonomial` (6206) | `…resStar_higherPoleMonomial` (`:1618`) |
| 270 | `canonicalLocalResidueDataKStar` (6227) | `…canonicalLocalResidueDataKStar` (`:1639`) |

## 12. The Wronskian / `ratFuncDXCoeff` block (rows #271–#289)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 271 | `natDegree_numDenomWronskian_lt` (6271) | PROOF-INGREDIENT | **`Polynomial.natDegree_wronskian_lt_add`** (`RingTheory/Polynomial/Wronskian.lean:111`), `Polynomial.wronskian` (`:43`) | probe M/H: the pin’s `n.derivative * d - n * d.derivative` is `-Polynomial.wronskian n d` (mathlib’s `wronskian a b = a * b' - a' * b`), so the 22-line degree computation collapses to `rw [hneg, natDegree_neg]; exact Polynomial.natDegree_wronskian_lt_add hw` |
| 272 | `ratFuncDXCoeff` (6293) | **BESPOKE** | — | new `def` (the Wronskian of `f.num`, `f.denom` over `denom²`); no port copy |
| 273 | `ratFuncDXCoeff_def` (6297) | PROOF-INGREDIENT | `rfl` | no port copy |
| 274 | `D_eq_ratFuncDXCoeff_smul_dX` (6302) | PROOF-INGREDIENT | row #215, `div_eq_mul_inv`, `mul_smul`, `inv_mul_cancel₀` | no port copy |
| 275 | `wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero` (6309) | PROOF-INGREDIENT | row #273, `zero_div` | no port copy; note `IsCoprime.wronskian_eq_zero_iff` (`Wronskian.lean:125`) is the mathlib analogue (off-path here) |
| 276 | `ord_algebraMap_denom_eq_zero_of_ord_eq_one` (6325) | PROOF-INGREDIENT | `RatFunc.{num_div_denom, isCoprime_num_denom, num_ne_zero, denom_ne_zero}`, `Place.{ord_mul, ord_inv, ord_nonneg_of_mem}` | parallel to row #221 for an arbitrary `f` |
| 277 | `ord_algebraMap_num_eq_one_of_ord_eq_one` (6355) | PROOF-INGREDIENT | row #276 | no port copy |
| 278 | `not_dvd_wronskian_of_ord_eq_one` (6368) | PROOF-INGREDIENT | rows #219/#276/#277, `dvd_add`, `dvd_sub`, `hp.prime.dvd_mul` | no port copy |
| 279 | `ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one` (6396) | PROOF-INGREDIENT | row #278, `Place.{ord_mul, ord_inv, ord_zpow}`, `ord_algebraMap_denom_eq_zero_of_ord_eq_one` | no port copy |
| 280 | `ord_placeInfty_ratFuncDXCoeff_ge` (6430) | PROOF-INGREDIENT | row #271, `ord_placeInfty` (`P1Dictionary.lean:342`), `RatFunc.{intDegree_div, intDegree_polynomial}`, `Polynomial.natDegree_pow`, `omega` | no port copy |
| 281 | `exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero` (6459) | PROOF-INGREDIENT | `exists_sub_algebraMap_intDegree_neg` (`P1Dictionary.lean`), rows #274/#280, `p1PlaceInfty_toValuationSubring`, `Derivation.map_algebraMap` | no port copy |
| 282 | `exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one` (6494) | PROOF-INGREDIENT | row #281, `Place.{ord_mul, ord_inv, ord_neg, ord_add_eq_left}`, `ord_placeInfty_X`, `Derivation.leibniz` | no port copy; uses chunk-1 `ord_add_eq_left` |
| 283 | `exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one` (6542) | PROOF-INGREDIENT | row #282, `Derivation.leibniz_inv`, `Place.{ord_neg, ord_mul, ord_zpow}`, `inv_inv` | no port copy |
| 284 | `exists_ord_zero_smul_of_smul_dX_eq` (6567) | PROOF-INGREDIENT | `Place.{ord_mul, ord_inv}`, `div_mul_cancel₀`, `smul_smul` | no port copy; the finite/infinite glue |
| 285 | `ordDifferentialWellDefined_ratFunc` (6581) | PROOF-INGREDIENT | `OrdDifferentialWellDefined` (chunk 1, `P1ResidueCore.lean:120`), rows #279/#283/#284, `eq_ofHeightOneSpectrum_or_eq_placeInfty`, `exists_irreducible_span` | the chunk capstone; assembles the finite side (#279) and the infinity side (#283) through #284 |
| 286 | `two_le_ord_placeInfty_p1PrincipalPartAtom` (6660) | PROOF-INGREDIENT | row #231, `Polynomial.natDegree_lt_natDegree`, `nlinarith` | parallel to row #232 |
| 287 | `not_dvd_of_degree_lt` (6682) | PROOF-INGREDIENT | `Polynomial.degree_le_of_dvd` (`Algebra/Polynomial/Degree/Domain.lean:63`), `not_lt` | probe M |
| 288 | `ord_finitePlace_of_degree_lt` (6688) | PROOF-INGREDIENT | row #287, `ord_finitePlace_ne_zero_iff` (`P1Dictionary.lean`) | no port copy |
| 289 | `ord_finitePlace_p1PrincipalPartAtom` (6696) | PROOF-INGREDIENT | rows #288/#231, `ord_finitePlace_self`, `Place.{ord_mul, ord_inv, ord_zpow}`, `div_eq_mul_inv` | no port copy |

## 13. Reuse wins, with probe evidence

### 13.1 The ℙ¹ divisor/degree block is phase-3.2a output (rows #145–#155)

Eleven rows import outright. Rows #149/#150 have two homes: the pin’s
`placeInfty`-specialised statements in `P1Dictionary.lean:357/391`, and the *more
general* `{vinf}` + `hvinf` versions that are `private` in `RatFuncDegree.lean:303/347`.
Import the public specialised pair; do not transcribe a third copy. Row #151’s port
proof deliberately avoids `placeInfty` (`exists_forall_ne_ofHeightOneSpectrum`), which
is why it lives in `RatFuncDegree` rather than `P1Dictionary`.

### 13.2 `HasPrincipalDivisors K (RatFunc K)` is missing, and chunk 1 assumes it

Probe P confirms `AlgebraicCurve.Place.uniformizer_ne_zero` and every engine/ord
substitute, but there is **no** `HasPrincipalDivisors K (RatFunc K)` instance in the
tree (grep for `instance … HasPrincipalDivisors` under `FLTForHuman/` is empty;
`P1ResidueCore.lean` uses it only as a `variable` at lines 345/435/452/461). Row #156
is the ℙ¹ base case and is a genuine chunk-2 deliverable.

### 13.3 The char-0 closure is one instance away (rows #187/#190/#191)

`[CharZero K]` gives `PerfectField K` by `inferInstance` (`PerfectField.ofCharZero`),
so `Algebra.IsAlgebraic.isSeparable_of_perfectField` discharges row #187 with no change
from the pin text (probe H). The port’s separable variants
(`HasCanonicalDivisor.lean:296/1042`) are stated with the separable hypothesis
explicitly; the two `_of_charZero` wrappers are one line each.

### 13.4 The fibre dictionary is already there; do not re-derive rows #236–#245

`FundamentalIdentity` (`Defs/PushPull.lean:632`), `SumRamificationInertia` (`:677`)
and `WeilExchange/FiberOverCount.lean:33` already carry the ramification–inertia sum
and its proof; `PushPull.lean:322/460` carry `ord_restrict` and
`deg_restrict_mul_inertiaDeg`; `WeilExchange/GaloisRamification.lean:106/153` carry the
Galois `ramificationIndex_smul`/`inertiaDeg_smul`. Row #236 is a re-shaping of
`FundamentalIdentity` to the pin’s `Finset s` binder, and #238/#241 then consume it
directly. The genuinely new part of the block is the Galois norm computation of #241
(mathlib `Algebra.norm_eq_prod_automorphisms` + `IsGalois.card_aut_eq_finrank`), plus
the `principalDivisorOf` definition and its instance.

### 13.5 mathlib’s Wronskian replaces the pin’s degree computation (row #271)

`Mathlib/RingTheory/Polynomial/Wronskian.lean` (v4.34.0) defines
`Polynomial.wronskian a b = a * b' - a' * b` with `degree_wronskian_lt_add`,
`natDegree_wronskian_lt_add`, `wronskian_eq_of_sum_zero` and
`IsCoprime.wronskian_eq_zero_iff`. The pin’s Wronskian is the **negative**,
`n' * d - n * d'`, and probe H closes row #271 in three lines. This is the single
largest proof saving in the chunk.

### 13.6 Row #245 is definitionally `Place.IsRational`

`Place.IsRational` (`Defs/PlaceEvaluation.lean:36`) is literally the `Function.Surjective`
statement, and `isRational_of_deg_eq_one` (`P1Dictionary.lean:175`) plus `deg_placeInfty`
give the one-line port. The pin’s unfolded spelling must still be landed for the checker.

## 14. Route options

- **R1 — import `P1Dictionary` / `RatFuncDegree` for rows #145–#155.** Do not touch
  the `placeInfty` alias; `P1ResidueCore.lean:278` already re-exports `p1PlaceInfty`.
- **R2 — promote the two private copies and consume the renamed block.** Row #164
  `Place.eq_ord_of_addHom_of_nonneg_iff` is `private` in `PlaceDictionary.lean:44`;
  promote it (or keep the chunk-2 consumer inside that module). Rows #197–#200 are
  already public as the no-prime `higherPoleCorrection` block; import that.
- **R3 — treat `CanonicalLocalResidueInstanceV2`, `HasCanonicalDivisor`,
  `PlaceDictionary`, `P1Dictionary` and `Genus/Index` as the public API.** That
  covers 70 of the 72 SUBSTITUTE rows; the other two are row #220
  (`Defs/CanonicalDivisor.lean`) and row #237 (`Genus/Index.lean`). Do
  not re-derive the `Mp72a103T2`/`KwNo6Pin` calculus.
- **R4 — land `instHasPrincipalDivisors` (#156) first.** Chunk 1’s own sections and
  every chunk-2 consumer that discharges `HasPrincipalDivisors` depend on it.
- **R5 — rows #190/#191: add the two `_of_charZero` wrappers, not new copies of the
  separable engines.** The engine is public and proved.
- **R6 — rows #236–#244: reuse `FundamentalIdentity`.** Land `RamificationInertiaIdentity`
  at the pin shape as a thin wrapper over the existing class; do not re-prove the
  fibre count. Budget only #241 (the Galois norm argument).
- **R7 — rows #271–#289: use mathlib’s Wronskian.** Write `ratFuncDXCoeff` once
  (#272) and route #271/#275/#278/#279 through `Polynomial.wronskian` /
  `dvd_derivative_iff` rather than the pin’s degree arithmetic.
- **R8 — the genuinely new mathematics is rows #157–#163, #204–#207 and #212–#253.**
  The first is a seven-lemma prelude; the second is four pin-`private` normal-form
  lemmas; the third is the `dX`/derivative/atom/Galois cone. Everything else is an
  import or a one-to-three-line assembly.
- **R9 — do not pull in `P1DifferentialCoeffUnitFinite`.** It is row #290 (pin line
  6745), past the boundary; the chunk consumes `P1DifferentialCoeffRegularFinite`
  (#79, `P1ResidueCore.lean:437`).

## 15. API drift (v4.34.0) — what the worker must change

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `Ideal.inertiaDeg'` (rows #167/#176 and the fibre engine) | deprecated → `Ideal.inertiaDeg` (`RingTheory/RamificationInertia/Inertia.lean:44`); `inertiaDeg'_algebraMap` deprecated → `Ideal.inertiaDeg_eq_of_isMaximal` | `Defs/PlaceDictionary.lean` and `WeilExchange/FiberOverCount.lean` deliberately keep the primed pin text under `set_option linter.deprecated false`; do the same in the new module (rows #167/#176 are substitutes, so no new text) |
| `Ideal.ramificationIdx'` | **not** deprecated in v4.34; the new `Ideal.ramificationIdx` (`RingTheory/RamificationInertia/Ramification.lean:52`) exists, but `Ideal.ramificationIdx_spec` is itself deprecated in favour of `Ideal.ramificationIdx'_spec` (probe D) | keep the pin’s primed text; do not migrate this chunk |
| `PerfectField K` from `[CharZero K]` | `PerfectField.ofCharZero` is an instance | row #187’s proof transcribes; no `haveI` needed (probe H) |
| `Polynomial.multiplicity` / `Polynomial.emultiplicity` | **do not exist** (probe M errors on `Polynomial.multiplicity`); only root `multiplicity`/`emultiplicity`, plus `Polynomial.rootMultiplicity_eq_multiplicity` | no change: this chunk uses `Polynomial.Separable` and derivatives, not multiplicity |
| `Polynomial.wronskian` sign | mathlib’s is `a * b' - a' * b`; the pin’s expression is its negative | rewrite through `-Polynomial.wronskian` (probe H) |
| `if_pos`/`if_neg`, `dif_pos`, `Set.mem_setOf_eq`, `Polynomial.degree_sub_lt` | the drift table’s renames (3.2a/3.2b) | not used anywhere in rows #145–#289; no edit |
| `Ideal.inertiaDeg`/`ramificationIdx` (unprimed) | require `q.IsPrime` and the scalar-tower instances (see the `_def` lemmas) | only relevant if a future bridge migrates off the primed names |

## 16. Recorded negatives

Confirmed against mathlib `v4.34.0` and the port; phrased so the search is not repeated.

1. **No `ag9b15u` / `MilneAvAg9bRd15UnitNormalFormLaurentSeed` anywhere under
   `FLTForHuman/`.** Rows #204–#207 are new; they are pin-`private` and stay `private`.
2. **No `HasPrincipalDivisors K (RatFunc K)` instance in the port.** Row #156 is the
   only source; chunk 1 assumes it as a variable. Do not go looking for a base-case
   instance elsewhere.
3. **No port `KaehlerRankOne`, `RamificationInertiaIdentity`, `principalDivisorOf`,
   `CanonicalLocalResidueKDifferentialCoordIndep`, `ratFuncDXCoeff`, `dX`,
   `hasPrincipalDivisors_of_isGalois`, `degree_eq_zero_of_isGalois`, or
   `surjective_algebraMap_residueField_placeInfty`.** These are the chunk’s new
   vocabulary/statements.
4. **No port `Place.ord_prod` and no port `sum_smul_apply_eq_ord_prod`.** Row #239 is
   pin-`private`; the generic product law is new.
5. **No mathlib `Polynomial.multiplicity` / `Polynomial.emultiplicity`** (and no
   `Polynomial.rootMultiplicity` route to Wronskians). `Polynomial.rootMultiplicity`,
   `pow_rootMultiplicity_dvd`, `le_rootMultiplicity_iff`,
   `rootMultiplicity_eq_multiplicity`, `Polynomial.divByMonic`,
   `Polynomial.divByMonic_eq_zero_iff` and `Polynomial.X_sub_C` all exist (probe M)
   but are **off this chunk’s path** — they belong to 3.2a’s `placeOfPoint` block.
6. **No mathlib statement of `placeInfty.ord = -intDegree` or
   `placeInfty.ord (X ^ n) = -n`.** The route is the port’s `ord_placeInfty` /
   `ord_placeInfty_X` plus `Place.ord_zpow`; mathlib supplies only
   `RatFunc.{intDegree*, inftyValuation*}`.
7. **No mathlib `RamificationInertiaIdentity` / `KaehlerRankOne` / `principalDivisorOf`.**
   The nearest existing objects are the port’s `FundamentalIdentity`,
   `SumRamificationInertia` and `IsCurveOver.kaehler_free_rank_one` (Corrections 4–5).
8. **No mathlib rational-function Wronskian or `ratFuncDXCoeff`.** The route is
   `Polynomial.wronskian` + `RatFunc.{num, denom, num_div_denom}`.
9. **`P1DifferentialCoeffUnitFinite` is row #290, not chunk 2.** The pin defines it
   at line 6745; the first row past the boundary is #290. The chunk’s name is
   `P1DifferentialCoeffRegularFinite`.
10. **The partial-fraction identity is off this chunk.** 
    `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`
    (`Mathlib/Algebra/Polynomial/PartialFractions.lean`, probe M) serves rows
    #102–#106 of chunk 1, not rows #145–#289.
11. **`Ideal.ramificationIdx_spec` is deprecated toward the primed name** (probe D);
    the unprimed API is present but half-migrated in v4.34.

## 17. What this changes for `WORKORDER-P3-2c-p1core-2.md`

**Scope / measurement.**

- The chunk is **145 rows**, **72 SUBSTITUTE / 67 PROOF-INGREDIENT / 6 BESPOKE**.
- The brief’s `P1DifferentialCoeffUnitFinite` is out of scope (row #290); the name here
  is `P1DifferentialCoeffRegularFinite`.
- The brief’s `ag9b*` rows are the four pin-`private` `ag9b15u_*` rows #204–#207, with
  no port counterpart.

**Discharged proofs (mark import-discharged; the statements still land).**

- rows #145–#155 — import `Defs/P1Dictionary` + `PrincipalDivisors/RatFuncDegree`;
- rows #164–#176 — import `Defs/PlaceDictionary` (promote #164, or keep the consumer
  in that module);
- rows #177–#186, #189, #251–#253 — import `Canonical/HasCanonicalDivisor`;
- rows #192–#196, #197–#200, #201–#202, #208–#211, #254–#270 — import
  `Defs/CanonicalLocalResidueInstanceV2` (the `higherPoleCorrection` block is the
  no-prime public name);
- rows #220 — import `Defs/CanonicalDivisor`; row #237 — import `Genus/Index`.

**New work, budgeted.**

- rows #156 (the ℙ¹ `HasPrincipalDivisors` instance — land first);
- rows #157–#163 (the differential-coefficient prelude);
- rows #187/#188/#190/#191 (the char-0 closures; #190/#191 wrap the port’s separable
  engines);
- rows #203–#207 (the `gate` wrapper and the four `ag9b15u` normal-form lemmas);
- rows #212–#232 (the `dX`/derivative/atom cone);
- rows #233–#245 (the `KaehlerRankOne` and Galois wrappers, reusing
  `FundamentalIdentity`);
- rows #246–#250 (coordinate independence);
- rows #271–#289 (the Wronskian/`ratFuncDXCoeff` cone and the capstone).

**Imports the worker may use.** The port modules above plus, on the mathlib side,
`Mathlib.RingTheory.Derivation.Basic`, `Mathlib.RingTheory.Kaehler.Basic`,
`Mathlib.RingTheory.Kaehler.Polynomial`, `Mathlib.FieldTheory.Separable`
(`Polynomial.Separable`), `Mathlib.RingTheory.Coprime.Basic`,
`Mathlib.RingTheory.Polynomial.Wronskian`, `Mathlib.Algebra.Polynomial.Div`,
`Mathlib.Algebra.Polynomial.Derivative`, `Mathlib.FieldTheory.Perfect`,
`Mathlib.RingTheory.Norm.Transitivity`, `Mathlib.FieldTheory.Galois.Basic`,
`Mathlib.LinearAlgebra.FiniteDimensional.Basic`,
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`,
`Mathlib.Algebra.BigOperators.Group.Finset.Basic`. The
`Mathlib.RingTheory.RamificationInertia.*` imports are needed only for the unprimed
bridges; the substitutes keep the primed statements.

**Checker wiring.** Already done per the order: the master `S_` file and its wrapper are
in `SOURCES` and `Defs/P1ResidueCore.lean` is in `PORT_FILES`. Verify the checker rises
and stays `0 mismatched / 0 missing`; rows #156, #204–#207, #212, #233, #236, #242,
#246 and #272 are the new public surface to reconcile.

## 18. Appendix — module map for the named constants

| name | module |
|---|---|
| `Polynomial.wronskian`, `wronskianBilin`, `degree_wronskian_lt_add`, `natDegree_wronskian_lt_add`, `wronskian_eq_of_sum_zero`, `IsCoprime.wronskian_eq_zero_iff` | `Mathlib/RingTheory/Polynomial/Wronskian.lean` |
| `Polynomial.Separable`, `separable_def`, `separable_def'` | `Mathlib/FieldTheory/Separable.lean` |
| `IsCoprime.isUnit_of_dvd'` | `Mathlib/RingTheory/Coprime/Basic.lean` |
| `Polynomial.dvd_derivative_iff`, `degree_derivative_lt`, `natDegree_lt_natDegree` | `Mathlib/Algebra/Polynomial/Derivative.lean`, `…/Degree/Domain.lean`, `…/Degree/Operations.lean` |
| `Polynomial.degree_le_of_dvd`, `eq_zero_of_dvd_of_degree_lt` | `Mathlib/Algebra/Polynomial/Degree/Domain.lean` |
| `Polynomial.{divByMonic, divByMonic_eq_zero_iff, rootMultiplicity, rootMultiplicity_eq_multiplicity, pow_rootMultiplicity_dvd, le_rootMultiplicity_iff}` (off-path) | `Mathlib/Algebra/Polynomial/Div.lean` |
| `Derivation.{leibniz_of_mul_eq_one, leibniz_div, leibniz_inv, map_algebraMap}` | `Mathlib/RingTheory/Derivation/Basic.lean` |
| `KaehlerDifferential.span_range_derivation`, `KaehlerDifferential.{D, finite}` | `Mathlib/RingTheory/Kaehler/Basic.lean` |
| `Derivation.map_aeval` | `Mathlib/RingTheory/Derivation/Basic.lean` |
| `KaehlerDifferential.map_surjective` | `Mathlib/RingTheory/Kaehler/Polynomial.lean` |
| `PerfectField`, `PerfectField.ofCharZero` (instance, `:306`), `Algebra.IsAlgebraic.isSeparable_of_perfectField` (instance, `:338`) | `Mathlib/FieldTheory/Perfect.lean` |
| `Ideal.inertiaDeg`, `inertiaDeg_def`, `inertiaDeg'_algebraMap` (deprecated) | `Mathlib/RingTheory/RamificationInertia/Inertia.lean`; legacy `Mathlib/NumberTheory/RamificationInertia/Inertia.lean` |
| `Ideal.ramificationIdx`, `ramificationIdx_def`, `ramificationIdx_spec` (deprecated) | `Mathlib/RingTheory/RamificationInertia/Ramification.lean` |
| `Finset.sum_fiberwise_of_maps_to`, `Finset.{sum_const, card_univ, sum_filter, mul_sum}` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` |
| `Algebra.norm_eq_prod_automorphisms`, `Algebra.norm_ne_zero_iff` | `Mathlib/RingTheory/Norm/Transitivity.lean`, `…/Norm/Basic.lean` |
| `IsGalois.card_aut_eq_finrank` | `Mathlib/FieldTheory/Galois/Basic.lean` |
| `finrank_eq_one_iff_of_nonzero'` | `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean` |
| `IsLocalRing.{residue_surjective, residue_eq_zero_iff, mem_maximalIdeal, ker_residue, ResidueField.algebraMap_eq}` | `Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean` |
| `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` (off-path) | `Mathlib/Algebra/Polynomial/PartialFractions.lean` |
| `RatFunc.{num, denom, num_div_denom, isCoprime_num_denom, num_ne_zero, denom_ne_zero, intDegree, intDegree_div, intDegree_polynomial, X_ne_zero, algebraMap_ne_zero}` | `Mathlib/FieldTheory/RatFunc/*` |

Port declarations referred to above:

- `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean` — `OrdDifferentialWellDefined`
  (120), `p1PlaceInfty` (278), `p1PlaceInfty_toValuationSubring` (281),
  `P1DifferentialCoeffRegularFinite` (437), `p1PrincipalPartAtom` (454),
  `ord_placeInfty_algebraMap'` (588), `gate_localResidueData_uniformizer_inv` (811);
- `…/Defs/P1Dictionary.lean` — `isRational_of_deg_eq_one` (175),
  `ord_ofHeightOneSpectrum_eq_zero_of_notMem` (330), `ord_placeInfty` (342),
  `ord_placeInfty_algebraMap` (347), `single_add_single_apply_eq_ord` (357),
  `degree_single_add_single` (391), `principalDivisor` (400),
  `principalDivisor_apply` (405), `degree_principalDivisor` (412);
- `…/PrincipalDivisors/RatFuncDegree.lean` — `ord_ofHeightOneSpectrum_of_span` (176),
  the private general `single_add_single_apply_eq_ord` (303) and
  `degree_single_add_single` (347), `degree_eq_zero_of_forall_eq_ord_algebraMap` (360),
  `degree_eq_zero_of_forall_eq_ord` (401);
- `…/Defs/PlaceDictionary.lean` — `eq_ord_of_addHom_of_nonneg_iff` (44, private),
  `neg_log_valuation_fiberCenter_eq_ord` (127), `le_ord_iff_mem_pow_fiberCenter` (169),
  `ramificationIndex_eq_ramificationIdx_fiberCenter` (192),
  `toValuationSubringOfRestrictEq` (228), `residueOfCenter` (240),
  `residueOfCenter_apply` (245), `ker_residueOfCenter` (249),
  `surjective_residueOfCenter` (255), `residueFieldEquivQuotientCenter` (324),
  `placeCongrEquiv` (338), `restrictResidueFieldEquiv` (351),
  `inertiaDeg_eq_inertiaDeg_fiberCenter` (363);
- `…/Canonical/HasCanonicalDivisor.lean` — `uniformizerSubring'''` (188) through
  `subsingleton_polynomialKaehler_of_isSeparable_of_finite` (275) for rows #177–#186,
  `ValSubringKaehlerFinite` (291),
  `valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_isSeparable` (296),
  `finite_kaehler_of_essFiniteType` (314), `ValSubringEssFiniteType` (331),
  `valSubringKaehlerFinite_of_essFiniteType` (341),
  `isSeparable_residueField_of_perfectField_of_finiteResidue` (1019, private),
  `isSeparable_residueField_forall_of_perfectField` (1030),
  `valSubringKaehlerSpanTop_of_kaehlerFinite_of_isSeparable` (1042);
- `…/Defs/CanonicalLocalResidueInstanceV2.lean` — `exists_mem_poleSubmodule` (317),
  `uniformizer_pow_inv_mem_poleSubmodule_self` (352),
  `higherPoleMonomial_sum_mem_poleSubmodule` (356),
  `higherPoleMonomial_coeff_eq_zero_of_mem` (364),
  `linearIndependent_higherPoleMonomial_mkQ` (394), `higherPoleCorrectionAux` (404),
  `higherPoleCorrection` (411), `higherPoleCorrection_apply_of_mem` (414),
  `higherPoleCorrection_uniformizer_pow_inv` (420),
  `canonicalLocalResidueDataKOfExtend` (438),
  `CanonicalLocalResidueDataK.res_algebraMap_mul_uniformizer_pow_inv` (340),
  `Mp72a103T2.mp72a103_t2_evalDepth_of_uniformizer_mul` (978),
  `mp72a103_t2_lift_eq_zero_of_depth_one` (1003),
  `mp72a103_t2_taylor_coeff_eq_zero_of_depth` (1011), `aCoeff` (1225),
  `aCoeff_zero` (1268), `aCoeff_add` (1280), `aCoeff_smul` (1330),
  `aCoeff_shift` (1389), `aCoeff_shift_pow` (1459), `aCoeff_one_eq_zero` (1476),
  `clearPow_mem` (1519), `clearedHat` (1529), `resStar` (1534),
  `aCoeff_clearedHat_of_le` (1538), `resStar_add` (1553), `resStar_smul` (1569),
  `resStarₗ` (1584), `resStar_simplePole` (1590), `resStar_of_mem` (1610),
  `resStar_higherPoleMonomial` (1618), `canonicalLocalResidueDataKStar` (1639);
- `…/Defs/CanonicalDivisor.lean` — `Place.uniformizer_ne_zero` (53);
- `…/Defs/IsCurveOver.lean` — `IsCurveOver` (23) with fields `finiteResidue` (25) and
  `kaehler_free_rank_one` (27);
- `…/Defs/Divisor.lean` — `HasPrincipalDivisors` (63);
- `…/Defs/PlaceEvaluation.lean` — `Place.IsRational` (36);
- `…/Genus/Index.lean` — `Divisor.degree_eq_sum_support` (45);
- `…/Genus/Stichtenoth.lean` — `RationalFunctionField.ord_placeInfty_X` (780);
- `…/Defs/PushPull.lean` — `Place.ord_restrict` (322),
  `Place.deg_restrict_mul_inertiaDeg` (460), `FundamentalIdentity` (632),
  `SumRamificationInertia` (677);
- `…/WeilExchange/FiberOverCount.lean` —
  `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` (33);
- `…/WeilExchange/GaloisRamification.lean` — `ramificationIndex_smul` (106),
  `inertiaDeg_smul` (153);
- `…/PrincipalDivisors/Transcendence.lean` —
  `finite_setOf_ord_ne_zero_of_finiteDimensional` (p3-2b row #94).

## 19. State at audit time

`FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean` is **848 ln** and contains chunk 1
only (header: declarations #0–#144, pin lines 295–3387); none of the chunk-2 names
(`dX`, `ratFuncDXCoeff`, `KaehlerRankOne`, `RamificationInertiaIdentity`,
`principalDivisorOf`, `instHasPrincipalDivisors`, `ag9b15u`) is present at audit time.
The classification above is therefore against the phase-3.1/3.2a/3.2b tree plus the
engine modules, and the outstanding items to re-check after the chunk-2 worker lands
are: the checker delta on the new public surface (#156, #204–#207, #212, #233, #236,
#242, #246, #272), the promotion decision for `PlaceDictionary.eq_ord_of_addHom_of_nonneg_iff`
(#164), and whether the worker reuses `FundamentalIdentity` (#236–#244) or re-proves
the fibre count — the latter would be the one avoidable duplication in the chunk.
