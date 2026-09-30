# Mathlib-first substitution audit — the phase-3.2e ℙ¹ residue core, chunk 4 (P3.2e)

**Method:** `lean/porting-playbook.md` §2.2 (audit the route, mathlib first), after the
phase-1/2/3.1/3.2a/3.2b/3.2c/3.2d/3.2d′ templates [`AUDIT-mathlib.md`](AUDIT-mathlib.md),
[`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md),
[`AUDIT-mathlib-p3-1.md`](AUDIT-mathlib-p3-1.md),
[`AUDIT-mathlib-p3-2a.md`](AUDIT-mathlib-p3-2a.md),
[`AUDIT-mathlib-p3-2b.md`](AUDIT-mathlib-p3-2b.md),
[`AUDIT-mathlib-p3-2c.md`](AUDIT-mathlib-p3-2c.md),
[`AUDIT-mathlib-p3-2d.md`](AUDIT-mathlib-p3-2d.md) and
[`AUDIT-mathlib-p3-2dprime.md`](AUDIT-mathlib-p3-2dprime.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Pre-port advice:
[`tools/deps/build/p32_engine_advise.log`](../../../tools/deps/build/p32_engine_advise.log)
§1 (the shared ℙ¹ engine). Work order:
[`WORKORDER-P3-2e-p1core-4.md`](WORKORDER-P3-2e-p1core-4.md). Generated append draft:
[`tools/deps/build/p32e_append.lean`](../../../tools/deps/build/p32e_append.lean) (2,460 ln,
produced by `tools/deps/build/gen_p32e.py`).

Source, the single master ℙ¹ `S_` file, pin lines 9,500–13,173 (the end of the file; 147
declarations, inventory rows #435–#579 = 145 rows), plus its one-declaration `Theorems/`
wrapper:

- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean#L9500-L13173)
  (the final chunk; the whole file is 13,173 ln / 580 declarations),
- [`Theorems/Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean)
  (the interface copy of the headline `solution`, published as
  `AlgebraicCurve.RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero`).

**Class convention** (unchanged from phases 1–3.2d′). SUBSTITUTE = the port can import an
existing declaration instead of proving the row: an already-landed port lemma or a
mathlib constant whose *type* is the pin's, or a pin `def`/`abbrev`/instance whose body is
`rfl`-equal to a mathlib/port term. A statement that differs from the port copy only by
binder spelling or by a `_root_.`-qualified pin header counts SUBSTITUTE with that
difference recorded. PROOF-INGREDIENT = the statement is bespoke (it mentions pin
vocabulary) but the proof is a short assembly of named mathlib/port lemmas. BESPOKE = a
definition/structure/class/`Prop` introducing new vocabulary, or an instance with no
mathlib/port counterpart; these are the recorded negatives and the real work.

**Scratch evidence:** `lean/ScratchAuditP32e.lean` (gitignored, 232 ln), compiled from
`lean/` with

```bash
timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP32e.lean
```

**final run clean, exit 0, 4.2 s wall** (120 resolving `#check`s, no errors, no warnings).
The probe ledger:

- **A** — the port substitutes and their exact namespaces: `Place.dCoordGenerates_of_valSubringKaehlerSpanTop`,
  `D_pow_succ_inv`, `Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule`
  / `_of_surj`, `gate_canonicalLocalResidueDataK_uniformizer_inv`, the `p0n22_cpf_*`
  representatives, the `res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap`
  headline; and the vocabulary the new rows consume (`RationalFunctionField.{placeInfty,p1PlaceInfty,finitePlace}`,
  `dX`, `p1PrincipalPartAtom`, `P1PlaceInftySimplePoleResidueEulerValue{,Monomial}`,
  `p1PlaceInftySimplePoleResidueEulerValue_of_monomial`, `p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial`,
  `p1MOneAtom_mul_differentialCoeff_mem_simplePole_{finitePlace,placeInfty}`,
  `aeval_root_eq_sum_range`, `trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt`,
  `finitePlaceResidueFieldAlgEquivAdjoinRoot`, `trace_finitePlace_residueField_eq_trace_adjoinRoot`,
  `P1FinitePlaceSimplePoleResidueAdjoinRootValue`, `p1DifferentialCoeffRegularFinite_dX`,
  `ordDifferentialWellDefined_ratFunc_of_perfectField`, `ordDifferential_placeInfty_D_ratFuncX`,
  `ord_placeInfty_X_inv`, `differentialCoeff_placeInfty_D_X_eq`, `X_pow_mul_differentialCoeff_D_X_eq_neg`,
  `surjective_algebraMap_residueField_placeInfty`, `CanonicalLocalResidueKDifferentialCoordIndep`,
  `canonicalLocalResidueDataK_res_X_pow_mul_D_X_of_coordIndep`, `HasSeparatingTranscendentalCore`,
  `valSubringKaehlerFinite_of_core`, `ratFuncDXCoeff`, `p1PartialFractionSpan_eq_top`,
  `weilOfKaehlerK`, `kaehlerResidueTermKFam`, `diagonalHom`, `ResidueTheoremK`,
  `IntermediateField.finiteDimensional_of_eq`, `Place.mk_mem_maximalIdeal_iff`, and the
  generic `FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_{of_lt,self}`).
- **M** — the mathlib `#check` ledger: `geom_sum_mul` (`Algebra/Ring/GeomSum.lean:232`),
  `Derivation.{leibniz, leibniz_pow, leibniz_inv, map_algebraMap, map_one_eq_zero}`,
  `Polynomial.{natDegree_X_pow, degree_X_pow, leadingCoeff_X_pow, natDegree_lt_natDegree,
  degree_sub_lt_left, degree_sub_lt_right, eval₂_eq_sum_range', derivative}`,
  `Finsupp.{single_eq_same, single_eq_of_ne, add_apply}`,
  `Finset.{sum_insert, sum_image, sum_eq_single_of_mem, sum_pair}`,
  `finsum_eq_finsetSum_of_support_subset`,
  `IntermediateField.{lift_adjoin_simple, adjoin_map}`, `IntermediateField.AdjoinSimple.{algebraMap_gen, coe_gen}`,
  `AdjoinRoot.{minpoly_powerBasis_gen_of_monic, aeval_eq, powerBasis_dim}`,
  `RatFunc.{num_div_denom, isCoprime_num_denom, num_ne_zero, algebraMap_ne_zero, algebraMap_X}`,
  `IsAlgClosed.degree_eq_one_of_irreducible`, `Module.Finite.of_surjective`, `Algebra.linearMap`,
  `Algebra.trace_algebraMap`, `finrank_eq_one_iff_of_nonzero'`,
  `add_pow_char`, `add_pow_char_pow`, `sum_pow_char`, `neg_one_pow_char`, `frobenius_def`,
  `charP_of_injective_ringHom`, `charP_of_injective_algebraMap`,
  `CharP.{cast_eq_zero_iff, char_is_prime_or_zero, charP_to_charZero}`, `ringChar.charP`,
  `IsScalarTower.algebraMap_apply`, `IsLocalRing.{residue_eq_zero_iff, ResidueField.algebraMap_eq}`,
  `Submodule.mem_span_singleton`, `zpow_add₀`, `zpow_mul`, `zpow_sub_one₀`, `inv_pow`,
  `Nat.{exists_eq_add_of_le, le_of_dvd, mul_div_cancel_left}`.
- **L** — off-path probes: `LaurentSeries`, `HahnSeries`, `Polynomial.{divByMonic, modByMonic}`,
  `Differential.{logDeriv, logDeriv_mul}`,
  `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`.
- **H** — compile-checked prototypes: the headline's `ringChar` split (#577); the
  `finiteDimensional_top` + `HasSeparatingTranscendentalCore` assembly (#442/#446); verbatim
  transcriptions of the two new `Prop`s (#436 `P1PlaceInftySimplePoleResidueEulerValueX`,
  #448 `CanonicalLocalResidueKSimplePoleCoordIndep`); and `placeInfty K = p1PlaceInfty K` by
  `rfl` (#578).

## 1. Summary — class counts

| block (rows) | SUBSTITUTE | PROOF-INGREDIENT | BESPOKE | rows |
|---|---:|---:|---:|---:|
| simple-pole / Euler-X machinery (#435–#441) | 0 | 6 | 1 | 7 |
| separability / transcendence (#442–#448) | 0 | 5 | 2 | 7 |
| simple-pole coord-indep and ℙ¹ discharge (#449–#458) | 0 | 10 | 0 | 10 |
| `dCoordGenerates` gates and the divisor instances (#459–#467) | 1 | 7 | 1 | 9 |
| generic Kähler/differential engine (#468–#470) | 3 | 0 | 0 | 3 |
| `ratFuncDXCoeff` integrality block (#471–#479) | 0 | 9 | 0 | 9 |
| `res` engine, char-0 / coord-indep clauses (#480–#492) | 2 | 11 | 0 | 13 |
| perfect-field `DCoordGenerates` / canonical divisor (#493–#499) | 0 | 6 | 1 | 7 |
| `ag9b13t` char-`p` engine (#500) | 1 | 0 | 0 | 1 |
| `residueTheoremK_placeInfty_clause_X_pow` (#501) | 0 | 1 | 0 | 1 |
| `ag9b12c_*` / `ag9b13e_*` perfect-field Euler–Cartier (#502–#523) | 0 | 22 | 0 | 22 |
| Kähler residue functional and per-generator engine (#524–#538) | 0 | 14 | 1 | 15 |
| `residueTheoremK_ratFunc_of_subrows` / `_main` (#539–#540) | 0 | 2 | 0 | 2 |
| `p0n21_rtk_*` char-free re-route (#541–#553) | 0 | 13 | 0 | 13 |
| `p0n22_cpf_*` char-free + Cartier cone (#554–#574) | 21 | 0 | 0 | 21 |
| `p0n22_cpf_*` capstones (#575–#577) | 0 | 3 | 0 | 3 |
| ℙ¹ alias and `solution` (#578–#579) | 0 | 2 | 0 | 2 |
| **total** | **28** | **111** | **6** | **145** |

**Headline.** The final master chunk is the ℙ¹ *computation*: it instantiates the generic
`LocalResidueCalculus` engine at `F = RatFunc K` and assembles the residue theorem and the
atom-1 headline from it. 28 of the 145 inventory rows are already landed verbatim (the whole
`p0n22_cpf_*` family and the Kähler/differential engine, §3–§4 below); the genuinely new
mathematics is the perfect-field `ag9b12c_*`/`ag9b13e_*` re-route (#502–#523), the Kähler
residue functional and its per-generator engine (#524–#538), the `p0n21_rtk_*` char-free
re-route (#541–#553), and the six BESPOKE vocabulary declarations (#436, #445, #448, #467,
#499, #524). Every theorem is a named assembly; there is no new analytic input. The three
reuse wins that dominate the route are `Defs/LocalResidueCalculus.lean` (the whole shared
cone), the Euler-value chain and its carriers already in `Defs/P1ResidueCore.lean` chunks
1–3 (`P1PlaceInftySimplePoleResidueEulerValue{,Monomial}` at `:3140/:3645`,
`p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial` at `:3806`,
`p1MOneAtom_mul_differentialCoeff_mem_simplePole_{finitePlace,placeInfty}` at `:2818/:2843`),
and mathlib's `Derivation` / char-`p` Frobenius APIs plus `geom_sum_mul`.

The endgame is

$$\mathrm{Tr}_{K}\bigl(\mathrm{res}_{\infty}(X^{n}\mathrm{d}X)\bigr) = 0 \quad (n \ge 0),$$

published as `AlgebraicCurve.RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero`;
its proof is #578 (`rfl`), `X_pow_mul_differentialCoeff_D_X_eq_neg`, the
`LocalResidueCalculus` headline and #519.

## 2. Corrections to the brief and the inventory

**Correction 1 — the pin range has 147 declarations, not 145.** The inventory
[`tools/deps/build/p32_master_inventory.txt`](../../../tools/deps/build/p32_master_inventory.txt)
rows #435–#579 are 145 rows, but pin lines 9,500–13,173 contain **two more** `scoped
instance`s that the inventory tool missed (its regex does not see `instance (priority :=
low)`):

| pin line | missing declaration | role |
|---:|---|---|
| 10,166–10,168 | `AlgebraicCurve.RationalFunctionField.instDCoordGenerates` (`[CharZero K]`) | body `ModularCurve.gate_dCoordGenerates_of_ratFunc_sat ⟨AlgEquiv.refl⟩ v`, i.e. row #462 |
| 10,880–10,887 | `AlgebraicCurve.RationalFunctionField.instDCoordGeneratesPerfectField` | body `exists_ne_zero_smul_dX_of_uniformizer K v`, i.e. row #493 |

Both must land (they are the `CharZero`/`PerfectField` scoped instances the rest of the
chunk assumes); the 145-row count is the inventory's, not the pin's surface. The same
omission pattern is already recorded in the header of
[`Canonical/HasCanonicalDivisor.lean`](../../FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean).

**Correction 2 — the generated append re-declares #459 and will not compile.**
`tools/deps/build/gen_p32e.py` builds its `omit` list as
`[468,469,470,480,481,500] + range(554,575)` (27 rows) and therefore keeps row #459
`Place.dCoordGenerates_of_valSubringKaehlerSpanTop`. But that exact declaration already
exists at
[`Canonical/HasCanonicalDivisor.lean:987`](../../FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean)
(full name `AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop`, probe A),
and `P1ResidueCore.lean` imports that module. Re-declaring it is a hard
"already declared" error; **row #459 must be added to the omit list** (making it 28 rows).
With that fix the new-declaration count is 147 − 28 = 119 (117 inventory rows + the 2
missed instances).

**Correction 3 — the master's `p0n22_cpf_*` are `RatFunc K`-specialisations of the generic
port copies; do not "fix" the mismatch by re-declaring.** The port homes the 3.2d′ generic
versions (`{K F} [Algebra K F]`, `LocalResidueCalculus.lean:397–1182`), while the master
`S_` file instantiates them at `F = RatFunc K` (pin 12,287 ff.). The port's
`p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj`
(`LocalResidueCalculus.lean:1182`) even carries an extra `hint` hypothesis the master's
`RatFunc K` copy discharges with `ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField`
(#519). This is safe only because the checker (`lean/spec/check_flt_statements.py:2509–2536`)
keys port declarations against *all* `SOURCES` candidates by last name and accepts a match
against any: the generic 3.2d′ `S_` file is registered (`:1638–1639`), so the generic port
copy verifies against it. Because the port *cannot* declare a second global
`AlgebraicCurve.p0n22_cpf_*`, the master's specialised copies are never landed — that is
the intended design, not a gap.

**Correction 4 — the 3.2d′ audit's "no port copy" rows are now substitutes for 3.2e.**
`AUDIT-mathlib-p3-2dprime.md` classified `D_pow_succ_inv`, `differentialCoeff_add''`,
`differentialCoeff_D_uniformizer_pow_inv`, `res_differentialCoeff_D_of_mem_poleSubmodule`,
`res_differentialCoeff_D_of_surj`, `ag9b13t_…` and the `p0n22_cpf_*` cone as
PROOF-INGREDIENT because no port copy existed *at that audit*. The 3.2d′ port has since
landed them all in `Defs/LocalResidueCalculus.lean`, so for set 3.2e they are SUBSTITUTE
(rows #468–#470, #480–#481, #500, #554–#574). Cross-reference that audit for their internal
structure; do not re-audit.

**Correction 5 — #448 is not the ported coord-independence predicate.** The port's
`CanonicalLocalResidueKDifferentialCoordIndep` (`P1ResidueCore.lean:1929`, pin row #246)
requires the residue of `D π' · (π')^{-(n+1)}` to vanish for all `n ≥ 1`; chunk 4's
`CanonicalLocalResidueKSimplePoleCoordIndep` (#448) is the *simple-pole* statement, value
`1` for `n = 0`. They are different `Prop`s (probe H, `Row448`), and the chunk derives #448
from `res_differentialCoeff_D_mul_inv_of_integral` (#483), not from the ported predicate.

**Correction 6 — the pin's `finsum` spelling is the preferred one.** The preliminary note
said the pin's `finsum_eq_finsetSum_of_support_subset` was the drifted spelling; probe M
shows the opposite: `finsum_eq_finset_sum_of_support_subset` is the *deprecated* alias
(`Mathlib/Algebra/BigOperators/Finprod.lean:381`), and the pin's camelCase name is
canonical in `v4.34.0`. No worker action.

## 3. The simple-pole / Euler-X machinery (rows #435–#441)

The Euler-value chain lives in `P1ResidueCore.lean` chunks 1–3; this block only adds the
`X`-specific carrier, the monic-ratio reduction and two thin consumers.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 435 | `residue_placeInfty_X_pow_natDegree_div_monic_eq_one` (9,500) | PROOF-INGREDIENT | `Polynomial.natDegree_lt_natDegree` (`Algebra/Polynomial/Degree/Operations.lean:73`), `Place.mk_mem_maximalIdeal_iff` (`Genus/Index.lean:88`), `IsLocalRing.residue_eq_zero_iff`, `map_sub`, `Subtype.ext`; port helper `degree_X_pow_natDegree_sub_lt_of_monic` (row #434) | probe A/M; no port copy |
| 436 | `P1PlaceInftySimplePoleResidueEulerValueX` (9,550) | **BESPOKE** | new `def : Prop` over `p1PrincipalPartAtom`, `simplePoleSubmodule`, `dX`, `differentialCoeff` | probe H (`Row436`) lands the statement verbatim; grep 0 in `FLTForHuman/` |
| 437 | `p1MonomialAtom_eq_monicRatio_mul` (9,565) | PROOF-INGREDIENT | `map_mul`, `pow_succ`, `Nat.sub_add_cancel`, `map_one`, `one_div`, `field_simp` | no port copy; 18 pin ln |
| 438 | `p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty` (9,583) | PROOF-INGREDIENT | `p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty` (`P1ResidueCore.lean:2843`), `irreducible_X`, `degree_X` | probe A; one line |
| 439 | `simplePoleResidueAux_placeInfty_monomial_eq_X` (9,590) | PROOF-INGREDIENT | `simplePoleResidueAux_mul_of_mem` (`P1ResidueCore.lean:3235`, **private**), `mul_mem_simplePoleSubmodule_of_mem` (`:3243`, **private**), row #435, `Subtype.ext` | same-module private access (chunk 4 appends to `P1ResidueCore`), so no promotion needed |
| 440 | `p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X` (9,613) | PROOF-INGREDIENT | ported carrier `P1PlaceInftySimplePoleResidueEulerValueMonomial` (`P1ResidueCore.lean:3645`), row #439 | probe A |
| 441 | `p1PrincipalPartMOneSimplePoleCancel_of_inftyX` (9,630) | PROOF-INGREDIENT | `p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial` (`:3806`), row #440, `ordDifferential_placeInfty_D_ratFuncX` (`:944`) | probe A; one line |

## 4. Separability and transcendence (rows #442–#448)

The `IntermediateField` leaves are new *names*, but `finiteDimensional_of_eq` and
`HasSeparatingTranscendentalCore` are already ported, so #446 is glue.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 442 | `finiteDimensional_top` (9,677) | PROOF-INGREDIENT | `Module.Finite.of_surjective`, `Algebra.linearMap`, `IntermediateField.mem_top` | probe H; mathlib/port grep 0, so the pin's `IntermediateField.finiteDimensional_top` is new |
| 443 | `adjoin_simple_gen_eq_top` (9,681) | PROOF-INGREDIENT | `IntermediateField.{lift_injective, lift_adjoin_simple, lift_top}`, `AdjoinSimple.coe_gen` | probe M |
| 444 | `transcendental_gen` (9,686) | PROOF-INGREDIENT | `AdjoinSimple.algebraMap_gen`, `transcendental_algebraMap_iff` | probe M |
| 445 | `IsPurelyTranscendentalSimple` (9,703) | **BESPOKE** | new `def : Prop` (`∃ t, Transcendental K t ∧ K⟮t⟯ = ⊤`) | no port counterpart |
| 446 | `hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple` (9,708) | PROOF-INGREDIENT | row #442, `IntermediateField.finiteDimensional_of_eq` (`P1ResidueCore.lean:3865`), `HasSeparatingTranscendentalCore` (`:3907`) | probe H compiles the body |
| 447 | `isPurelyTranscendentalSimple_adjoin_simple` (9,723) | PROOF-INGREDIENT | rows #443/#444/#445 | 84 pin ln, `⟨AdjoinSimple.gen K α, ⋯, ⋯⟩` |
| 448 | `CanonicalLocalResidueKSimplePoleCoordIndep` (9,807) | **BESPOKE** | new `def : Prop`; **not** the ported `CanonicalLocalResidueKDifferentialCoordIndep` (`:1929`) | probe H (`Row448`); Correction 5 |

## 5. Simple-pole coordinate independence and the ℙ¹ discharge (rows #449–#458)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 449 | `p1XAtom_mul_differentialCoeff_dX_eq_neg` (9,827) | PROOF-INGREDIENT | `differentialCoeff_placeInfty_D_X_eq` (`P1ResidueCore.lean:923`), `RatFunc.algebraMap_X`, `inv_inv`, `field_simp` | probe M |
| 450 | `trace_placeInfty_residueField_one` (9,850) | PROOF-INGREDIENT | `Algebra.trace_algebraMap`, `deg_placeInfty` (`P1Dictionary.lean:292`), `one_smul` | probe M |
| 451 | `simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one` (9,856) | PROOF-INGREDIENT | `localResidueData_res_eq_simplePoleResidueAux` (`CanonicalLocalResidueInstanceV2.lean:297`), `canonicalLocalResidueDataKOfExtend` (`:438`), row #448, `ord_placeInfty_X_inv` (`:892`) | no port copy |
| 452 | `p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep` (9,868) | PROOF-INGREDIENT | rows #451/#450 | 10 pin ln |
| 453 | `p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep` (9,884) | PROOF-INGREDIENT | row #441 | one line |
| 454 | `adjoin_simple_map_algHom'` (9,930) | PROOF-INGREDIENT | `IntermediateField.adjoin_map`, `Set.image_singleton` | probe M |
| 455 | `adjoin_simple_eq_top_of_algEquiv` (9,934) | PROOF-INGREDIENT | row #454, `AlgHom.fieldRange_eq_map`, `AlgEquiv.fieldRange_eq_top` | probe M |
| 456 | `IsPurelyTranscendentalSimple.congr` (9,953) | PROOF-INGREDIENT | row #455, `isAlgebraic_algHom_iff` | probe M |
| 457 | `isPurelyTranscendentalSimple_ratFunc` (9,969) | PROOF-INGREDIENT | row #447, `RatFunc.transcendental_X`, `RatFunc.algEquivOfTranscendental` | no port copy |
| 458 | `isPurelyTranscendentalSimple_of_ratFuncAlgEquiv` (9,982) | PROOF-INGREDIENT | rows #456/#457 | one line |

## 6. `dCoordGenerates` gates and the canonical-divisor instances (rows #459–#467)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 459 | `Place.dCoordGenerates_of_valSubringKaehlerSpanTop` (10,055) | **SUBSTITUTE** | `Place.dCoordGenerates_of_valSubringKaehlerSpanTop` (`Canonical/HasCanonicalDivisor.lean:987`) | probe A; **collision — must be omitted from the append** (Correction 2) |
| 460 | `Place.dCoordGenerates_of_valSubringKaehlerFinite_of_charZero` (10,079) | PROOF-INGREDIENT | `valSubringKaehlerSpanTop_of_kaehlerFinite_of_charZero` (`P1ResidueCore.lean:1088`), row #459 | one line |
| 461 | `Place.dCoordGenerates_of_isPurelyTranscendentalSimple` (10,095) | PROOF-INGREDIENT | `valSubringKaehlerFinite_of_core` (`P1ResidueCore.lean:3922`), row #446 | probe A |
| 462 | `gate_dCoordGenerates_of_ratFunc_sat` (10,124) | PROOF-INGREDIENT | rows #461/#458 | consumed by the missed instance at pin 10,166 |
| 463 | `exists_smul_dX_eq` (10,246) | PROOF-INGREDIENT | `span_dX_eq_top` (`P1ResidueCore.lean:1285`), `Submodule.mem_span_singleton` | probe M |
| 464 | `ordDifferential_dX_of_ne_placeInfty` (10,255) | PROOF-INGREDIENT | `p1DifferentialCoeffUnitFinite_dX` (`:2766`), `Place.ordDifferential` | one line |
| 465 | `ordDifferential_dX_placeInfty` (10,260) | PROOF-INGREDIENT | `ordDifferential_placeInfty_D_ratFuncX` (`:944`) | one line |
| 466 | `exists_divisor_smul_dX` (10,264) | PROOF-INGREDIENT | `HasPrincipalDivisors.exists_divisor`, `Finsupp.{add_apply, single_eq_same, single_eq_of_ne}`, `Divisor.degree_single`, `deg_placeInfty`, `Place.ordDifferential_smul` | probe M |
| 467 | `instHasCanonicalDivisorRatFunc` (10,288) | **BESPOKE** | new `scoped instance`; the port has **no** RatFunc `HasCanonicalDivisor` instance (grep `instHasCanonicalDivisor` = 0) and takes it as a section variable throughout `P1ResidueCore` (`:348/:438/:455/:1512/:2370/:2442/:3541/:3801`) | body: `exists_smul_dX_eq` + `exists_divisor_smul_dX` |

## 7. The generic Kähler/differential engine (rows #468–#470) — all SUBSTITUTE

Byte-for-byte the 3.2d′ engine, now homed generically. Span diffs of pin 10,364–10,401
against `LocalResidueCalculus.lean:96–126` are identical (only the `p2m_*` scaffolding and
the `end`/`namespace` lines differ).

| row | pin decl (line) | class | port name (module:line) | evidence |
|---:|---|---|---|---|
| 468 | `D_pow_succ_inv` (10,364) | SUBSTITUTE | `D_pow_succ_inv` (`Defs/LocalResidueCalculus.lean:96`, public) | span-diff identical; probe A |
| 469 | `Place.differentialCoeff_add''` (10,379) | SUBSTITUTE | `_root_.AlgebraicCurve.Place.differentialCoeff_add''` (`:109`, **private**) | span-diff identical; private in the port, so not importable by name — but nothing in `P1ResidueCore` chunk 4 consumes it (row #506 is its own copy) |
| 470 | `Place.differentialCoeff_D_uniformizer_pow_inv` (10,385) | SUBSTITUTE | `_root_.AlgebraicCurve.Place.differentialCoeff_D_uniformizer_pow_inv` (`:114`, **private**) | span-diff identical; consumed only inside `LocalResidueCalculus` |

## 8. The `ratFuncDXCoeff` integrality block (rows #471–#479)

All new transcriptions; the Wronskian and the `dX`-coefficient API are already ported.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 471 | `ratFuncDXCoeff_eq_of_D_eq_smul_dX` (10,403) | PROOF-INGREDIENT | `D_eq_ratFuncDXCoeff_smul_dX` (`P1ResidueCore.lean:2064`), `smul_eq_zero`, `dX_ne_zero` (`:1301`) | probe A |
| 472 | `ratFuncDXCoeff_zero` (10,411) | PROOF-INGREDIENT | row #471, `map_zero`, `zero_smul` | one line |
| 473 | `ord_algebraMap_denom_eq_zero_of_ord_nonneg` (10,420) | PROOF-INGREDIENT | `RatFunc.{num_div_denom, isCoprime_num_denom, num_ne_zero, denom_ne_zero, algebraMap_ne_zero}`, `Ideal.mem_span_singleton`, `Place.ord_ofHeightOneSpectrum_ne_zero_iff` | probes M; no port copy |
| 474 | `ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg` (10,448) | PROOF-INGREDIENT | row #473, `wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero` (`:2071`), `ratFuncDXCoeff_def` (`:2059`), `ord_mul`, `ord_inv`, `ord_zpow` | no port copy |
| 475 | `ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one` (10,486) | PROOF-INGREDIENT | `exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one` (`:2302`), row #471 | one line |
| 476 | `ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg` (10,493) | PROOF-INGREDIENT | `exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero` (`:2219`), `ord_placeInfty_ratFuncDXCoeff_ge` (`:2190`) | no port copy |
| 477 | `ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le` (10,522) | PROOF-INGREDIENT | `eq_ofHeightOneSpectrum_or_eq_placeInfty`, `exists_irreducible_span`, `ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one` (`:2157`), rows #475/#476 | no port copy; the perfect-field twin is #517 |
| 478 | `differentialCoeff_D_eq_ratFuncDXCoeff_div` (10,558) | PROOF-INGREDIENT | `Place.differentialCoeff_unique`, `D_eq_ratFuncDXCoeff_smul_dX`, `div_mul_cancel₀` | no port copy; twin of #518 |
| 479 | `differentialCoeff_D_mem_of_mem` (10,567) | PROOF-INGREDIENT | row #477, row #478, `Place.{mem_of_ord_nonneg, ord_mul, ord_inv}`, `div_ne_zero` | no port copy; twin of #519 |

## 9. The `res` engine and the char-0 / coord-indep clauses (rows #480–#492)

The two `res_differentialCoeff_D_of_*` rows are the 3.2d′ engine (SUBSTITUTE); everything
from #482 on is the ℙ¹ clause layer.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 480 | `CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule` (10,594) | **SUBSTITUTE** | `Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule` (`Defs/LocalResidueCalculus.lean:127`) | span-diff identical modulo the `p2m_open_scoped` line; probe A |
| 481 | `CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj` (10,638) | **SUBSTITUTE** | `…_of_surj` (`:170`) | probe A |
| 482 | `…res_differentialCoeff_D_mul_pow_inv_of_surj` (10,649) | PROOF-INGREDIENT | `D_pow_succ_inv` (row #468), row #481, `charZero_of_injective_algebraMap`, `map_inv₀`, `map_natCast`, `inv_mul_cancel_left₀`, `Algebra.smul_def` | no port copy; the char-0 engine |
| 483 | `…res_differentialCoeff_D_mul_inv_of_integral` (10,680) | PROOF-INGREDIENT | `Derivation.leibniz`, `Place.differentialCoeff_add''` (#469), `differentialCoeff_smul`, `differentialCoeff_dCoord`, `gate_canonicalLocalResidueDataK_uniformizer_inv` (`LocalResidueCalculus.lean:384`), `R.res_of_mem`, `field_simp` | no port copy; 54 pin ln |
| 484 | `canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc` (10,734) | PROOF-INGREDIENT | row #482, row #479 | one line |
| 485 | `canonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_ratFunc` (10,742) | PROOF-INGREDIENT | row #483, row #479 | one line |
| 486 | `canonicalLocalResidueKSimplePoleCoordIndep_ratFunc` (10,752) | PROOF-INGREDIENT | row #485 | one line; the char-0 discharge of #448 |
| 487 | `canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty` (10,762) | PROOF-INGREDIENT | row #484, `surjective_algebraMap_residueField_placeInfty` (`P1ResidueCore.lean:1913`) | no port copy |
| 488 | `canonicalLocalResidueDataK_res_X_pow_mul_D_X` (10,769) | PROOF-INGREDIENT | `X_pow_mul_differentialCoeff_D_X_eq_neg` (`:1950`), row #487 | distinct from the ported `…_of_coordIndep` (`:1967`), which assumes the stronger coord-indep predicate |
| 489 | `canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow` (10,778) | PROOF-INGREDIENT | `diagonalHom_apply`, row #488, `map_zero` | distinct from `…_kaehlerResidueTerm_X_pow_of_coordIndep` (`:1978`) |
| 490 | `surjective_algebraMap_residueField_of_deg_eq_one` (10,793) | PROOF-INGREDIENT | `finrank_eq_one_iff_of_nonzero'` (`LinearAlgebra/FiniteDimensional/Basic.lean:602`), `Algebra.algebraMap_eq_smul_one` | probe M; no port copy |
| 491 | `surjective_algebraMap_residueField_ratFunc_of_isAlgClosed` (10,801) | PROOF-INGREDIENT | row #490, `deg_ofHeightOneSpectrum`, `IsAlgClosed.degree_eq_one_of_irreducible` (`FieldTheory/IsAlgClosed/Basic.lean:216`), `surjective_algebraMap_residueField_placeInfty` | probe M |
| 492 | `canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed` (10,816) | PROOF-INGREDIENT | row #484, row #491 | one line |

## 10. Perfect-field `DCoordGenerates` and the canonical divisor (rows #493–#501)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 493 | `exists_ne_zero_smul_dX_of_uniformizer` (10,860) | PROOF-INGREDIENT | `eq_ofHeightOneSpectrum_or_eq_placeInfty`, `ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one` (`:2157`), `PerfectField.separable_of_irreducible`, `exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one` (`:2302`) | no port copy; body of the missed instance at pin 10,880 |
| 494 | `p1DifferentialCoeffUnitFinite_dX_of_perfectField` (10,903) | PROOF-INGREDIENT | `ord_differentialCoeff_dX_ofHeightOneSpectrum` (`:1460`), `PerfectField.separable_of_irreducible` | no port copy; the char-0 twin is `p1DifferentialCoeffUnitFinite_dX` (`:2766`) |
| 495 | `p1DifferentialCoeffRegularFinite_dX_of_perfectField` (10,912) | PROOF-INGREDIENT | `p1DifferentialCoeffRegularFinite_of_unitFinite` (`:2453`), row #494 | one line |
| 496 | `ordDifferential_dX_of_ne_placeInfty_of_perfectField` (10,917) | PROOF-INGREDIENT | row #494, `Place.ordDifferential` | one line |
| 497 | `ordDifferential_dX_placeInfty_of_perfectField` (10,922) | PROOF-INGREDIENT | `ordDifferential_placeInfty_D_ratFuncX` (`:944`), `ordDifferentialWellDefined_ratFunc_of_perfectField` (`:2727`) | one line |
| 498 | `exists_divisor_smul_dX_of_perfectField` (10,927) | PROOF-INGREDIENT | rows #496/#497, `HasPrincipalDivisors.exists_divisor`, `Finsupp.*`, `Divisor.degree_single`, `deg_placeInfty` | twin of #466 |
| 499 | `instHasCanonicalDivisorRatFuncPerfectField` (10,952) | **BESPOKE** | new `scoped instance`; no port counterpart | body: `exists_smul_dX_eq` + row #498 |
| 500 | `…ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero` (11,024) | **SUBSTITUTE** | `_root_.ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_…` (`Defs/LocalResidueCalculus.lean:191`, **private**) | span-diff identical except an unused `[HasCanonicalLocalResidueKStar K F]` section variable; private in the port, consumed only there |
| 501 | `residueTheoremK_placeInfty_clause_X_pow` (11,140) | PROOF-INGREDIENT | `kaehlerResidueTermKFam_apply` (`Defs/LocalResidue.lean:213`), row #489 | one line |

## 11. The perfect-field Euler–Cartier block (rows #502–#523)

This is the chunk's real new work: the pin re-derives the finite-place residue value and the
Euler value over `[PerfectField K]` (no `CharZero`), using `PerfectField.separable_of_irreducible`
where the ported chunks 1–3 used `hpirr.separable` under `[CharZero K]`. Every statement is a
new name; the ported char-0 twins are listed so the worker reuses their *proof shape* rather
than re-deriving the Wronskian algebra.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 502 | `ag9b12c_trace_root_pow_div_derivative_of_lt_of_perfectField` (11,202) | PROOF-INGREDIENT | `FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_of_lt` (`P1ResidueCore.lean:69`), `AdjoinRoot.{powerBasis, minpoly_powerBasis_gen_of_monic, powerBasis_gen}`, `Module.Finite.of_basis` | probe A/M; the port's generic power-basis lemma needs no `CharZero`, so it is reusable in char `p` |
| 503 | `ag9b12c_trace_root_pow_div_derivative_self_of_perfectField` (11,215) | PROOF-INGREDIENT | `…_minpoly_self` (`:82`), rows #502 | idem |
| 504 | `ag9b12c_aeval_root_eq_sum_range` (11,229) | PROOF-INGREDIENT | `Polynomial.eval₂_eq_sum_range'` (`Algebra/Polynomial/Eval/Degree.lean:49`), `Finset.sum_congr`, `Algebra.smul_def` | probe M; duplicate of the ported `aeval_root_eq_sum_range` (`:3045`) under the `ag9b12c_` name |
| 505 | `ag9b12c_trace_adjoinRoot_mk_div_mk_derivative_of_perfectField` (11,235) | PROOF-INGREDIENT | rows #502/#503/#504, `AdjoinRoot.aeval_eq`, `Finset.sum_div`, `map_sum`, `Finset.sum_eq_single` | duplicate of `trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt` (`:3051`) |
| 506 | `ag9b12c_differentialCoeff_add` (11,268) | PROOF-INGREDIENT | `Place.differentialCoeff_unique`, `add_smul`, `differentialCoeff_smul_dCoord` | a third copy (`differentialCoeff_add'` `:3290`, `add''` `LocalResidueCalculus.lean:109`) |
| 507 | `ag9b12c_differentialCoeff_D_mem_finitePlace` (11,274) | PROOF-INGREDIENT | `denom_sq_smul_D_eq` (`:1266`), `differentialCoeff_unique`, `algebraMap_mem_ofHeightOneSpectrum`, `denom_notMem_of_mem_ofHeightOneSpectrum` (`:3259`), `ord_differentialCoeff_dX_ofHeightOneSpectrum`, `PerfectField.separable_of_irreducible` | char-0 twin `differentialCoeff_D_mem_finitePlace` (`:3300`) |
| 508 | `ag9b12c_uniformizer_div_mem_finitePlace` (11,310) | PROOF-INGREDIENT | `Place.{uniformizer_ne_zero, ord_mul, ord_inv, ord_uniformizer}`, `ord_finitePlace_self` (`:527`) | twin `uniformizer_div_mem_finitePlace` (`:3342`) |
| 509 | `ag9b12c_one_sub_uniformizer_div_mul_differentialCoeff_D` (11,321) | PROOF-INGREDIENT | `Derivation.leibniz`, row #506, `differentialCoeff_dCoord`, `differentialCoeff_smul`, `linear_combination` | twin `one_sub_uniformizer_div_mul_differentialCoeff_D` (`:3353`) |
| 510 | `ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace` (11,353) | PROOF-INGREDIENT | row #508, `differentialCoeff_D_algebraMap_polynomial` (`:3295`), row #507 | twin `…_mem_finitePlace` (`:3387`) |
| 511 | `ag9b12c_residue_uniformizer_div_mul_differentialCoeff_D_eq_one` (11,368) | PROOF-INGREDIENT | rows #509/#510, `Place.mem_maximalIdeal_iff_adicValuation_lt_one`, `HeightOneSpectrum.valuation_lt_one_iff_mem`, `Ideal.mul_mem_right` | twin `residue_uniformizer_div_mul_differentialCoeff_D_eq_one` (`:3403`) |
| 512 | `ag9b12c_residue_algebraMap_derivative_ne_zero` (11,415) | PROOF-INGREDIENT | `PerfectField.separable_of_irreducible`, `IsUnit.of_dvd'` | twin `residue_algebraMap_derivative_ne_zero` (`:3455`) |
| 513 | `ag9b12c_simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne` (11,429) | PROOF-INGREDIENT | `Place.simplePoleResidueAux_apply`, rows #510/#511, `map_mul` | twin `simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne` (`:3468`) |
| 514 | `ag9b12c_p1FinitePlaceSimplePoleResidueAdjoinRootValue_of_perfectField` (11,483) | PROOF-INGREDIENT | row #513, `finitePlaceResidueFieldAlgEquivAdjoinRoot_mk` (`:3098`), `map_div₀` | the ported carrier `P1FinitePlaceSimplePoleResidueAdjoinRootValue` (`:3131`) is the pin's own `def` |
| 515 | `ag9b12c_trace_finitePlace_simplePoleResidue_mOne_of_perfectField` (11,498) | PROOF-INGREDIENT | row #514, `trace_finitePlace_residueField_eq_trace_adjoinRoot` (`:3113`), row #505 | twin `trace_finitePlace_simplePoleResidue_of_adjoinRootValue` (`:3159`) |
| 516 | `ag9b12c_p1MOneSimplePoleCancel_dX_of_inftyEulerValue_of_perfectField` (11,511) | PROOF-INGREDIENT | row #515, `P1PlaceInftySimplePoleResidueEulerValue` (`:3140`), `add_neg_cancel` | no port copy |
| 517 | `ag9b13e_ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le_of_perfectField` (11,556) | PROOF-INGREDIENT | perfect-field re-route of row #477 with `PerfectField.separable_of_irreducible` | probe A/M; no port copy |
| 518 | `ag9b13e_differentialCoeff_D_eq_ratFuncDXCoeff_div_of_perfectField` (11,593) | PROOF-INGREDIENT | `differentialCoeff_unique`, `D_eq_ratFuncDXCoeff_smul_dX`, `div_mul_cancel₀`; twin of #478 | no port copy |
| 519 | `ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField` (11,603) | PROOF-INGREDIENT | rows #517/#518, `Place.{mem_of_ord_nonneg, ord_mul, ord_inv}` | the shared `hint` for the whole char-`p` cone, consumed by #573 |
| 520 | `ag9b13e_canonicalLocalResidueKSimplePoleCoordIndep_ratFunc_of_perfectField` (11,624) | PROOF-INGREDIENT | row #519, row #483 | perfect-field discharge of #448 |
| 521 | `ag9b13e_p1PlaceInftySimplePoleResidueEulerValueX_of_perfectField` (11,637) | PROOF-INGREDIENT | row #520, row #452 | one line |
| 522 | `ag9b13e_p1PlaceInftySimplePoleResidueEulerValueMonomial_of_perfectField` (11,642) | PROOF-INGREDIENT | row #521, row #497, row #440 | one line |
| 523 | `ag9b13e_p1PlaceInftySimplePoleResidueEulerValue_of_perfectField` (11,648) | PROOF-INGREDIENT | row #522, row #497, `p1PlaceInftySimplePoleResidueEulerValue_of_monomial` (`:3789`) | one line |

## 12. The Kähler residue functional and its per-generator engine (rows #524–#538)

The `weilOfKaehlerK`/`kaehlerResidueTermKFam` vocabulary is ported; the new content is the
linear functional and the atom decomposition.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 524 | `kaehlerResidueFunctionalK` (11,708) | **BESPOKE** | new `def : F →ₗ[K] K` = `(weilOfKaehlerK Rfam hω).comp (principalAdele K F)`; port vocabulary `weilOfKaehlerK` (`Defs/LocalResidue.lean:287`), `principalAdele` (`P1ResidueCore.lean:338`) | no port copy |
| 525 | `kaehlerResidueFunctionalK_eq_finsum` (11,712) | PROOF-INGREDIENT | `rfl` | probe M (`finsum_eq_finsetSum_of_support_subset`) |
| 526 | `kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl` (11,717) | PROOF-INGREDIENT | `finsum_eq_finsetSum_of_support_subset`, `by_contra` | probe M |
| 527 | `kaehlerResidueFunctionalK_eq_zero_of_singleton` (11,728) | PROOF-INGREDIENT | row #526, `Finset.mem_singleton` | no port copy |
| 528 | `kaehlerResidueFunctionalK_eq_zero_of_pair` (11,740) | PROOF-INGREDIENT | row #526, `Finset.sum_pair`, `Finset.mem_insert` | no port copy |
| 529 | `kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule` (11,762) | PROOF-INGREDIENT | `kaehlerResidueTermKFam_apply` (`Defs/LocalResidue.lean:213`), `diagonalHom_apply`, `CanonicalLocalResidueDataK.res_simplePole` (`Defs/LocalResidue.lean:41`) | no port copy |
| 530 | `kaehlerResidueTermKFam_smul_diagonal` (11,781) | PROOF-INGREDIENT | `differentialCoeff_smul`, `ring` | no port copy |
| 531 | `weilOfKaehlerK_smul_diagonal` (11,792) | PROOF-INGREDIENT | row #530, `weilOfKaehlerK_apply` (`Defs/LocalResidue.lean`), `finsum_congr` | no port copy |
| 532 | `kaehlerResidueFunctionalK_dX_X_pow` (11,809) | PROOF-INGREDIENT | row #527, `kaehlerResidueTermKFam_eq_zero_of_ord_nonneg` (`Defs/LocalResidue.lean`), `pow_X_mul_mem_of_ne_placeInfty` (`:425`), row #501 | no port copy |
| 533 | `kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne` (11,823) | PROOF-INGREDIENT | `p1PrincipalPartAtom_mem_of_ne_finitePlace` (`:1573`), `kaehlerResidueTermKFam_eq_zero_of_ord_nonneg` | no port copy |
| 534 | `kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le` (11,835) | PROOF-INGREDIENT | `p1PrincipalPartAtom_ne_zero` (`:841`), `two_le_ord_placeInfty_p1PrincipalPartAtom` (`:2387`), `ordDifferential_placeInfty_D_ratFuncX`, `omega` | no port copy |
| 535 | `kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le` (11,861) | PROOF-INGREDIENT | `p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg` (`:2968`) | no port copy |
| 536 | `kaehlerResidueTermKFam_atom_mOne_two_place_sum` (11,873) | PROOF-INGREDIENT | `p1MOneAtom_mul_differentialCoeff_mem_simplePole_{finitePlace,placeInfty}` (`:2818/:2843`), row #529, `p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep` (row #453) | no port copy |
| 537 | `kaehlerResidueFunctionalK_dX_atom` (11,894) | PROOF-INGREDIENT | row #528, rows #533–#536 | no port copy |
| 538 | `kaehlerResidueFunctionalK_dX_eq_zero` (11,917) | PROOF-INGREDIENT | `p1PartialFractionSpan_eq_top` (`:806`), rows #532/#537, `Submodule.span_le`, `LinearMap.mem_ker` | no port copy |

## 13. `residueTheoremK_ratFunc` and the char-free `p0n21_rtk` re-route (rows #539–#553)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 539 | `residueTheoremK_ratFunc_of_subrows` (11,950) | PROOF-INGREDIENT | row #538, row #531, `exists_smul_eq_of_ne_zero` (`:325`) | no port copy |
| 540 | `residueTheoremK_ratFunc_of_isAlgClosed_main` (11,973) | PROOF-INGREDIENT | row #539, `ordDifferentialWellDefined_ratFunc` (`:2339`), rows #492/#486, `p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed` (`:2989`) | no port copy; the char-0 capstone |
| 541 | `p0n21_rtk_p1MOneSimplePoleCancel_dX_of_perfectField` (12,030) | PROOF-INGREDIENT | row #516, row #523 | one line |
| 542 | `p0n21_rtk_kaehlerResidueFunctionalK_dX_X_pow` (12,044) | PROOF-INGREDIENT | row #527, `p1DifferentialCoeffRegularFinite_dX_of_perfectField` (row #495), `CanonicalLocalResidueDataK.res_…X_pow_of_coordIndep` | perfect-field twin of #532 |
| 543 | `p0n21_rtk_kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne` (12,063) | PROOF-INGREDIENT | row #533 twin using row #495 | idem |
| 544 | `p0n21_rtk_kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le` (12,075) | PROOF-INGREDIENT | row #534 twin | idem |
| 545 | `p0n21_rtk_kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le` (12,101) | PROOF-INGREDIENT | row #535 twin | idem |
| 546 | `p0n21_rtk_kaehlerResidueTermKFam_atom_mOne_two_place_sum` (12,113) | PROOF-INGREDIENT | row #536 twin using row #541 | idem |
| 547 | `p0n21_rtk_kaehlerResidueFunctionalK_dX_atom` (12,129) | PROOF-INGREDIENT | row #537 twin | idem |
| 548 | `p0n21_rtk_kaehlerResidueFunctionalK_dX_eq_zero` (12,149) | PROOF-INGREDIENT | row #538 twin | idem |
| 549 | `p0n21_rtk_residueTheoremK_ratFunc_of_subrows_charFree` (12,180) | PROOF-INGREDIENT | row #548, row #531, `exists_smul_eq_of_ne_zero` | char-free twin of #539 |
| 550 | `p0n21_rtk_residueTheoremK_ratFunc_of_coordIndep_higherDeg_of_perfectField` (12,194) | PROOF-INGREDIENT | row #549, row #497, `p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed` | one line |
| 551 | `p0n21_rtk_residueTheoremK_ratFunc_of_isAlgClosed_of_coordIndep` (12,206) | PROOF-INGREDIENT | row #550 + `…_of_algClosed` | one line |
| 552 | `p0n21_rtk_surjective_algebraMap_residueField_of_deg_eq_one` (12,225) | PROOF-INGREDIENT | row #490 twin | idem |
| 553 | `p0n21_rtk_surjective_algebraMap_residueField_ratFunc_of_isAlgClosed` (12,234) | PROOF-INGREDIENT | row #491 twin | consumed by #575 |

## 14. The `p0n22_cpf_*` cone, its capstones and the headline (rows #554–#579)

Rows #554–#574 are SUBSTITUTE (the generic cone, §7/Correction 3); the three capstones and
the headline are new glue.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 554–574 | `p0n22_cpf_*` (12,287–13,085) | **SUBSTITUTE** ×21 | `Defs/LocalResidueCalculus.lean:397–1182` (same names, generic `{K F}` statements) | Correction 3; span-diff shows only the `RatFunc K` ↔ `F` instantiation; the generator already omits them |
| 575 | `p0n22_cpf_canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed` (13,090) | PROOF-INGREDIENT | row #574, row #553 | 8 pin ln |
| 576 | `p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_of_charP` (13,098) | PROOF-INGREDIENT | row #551, row #575 | one line |
| 577 | `p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main` (13,105) | PROOF-INGREDIENT | `CharP.char_is_prime_or_zero` (`Algebra/CharP/Defs.lean:245`), `ringChar.charP` (`:160`), `CharP.charP_to_charZero` (`:108`), rows #576/#540 | probe H checks the `ringChar` split |
| 578 | `RationalFunctionField.placeInfty_eq_p1PlaceInfty` (13,145) | PROOF-INGREDIENT | `rfl`; port `@[reducible] def p1PlaceInfty : Place K (RatFunc K) := placeInfty K` (`P1ResidueCore.lean:283`) | probe H |
| 579 | `solution` (13,152) | PROOF-INGREDIENT | row #578, `X_pow_mul_differentialCoeff_D_X_eq_neg` (`:1950`), `res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap` (`LocalResidueCalculus.lean:1212`), row #519, `surjective_algebraMap_residueField_placeInfty` | published by the wrapper as `AlgebraicCurve.RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero` |

## 15. Reuse wins, with probe and diff evidence

### 15.1 The whole generic cone is already homed (rows #468–#470, #480–#481, #500, #554–#574)

`Defs/LocalResidueCalculus.lean` (1,229 ln) is the 3.2d′ deliverable. Span diffs:

- `D_pow_succ_inv`, `differentialCoeff_add''`, `differentialCoeff_D_uniformizer_pow_inv`
  (pin 10,364–10,401 vs port 96–126): identical;
- `res_differentialCoeff_D_of_mem_poleSubmodule` / `_of_surj` (pin 10,594–10,647 vs port
  127–190): identical except the pin's `p2m_open_scoped` line;
- `ag9b13t_…` (pin 11,024–11,057 vs port 191–232): identical except an unused
  `[HasCanonicalLocalResidueKStar K F]` section variable;
- the 21 `p0n22_cpf_*` (pin 12,287–13,085 vs port 397–1,182): identical modulo the
  `RatFunc K` ↔ generic-`F` instantiation.

The master file references `p0n22_cpf_` 63 times, `ag9b15u_` 13, `ag9b14c_` 6 and
`ag9b13t_` 3; homing the cone here is what lets this chunk import instead of re-transcribing
~1,050 content lines.

### 15.2 The Euler-value chain is chunks-1–3 output (rows #440, #522, #523)

`P1ResidueCore.lean` already carries the carriers and reductions the chunk instantiates:
`P1PlaceInftySimplePoleResidueEulerValue` (`:3140`), `…TopDeg` (`:3637`), `…Monomial`
(`:3645`), `p1PlaceInftySimplePoleResidueEulerValue_of_topDeg` (`:3721`),
`…TopDeg_of_monomial` (`:3733`), `…_of_monomial` (`:3789`), and the finite-place twins
`P1FinitePlaceSimplePoleResidueAdjoinRootValue` (`:3131`),
`trace_finitePlace_simplePoleResidue_of_adjoinRootValue` (`:3159`). Rows #440/#522/#523 are
one-line instantiations.

### 15.3 mathlib's `Derivation` and char-`p` Frobenius APIs carry every calculus step

`Derivation.{leibniz, leibniz_pow, leibniz_inv, map_algebraMap, map_one_eq_zero}` are the
pin's own leaves (probe M). The Cartier block is exactly `add_pow_char`, `add_pow_char_pow`,
`sum_pow_char`, `neg_one_pow_char`, `frobenius_def`, `charP_of_injective_{ringHom,
algebraMap}`, `CharP.{cast_eq_zero_iff, char_is_prime_or_zero, charP_to_charZero}` and
`ringChar.charP` (probe M, probe H for the split). No derivation step in rows #435–#579
needs a new mathlib lemma.

### 15.4 `geom_sum_mul` is the geometric core (row #565)

`p0n22_cpf_res_geom_core` (~140 pin ln) is a named assembly whose only "hard" leaf is
`geom_sum_mul` (`Mathlib/Algebra/Ring/GeomSum.lean:232`), plus
`Finset.sum_eq_single_of_mem`, `ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one` and the
gate (all ported).

## 16. Route options

- **R1 — import the 29 substitutes; omit them from the append.** Rows #459, #468–#470,
  #480–#481, #500, #554–#574. Correction 2 is the one edit needed to `gen_p32e.py`.
- **R2 — transcribe the new clause layers as named assemblies (rows #482–#499, #501–#553,
  #575–#579).** Every statement is new but every proof is a short assembly over the ported
  carriers; the longest are #483 (54 pin ln) and #538 (~33).
- **R3 — do not build a `Differential` instance to reach `Differential.logDeriv_mul`.** The
  pin's `p0n22_cpf_logDeriv_mul` (#558) is a 19-line `linear_combination` over
  `Derivation.leibniz`; mathlib's `Differential` (`RingTheory/Derivation/DifferentialRing.lean`)
  is a `Derivation ℤ R R` typeclass and would need a `Differential F` instance (recorded
  negative §17.2).
- **R4 — do not route the `p0n22` Laurent expansion through `HahnSeries`/`LaurentSeries`.**
  The pin's expansion (row #564) is a finite sum plus a remainder in `toValuationSubring`,
  not a `LaurentSeries` equality (recorded negative §17.3).
- **R5 — no partial-fraction route for the "Cartier" rows.** The pin's partial-fraction tool
  is `p1PartialFractionSpan_eq_top` (`P1ResidueCore.lean:806`), already ported; the
  `ag9b12c_*`/`ag9b13e_*` rows are characteristic-`p` Frobenius identities (recorded
  negative §17.4).
- **R6 — reuse the char-0 twins' proof shapes for the perfect-field block.** The ported
  `differentialCoeff_D_mem_finitePlace` (`:3300`), `uniformizer_div_mem_finitePlace`
  (`:3342`), `one_sub_uniformizer_div_mul_differentialCoeff_D` (`:3353`),
  `residue_uniformizer_div_mul_differentialCoeff_D_eq_one` (`:3403`) and
  `simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne` (`:3468`) are the same proofs
  with `hpirr.separable` replaced by `PerfectField.separable_of_irreducible`.

## 17. API drift (`v4.34.0`) — what the worker must change

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `Polynomial.degree_sub_lt hdeg hp0 hlc` (row #434's helper, consumed by #435) | **does not exist**; v4.34 has `Polynomial.degree_sub_lt_left` / `degree_sub_lt_right` (`Algebra/Polynomial/Degree/Defs.lean:543/562`) | not used in the new rows (the helper is already ported); if a new proof needs it, use the `_left`/`_right` split |
| `finsum_eq_finsetSum_of_support_subset` (row #525) | exists and is the **canonical** spelling; the snake-case `finsum_eq_finset_sum_of_support_subset` is the deprecated alias (`Algebra/BigOperators/Finprod.lean:381`) | keep the pin's camelCase name (probe M) |
| `haveI : CharP K 0` / `CharP F p` / `CharP v.ResidueField p` in `Prop` goals (rows #569–#573, #576–#577) | `linter.style.haveILetI` fires (3.2b §2, 3.2d′ §10) | keep `haveI` (instance search needs it inline); suppress locally if warning-strict |
| pin `private theorem _root_.ModularCurve.…` headers | the port writes `private theorem …` in the same namespace (`LocalResidueCalculus.lean:191`) | no statement change; the checker normalises `_root_.` |
| `intermediate_field` `K⟮t⟯` notation | scoped; needs `open scoped IntermediateField` (probe H) | not a statement change, just elaboration |
| pin's missing declarations | `p32_master_inventory.txt` omits the two `scoped instance (priority := low)` declarations (Correction 1) | land them explicitly |

## 18. Recorded negatives

Confirmed against mathlib `v4.34.0` and the port; phrased so the search is not repeated.

1. **No `ag9b12c_*`, `ag9b13e_*`, `p0n21_rtk_*`, `kaehlerResidueFunctionalK*`,
   `CanonicalLocalResidueKSimplePoleCoordIndep`, `IsPurelyTranscendentalSimple`,
   `residueTheoremK_ratFunc_of_subrows`, `residueTheoremK_placeInfty_clause_X_pow` or
   `instHasCanonicalDivisorRatFunc{,PerfectField}` in the port.** Greps over
   `FLTForHuman/` and `Reserve/` return nothing. These are the chunk's real new work
   (117 inventory rows), plus the two missed instances.
2. **No `Polynomial.logDeriv` in `v4.34.0`.** The only algebraic log derivative is
   `Differential.logDeriv` (`Mathlib/FieldTheory/Differential/Basic.lean:29`), which needs a
   `Differential` instance (route R3); `Analysis.Calculus.logDeriv` and `Meromorphic.logDeriv`
   are analytic and off-path.
3. **No route from `LaurentSeries`/`HahnSeries` to `Place.ord`.** `LaurentSeries R` is
   `HahnSeries ℤ R` (`Mathlib/RingTheory/LaurentSeries.lean:102`) with an `X`-adic valuation,
   but row #564's Laurent expansion is a finite-sum-plus-remainder statement in the valuation
   subring, not a `LaurentSeries` equality. Do not route the `p0n22` expansion through
   `HahnSeries`.
4. **`Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`
   (`Mathlib/Algebra/Polynomial/PartialFractions.lean:341`) is off-path.** The pin's
   "Cartier" rows are characteristic-`p` Frobenius identities (`add_pow_char`, `sum_pow_char`),
   not partial fractions; the pin's own partial-fraction input is the ported
   `p1PartialFractionSpan_eq_top`.
5. **`Polynomial.divByMonic` / `modByMonic` / `derivative` exist but are off this chunk's
   path.** No declaration in rows #435–#579 mentions `divByMonic`/`modByMonic`; the
   `Polynomial` leaves that *are* used are `natDegree_lt_natDegree`, `eval₂_eq_sum_range'`,
   `degree_X_pow`, `leadingCoeff_X_pow` and `degree_sub_lt_{left,right}` (probe M).
6. **No port `HasCanonicalDivisor (K := K) (F := RatFunc K)` instance.** The port takes it as
   a section variable throughout `P1ResidueCore.lean`; rows #467/#499 are the missing
   enablers. The general port theorem is `hasCanonicalDivisor_of_isCurveOver`
   (`Canonical/HasCanonicalDivisor.lean`), not an instance.
7. **`ag9b13t_…` (row #500) and the two differential helpers (#469/#470) are `private` in
   `Defs/LocalResidueCalculus.lean`.** They cannot be imported by name into
   `P1ResidueCore`; the chunk does not need them (row #506 is its own `differentialCoeff_add`
   copy, and the capstones go through `p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj`).
   Recorded debt: the same helpers are duplicated `private` in `P1ResidueCore`.
8. **`IntermediateField.finiteDimensional_top` is absent from mathlib and the port**, so
   row #442 is a new name (its one-line body compiles, probe H). `IntermediateField.
   finiteDimensional_of_eq` *is* ported (`P1ResidueCore.lean:3865`) and is the ingredient for
   #446.
9. **The master's `p0n22_cpf_*` copies are not type-identical to the port's** (`RatFunc K`
   vs generic `F`); do not re-declare them — the names are globally taken and the checker
   accepts the generic 3.2d′ source (Correction 3).
10. **No `Polynomial.degree_sub_lt` in `v4.34.0`** — only `degree_sub_lt_left` and
    `degree_sub_lt_right` (`Algebra/Polynomial/Degree/Defs.lean:543/562`). The new rows do
    not call it, but the name is a trap for anyone porting row #434's proof body afresh.

## 19. What this changes for `WORKORDER-P3-2e-p1core-4.md`

**Scope / measurement.**

- Pin lines 9,500–13,173 contain **147 declarations**: the inventory's 145 rows #435–#579
  plus two `scoped instance (priority := low)` declarations the inventory tool missed
  (Correction 1). The append must carry the two instances.
- **28 SUBSTITUTE / 111 PROOF-INGREDIENT / 6 BESPOKE** over the 145 inventory rows.
- **The generator's omit list is wrong by one.** `gen_p32e.py` omits 27 rows but keeps
  #459 (`Place.dCoordGenerates_of_valSubringKaehlerSpanTop`), which collides with
  `Canonical/HasCanonicalDivisor.lean:987`; add #459 to `omit` (Correction 2).

**Discharged proofs (mark import-discharged; the statements still land in `SOURCES`).**

- #459 — import from `Canonical/HasCanonicalDivisor.lean:987`;
- #468–#470, #480–#481, #500, #554–#574 — import from `Defs/LocalResidueCalculus.lean`
  (`:96/:109/:114/:127/:170/:191/:397–1182`).

**New work, budgeted (117 inventory rows + 2 instances).**

- #435–#441, #449–#453, #463–#466, #471–#479 — named assemblies over the ported ℙ¹
  dictionary, Wronskian and Euler-value chain;
- #467, #499 — the two RatFunc `HasCanonicalDivisor` instances;
- #482–#492 — the char-0 clause layer (the two longest are #483 and #488);
- #493–#498, #501 — the perfect-field `DCoordGenerates`/divisor layer and the place-∞ clause;
- #502–#523 — the perfect-field `ag9b12c_*`/`ag9b13e_*` Euler–Cartier re-route (22 rows,
  each a short twin of a ported char-0 proof);
- #524–#538 — the Kähler residue functional and its per-generator engine (the new
  mathematics of the chunk);
- #539–#553 — `residueTheoremK_ratFunc` and the char-free `p0n21_rtk_*` re-route;
- #575–#579 — the three capstones, the `rfl` alias and the headline.

**Imports the worker may use.** The port modules `Defs/{P1ResidueCore, LocalResidueCalculus,
P1Dictionary, CanonicalLocalResidueInstanceV2, PlaceDictionary, RatFuncPlaces}.lean`,
`Canonical/HasCanonicalDivisor.lean`, plus, on the mathlib side,
`Mathlib.RingTheory.Derivation.Basic`, `Mathlib.Algebra.CharP.{Defs,Lemmas,Frobenius,Algebra}`,
`Mathlib.Algebra.Ring.GeomSum`, `Mathlib.FieldTheory.IsAlgClosed.Basic`,
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`, `Mathlib.RingTheory.PowerBasis`,
`Mathlib.RingTheory.AdjoinRoot`, `Mathlib.LinearAlgebra.FiniteDimensional.Basic`,
`Mathlib.RingTheory.Trace.Defs`, `Mathlib.RingTheory.LocalRing.ResidueField.Basic`. Do
**not** import `Mathlib.RingTheory.LaurentSeries`, `Mathlib.Algebra.Polynomial.PartialFractions`
or `Mathlib.FieldTheory.Differential.Basic` — off-path (§18.2–§18.4).

**Checker wiring.** `SOURCES` already list the `Theorems/` wrapper and the master `S_` file
(`spec/check_flt_statements.py:1631–1632`) and the 3.2d′ files (`:1638–1639`); `PORT_FILES`
already include `Defs/P1ResidueCore.lean` and `Defs/LocalResidueCalculus.lean`. No checker
edit. Note that the checker iterates `PORT_FILES` and looks each port declaration up among
*all* source candidates by last name (`:2538–2570`), so "0 missing" is not by itself
evidence of source coverage: the 3.2e rows verify as a subset of the master + 3.2d′ surfaces.

**Stop-early.** The two unanticipated items are Correction 1 (the inventory misses two
instances) and Correction 2 (the generated append re-declares #459 and will not compile as
generated). A worker who trusts `p32e_append.lean` verbatim hits the name collision on the
first build.

## 20. Appendix — module map for the named constants

| name | module |
|---|---|
| `Place.dCoordGenerates_of_valSubringKaehlerSpanTop` | `FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean` |
| `D_pow_succ_inv`, `Place.differentialCoeff_add''`, `Place.differentialCoeff_D_uniformizer_pow_inv`, `CanonicalLocalResidueDataK.res_differentialCoeff_D_of_{mem_poleSubmodule,surj}`, `ag9b13t_…`, `gate_canonicalLocalResidueDataK_uniformizer_inv`, `p0n22_cpf_*` | `FLTForHuman/AlgebraicCurve/Defs/LocalResidueCalculus.lean` |
| `p1PlaceInfty`, `dX`, `p1PrincipalPartAtom`, `finitePlace`, `P1PlaceInftySimplePoleResidueEulerValue{,TopDeg,Monomial}`, `p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial`, `p1MOneAtom_mul_differentialCoeff_mem_simplePole_{finitePlace,placeInfty}`, `aeval_root_eq_sum_range`, `trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt`, `finitePlaceResidueFieldAlgEquivAdjoinRoot`, `trace_finitePlace_residueField_eq_trace_adjoinRoot`, `P1FinitePlaceSimplePoleResidueAdjoinRootValue`, `ratFuncDXCoeff`, `X_pow_mul_differentialCoeff_D_X_eq_neg`, `p1PartialFractionSpan_eq_top`, `CanonicalLocalResidueKDifferentialCoordIndep`, `HasSeparatingTranscendentalCore`, `valSubringKaehlerFinite_of_core`, `IntermediateField.finiteDimensional_of_eq` | `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean` |
| `placeInfty`, `finitePlace` (def), `deg_placeInfty` | `FLTForHuman/AlgebraicCurve/Defs/{RatFuncPlaces,P1Dictionary}.lean` |
| `simplePoleSubmodule`, `simplePoleResidueAux`, `mem_simplePoleSubmodule`, `localResidueData_res_eq_simplePoleResidueAux`, `CanonicalLocalResidueDataK.res_simplePole` | `FLTForHuman/AlgebraicCurve/Defs/{CanonicalLocalResidueInstanceV2,LocalResidue}.lean` |
| `weilOfKaehlerK`, `kaehlerResidueTermKFam`, `ResidueTheoremK` | `FLTForHuman/AlgebraicCurve/Defs/LocalResidue.lean` |
| `Place.mk_mem_maximalIdeal_iff` | `FLTForHuman/AlgebraicCurve/Genus/Index.lean` |
| `geom_sum_mul` | `Mathlib/Algebra/Ring/GeomSum.lean` |
| `Derivation.{leibniz, leibniz_pow, leibniz_inv, map_algebraMap, map_one_eq_zero}` | `Mathlib/RingTheory/Derivation/Basic.lean` |
| `add_pow_char`, `add_pow_char_pow`, `sum_pow_char`, `neg_one_pow_char` | `Mathlib/Algebra/CharP/Lemmas.lean` |
| `frobenius_def` | `Mathlib/Algebra/CharP/Frobenius.lean` |
| `charP_of_injective_{ringHom,algebraMap}` | `Mathlib/Algebra/CharP/Algebra.lean` |
| `CharP.{cast_eq_zero_iff, char_is_prime_or_zero, charP_to_charZero}`, `ringChar.charP` | `Mathlib/Algebra/CharP/Defs.lean` |
| `Polynomial.{natDegree_X_pow, degree_X_pow, leadingCoeff_X_pow}` | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` |
| `Polynomial.{natDegree_lt_natDegree}`, `degree_sub_lt_left/right` | `Mathlib/Algebra/Polynomial/Degree/{Operations,Defs}.lean` |
| `Polynomial.eval₂_eq_sum_range'` | `Mathlib/Algebra/Polynomial/Eval/Degree.lean` |
| `finsum_eq_finsetSum_of_support_subset` | `Mathlib/Algebra/BigOperators/Finprod.lean` |
| `IsAlgClosed.degree_eq_one_of_irreducible` | `Mathlib/FieldTheory/IsAlgClosed/Basic.lean` |
| `finrank_eq_one_iff_of_nonzero'` | `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean` |
| `Algebra.trace_algebraMap` | `Mathlib/RingTheory/Trace/Defs.lean` |
| `RatFunc.{num_div_denom, isCoprime_num_denom, num_ne_zero, algebraMap_ne_zero, algebraMap_X}` | `Mathlib/FieldTheory/RatFunc/Basic.lean` (`algebraMap_X`: `AsPolynomial.lean`) |
| `AdjoinRoot.{minpoly_powerBasis_gen_of_monic, aeval_eq, powerBasis_dim}` | `Mathlib/RingTheory/AdjoinRoot.lean` |
| `LaurentSeries`, `HahnSeries` | `Mathlib/RingTheory/LaurentSeries.lean`, `Mathlib/RingTheory/HahnSeries/*` |
| `Differential.{logDeriv, logDeriv_mul}` | `Mathlib/FieldTheory/Differential/Basic.lean` |
| `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` | `Mathlib/Algebra/Polynomial/PartialFractions.lean` |
