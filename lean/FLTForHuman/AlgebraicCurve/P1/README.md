# The `P1/` residue core

This directory holds the port of FLT's master $`\mathbb{P}^1`$ file,
[`S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean)
(13,173 pin lines, 580 declarations). It is the **base case of the residue
theorem**: the case $`F = K(X)`$.

**The mathematics is written up in
[math/022-global-residue-theorem.md](../../../../math/022-global-residue-theorem.md)**
§§1–2 — the residue functional, partial fractions on $`\mathbb{P}^1`$, the
simple-pole cancellation, and the higher-pole vanishing. This file does not repeat
it; it only maps the Lean modules onto that story.

The headline, at the end of the chain, is

$$\mathrm{Tr}_{K}\bigl(\mathrm{res}_{\infty}(X^{n}\\,\mathrm{d}X)\bigr) = 0 \qquad (n \ge 0),$$

published as `AlgebraicCurve.RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero`,
and the full $`\mathbb{P}^1`$ statement `ResidueTheoremK K (RatFunc K)` for
$`K`$ algebraically closed. Both feed the general residue theorem
(`residueTheoremK_of_isAlgClosed`) and hence Riemann–Roch.

## The 15 modules are one linear chain

They are **not** 15 topics. They are 15 *consecutive slices* of a single Lean file,
`Defs/P1ResidueCore.lean` (6,470 lines), cut by R1 of
[PLAN-RECTIFY-DEFS.md](../../../topics/riemannRoch/PLAN-RECTIFY-DEFS.md) §5.1.
Lean forbids forward references, so the original declaration order was already a
topological order of its own dependency graph; cutting it consecutively — each
slice importing the one before — cannot break a backward reference. The split
preserves statements, names and namespaces verbatim (the checker is unaffected),
and it buys build economy: editing a lemma rebuilds only that slice and its
successors, not a 6,000-line tower. The line count is preserved, not reduced: the
15 slices together are essentially the original file.

Building [`Core.lean`](Core.lean) builds the whole chain.

| # | module | role |
|---:|---|---|
| 1 | [`EnginePrelude.lean`](EnginePrelude.lean) | `FLT.EulerDualBasis` trace prelude, `Place`/valuation prelude, $`\mathbb{P}^1`$ generators and partial fractions |
| 2 | [`Differential.lean`](Differential.lean) | the Kähler differential of $`K(X)`$: `dX`, its order at finite places and at infinity |
| 3 | [`UnitNormalForm.lean`](UnitNormalForm.lean) | `dX` spans, derivative/non-divisibility, first finite-place atom orders |
| 4 | [`DXCoeff.lean`](DXCoeff.lean) | `KaehlerRankOne`, `RamificationInertiaIdentity`, coordinate independence, the $`X \mapsto 1/X`$ chart |
| 5 | [`DivisorAction.lean`](DivisorAction.lean) | Wronskian bound, `ratFuncDXCoeff` and its ord behaviour, `ordDifferentialWellDefined_ratFunc` |
| 6 | [`UnitFinite.lean`](UnitFinite.lean) | `P1DifferentialCoeffUnitFinite`, explicit Kähler bases, ramification–inertia wrappers, degree-one reductions |
| 7 | [`FinitePlaceResidue.lean`](FinitePlaceResidue.lean) | `ValuationSubring` helpers, the Dedekind-model gate, simple-pole membership of the atoms |
| 8 | [`TraceEngine.lean`](TraceEngine.lean) | the Euler trace formula at a finite place, the `AdjoinRoot p` residue-field iso, the simple-pole bridge rows |
| 9 | [`Separating.lean`](Separating.lean) | char-$`0`$ separability, `HasSeparatingTranscendentalCore`, the monic-ratio $`\infty`$-chart reduction |
| 10 | [`Adjoin.lean`](Adjoin.lean) | pure transcendentality and self-adjoin (`IsPurelyTranscendentalSimple`) |
| 11 | [`PerfectPrelude.lean`](PerfectPrelude.lean) | the perfect-field route: simple-pole coordinate independence, `dCoordGenerates` gates, transport composites |
| 12 | [`KaehlerIntegral.lean`](KaehlerIntegral.lean) | Kähler integrality: `exists_smul_dX_eq`, `ordDifferential_dX_*`, the generic `res_differentialCoeff_D_mul_*` engine |
| 13 | [`PerfectField.lean`](PerfectField.lean) | perfect-field `DCoordGenerates` instances and profile values, `residueTheoremK_placeInfty_clause_X_pow` |
| 14 | [`PerfectResidue.lean`](PerfectResidue.lean) | the second (perfect-field, `ag9b12c_*`) run of the Euler trace and simple-pole computation |
| 15 | [`Core.lean`](Core.lean) | the endgame: `kaehlerResidueFunctionalK` vanishing on generators, the char-free/alg-closed assemblies, the headlines |

## What each slice contains

**1. `EnginePrelude`.** The opening block `FLT.EulerDualBasis` proves Euler's
formula for the trace against a power basis,
$`\mathrm{Tr}(x^{k}/\mathrm{minpoly}'(x)) = 0`$ for $`k \lt d-1`$ and $`= 1`$ for
$`k = d-1`$; this is the computational heart reused later. Then the `Place`
prelude (`ord_add_eq_min`, the comap-of-a-valuation-subring DVR argument), the
$`\mathbb{P}^1`$ setup (`p1PlaceInfty`, the generator sets
`P1PolynomialGenerators` / `P1PrincipalPartGenerators` /
`P1PartialFractionGenerators`, the atom `p1PrincipalPartAtom`), the
finite-residue instances, and the spanning theorem
`p1PartialFractionSpan_eq_top` that reduces everything to generators.

**2–3. `Differential`, `UnitNormalForm`.** The Kähler differential layer: `dX` is
nonzero and spans $`\Omega_{K(X)/K}`$ (`span_dX_eq_top`), its order is computed at
finite places (`ord_differentialCoeff_dX_ofHeightOneSpectrum`) and at infinity
(`ord_placeInfty_X_inv`), and the derivative non-divisibility lemmas
(`not_dvd_derivative_of_ord_eq_one`) set up the simple-pole computation.

**4–5. `DXCoeff`, `DivisorAction`.** The rank-one and ramification–inertia
vocabulary, then the Wronskian bound `natDegree_numDenomWronskian_lt` and its
consequence `ratFuncDXCoeff`, the coefficient of `dX` in `D f`, with its ord
behaviour at finite and infinite places, ending in
`ordDifferentialWellDefined_ratFunc`.

**6–7. `UnitFinite`, `FinitePlaceResidue`.** The unit/regular finiteness
predicates, the explicit bases `kaehlerPolynomialBasis` and
`kaehlerRatFuncBasis`, the ramification–inertia wrappers, and the simple-pole
membership results for the atoms
(`p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace` /
`_placeInfty`), which are what makes the residue computable.

**8. `TraceEngine`.** The longest slice and the core computation. It transports
the local residue at a finite place $`p`$ to `AdjoinRoot p`
(`finitePlaceResidueFieldAlgEquivAdjoinRoot`), evaluates the trace with the Euler
formula (`trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt`), and packages the
two bridge rows the rest of the chain consumes:
`P1FinitePlaceSimplePoleResidueAdjoinRootValue` and
`P1PlaceInftySimplePoleResidueEulerValue`. Its own
`DerivativeRegular` / `LeibnizCore` / `BridgeDischarge` block proves separability
in characteristic $`0`$.

**9–11. `Separating`, `Adjoin`, `PerfectPrelude`.** The separating transcendental
and the self-adjoin/pure-transcendentality facts that let a general curve be
related to $`K(X)`$, and the first perfect-field pass: simple-pole coordinate
independence and the `dCoordGenerates` gates.

**12–14. `KaehlerIntegral`, `PerfectField`, `PerfectResidue`.** The integrality
engine (`exists_smul_dX_eq`, the `ratFuncDXCoeff` ord controls, the generic
`res_differentialCoeff_D_mul_*` lemmas), the perfect-field instances and profile
values, and the second run of the Euler/simple-pole computation under the
`ag9b12c_*` names — the characteristic-$`p`$ counterpart of slice 8.

**15. `Core`.** The endgame. `kaehlerResidueFunctionalK` is checked on the
partial-fraction generators and shown to vanish (`kaehlerResidueFunctionalK_dX_eq_zero`),
the kernel/per-generator engine assembles it, and the char-free and
algebraically-closed routes (`EngineCharFree`, `AlgClosedAnyChar`) meet in the
`ringChar` split `p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main`. The file
closes with `placeInfty_eq_p1PlaceInfty` and the published headline
`trace_localResidue_placeInfty_X_pow_eq_zero`.

## Companion files in this directory

The 15 slices above are the `P1ResidueCore` chain. Five further modules sit here
and are not part of that chain:

* [`Dictionary.lean`](Dictionary.lean) — the $`\mathbb{P}^1`$ place/order dictionary
  (set 3.2a), moved here from `Defs/` by R1.
* [`TwoPlace.lean`](TwoPlace.lean) — the atom-2 two-place cancellation tail and
  headline (set 3.2f).
* [`DivPow.lean`](DivPow.lean) and [`DivPowEnding.lean`](DivPowEnding.lean) — the
  atom-3 `P1Tower` tail and its headline (sets 3.2f–g).
* [`PerfectBase.lean`](PerfectBase.lean) — `residueTheorem_ratFunc_of_perfectField`,
  the perfect-field base case (set 3.2g).

## Background

The pin's four big row-2 files share most of one engine (the master file and the
$`K`$-base file share 572 of 580 declaration names), so the port deduplicated it and
carried it once. The original was ported in four ordered chunks — pin rows
0–144, 145–289, 290–434 and 435–579 — recorded in
[PLAN-P3-2.md](../../../topics/riemannRoch/PLAN-P3-2.md) §§3–3.7; the 15 slices
refine that same declaration order. Residual duplication and scaffolding in the
chain (the `ag9b12c_*` second run, the empty `AxiomAudit` sections, and the
`R1`–`R10` promotion debt) are recorded in
[PLAN-P3-2.md](../../../topics/riemannRoch/PLAN-P3-2.md) §6.1.

## Links

* [math/022 — The global residue theorem](../../../../math/022-global-residue-theorem.md)
  — the mathematics of this directory, §§1–2.
* [PLAN-RECTIFY-DEFS.md](../../../topics/riemannRoch/PLAN-RECTIFY-DEFS.md)
  — the `Defs/` rectification and the R1 split §5.1.
* [PLAN-P3-2.md](../../../topics/riemannRoch/PLAN-P3-2.md) — the row-2 scoping,
  closeout and residual-items checklist.
* [HANDOFF-P3-2.md](../../../topics/riemannRoch/HANDOFF-P3-2.md) — the state of
  row 2 after R1.
