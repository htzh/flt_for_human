# Riemann–Roch in the FLT curve layer: which form to port, and what to derive

**Status.** Foundational question, split out of the Deligne–Serre weight-one scout
(§4.1 there) because it is not incidental to that cone. The pin-only counts are
against `anthropics/fermats-last-theorem@aa2d8b3`; the port/frontier numbers are a
measurement of the date and move (frontier 541 at this measurement). Reproduce in §6.

Companions: [../lean/topics/PORTING-RR.md](../lean/topics/PORTING-RR.md) (the port
blueprint that consumes this study; phase 1 is the 14-node genus / index engine),
[flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md)
(the whole curve-layer survey: what FLT builds itself and where mathlib is used),
[flt-ffg-field-theory.md](flt-ffg-field-theory.md) (the field-extension segment),
[deligne-serre-weight-one-scout.md](deligne-serre-weight-one-scout.md) §4.1 (where the
question surfaced), [eichler-shimura-scout.md](eichler-shimura-scout.md) (the
cusp-forms / cohomology transport that consumes the dimension results).

## 0. The question

The curve layer under the Deligne–Serre/FLT cone needs *some form of Riemann–Roch*.
The pin contains several different statements and several different proofs of them,
and the porting question is:

> Which form is minimally needed, and should the sibling statements be derived from
> it — or should the pin's siloed proofs be kept?

Two features make this non-trivial.

* **The full formula is not used everywhere.** Some consumers need only the
  finiteness of the Riemann–Roch space $`\mathrm{LSpace}\,D`$, or only the Riemann
  inequality; the full dimension formula is needed by a smaller set.
* **Some statements are prerequisites of RR, not consequences.** Finiteness is what
  makes $`\ell D = \dim \mathrm{LSpace}\,D`$ meaningful, and the existence of a
  canonical divisor is a hypothesis of every RR statement below. Neither can be
  derived from RR.

## 1. The statements and their logical relations

All definitions are the pin's:

* `LSpace D := riemannRochSpace D` and `ell D := Module.finrank K (LSpace D)`;
* `indexOfSpecialty D := Module.finrank K (adeleSpace K F ⧸ (adeleBdd D ⊔ globalSub K F))`
  — an adelic index, not by definition $`\ell(K-D)`$;
* `genus K F := (Divisor.degree (canonicalDivisorOf ω) + 2).toNat / 2`, given
  `HasCanonicalDivisor`; and `hasCanonicalDivisor_of_isCurveOver` supplies that for a
  curve.

**Three genus notions — only one is "Stichtenoth".** FLT carries three, and they are
easy to conflate:

* `genus K F`, the canonical-divisor (Serre-duality) genus, is the one appearing in the
  RR predicates. Its input `HasCanonicalDivisor` is constructed **directly** by
  `hasCanonicalDivisor_of_isCurveOver` (1,723 lines, from Kähler differentials,
  separating transcendence and DVR theory) and depends on **neither** Stichtenoth **nor**
  the RR formula.
* `genusFF K F := Module.finrank K (H1 (0 : Divisor K F))` is the cohomological genus
  (`Def_AlgebraicCurve_Repartitions.lean`). `genus_eq_genusFF` (30 lines) proves
  `genus = genusFF`, conditional on `FunctionFieldRiemannRoch` and `WeilDualityAdelic`.
* the **Stichtenoth** $`\gamma`$ of `RiemannGenusReachedAt γ D₀` /
  `StichtenothGenusExists` is a genus defined by the maximality of
  $`\deg D - \ell D`$ — Stichtenoth's Riemann–Roch-space construction. It is a *proof
  route* to genus existence and the index formula
  (`exists_genus_riemannIndex_of_isCurveOver` depends on it), not the definition FLT
  uses.

So avoiding Stichtenoth removes the adelic proof of *genus existence and the index
formula*, not the genus definition; the canonical-divisor genus and `genusFF` stand
independently.

The predicates of `Definitions/Def_AlgebraicCurve_RiemannRochRows.lean`:

| predicate | statement |
|---|---|
| `RiemannInequality` | $`\deg D + 1 - g \le \ell D`$ |
| `RiemannIndexFormula` | $`\mathrm{index}(D) = \ell D - (\deg D + 1 - g)`$ |
| `WeilDualityAdelic` | $`\mathrm{index}(D) = \ell(K - D)`$ |
| `WeilDuality` | $`\ell D - (\deg D + 1 - g) = \ell(K - D)`$ |
| `WeilOmegaEllAgrees` | $`\dim \Omega(D) = \ell(K - D)`$ |
| `FunctionFieldRiemannRoch` | $`\ell D - \ell(K - D) = \deg D + 1 - g`$ |

with two thin assemblies in the same file,

```text
functionFieldRiemannRoch_of_riemann_and_duality : WeilDuality → FunctionFieldRiemannRoch
weilDuality_of_riemannIndex_of_adelic            : RiemannIndexFormula → WeilDualityAdelic → WeilDuality
```

Mathematically, over a curve with a chosen canonical divisor and using
$`\ell 0 = 1`$, the full formula gives

* the Riemann inequality, since $`\ell(K-D) \ge 0`$;
* the index formula, once $`\mathrm{index}(D) = \ell(K-D)`$ is known
  (`WeilDualityAdelic`);
* $`\ell K = g`$, from $`D = 0`$;
* $`\deg K = 2g - 2`$, from $`D = K`$;
* $`\dim \Omega(D) = \ell(K-D)`$ once `WeilOmegaEllAgrees` is identified with the
  dual index.

It does **not** give finiteness of `LSpace D`, `HasCanonicalDivisor`, or the
identification of the adelic `indexOfSpecialty` with $`H^1`$. So the logical shape is
a lattice: two prerequisites → one full-RR statement → derived siblings, with the
$`H^1`$ identification orthogonal.

## 2. What the Deligne–Serre cone uses, and how it gets there

The forward cone reaches this family through the differentials ↔ cusp-forms transport
(`studies/deligne-serre-weight-one-scout.md` §4.1):

```text
ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm  (6 dependents)
  → ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm             (5)
  → CuspForm.IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq               (4)
  → CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt (3)
  → DeligneSerre residual representation
```

The dimension inputs are the genus / differentials / $`H^1`$ statements:
`finite_and_finrank_regularDifferentials_eq_genus` ($`\dim \Omega = g`$),
`ModularCurve.two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le`,
`ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF`,
`indexOfSpecialty_eq_finrank_H1`, and the rank-two/eigenspace results
(`ModularCurve.nonempty_basis_fin_two_rationalTateModule_jH`,
`CohCarrier.nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two`).

The **arithmetic** dimension route is independent: `CuspForm.finiteDimensional_Gamma1`,
the $`\Gamma_1`$-integral basis, and the coefficient-ring gate
`DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen`
have **zero RR ancestors**. Sturm / q-expansion and integral-Hecke dimension theory
bypass this layer entirely.

## 3. The pin's RR family is siloed, with thin assemblies

Cone nodes attributable to the RR family (pin-only; `ported` is the frontier
measurement):

| group | nodes | `S_` lines | ported |
|---|---:|---:|---:|
| analytic residue / Tate machinery | 7 | 33,534 | 0 |
| genus existence (Stichtenoth route) | 9 | 8,948 | 0 |
| canonical divisor / genus | 6 | 4,483 | 0 |
| genus / `genusFF` comparisons | 16 | 4,330 | 0 |
| finiteness of `LSpace` | 8 | 4,273 | 1 |
| `ell` / Riemann inequality | 12 | 4,064 | 0 |
| differentials / $`\Omega`$ dimension | 7 | 2,572 | 0 |
| index of speciality / $`H^1`$ | 3 | 296 | 0 |
| full RR / index / duality statements | 4 | 210 | 0 |
| **total** | **72** | **62,710** | **1** |

The structure is the **opposite of a hub**: the full-RR *statements* are four nodes
totalling 210 lines, and almost every other node **cites nothing within the family**
— each carries its own self-contained proof. The only assembly edges are the four
full-RR lemmas plus `finite_and_finrank_regularDifferentials_eq_genus`,
`genus_eq_genusFF`, `exists_genus_riemannIndex_of_isCurveOver`,
`sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable` and
`genusFF_le_of_constantFieldExtension_of_isAlgClosed`.

There are **two routes to the full formula**:

* **analytic.** `functionFieldRiemannRoch_of_isAlgClosed` (39 lines) cites
  `residueTheoremK_of_isAlgClosed` (8,121) and
  `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` (6,257). The residue
  theorem is fed by `residueTheoremK_ratFunc_of_isAlgClosed` (13,170) and
  `tateAgreement` (4,816) through `residueTraceCompletionCommute` (1,109). The
  6,257-line node is self-contained in its **imports** but not in its mathematics:
  it inlines the Stichtenoth pole-divisor package (§3.1). The residue-theorem half
  of this route is opened up in [math/021](../math/021-tate-residue.md).
* **adelic / Stichtenoth.** `stichtenothGenusExists` (2,545) →
  `exists_genus_riemannIndex_of_stichtenothGenusExists` (1,632) →
  `weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists` (55):
  genus existence via the Riemann–Roch-space chain (`RiemannGenusReachedAt`,
  `omegaSpace_finite_of_genusReached`), then adelic duality.

The analytic route is larger in isolation, but the residue theorem is reached by the
differentials layer anyway (`exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero`,
`sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials`), so its *marginal* cost
for RR is smaller than its group total.

### 3.1 What each route assumes, and what it produces

"Self-contained" describes the imports of the 6,257-line analytic node, not its
mathematics. `S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean`
imports only the `Definitions/` modules, but it also **re-states the Stichtenoth
pole-divisor package inside itself**: `PoleDivisorPackage.ofTranscendenceTower`
([line 5409](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean#L5409)),
`stichtenothGenusExists_of_ratFunc_tower`
([line 5739](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean#L5739))
and `RationalFunctionField.stichtenothGenusExists`
([line 5895](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean#L5895))
are proved there. Its assembly is therefore

```text
ResidueTheoremK  --> exists_weilMax_of_residueTheoremK        (line 6059)
                       for ω ≠ 0, weilOfKaehlerK ω has maximal divisor div ω
inline Stichtenoth -> RiemannGenusReachedAt γ D0              (line 6155)
        +-- stichtenothGenus_eq_genus_of_weilMax : γ = g      (line 6128)
        +-- riemannIndexFormula_of_weilMax                     (line 6167)
        +-- weilOmegaEllAgrees -> WeilDualityAdelic -> WeilDuality
                                    -> FunctionFieldRiemannRoch
```

The residue theorem's marginal contribution to RR is exactly the **maximal-divisor
property** `p0n25_wkc_exists_weilMax_of_residueTheoremK`
([line 6059](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean#L6059)):
for every nonzero $`\omega`$, the adelic functional `weilOfKaehlerK ω` is nonzero and
`canonicalDivisorOf ω` is its largest bounding divisor
(`p0n25_wkc_weilOfKaehlerK_omegaSpace_le_canonical`,
[line 6040](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean#L6040);
nonvanishing by the simple-pole/trace probe). With that, the inline engine's
$`\gamma`$ is identified with the canonical genus $`g = (\deg K + 2)/2`$
(`p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax`,
[line 6128](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean#L6128)),
and the last steps are the thin assemblies `weilDuality_of_riemannIndex_of_adelic`
([Def_AlgebraicCurve_RiemannRochRows.lean, line 56](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean#L56))
and `functionFieldRiemannRoch_of_riemann_and_duality`
([line 51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean#L51)).

So the genus existence and the index formula in the analytic route are the **same
pole-divisor argument** as the Stichtenoth route, written a second time; the residue
theorem supplies the canonical-divisor identification and the duality, not the
finiteness. This is why the blueprint excludes the analytic RR node: the Stichtenoth
assembly already produces the formula, and the residue theorem's *marginal* RR value
is the identification of the canonical divisor with `div ω`.

**Canonical divisor: a hypothesis in the statement, on both sides.** Every full-RR
predicate in `Def_AlgebraicCurve_RiemannRochRows.lean` is quantified over
`[IsCurveOver] [HasCanonicalDivisor] [∀ v, v.DCoordGenerates]` and a chosen nonzero
$`\omega`$, and the formula is stated with `canonicalDivisorOf ω`
([lines 44–49](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean#L44-L49)).
The residue-theorem wrapper carries `[HasCanonicalDivisor]` in its binders too,
although the statement of `ResidueTheoremK` itself does not mention a canonical
divisor. Existence is not assumed away: `hasCanonicalDivisor_of_isCurveOver`
([1,723 lines](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean))
constructs it from `PerfectField K` + `Algebra.EssFiniteType K F` + `IsCurveOver K F`
using separating transcendence and Kähler differentials, and its imports contain no RR
and no Stichtenoth, so the dependency is not circular. The Stichtenoth engine, by
contrast, does not consume the hypothesis: `exists_weilCanonical_riemannRoch` constructs
its own $`W`$ and proves RR against $`g_{\mathrm{FF}}`$, and $`\gamma = g`$ is
downstream (`genus_eq_genusFF`,
[Thm_AlgebraicCurve_genus_eq_genusFF.lean, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_genus_eq_genusFF.lean#L7),
conditional on RR + adelic duality). The only phase-1 node that takes
`HasCanonicalDivisor` is `exists_linearEquiv_regularDifferentials_omegaSpace_zero`.

**Riemann existence is nowhere in the RR route.** The residue theorem is over an
arbitrary `[IsAlgClosed K]` and is proved from the adic completion/trace chain, not
from a complex manifold; the pin's one Riemann-surface construction
(`Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex`,
[ℂ-specific](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.lean))
is outside the RR closure, and the RR files import only `Definitions/`. Riemann
existence would be one way to *produce* the places and residue data from the function
field; in this layer those are hypotheses (`HasLocalResidue`,
`HasCanonicalLocalResidueKStar`, `DCoordGenerates`, `HasSeparableResidue`). The
mathematics of the completion/trace chain — Tate's commutator definition of the
residue, the agreement theorem, and how the local identity becomes the global
residue theorem — is opened up in
[math/021](../math/021-tate-residue.md).

## 4. Options

**Option A — full RR as the hub.** Port one proof of `FunctionFieldRiemannRoch` and
derive the sibling inequality / index / canonical-degree statements from it. The
derivation candidates are the `ell` / Riemann-inequality group (12 nodes / 4,064
lines), the index equalities (3 / 296), `two_mul_genus_sub_two_eq_of_degree_canonical`
(1,229), `degree_canonicalDivisor_eq_of_riemannRoch` (16) and
`ell_canonicalDivisor_eq_genus_of_riemannRoch` (13) — about 5,600 lines. It does
**not** remove finiteness, `hasCanonicalDivisor_of_isCurveOver` (a prerequisite
constructed from `IsCurveOver`, not a consequence of RR), the $`H^1`$
identification, or the $`\Omega`$-dimension result.

**Option B — siloed proofs only, as the pin does.** Avoids committing to a full-RR
proof, but the cone genuinely uses the formula
(`two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le`,
`twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma`), so *some* full-RR statement
must exist anyway. B is not viable on its own.

**Option C — hybrid (recommended shape).**

1. Port the **prerequisite core** once: finiteness of `LSpace` (the self-contained
   `finiteDimensional_lSpace`, 1,092, and
   `finiteDimensional_lSpace_zero_of_constantsAreBase`, 2,545),
   `hasCanonicalDivisor_of_isCurveOver` (1,723), the definitions, and the
   $`H^1`$ identification `indexOfSpecialty_eq_finrank_H1` (126).
2. Port **one** full-RR route (§5.3 measures it: the function-field / Stichtenoth
   engine is ~3,700 projected lines, pure algebra, and the API the consumers use; the
   analytic route is larger but still needed for `ResidueTheorem` and the
   differential residues).
3. Derive the inequality / index / canonical-degree siblings from the chosen route
   where the derivation is shorter than the siloed proof. The cheap siloed lemmas
   (`ell_le_degree_add_ellZero`, 354; `ell_le_ell_sub_single_add_deg`, 353) may be
   worth keeping; the larger ones (`ell_sub_ell_le_degree_sub_degree`, 723;
   `two_mul_genus_sub_two_eq_of_degree_canonical`, 1,229) are the derivation
   candidates.
4. Never try to derive finiteness or the canonical divisor from RR.

## 5. Measurement

`port_advise` on the 71 needed nodes of the family (frontier 541): 142 `S_`+`Thm_`
files / 2,780 declarations, **146 substitutions** (79 unique names, 3,838 lines
already in the port), **441 names proved in ≥2 target files** (26,425 removable
lines; 24,140 excluding the substituted names), an **8,225-line unique shared
prelude**, and **≈34,500 projected new lines** (62,514 − 3,838 − 24,140), ≈45% less
than the raw 62,514. The top removable names are the adelic/RR prelude
(`adeleBddQuotSingleEquivResidueField` 1,240, `ell_le_ell_sub_single_add_deg` 1,040,
`finrank_adeleBdd*` 720 + 680, `lSpaceShiftEquiv` 466,
`indexOfSpecialty_eq_of_genusReached` 432, `ell_le_degree_add_ellZero` 410).

So the siloing is expensive (≈45% duplication) regardless of which form is chosen;
a shared prelude pays for itself. The open empirical question is the two routes'
marginal costs, which the same command answers on the route sub-sets.

### 5.1 Prune: is either route avoidable?

`prune.py` answers the complementary question: if a route were replaced, what could be
dropped, and what would have to be rewired. Its criterion is
`prunable(R) = closure(root) \ closure(root with R deleted)` — a node is droppable only
if every path from the root passes through `R` — and it reports the *rewiring frontier*,
the kept nodes whose proofs directly cite a pruned node. Measured at frontier 541 on
`FLT.fermatLastTheorem`:

| removed route | `R` | prunable | rewiring frontier |
|---|---:|---:|---:|
| Stichtenoth / adelic (9 nodes: `stichtenothGenusExists`, `finiteDimensional_lSpace_zero_of_constantsAreBase`, `exists_genus_riemannIndex_of_stichtenothGenusExists`, `RiemannGenusReachedAt.eq_of_ge`, `omegaSpace_finite_of_genusReached`, `indexOfSpecialty_eq_of_genusReached`, `indexOfSpecialty_eq_zero_of_genusReached`, `exists_riemannGenusReachedAt_nsmul_single_…`, `weilDualityAdelic_of_…`) | 11,437 lines | **9 / 11,437** | **70** |
| analytic residue / Tate (all `residueTheorem*`, `tateAgreement`, `residueTrace*`, `CellDissection*`) | 64,873 lines | **35 / 95,884** | **14** |

Reading the frontiers:

* Of the 70 retained nodes citing the Stichtenoth set, **48 have an analytic RR
  statement in their closure** (bridgeable to the analytic route); **22 do not**.
  Categorized, the 22 are **14 that need the `genusReached` / index API**
  (`indexOfSpecialty_eq_of_genusReached`, `omegaSpace_finite_of_genusReached`,
  `RiemannGenusReachedAt.eq_of_ge` — e.g.
  `genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed` 1,204,
  `exists_divisor_degree_eq_one_of_finite` 911,
  `RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq` 545,
  `exists_weilCanonical_riemannRoch` 288), **5 that need the $`\mathbb{P}^1`$
  finiteness** `finiteDimensional_lSpace_zero_of_constantsAreBase`
  (`Divisor.exists_torsion_descent_of_constantFieldExtension` 878,
  `Divisor.finrank_riemannRochSpace_le_…` 510), and **3 thin wrappers**
  (`exists_genus_riemannIndex_of_isCurveOver` 60,
  `weilDifferentialRankOne_of_isCurveOver` 56,
  `stichtenothGenusExists_of_isCurveOver` 51).
* The 14 retained nodes citing the analytic block are the differentials / residue
  layer (`exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero`,
  `sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials`,
  `functionFieldRiemannRoch_of_isAlgClosed`), which the Stichtenoth route does not
  supply.

**The two routes are complementary, not redundant.** The analytic route gives the RR
formula *and* the differentials / residues; Stichtenoth gives *genus existence* and the
`RiemannGenusReachedAt` / index API. Neither subsumes the other. But they are not
independent in the genus/finiteness input: the analytic RR node re-proves the same
pole-divisor package inline (§3.1), so its marginal value for RR is the residue
theorem and the canonical-divisor identification, not a second proof of genus
existence. In particular the prune's "no analytic producer of genus existence" holds
only for a producer *distinct from the pole-divisor argument*; the analytic node
carries a copy of that argument, and porting it would port the duplication, not remove
it.

**The interfaces are thin.** `exists_genus_riemannIndex_of_isCurveOver` (60 lines)
turns `IsCurveOver` + `ConstantsAreBase` into
$`\exists\gamma,\ \forall D,`$ `Finite … ∧ indexOfSpecialty D = ell D − (deg D + 1 − γ)`;
`stichtenothGenusExists_of_isCurveOver` (51) and `weilDifferentialRankOne_of_isCurveOver`
(56) are wrappers. So the APIs can be swapped at ~170 lines; the content behind them
(`stichtenothGenusExists` 2,545 + `exists_genus_riemannIndex_of_stichtenothGenusExists`
1,632) is the genus existence itself.

**Consequence.** Avoid Stichtenoth only if genus existence will be built another way:
the "API needed elsewhere" is not just the RR formula but the genus / index API (14
consumers) plus the $`\mathbb{P}^1`$ finiteness (5). The analytic API, by contrast, is
needed by the differentials layer, so it is worth porting regardless. The cheap hybrid
is: port the analytic route (RR + differentials) and the thin interfaces, reduce
Stichtenoth to a genus-existence provider, and decide whether to port that provider
(≈4,200 lines) or re-derive it.

### 5.2 Who consumes the Stichtenoth genus, and why not the canonical one

The Stichtenoth API has 104 dependents in the D-S cone (`AlgebraicCurve` 51,
`ModularCurve` 46, `DeligneSerre` 3, `CohCarrier` 2, `CuspForm` 2) and lies in 22/49
landmarks. The consumers closest to the forward target are:

* the **rank-two / Tate-module finiteness** results —
  `ModularCurve.moduleFinite_padicInt_tateModule_jOne` and `…_jH`,
  `ModularCurve.nonempty_basis_fin_two_rationalTateModule_jH`,
  `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH`;
* the **Hecke-algebra dimension** results —
  `CuspForm.IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq`,
  `ModularCurve.linearIndependent_rationalHeckeRepOne_of_linearIndependent`,
  `ModularCurve.rationalRankTwoNebentypus_family`;
* the **modular-function-field genus comparisons** —
  `ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd`,
  `ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup`;
* **`Pic0` torsion / finiteness** — `Pic0.finite_torsion_of_isAlgClosed_of_charZero`,
  `Pic0.natCard_torsion_prime_eq_pow_genus`;
* through `weilDifferentialRankOne_of_isCurveOver` (which cites
  `stichtenothGenusExists`), the **Serre-duality layer** —
  `exists_linearEquiv_regularDifferentials_omegaSpace_zero`,
  `exists_weilCanonical_riemannRoch`, and the modular-function-field genus wrappers.

What these consume is **not a genus number** but the API's outputs: finiteness of
`LSpace D`, of the adelic quotient `adeleSpace ⧸ adeleBddPrincipal D`, and of
`omegaSpace D`, together with the **index formula**
$`\mathrm{index}(D) = \ell D - (\deg D + 1 - \gamma)`$. The canonical-divisor genus
supplies only $`g = (\deg K + 2)/2`$ and $`K`$; it gives none of those finiteness
statements, and the identity $`\gamma = g`$ is itself a consequence of RR
(`degree_canonicalDivisor_eq_of_riemannRoch`,
`ell_canonicalDivisor_eq_genus_of_riemannRoch`, `genus_eq_genusFF`). Substituting the
canonical genus for $`\gamma`$ would assume the index formula it is meant to provide —
circular. Stichtenoth is the pin's **engine of finiteness and the index formula**;
`finiteDimensional_lSpace` (self-contained, 1,092 lines) covers only the general-curve
finiteness of `LSpace`, not the adelic quotient or $`\Omega`$.

### 5.3 Which route first: the function-field (Stichtenoth) engine

The measurement supports porting the function-field route first. The genus / index
engine — the nine Stichtenoth nodes of §5.1 plus `indexOfSpecialty_eq_finrank_H1`,
`exists_genus_riemannIndex_of_isCurveOver`, `weilDifferentialRankOne_of_isCurveOver`,
`exists_weilCanonical_riemannRoch` and
`exists_linearEquiv_regularDifferentials_omegaSpace_zero` — is 14 nodes / 12,262 raw
`S_` lines, but `port_advise` projects only **≈3,700 lines**: 1 substitution (6 lines),
155 names shared across ≥2 target files (8,523 removable lines), a 2,458-line unique
prelude. The reduction is the pin's own sibling duplication — the two 2,545-line files
and the 1,346/1,094/1,094/1,093-line files share one prelude — which the port avoids by
writing the shared home once.

Why first:

* It is **pure algebra** (valuations, RR spaces, the adelic index), with no contour
  integrals, and it is the **interface the consumers use**: the 104 dependents of §5.2
  (rank-two Tate-module finiteness, Hecke-algebra dimensions, `genusFF` comparisons,
  `Pic0` torsion, Serre duality) consume the `RiemannGenusReachedAt` / index API, not
  the analytic one.
* It is the **single home for genus existence, adelic quotient finiteness and the
  index formula**. The analytic route's own copies of these (inside the 6,257-line
  `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`) are the same
  pole-divisor argument written a second time (§3.1), so porting the analytic node
  would duplicate the engine rather than replace it.
* It is **cheap** at this measurement: ≈3,700 projected lines against the RR family's
  34,500 and the analytic block's 64,873 raw lines.

**Caveat: the analytic block is not thereby deleted.** The D-S cone still needs
`ResidueTheorem` and the differential residues. The non-analytic `ResidueTheorem`
routes (`residueTheorem_of_perfectField` 45,
`residueTheorem_ratFunc_of_perfectField` 4,340,
`residueTheorem_functionField_of_smoothOfRelativeDimension_one` 76) are **outside the
D-S cone**, and the three analytic-only consumers
(`exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero`,
`sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials`,
`functionFieldRiemannRoch_of_isAlgClosed`) all have `residueTheoremK` / `tateAgreement`
ancestors. What the function-field engine *does* make avoidable is the analytic block's
**RR-specific** node `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`
(6,257), once the formula comes from the Stichtenoth assembly
(`weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists`).

**Recommended order:** prerequisites → function-field genus / index engine (≈3,700) →
the analytic block for `ResidueTheorem` and differential residues only → the
differentials ↔ cusp-forms transport → per-file applications.

## 6. Reproduce

```bash
cd tools/deps

# the RR-family target nodes (pin-only: the forward cone, filtered by §3's predicates)
python3 - <<'PY' > build/rr_family_nodes.txt
import frontier, re
fr = frontier.Frontier()
root = fr.pay.pid('DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen')
cone = fr.closure(root); front = fr.frontier('union')
def group(q):
    if not q.startswith('AlgebraicCurve.'): return None
    s = q[len('AlgebraicCurve.'):]
    if re.search(r'residueTheorem|ResidueTheoremK|tateAgreement|residueTrace', s): return 'analytic'
    if re.search(r'functionFieldRiemannRoch|FunctionFieldRiemannRoch|RiemannIndex|RiemannInequality|WeilDuality|WeilOmegaEllAgrees', s): return 'fullRR'
    if re.search(r'RiemannGenusReachedAt|StichtenothGenusExists|stichtenothGenusExists|exists_genus_riemannIndex|RiemannGenusBounded|omegaSpace_finite_of_genusReached|indexOfSpecialty_eq_of_genusReached|indexOfSpecialty_eq_zero_of_genusReached', s): return 'stichtenoth'
    if re.search(r'finiteDimensional_lSpace|\.finite|FiniteDimensional', s): return 'finite'
    if re.search(r'indexOfSpecialty|indexOfSpecialty_eq_finrank_H1', s): return 'index'
    if re.search(r'HasCanonicalDivisor|hasCanonicalDivisor|canonicalDivisor|canonicalClass|degree_canonical', s): return 'canonical'
    if re.search(r'finite_and_finrank_regularDifferentials|omegaSpace|regularDifferentials|regularDiffs|mem_regularDiffs', s): return 'differentials'
    if re.search(r'\bell_|\bell\b|lSpace|LSpace|mul_mem_lSpace|mem_lSpace|ell_le|ell_sub|ell_eq|ell_map|ell_nsmul', s): return 'ell'
    if re.search(r'genus|genusFF', s): return 'genus'
    return None
print(','.join(fr.pay.qual(i) for i in cone
               if i not in front and group(fr.pay.qual(i))))
PY
python3 port_advise.py --nodes "$(cat build/rr_family_nodes.txt)" --json build/rr_family_advise.json
```

The classification table of §3 is the same loop with `group` kept as the key; the
transport chain and consumer counts of §2 use `frontier.Frontier`'s `cited_by`/`cites`
restricted to the forward cone.

The §5.1 prune experiment:

```bash
cd tools/deps
python3 - <<'PY'
import frontier, prune
fr = frontier.Frontier(); pay = fr.pay
root = pay.pid('FLT.fermatLastTheorem')
stich, _ = pay.ids([
 'AlgebraicCurve.RationalFunctionField.stichtenothGenusExists',
 'AlgebraicCurve.RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase',
 'AlgebraicCurve.exists_genus_riemannIndex_of_stichtenothGenusExists',
 'AlgebraicCurve.exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists',
 'AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge',
 'AlgebraicCurve.omegaSpace_finite_of_genusReached',
 'AlgebraicCurve.indexOfSpecialty_eq_of_genusReached',
 'AlgebraicCurve.indexOfSpecialty_eq_zero_of_genusReached',
 'AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists'])
print('prunable', len(prune.prunable(pay.cites, root, stich)),
      'frontier', len(prune.frontier(pay.cites, root, stich)))
PY
```

The §5.3 function-field engine measurement:

```bash
cd tools/deps
ENGINE='AlgebraicCurve.RationalFunctionField.stichtenothGenusExists,AlgebraicCurve.RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase,AlgebraicCurve.exists_genus_riemannIndex_of_stichtenothGenusExists,AlgebraicCurve.exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists,AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge,AlgebraicCurve.omegaSpace_finite_of_genusReached,AlgebraicCurve.indexOfSpecialty_eq_of_genusReached,AlgebraicCurve.indexOfSpecialty_eq_zero_of_genusReached,AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists,AlgebraicCurve.indexOfSpecialty_eq_finrank_H1,AlgebraicCurve.exists_genus_riemannIndex_of_isCurveOver,AlgebraicCurve.weilDifferentialRankOne_of_isCurveOver,AlgebraicCurve.exists_weilCanonical_riemannRoch,AlgebraicCurve.exists_linearEquiv_regularDifferentials_omegaSpace_zero'
python3 port_advise.py --nodes "$ENGINE" --json build/stich_advise.json
```
