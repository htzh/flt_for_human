# Riemann–Roch in the FLT curve layer: which form to port, and what to derive

**Status.** Foundational question, split out of the Deligne–Serre weight-one scout
(§4.1 there) because it is not incidental to that cone. The pin-only counts are
against `anthropics/fermats-last-theorem@aa2d8b3`; the port/frontier numbers are a
measurement of the date and move (frontier 541 at this measurement). Reproduce in §6.

Companions: [flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md)
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
  `residueTheoremK_of_isAlgClosed` (8,121) and the self-contained
  `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` (6,257). The residue
  theorem is fed by `residueTheoremK_ratFunc_of_isAlgClosed` (13,170) and
  `tateAgreement` (4,816) through `residueTraceCompletionCommute` (1,109).
* **adelic / Stichtenoth.** `stichtenothGenusExists` (2,545) →
  `exists_genus_riemannIndex_of_stichtenothGenusExists` (1,632) →
  `weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists` (55):
  genus existence via the Riemann–Roch-space chain (`RiemannGenusReachedAt`,
  `omegaSpace_finite_of_genusReached`), then adelic duality.

The analytic route is larger in isolation, but the residue theorem is reached by the
differentials layer anyway (`exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero`,
`sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials`), so its *marginal* cost
for RR is smaller than its group total.

## 4. Options

**Option A — full RR as the hub.** Port one proof of `FunctionFieldRiemannRoch` and
derive the sibling inequality / index / canonical-degree statements from it. The
derivation candidates are the `ell` / Riemann-inequality group (12 nodes / 4,064
lines), the index equalities (3 / 296), `two_mul_genus_sub_two_eq_of_degree_canonical`
(1,229), `degree_canonicalDivisor_eq_of_riemannRoch` (16) and
`ell_canonicalDivisor_eq_genus_of_riemannRoch` (13) — about 5,600 lines. It does
**not** remove finiteness, `hasCanonicalDivisor_of_isCurveOver` (a hypothesis, not a
consequence), the $`H^1`$ identification, or the $`\Omega`$-dimension result.

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
2. Port **one** full-RR route — and decide which by its *marginal* cost, not its
   group total (the analytic route is largely paid for by the differentials layer;
   the Stichtenoth route is more algebraic).
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
`RiemannGenusReachedAt` / index API. Neither subsumes the other, and the pin has no
analytic producer of genus existence.

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

