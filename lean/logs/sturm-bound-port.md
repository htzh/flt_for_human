# The Sturm-bound port — measured record

**Scope.** FLT's arithmetic-level Sturm bound and its dependency cone, ported
into `FLTForHuman/ModularForms/`. The cone is six theorem nodes — the two
headlines `ModularForm.sturm_bound_of_isArithmetic` (29 raw lines) and
`ModularForm.sturm_bound_Gamma0` (26), the general vanishing
`eq_zero_of_lt_order_qExpansion_of_isArithmetic` (56), the level-one vanishing
`levelOne_eq_zero_of_lt_order_qExpansion` (82), the group input
`Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj` (31) and the two
analytic `q`-expansion lemmas (54 + 35) — plus the leaf
`CongruenceSubgroup.one_mem_strictPeriods_Gamma0` (18). All eight are
`Theorems/` wrapper targets.

A later addition closes the loop on FLT's *second* use of the norm (open
question 5 of [../../studies/hecke-finiteness-coverage.md](../../studies/hecke-finiteness-coverage.md)
§9): the two **coefficient-form** bounds
`CuspForm.eq_zero_of_qExpansion_coeff_eq_zero` and
`CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero`, which FLT proves in the
`section SturmBound` of `P2M/Sol/S_CuspForm_finiteDimensional_cuspForm.lean`
through `CuspForm.norm` and its ~300-line norm block. They are
re-derived here from `sturm_bound_of_isArithmetic`: the `relIndex = Nat.card`
bridge is `rfl`, `PowerSeries.nat_le_order` turns the coefficient hypothesis into
the order hypothesis, and the `k < 0` case is `ModularForm.isZero_of_neg_weight`.
Their consumer in the same FLT file is `CuspForm.qCoeffTrunc` plus
`FiniteDimensional.of_injective`, and its published output is `solution`, which
the wrapper `Thm_CuspForm_finiteDimensional_cuspForm.lean` turns into
`CuspForm.finiteDimensional_cuspForm` (closure 1, indeg 4, all consumers inside
the endgame). The port carries `qCoeffTrunc` and that corollary in
`SturmBound.lean`. One attribution caveat, measured 2026-09-24: the graph's
`CuspForm.finiteDimensional_Gamma0` node (closure 7, indeg 38) is **not** this
file's `scoped instance` of the same name — it is the sibling
`S_CuspForm_finiteDimensional_Gamma0.lean`, whose `solution` specialises
`CuspForm.finiteDimensional_of_isArithmetic`; all 38 consumers import
`Thm_CuspForm_finiteDimensional_Gamma0`. This file's instance is a duplicate
used only by this file's own `solution`. So the `NormCofactor`
section is not needed in the port and `Reserve/ModularForms/CuspFormNorm.lean` is
left a standalone API; the spec consumer's Zone E now consumes the library
corollary rather than re-proving it.

This is the cheap mandatory sub-cone of the Hecke finiteness targets
([../../studies/hecke-finiteness-coverage.md](../../studies/hecke-finiteness-coverage.md)
§4): `HasIntegralStructure.moduleFinite_heckeAlgebra` (closure 18) → `intLattice_fg`
(9) → `sturm_bound_Gamma0` (7).

## Deliverables

| module | role | lines |
|---|---|---|
| `ModularForms/QExpansionOrder.lean` | `qExpansion_coeff_nat_mul`, `qExpansion_prod` | 106 |
| `ModularForms/SturmBound.lean` | the level-one and general vanishing, the period input, both headlines, the two coefficient-form bounds, `qCoeffTrunc` + the finite-dimensionality corollaries, the weight-2 vanishing corollaries | 446 |
| `spec/SturmConsumer.lean` | Zones A–E wire test | 105 |

## Checker

- `SOURCES` gains the eight wrappers and, for the coefficient-form addendum, the
  `S_CuspForm_finiteDimensional_cuspForm.lean` source and the
  `Thm_CuspForm_finiteDimensional_cuspForm.lean` wrapper; `PORT_FILES` the two
  modules.
- **1,260 identical (69 promoted), 0 mismatched, 0 missing**, 14 own-proof
  exemptions, 1,274 port declarations. The eight Sturm nodes, the two
  coefficient-form bounds, `qCoeffTrunc` and `finiteDimensional_cuspForm` are
  transcribed statements, so none is promoted; the addendum is the +4 over the
  Sturm port's 1,256/1,270. FLT's `scoped instance finiteDimensional_Gamma0` is
  transcribed but invisible to the checker (`DECL_RE` reads no `scoped`).

## Verification

- `timeout 240 lake build`: **4,113 jobs, 0 warnings, no `sorry`**.
- `#print axioms` on all eight Sturm declarations and on the addendum's
  `qCoeffTrunc`/`finiteDimensional_Gamma0`/`finiteDimensional_cuspForm`:
  `[propext, Classical.choice, Quot.sound]`.
- `spec/SturmConsumer.lean`: exit 0, **0 errors, 0 warnings**; Zone D applies
  `sturm_bound_Gamma0` at `Γ₀(2)` and `sturm_bound_of_isArithmetic` at `𝒮ℒ`;
  Zone E consumes `CuspForm.qCoeffTrunc` and the corollary
  `CuspForm.finiteDimensional_cuspForm` (and the instance
  `finiteDimensional_Gamma0`) at arbitrary `N`, `k`, with no `CuspForm.norm`.

## v4.33 (note) → v4.34 (project) drift — proofs only

- `ENat.toNat_coe` → `ENat.toNat_natCast`.
- `if_pos` is deprecated; the `qExpansion_coeff_nat_mul` reindexing uses
  `ite_eq_left`.
- `ModularForm.coe_zero` is deprecated; the final coercion is `simpa`.
- `periodic_comp_ofComplex` is `SlashInvariantFormClass.periodic_comp_ofComplex`
  in v4.34 (an unqualified call resolves to the `UpperHalfPlane` function-
  periodicity version and fails).
- `haveI` for the `FiniteIndex`/`Normal`/`Fact` instances trips
  `linter.style.haveILetI`; the module disables it as the pin's walls are
  load-bearing.

## Dedup and overlap

- The pin's `S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean` carries
  a second private copy of `qExpansion_coeff_nat_mul` (54 lines) beside its own
  proof; the port writes it once in `QExpansionOrder.lean` and imports it.
- `HeckeEigenform.lean` already had a `private`
  `CuspForm.one_mem_strictPeriods_Gamma0` (a one-line twin of the public leaf);
  the new public `CongruenceSubgroup.one_mem_strictPeriods_Gamma0` is the
  wrapper target and is the one the consumer uses. The private twin is left in
  place (removing it would mean editing the paused Hecke face for a one-liner).
- mathlib supplies the level-one Sturm bound (`ModularForm.sturm_bound_levelOne`)
  and the whole analytic API (`qExpansion_mul`, `cuspFunction_mul`,
  `qExpansion_coeff_unique`, `analyticAt_cuspFunction_zero`,
  `PowerSeries.nat_le_order`/`order_le`/`coeff_of_lt_order`); FLT's contribution
  is the reduction from arithmetic level to level one.
- The coefficient-form addendum removes FLT's *other* use of the norm: the
  `NormCofactor` section (pin lines 151–321, 171 lines) plus the `CuspForm.norm`
  definition and zero-set block (lines 7–60, 54 lines) and FLT's own level-one
  induction (lines 72–148, 77 lines) — ≈300 pin lines — are not ported at all,
  and the ported `CuspForm.qCoeffTrunc` +
  `CuspForm.finiteDimensional_{Gamma0,cuspForm}` corollaries consume the two
  coefficient-form bounds instead. This is the answer to
  [../../studies/hecke-finiteness-coverage.md](../../studies/hecke-finiteness-coverage.md)
  §9 question 5.

## Consumers of the pin file's public surface

Measured 2026-09-24 by source grep over the pin plus the graph. The only file
importing `S_CuspForm_finiteDimensional_cuspForm.lean` is its wrapper, and of the
file's public declarations **only `solution` has a consumer**: the wrapper
`Thm_CuspForm_finiteDimensional_cuspForm.lean`, i.e.
`CuspForm.finiteDimensional_cuspForm` (graph closure 1, indeg 4). The other 22
public names are referenced by no other FLT file:

- the two `p2m_export`ed privates `CuspForm.norm`, `CuspForm.norm_eq_zero_iff`;
- `CuspForm.coe_norm_eq_coe_modularFormNorm`;
- `CuspForm.levelOne_eq_zero_of_qExpansion_coeff_eq_zero`;
- the fourteen-declaration `NormCofactor` cluster (`upperRight_one_mem_SL`,
  `slash_upperRightHom_apply`, `mdiff_quotientFunc`,
  `isBoundedAtImInfty_quotientFunc`, `smul_mk_one_eq`, `normCofactor`,
  `coe_norm_eq_mul_normCofactor`, `mdiff_normCofactor`,
  `isBoundedAtImInfty_normCofactor`, `normCofactor_vadd_one`,
  `periodic_normCofactor`, `analyticAt_cuspFunction_normCofactor`,
  `qExpansion_norm_eq_mul`, `qExpansion_norm_coeff_eq_zero`);
- the two coefficient-form bounds and `qCoeffTrunc`;
- the `scoped instance finiteDimensional_Gamma0`.

Three false-positive traps, all checked: `CuspForm.coe_norm_eq_coe_modularFormNorm`
and `CuspForm.norm_eq_zero_iff` recur in `S_ModularForm_S2_Gamma0_2_eq_zero.lean`
as that file's own private copies (its norm-route site), not as references;
`slash_upperRightHom_apply` recurs as a local definition in
`S_CuspForm_exists_qCoeff_eq_ite_dvd_of_prime.lean`; and the 38
`CuspForm.finiteDimensional_Gamma0` references all import
`Thm_CuspForm_finiteDimensional_Gamma0`, i.e. the sibling
`S_CuspForm_finiteDimensional_Gamma0.lean` (`finiteDimensional_of_isArithmetic`),
not this file's instance.

## Pointers

- [../../studies/hecke-finiteness-coverage.md](../../studies/hecke-finiteness-coverage.md)
  — the finiteness routes and the place of this cone in them.
- [../../math/012-sturm-bound.md](../../math/012-sturm-bound.md) — the
  mathematics of the bound and the port map.
- [../../lean/topics/hecke/TOPIC-t10-finite-algebra.md](../../lean/topics/hecke/TOPIC-t10-finite-algebra.md)
  §7 — where the Sturm bound sits in the two finiteness routes.
