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

This is the cheap mandatory sub-cone of the Hecke finiteness targets
([../../studies/hecke-finiteness-coverage.md](../../studies/hecke-finiteness-coverage.md)
§4): `HasIntegralStructure.moduleFinite_heckeAlgebra` (closure 18) → `intLattice_fg`
(9) → `sturm_bound_Gamma0` (7).

## Deliverables

| module | role | lines |
|---|---|---|
| `ModularForms/QExpansionOrder.lean` | `qExpansion_coeff_nat_mul`, `qExpansion_prod` | 110 |
| `ModularForms/SturmBound.lean` | the level-one and general vanishing, the period input, both headlines | 210 |
| `spec/SturmConsumer.lean` | Zones A–D wire test | 75 |

## Checker

- `SOURCES` gains the eight wrappers; `PORT_FILES` the two modules.
- **1,250 → 1,258 identical (69 promoted), 0 mismatched, 0 missing**, 14
  own-proof exemptions, 1,272 port declarations. All eight are transcribed
  statements, so none is promoted.

## Verification

- `timeout 180 lake build`: **4,112 jobs, 0 warnings, no `sorry`**.
- `#print axioms` on all eight declarations:
  `[propext, Classical.choice, Quot.sound]`.
- `spec/SturmConsumer.lean`: exit 0, **0 errors, 0 warnings**; Zone D applies
  `sturm_bound_Gamma0` at `Γ₀(2)` and `sturm_bound_of_isArithmetic` at `𝒮ℒ`.

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

## Pointers

- [../../studies/hecke-finiteness-coverage.md](../../studies/hecke-finiteness-coverage.md)
  — the finiteness routes and the place of this cone in them.
- [../../math/012-sturm-bound.md](../../math/012-sturm-bound.md) — the
  mathematics of the bound and the port map.
- [../../lean/topics/hecke/TOPIC-t10-finite-algebra.md](../../lean/topics/hecke/TOPIC-t10-finite-algebra.md)
  §7 — where the Sturm bound sits in the two finiteness routes.
