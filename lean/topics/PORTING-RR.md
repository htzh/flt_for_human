# Porting: the Riemann–Roch foundation of the curve layer

**Status: SCOPED, phase 1 not started (2026-09-29).** Pin `aa2d8b3`; the port's mathlib
is `v4.34.0`. This is the port blueprint for the foundational Riemann–Roch effort, split
out of the Deligne–Serre scout because it is not incidental to that cone. **Phase 1 is
fixed — the 14-node genus / index engine; the rest of the route is TBD**, and the effort
may go beyond Riemann–Roch (Serre duality, the Weil pairing, `genusFF`).

Companions:

- [../../studies/riemann-roch-strategy.md](../../studies/riemann-roch-strategy.md) — the
  measurement and the options: the statements and their logical relations, the two
  routes, the prune, the siloing, the 14-node projection, and who consumes what.
- [PORTING-AC.md](PORTING-AC.md) (retired) and [algebraicCurve/](algebraicCurve/) — the
  place / divisor vocabulary phase 1 imports.
- [../../studies/flt-function-field-theory-and-mathlib.md](../../studies/flt-function-field-theory-and-mathlib.md)
  — the whole curve-layer survey (what FLT builds and where mathlib is used).
- [../porting-playbook.md](../porting-playbook.md) — the rules (§2.4 dedup before
  coding, §3.2 one directory per theory, §4 faithfulness).

## 0. Scope

Phase 1 is the **genus / index engine**: Stichtenoth genus existence, the
`RiemannGenusReachedAt` API, the index formula (`indexOfSpecialty`), `Ω`-finiteness, and
the thin assemblies that produce `WeilDualityAdelic` (hence Riemann–Roch) and the Weil
canonical divisor. It is measured at **14 nodes / 12,262 raw `S_` lines**, projecting to
**≈3,700 lines** after dedup (studies §5.3), and it is the interface 104 forward-cone
nodes actually consume.

Out of scope for phase 1, and TBD:

- the analytic `ResidueTheorem` / differential-residue block — `residueTheoremK` (8,121),
  `residueTheoremK_ratFunc` (13,170), `tateAgreement` (4,816), `CellDissection`, and the
  two `evalAt` statements — needed by the differentials layer;
- `hasCanonicalDivisor_of_isCurveOver` (1,723), needed by one phase-1 interface node;
- the differentials ↔ cusp-forms transport and the per-file applications;
- anything beyond Riemann–Roch — Serre duality, the Weil pairing, `genusFF` computations.

Phase 1 deliberately does **not** include the analytic RR-specific node
`functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` (6,257): the engine's own
assemblies already produce the RR formula and Weil duality.

## 1. Phase 1 targets

All 14 are unported at the frontier-541 measurement. The `home` column is the proposed
file in the port's existing `AlgebraicCurve/` tree.

| node | `S_` lines | what it states | home |
|---|---:|---|---|
| `RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase` | 2,545 | `ConstantsAreBase K F → FiniteDimensional K (LSpace 0)` | `Genus/Stichtenoth.lean` |
| `RationalFunctionField.stichtenothGenusExists` | 2,545 | `StichtenothGenusExists K F` for a separable `RatFunc K`-tower curve | `Genus/Stichtenoth.lean` |
| `exists_genus_riemannIndex_of_stichtenothGenusExists` | 1,632 | `StichtenothGenusExists → ∃ γ, ∀ D, Finite (adeleSpace ⧸ adeleBddPrincipal D) ∧ indexOfSpecialty D = ell D − (deg D + 1 − γ)` | `Genus/Stichtenoth.lean` |
| `exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists` | 33 | `RiemannGenusReachedAt γ D₀ → ∃ n, RiemannGenusReachedAt γ (n • single Q 1)` | `Genus/Stichtenoth.lean` |
| `RiemannGenusReachedAt.eq_of_ge` | 1,094 | `RiemannGenusReachedAt γ D₀ → D₀ ≤ D → deg D − ell D = γ − 1` | `Genus/Stichtenoth.lean` |
| `exists_genus_riemannIndex_of_isCurveOver` | 60 | curve-level wrapper: `IsCurveOver + ConstantsAreBase → ∃ γ, ∀ D, …` | `Genus/Stichtenoth.lean` |
| `weilDifferentialRankOne_of_isCurveOver` | 56 | `WeilDifferentialRankOne K F` | `Genus/Stichtenoth.lean` |
| `indexOfSpecialty_eq_of_genusReached` | 1,094 | `RiemannGenusReachedAt γ D₀ → Finite (adeleSpace ⧸ adeleBddPrincipal D) ∧ indexOfSpecialty D = ell D − (deg D + 1 − γ)` | `Genus/Index.lean` |
| `indexOfSpecialty_eq_zero_of_genusReached` | 1,093 | `RiemannGenusReachedAt γ D₀ → indexOfSpecialty D₀ = 0` | `Genus/Index.lean` |
| `omegaSpace_finite_of_genusReached` | 1,346 | `RiemannGenusReachedAt γ D₀ → Module.Finite K (omegaSpace D)` | `Genus/Index.lean` |
| `indexOfSpecialty_eq_finrank_H1` | 126 | `indexOfSpecialty D = Module.finrank K (H1 D)` | `Genus/Index.lean` |
| `weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists` | 55 | `FunctionFieldRiemannRoch → StichtenothGenusExists → WeilDualityAdelic` | `RiemannRoch/Assembly.lean` |
| `exists_weilCanonical_riemannRoch` | 288 | `∃ W, ∀ D, ell D − ell (W − D) = deg D + 1 − genusFF` — RR with the cohomological genus | `RiemannRoch/Assembly.lean` |
| `exists_linearEquiv_regularDifferentials_omegaSpace_zero` | 295 | regular differentials ≃ `omegaSpace 0`; **takes `ResidueTheorem` and `HasCanonicalDivisor` as hypotheses** | `Canonical/WeilDifferential.lean` |
| **total** | **12,262** | | |

The last row is a **conditional interface**: the pin states it with
`(hRT : ResidueTheorem K F)` and `[HasCanonicalDivisor (K := K) (F := F)]`, so it can
land in phase 1 with those hypotheses and be fed later. The other 13 nodes are
unconditional against the ported vocabulary.

## 2. Prerequisites

- **The place / divisor vocabulary is already ported** and must be imported, not
  re-proved: the 17-file, 372-declaration `AlgebraicCurve/` tree
  (`Defs/{Place,PlacesOverDVR,PlaceDictionary,RatFuncPlaces,Divisor,PushPull,Correspondence,SemilinearAut}.lean`,
  `PrincipalDivisors/{RatFuncDegree,Transcendence}.lean`), 77 in-cone pin nodes verified
  at frontier 541.
- The definitions the nodes are phrased with are the pin's
  `Def_AlgebraicCurve_{DivisorClassGroup,AdelicIndex,CanonicalDivisor,Repartitions,IsCurveOver}`
  vocabulary; the definitions work order of the AC effort covers the ported part.
- The **interface nodes** of §1 need `hasCanonicalDivisor_of_isCurveOver` (TBD) and
  `ResidueTheorem` (TBD), and the two engines that consume the genus API — the rank-two
  Tate-module finiteness and the Hecke-algebra dimension results — are consumers, not
  prerequisites.

## 3. The rest of the route (TBD)

Candidate phases, to be decided after phase 1 lands:

- **Phase 2 — the canonical divisor.** `hasCanonicalDivisor_of_isCurveOver` (1,723),
  which unblocks the differentials layer and the `HasCanonicalDivisor` interfaces.
- **Phase 3 — the analytic block.** `residueTheoremK_ratFunc_of_isAlgClosed` (13,170),
  `residueTheoremK_of_isAlgClosed` (8,121), `tateAgreement` (4,816),
  `residueTraceCompletionCommute` (1,109), the `CellDissection` machinery, and the
  differential-residue statements
  (`exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero`,
  `sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials`). The non-analytic
  `ResidueTheorem` routes (`residueTheorem_of_perfectField`,
  `residueTheorem_functionField_of_smoothOfRelativeDimension_one`) are outside the D-S
  cone and may or may not help here.
- **Phase 4 — the applications.** The differentials ↔ cusp-forms transport
  (`ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`
  and the Hecke chain), then the per-file statements grouped by application
  (`RationalFunctionField` ord computations, divisor class group / principal divisors,
  `Pic0`/Jacobian, `RegularProlongation` residue calculus).
- **Beyond RR.** Serre duality, the Weil pairing, `genusFF` — decide scope when the
  engine's consumers are known.

Open decisions, recorded in
[../../studies/riemann-roch-strategy.md](../../studies/riemann-roch-strategy.md) §4:
whether to derive the siloed `ell` / Riemann-inequality / index / canonical-degree
siblings from the engine's RR assembly, or keep the pin's proofs.

## 4. Porting discipline

The playbook in full; the points that matter here:

- **Run `port_advise.py` on the phase-1 slice before transcribing.** The pin's sibling
  files share 8,523 removable lines and a 2,458-line unique prelude (studies §5.3): the
  shared home is written **once**, never `private` per consumer.
- **Statements verbatim from the pin wrappers**, keeping the `AlgebraicCurve.*` names so
  the statement checker's `Thm_AlgebraicCurve_*` map stays mechanical.
- **One home per theory**, inside the existing `AlgebraicCurve/` tree — not a new
  top-level directory, and not `RiemannRoch/` before there is more than the two assembly
  nodes to put there.
- `lake build` green per module, no `sorry`/`admit`/`axiom`, `#print axioms` clean,
  bounded builds (>60 s is a blow-up to bisect).

## 5. Reproduce

```bash
cd tools/deps

# the 14-node engine, pre-port advice (studies §5.3)
export ENGINE='AlgebraicCurve.RationalFunctionField.stichtenothGenusExists,AlgebraicCurve.RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase,AlgebraicCurve.exists_genus_riemannIndex_of_stichtenothGenusExists,AlgebraicCurve.exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists,AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge,AlgebraicCurve.omegaSpace_finite_of_genusReached,AlgebraicCurve.indexOfSpecialty_eq_of_genusReached,AlgebraicCurve.indexOfSpecialty_eq_zero_of_genusReached,AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists,AlgebraicCurve.indexOfSpecialty_eq_finrank_H1,AlgebraicCurve.exists_genus_riemannIndex_of_isCurveOver,AlgebraicCurve.weilDifferentialRankOne_of_isCurveOver,AlgebraicCurve.exists_weilCanonical_riemannRoch,AlgebraicCurve.exists_linearEquiv_regularDifferentials_omegaSpace_zero'
python3 port_advise.py --nodes "$ENGINE" --json build/stich_advise.json

# the frontier split (ported / needed) for the same nodes
python3 - <<'PY'
import frontier, os
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
nodes = os.environ['ENGINE'].split(',')
for n in nodes:
    i = pay.pid(n)
    print('P' if i in front else 'N', fr.lines(i), n)
PY
```

The measurements behind the phase-1 numbers — the RR-family classification, the prune of
the two routes, and the siloing — are reproduced from
[../../studies/riemann-roch-strategy.md](../../studies/riemann-roch-strategy.md) §6.
