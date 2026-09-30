# Porting: the Riemann–Roch foundation of the curve layer

**Status: phase 1 COMPLETE; phase 2 COMPLETE; phase 3 PLANNED — the bridge
(2026-09-30); the analytic residue block deferred, TBD.** Phase 2 — the canonical
divisor, `hasCanonicalDivisor_of_isCurveOver` (1,723 ln) plus its two
Kähler-differential prerequisites — is landed: `Defs/KaehlerTranscendental.lean` (94)
and `Canonical/HasCanonicalDivisor.lean` (1,559), from
[riemannRoch/WORKORDER-P2-canonical.md](riemannRoch/WORKORDER-P2-canonical.md) with
the mathlib audit [riemannRoch/AUDIT-mathlib-p2.md](riemannRoch/AUDIT-mathlib-p2.md).
Checker **3060 identical / 0 mismatched / 0 missing / 30 own-proof** (3090 checked);
full `lake build` green (4837 jobs); `spec/RiemannRochConsumer.lean` 0 errors; the
headline and both Kähler theorems are `[propext, Classical.choice, Quot.sound]`.
Method record: [../logs/riemann-roch-friction.md](../logs/riemann-roch-friction.md).
Pin `aa2d8b3`; the port's mathlib is `v4.34.0`. This is the port blueprint for the
foundational Riemann–Roch effort, split out of the Deligne–Serre scout because it is
not incidental to that cone. **Phase 1 is fixed — the 14-node genus / index engine;
phase 3 is now the bridge to the canonical-genus / duality API; the analytic residue
block is deferred (TBD)**, and the effort may go beyond Riemann–Roch (Serre duality,
the Weil pairing, `genusFF`).

**What shipped (homes).** `Defs/{Repartitions,AdelicIndex,IsCurveOver,CanonicalDivisor,
RiemannRochRows,PoleDivisorPackage,CanonicalDivisorUniformizer,LocalResidue,WeilOfKaehler,
RegularDifferentials}.lean` (the definition layer, ~1,700 written lines);
`IsCurveOver/SeparatingTranscendental.lean`; `Genus/Index.lean` (1,517);
`Genus/Stichtenoth.lean` (976); `RiemannRoch/Assembly.lean` (736);
`Canonical/WeilDifferential.lean` (474). **Phase 2 adds**
`Defs/KaehlerTranscendental.lean` (94) and `Canonical/HasCanonicalDivisor.lean`
(1,559), so every curve now has a canonical divisor unconditionally
(`PerfectField` + `Algebra.EssFiniteType` + `IsCurveOver`), which is what phase 1's
conditional `HasCanonicalDivisor` interfaces consume. **The algebraic Riemann–Roch
is therefore already in the port**: `exists_weilCanonical_riemannRoch` (288) proves
$`\exists W, \forall D, \ell D - \ell(W-D) = \deg D + 1 - g_{\mathrm{FF}}`$ with the
cohomological genus, on top of `exists_genus_riemannIndex_of_isCurveOver`,
`indexOfSpecialty_eq_of_genusReached` / `…_zero_of_genusReached`,
`omegaSpace_finite_of_genusReached`, and `weilDifferentialRankOne_of_isCurveOver`.
What is missing is not RR but its **canonical-genus / duality form** and the
`ResidueTheorem` input; phase 3 is the bridge, §3. The phase-1 differentials
headline remains **conditional**
(`ResidueTheorem`, `HasCanonicalDivisor`, … kept as hypotheses). Written total
≈5,350 lines (phase 1) + 1,653 (phase 2) against the projections. The
mathlib route audits are
[riemannRoch/AUDIT-mathlib.md](riemannRoch/AUDIT-mathlib.md) (5 substitutes, 78
proof-ingredients, 53 bespoke negatives) and
[riemannRoch/AUDIT-mathlib-p2.md](riemannRoch/AUDIT-mathlib-p2.md) (6 / 111 / 23).

**Scope correction (measured, `riemannRoch/PLAN.md` §1).** The 12,262 raw lines of §0
are the 14 auto-generated `S_` files, which *import the pin's `Definitions/` modules*.
Those definition modules are prerequisites the port does not yet have (no `LSpace`,
`ell`, `repartitions`, `adeleBdd`, `indexOfSpecialty`, `omegaSpace`, `genusFF`,
`HasCanonicalDivisor` under `FLTForHuman/`). `port_advise --with-defs` prices the full
phase-1 scope at **42 files / 1,001 declarations / 15,375 raw lines** (12,262 `S_` +
3,113 definitions), **8,584 removable**, **≈5,700 projected** — not 3,700. Budget
5,000–6,000 written lines across the sets in `riemannRoch/PLAN.md` §2.

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

Out of scope for phase 1 (and now the phase-2 result, or deferred):

- the analytic `ResidueTheorem` / differential-residue block — `residueTheoremK` (8,121),
  `residueTheoremK_ratFunc` (13,170), `tateAgreement` (4,816), `CellDissection`, and the
  two `evalAt` statements — needed by the differentials layer, **deferred, TBD** (§3);
- `hasCanonicalDivisor_of_isCurveOver` (1,723) — **landed in phase 2**;
- the differentials ↔ cusp-forms transport and the per-file applications (phase 4);
- anything beyond Riemann–Roch — Serre duality, the Weil pairing, `genusFF` computations.

Phase 1 deliberately does **not** include the analytic RR-specific node
`functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` (6,257): the engine's own
assemblies already produce the RR formula and Weil duality, and phase 3 re-provides its
**statement** with the bridge proof (§3).

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
  at frontier 541 — the starting point of phase 1. The tree has since grown to 34
  files / 841 declarations with the `Genus/`, `RiemannRoch/` and `Canonical/` homes,
  holding 111 cone nodes at frontier 608.
- The definitions the nodes are phrased with are the pin's
  `Def_AlgebraicCurve_{DivisorClassGroup,AdelicIndex,CanonicalDivisor,Repartitions,IsCurveOver}`
  vocabulary; the definitions work order of the AC effort covers the ported part.
- The **interface nodes** of §1 need `hasCanonicalDivisor_of_isCurveOver` (TBD) and
  `ResidueTheorem` (TBD), and the two engines that consume the genus API — the rank-two
  Tate-module finiteness and the Hecke-algebra dimension results — are consumers, not
  prerequisites.

## 3. The rest of the route

**Phase 2 — the canonical divisor (COMPLETE).** `hasCanonicalDivisor_of_isCurveOver`
(1,723), `Defs/KaehlerTranscendental.lean` (94) and `Canonical/HasCanonicalDivisor.lean`
(1,559).

**Phase 3 — the bridge to the canonical-genus / duality API (PLANNED, 2026-09-30).**
The algebraic RR is already in phase 1: `exists_weilCanonical_riemannRoch` proves
$`\exists W, \forall D, \ell D - \ell(W-D) = \deg D + 1 - g_{\mathrm{FF}}`$, with the
genus-index engine and rank-one behind it (see the header). What the forward cone
consumes and the port does not yet have is the **canonical-genus form** and the
predicate producers:

- `genus_eq_genusFF` (30) and `ell_canonicalDivisor_eq_genus_of_riemannRoch` (13) —
  the only RR nodes the D-S cone cites directly (5 and 8 consumers respectively);
- producers for the already-ported predicates `FunctionFieldRiemannRoch`,
  `WeilDualityAdelic`, `WeilDuality`, `WeilOmegaEllAgrees`, `RiemannIndexFormula`
  (`Defs/RiemannRochRows.lean` has the definitions and the thin assemblies only);
- `finite_and_finrank_regularDifferentials_eq_genus` (220) and its 8 consumers,
  which in the pin reach `functionFieldRiemannRoch_of_isAlgClosed` (6,257).

The bridge is small but it needs the residue theorem: the canonical-divisor
identification (equivalently $`\deg K = 2\gamma - 2`$, $`\ell K = \gamma`$) is exactly
the residue-theorem content. The already-ported
`weilOfKaehler_ne_zero_and_maximal` and
`weilOfKaehler_mem_omegaSpace_of_residueTheorem` supply the pin's `hsup`, and the
already-ported rank-one / index-formula / residue-pairing lemmas plus the pin's
`MirrorAssembly`
(`S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean`
lines 5971–6257, ≈300 lines) give `RiemannIndexFormula` → `WeilOmegaEllAgrees` →
`WeilDualityAdelic` → `WeilDuality` → `FunctionFieldRiemannRoch`. The port keeps the
pin's **statement** `functionFieldRiemannRoch_of_isAlgClosed` and gives it this proof,
so the five `genus_eq_genusFF` consumers and the differentials-genus leaf compile
unchanged and the 6,257-line inlined-engine proof is never transcribed.

Shape and discipline:

- one home, `RiemannRoch/Bridge.lean` (or an extension of `RiemannRoch/Assembly.lean`);
- `ResidueTheorem` stays a **hypothesis**, exactly as in phase 1's
  `exists_linearEquiv_regularDifferentials_omegaSpace_zero`; the bridge lands
  conditionally and is fed when a residue theorem is available;
- `functionFieldRiemannRoch_of_isAlgClosed` is spelled from the pin wrapper, and
  `genus_eq_genusFF` / `ell_canonicalDivisor_eq_genus_of_riemannRoch` verbatim from
  theirs, so the checker's `Thm_AlgebraicCurve_*` map stays mechanical;
- add the small unconditional `constantsAreBase_of_isAlgClosed` (the pin's
  `p0n20_rr_constantsAreBase_of_isAlgClosed`, ≈40 lines) if the D-S application does
  not already supply `ConstantsAreBase`.

**Measured payout (2026-09-30).** On the D-S forward cone the analytic block
`residueTheorem|tateAgreement|residueTrace|CellDissection` is 18 nodes / 46,321
lines; deleting it is `prunable = 24 nodes / 56,383 lines`, and the forward target
falls from 1,897 to 1,874 needed nodes — a **23-node / 56,233-line saving** for a
bridge of ≈300–500 written lines. Deferring the two differential-residue
applications too is 25 / 57,007; the whole analytic complex block (a separate
subject) is 217 / 148,594. The bridge's prerequisites are already ported
(`exists_weilCanonical_riemannRoch`, `weilOfKaehler_ne_zero_and_maximal`,
`weilOfKaehler_mem_omegaSpace_of_residueTheorem`,
`exists_linearEquiv_regularDifferentials_omegaSpace_zero`, plus the rank-one /
index-formula / residue-pairing lemmas), so the only new cost is the bridge file
itself. The weaker RR siblings inside this cone are 3 nodes / 59 lines
(`degree_canonicalDivisor_eq_of_riemannRoch`,
`ell_canonicalDivisor_eq_genus_of_riemannRoch`, `genus_eq_genusFF`), all supplied
by the bridge; the alternative RR *forms* are outside the cone. Working and
reproduction: [../../studies/riemann-roch-strategy.md](../../studies/riemann-roch-strategy.md)
§4.1, §5.1 and
[../../studies/deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md)
§4.2.

**Deferred — the analytic / residue-theorem block (TBD, 2026-09-30).** Phase 3 does
**not** include a proof of `ResidueTheorem` itself. Both routes are large and siloed:
the Tate/K-family one (`residueTheoremK_ratFunc_of_isAlgClosed` 13,170,
`residueTheoremK_of_isAlgClosed` 8,121, `tateAgreement` 4,816,
`residueTraceCompletionCommute` 1,109) and the plain perfect-field one
(`residueTheorem_of_perfectField` 45, `residueTheorem_ratFunc_of_perfectField` 4,340,
the three `trace_localResidue_*` files totalling 21,099, `residueTraceCompletionCommute_v2`
1,109). `port_advise` prices the K-family route at 10 target files / 1,269 declarations
(303 substitutions ≈6,434 lines) and the plain perfect-field route at 12 files / 1,008
declarations (155 substitutions ≈3,160 lines); a **union** run is needed before the
choice is made. The D-S cone's other residue consumers (the differential-residue
statements `exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero`,
`sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials`) may force the K-family,
so this decision waits until those are scoped. `HasCanonicalLocalResidueKStar`'s
construction (the Cohen–Laurent / `Lg37CompletionSection` prelude) is a shared
prerequisite of the bridge, the differentials headline, and both residue routes, and is
currently absent from the port — scope it as its own work item when the block is
picked up.

**Phase 4 — the applications.** The differentials ↔ cusp-forms transport
(`ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`
and the Hecke chain), then the per-file statements grouped by application
(`RationalFunctionField` ord computations, divisor class group / principal divisors,
`Pic0`/Jacobian, `RegularProlongation` residue calculus).

**Beyond RR.** Serre duality, the Weil pairing, `genusFF` — decide scope when the
engine's consumers are known.

**Decisions recorded.** The algebraic-vs-analytic choice is settled for the port: keep
the algebraic engine, bridge to the canonical-genus / duality API, defer the analytic
block. The remaining open decision —
[../../studies/riemann-roch-strategy.md](../../studies/riemann-roch-strategy.md) §4 —
is whether to derive the siloed `ell` / Riemann-inequality / index / canonical-degree
siblings from the engine's RR assembly or keep the pin's proofs; the bridge makes the
derivation candidates cheaper, since they can cite `FunctionFieldRiemannRoch` and
`WeilDuality` directly.

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
