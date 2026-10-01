# Porting: the Riemann–Roch foundation of the curve layer

**Status: phase 1 COMPLETE; phase 2 COMPLETE; phase 3.1 COMPLETE; phase 3.2
(row 2, the ℙ¹ residue core) COMPLETE; rows 3.3/3.4 (the Tate agreement and the
trace-completion commutation) COMPLETE; row 3.6 (the K ending) COMPLETE; row 3.7
(the RR assembly against the K ending) COMPLETE, together with the K-route general
`ResidueTheorem` over algebraically closed fields; only row 3.5 (the perfect-field
ending) remains of phase 3 (2026-09-30).** The seven work-item rows of §3 are executed as phases 3.1–3.7, one
dispatch and review gate each; the operative plan is
[riemannRoch/PLAN-P3-1.md](riemannRoch/PLAN-P3-1.md) and phase 3.1 was specified by
[riemannRoch/WORKORDER-P3-1-residue-instance.md](riemannRoch/WORKORDER-P3-1-residue-instance.md).
**Phase 3.1 landed the `HasCanonicalLocalResidueKStar` producer** —
`Defs/PlaceCompletion.lean` (551 ln) and `Defs/CanonicalLocalResidueInstanceV2.lean`
(1,696 ln), 2,247 written against the 2,600 projection — so the K-side hypotheses
can now be discharged unconditionally; the audit is
[riemannRoch/AUDIT-mathlib-p3-1.md](riemannRoch/AUDIT-mathlib-p3-1.md) and the
closeout is PLAN-P3 §1.6.
Phase 2 — the canonical
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
phase 3 is now the residue-theorem block (both pin endings on one shared core),
followed by the RR assembly that transcribes the pin's `MirrorAssembly` against the
K ending; the choice against the PF-plus-new-bridge alternative is recorded in §3**,
and the effort may go beyond Riemann–Roch (Serre duality, the Weil pairing, `genusFF`).

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
`ResidueTheorem` input; phase 3 supplies the residue theorem and then the RR assembly,
§3. The phase-1 differentials headline remains **conditional** until then
(`ResidueTheorem`, `HasCanonicalDivisor`, … kept as hypotheses). Written total
≈5,350 lines (phase 1) + 1,653 (phase 2) against the projections. The
mathlib route audits are
[riemannRoch/AUDIT-mathlib.md](riemannRoch/AUDIT-mathlib.md) (5 substitutes, 78
proof-ingredients, 53 bespoke negatives) and
[riemannRoch/AUDIT-mathlib-p2.md](riemannRoch/AUDIT-mathlib-p2.md) (6 / 111 / 23).

**Scope correction (measured, `riemannRoch/PLAN-P1.md` §1).** The 12,262 raw lines of §0
are the 14 auto-generated `S_` files, which *import the pin's `Definitions/` modules*.
Those definition modules are prerequisites the port does not yet have (no `LSpace`,
`ell`, `repartitions`, `adeleBdd`, `indexOfSpecialty`, `omegaSpace`, `genusFF`,
`HasCanonicalDivisor` under `FLTForHuman/`). `port_advise --with-defs` prices the full
phase-1 scope at **42 files / 1,001 declarations / 15,375 raw lines** (12,262 `S_` +
3,113 definitions), **8,584 removable**, **≈5,700 projected** — not 3,700. Budget
5,000–6,000 written lines across the sets in `riemannRoch/PLAN-P1.md` §2.

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

Out of scope for phase 1 (and now the phase-2 result, or phase 3 / phase 4):

- the analytic `ResidueTheorem` / differential-residue block — `residueTheoremK` (8,121),
  `residueTheoremK_ratFunc` (13,170), `tateAgreement` (4,816), `CellDissection`, and the
  two `evalAt` statements — needed by the differentials layer, **phase 3** (§3);
- `hasCanonicalDivisor_of_isCurveOver` (1,723) — **landed in phase 2**;
- the differentials ↔ cusp-forms transport and the per-file applications (phase 4);
- anything beyond Riemann–Roch — Serre duality, the Weil pairing, `genusFF` computations.

Phase 1 deliberately does **not** include the analytic RR-specific node
`functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` (6,257): the engine's own
assemblies already produce the RR formula and Weil duality, and phase 3 re-provides its
**statement** by transcribing the pin's `MirrorAssembly` against the K ending (§3).

## 1. Phase 1 targets

All 14 were unported at the frontier-541 measurement; phase 1 has since landed them
(header). The `home` column is the file in the port's existing `AlgebraicCurve/` tree.

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
- The **interface nodes** of §1 need `hasCanonicalDivisor_of_isCurveOver` (**landed in
  phase 2**) and `ResidueTheorem` (**phase 3**), and the two engines that consume the  genus API — the rank-two Tate-module finiteness and the Hecke-algebra dimension
  results — are consumers, not prerequisites.

## 3. The rest of the route

**Phase 2 — the canonical divisor (COMPLETE).** `hasCanonicalDivisor_of_isCurveOver`
(1,723), `Defs/KaehlerTranscendental.lean` (94) and `Canonical/HasCanonicalDivisor.lean`
(1,559).

**Phase 3 — the residue-theorem block and the RR ending (2026-09-30; the seven
work-item rows below are executed as phases 3.1–3.7, one dispatch and review gate
each — phase 3.1 in progress).** The
algebraic RR is already in phase 1: `exists_weilCanonical_riemannRoch` proves
$`\exists W, \forall D, \ell D - \ell(W-D) = \deg D + 1 - g_{\mathrm{FF}}`$, with the
genus-index engine and rank-one behind it. What the forward cone consumes and the port
does not yet have is the **canonical-genus form**, and the one input that produces it
is a residue theorem: the canonical-divisor identification (equivalently
$`\deg K = 2\gamma - 2`$, $`\ell K = \gamma`$) *is* the residue-theorem content. The
D-S scout's §4.2 priced the payout — pruning the analytic block saves 23 nodes /
56,233 lines on the forward cone — and
[riemann-roch-strategy.md](../../studies/riemann-roch-strategy.md) §5.4 scouted the two
pin routes and fixed the shape.

*Decision (2026-09-30): port **both endings** on one shared core, and transcribe the
pin's RR assembly against the K ending; do not write a new bridge.* Two endings is
≈2,100 written lines more than the "perfect-field ending plus a new bridge"
alternative, but it adds **no new proof obligation** — every statement and proof is a
pin transcription, and the K ending is exactly what the pin's `MirrorAssembly` already
consumes. The PF-only alternative would restate the five K-citing lemmas over plain
`ResidueTheorem`; §5.4 shows all five are reroutable, but the restatement and the
`kaehlerResidueTerm` identification are the risk, and the routes share so much that
the second ending's marginal cost is small.

*Measured shape (frontier 608; `port_advise`; written = raw − substitutions −
removable-excluding-substituted).* The two routes share one ℙ¹ core, and the pin
duplicated it (`tateAgreement` and `tateAgreement_v2` are byte-identical except the
instance import; the two ℙ¹ base files share 523 of 563 declarations), so the port
writes each piece **once** and then the endings:

| work item | pin raw | written |
|---|---:|---:|
| **3.1** `HasCanonicalLocalResidueKStar` — `Defs/PlaceCompletion.lean` (529) + `Defs/CanonicalLocalResidueInstanceV2.lean` (2,173) | 2,702 | **2,247 — DONE** (551 + 1,696) |
| ℙ¹ core + base case — three `trace_localResidue_*` + `residueTheorem_ratFunc_of_perfectField` + helpers | 29,118 | ≈17,300 — **re-scoped, see below** |
| Tate agreement — `tateAgreement_v2` + `tateTraceCompat_of_isSeparable` + `tateChainRule` + `tateCommFinite` | 13,323 | ≈8,000 |
| trace-completion commutation — `residueTraceCompletionCommute_v2` | 1,109 | ≈525 |
| perfect-field ending — `residueTheorem_of_…residueTraceCompletionCommute` + `residueTheorem_of_perfectField` + helpers | 9,075 | ≈7,050 |
| K ending — `residueTheoremK_ratFunc_of_isAlgClosed` (13,170) + `residueTheoremK_of_isAlgClosed` (8,121) + wrappers, marginal over the shared core | 21,300 | **1,689 — DONE** ([riemannRoch/WORKORDER-P3-6-kend.md](riemannRoch/WORKORDER-P3-6-kend.md) §8) |
| RR assembly — the pin's `MirrorAssembly` (`S_…residueTheoremK….lean` 5971–6257) against the K ending | ≈300 | **694 — DONE** ([riemannRoch/WORKORDER-P3-7-rr-kend.md](riemannRoch/WORKORDER-P3-7-rr-kend.md) §7; plus the K-route general `ResidueTheorem`, `ResidueTheorem/GeneralFromK.lean`) |
| **residue union + instance + RR assembly (two endings)** | | **≈34,000** |

The per-item rows overlap in their shared helpers (they sum to ≈38,000); the union is
≈34,000 — residue union ≈31,000 + instance ≈2,600 + RR assembly ≈400. The rejected
PF-plus-new-bridge plan is ≈31,900 written (PF ≈28,900 + instance ≈2,600 + bridge
≈400). Full working: strategy §5.4; the forward-cone payout: D-S scout §4.2. The
first phase, 3.1 (`HasCanonicalLocalResidueKStar`), is specified by
[riemannRoch/PLAN-P3-1.md](riemannRoch/PLAN-P3-1.md) and
[riemannRoch/WORKORDER-P3-1-residue-instance.md](riemannRoch/WORKORDER-P3-1-residue-instance.md).

**Row 2 re-scope (measured 2026-09-30).** Row 2's ≈17,300 is confirmed —
`port_advise` on `build/pf_core.txt`: 16 `S_` files / 1,175 decls, raw **29,118**,
199 substitutions / 3,378 ln (≈731 ln of that false positives), **9,526 removable**
(197 shared names; once-each union ≈5,105), so ≈16.2k written. The row is **not**
four independent files: the master ℙ¹ file shares **572 of 580 declarations (99%)**
with the K base file of row 6, and the other three share 97% / 69% / 49%; the
master's only "unique" names are the `p1PlaceInfty` twins of row 6's `placeInfty`.
So the ℙ¹ engine is one development written twice, the two endings are small
marginals, and the row must be split into the engine blocks 3.2a–d plus the two
endings. The full measurement, the four proposed boundaries and the reproduce
commands are in [riemannRoch/PLAN-P3-2.md](riemannRoch/PLAN-P3-2.md). **3.2a (the
ℙ¹ place/ord dictionary) is landed and accepted:** `Defs/PlaceEvaluation.lean`,
`Defs/PlaceEvaluationAlgebra.lean`, `Defs/P1Dictionary.lean` (1,633 ln; checker
3316 / 0 / 0; no cascade), with the mathlib audit
[riemannRoch/AUDIT-mathlib-p3-2a.md](riemannRoch/AUDIT-mathlib-p3-2a.md) and the
closeout in PLAN-P3-2 §3.1. The audit found two scope gaps the 91-declaration
measurement missed (the dropped `placeOfPoint` block and `PlaceEvaluationAlgebra`),
so every later 3.2 block is audited before acceptance. **Row 2 is complete
(2026-09-30):** the master ℙ¹ file became the `P1/` chain (R1 definitions round,
[riemannRoch/PLAN-RECTIFY-DEFS.md](riemannRoch/PLAN-RECTIFY-DEFS.md) §5.1), the three
sibling tails landed as `P1/TwoPlace.lean` + `P1/DivPow.lean` (3.2f), and the last two
headlines as `P1/DivPowEnding.lean` + `P1/PerfectBase.lean` (3.2g), once rows 3.3
(Tate agreement) and 3.4 (trace-completion commutation) were ported under `Tate/`.
Checker **4049 / 0 / 0 / 30**. `Defs/` is definitions only; theory lives in the
subject dirs.

Homes and discipline:

- one home **per piece, not per consumer**: `Defs/PlaceCompletion.lean`,
  `Defs/CanonicalLocalResidueInstanceV2.lean`, `Defs/P1ResidueCore.lean` (the shared ℙ¹
  core), `Defs/TateAgreement.lean`, `Defs/ResidueTraceCompletionCommute.lean`,
  `ResidueTheorem/PerfectField.lean`, `ResidueTheorem/KFamily.lean`;
- the RR assembly keeps the pin's statement `functionFieldRiemannRoch_of_isAlgClosed`
  (and `genus_eq_genusFF` / `ell_canonicalDivisor_eq_genus_of_riemannRoch` verbatim), so
  the checker's `Thm_AlgebraicCurve_*` map stays mechanical; the pin's
  `MirrorAssembly` supplies the proof against the K ending, and the 6,257-line
  inlined-engine proof is never transcribed;
- `ResidueTheorem` / `ResidueTheoremK` stay the pin's definitions, exactly as phase 1
  already has them; `ResidueTheorem` remains a hypothesis only where phase 1's
  `exists_linearEquiv_regularDifferentials_omegaSpace_zero` already takes it;
- add the small unconditional `constantsAreBase_of_isAlgClosed` (the pin's
  `p0n20_rr_constantsAreBase_of_isAlgClosed`, ≈40 lines) if the D-S application does
  not already supply `ConstantsAreBase`;
- the `_v2` names are dropped: the port keeps **one name per piece** — see the name
  policy below.

**API surface and name policy.** The block's public API — what downstream (outside the
D-S cone) actually calls — is small. Already in the port: the Props `ResidueTheorem`
and `ResidueTheoremK` and the class `HasCanonicalLocalResidueKStar`, plus
`weilOfKaehler_mem_omegaSpace_of_residueTheorem`. Phase 3 adds:

- `residueTheorem_of_perfectField` → `residueTheorem_functionField_of_smoothOfRelativeDimension_one`
  → the `AlgebraicGeometry.Scheme.TwoAffineOpenCover` residue/Serre-pairing lemmas
  (222 + 166) and `ModularCurve.functionField_residuePackage_degeneracyRoof_of_finiteAlong`
  (168);
- `residueTheorem_of_isAlgClosed` → `ModularCurve.weilKaehlerAgree_modularFunctionFieldC`
  (52), with `weilKaehlerAgree_of_residueTheorem`;
- `residueTheoremK_of_isAlgClosed` → `sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials`
  (142) and the differential-residue statements.

The shared internals — `tateAgreement`/`_v2`, `residueTraceCompletionCommute`/`_v2`,
`residueTheoremK_ratFunc_of_isAlgClosed` / `residueTheorem_ratFunc_of_perfectField`,
the three `trace_localResidue_*` — have no out-of-cone *direct* consumers, but each
family reaches out-of-cone consumers through its own ending (the modularity stack on
the perfect-field side, `sum_eq_zero_…` on the K side), so neither chain is redundant.

**Name policy: one name, drop the `_v2` duplicates.** The `_v2` files are the same
proof as their un-suffixed twins — `tateAgreement` ≡ `tateAgreement_v2` and
`residueTraceCompletionCommute` ≡ `residueTraceCompletionCommute_v2` (byte-identical
but for the instance import), and the two ℙ¹ base files share 523 of 563 declarations —
so the port keeps **one home and one name per piece**, the un-suffixed pin name, and
drops the `_v2` spellings. Two mechanical consequences: the transcribed perfect-field
files take a one-line import/reference edit to the shared name (their statements are
unchanged), and the un-suffixed files are proved against
`Defs/CanonicalLocalResidueInstanceV2`, since the pin's V1 module
(`Def_AlgebraicCurve_CanonicalLocalResidueInstance`) is a 694-line shim with three
private lemmas that imports V2 anyway — so the instance is the same.

*Frontier consequence (accepted, and cheap to repair).* Because `frontier.py` matches
by last name, the two dropped `_v2` pin nodes will still read as *needed* after the
port lands: `prunable` on `FLT.fermatLastTheorem` for the pair is exactly **2 nodes /
5,925 lines** (`tateAgreement_v2` 4,816 + `residueTraceCompletionCommute_v2` 1,109),
with a 3-node rewiring frontier — `fibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates`
(7,954), `trace_localResidue_finitePlace_div_pow_eq_zero` (2,150) and
`residueTheorem_of_perfectField` (45) — which are the three files that take the
one-line reference edit. The honest reading is to put the pair in the tooling's avoid
set when measuring this cone:

```bash
python3 frontier.py --target '<target>' \
  --remove 'tateAgreement_v2' --remove 'residueTraceCompletionCommute_v2'
```

The out-of-cone consumers are unaffected — they call the two producers
(`residueTheorem_of_perfectField`, `residueTheorem_of_isAlgClosed`), not the duplicated
internals. This is the deliberate reversal of the earlier "claim both names" policy:
one name per proof, an exactly-known 5,925-line frontier over-count, and no double
naming downstream.

**Forward-cone payout and route evidence.** Deleting the analytic block
`residueTheorem|tateAgreement|residueTrace|CellDissection` from the D-S forward cone
is `prunable = 24 nodes / 56,383 lines` and takes the forward target from 1,897 to
1,874 needed nodes — saving **23 nodes / 56,233 lines**; deferring the two
differential-residue applications too is 25 / 57,007, and the whole analytic complex
block is 217 / 148,594. On the whole `FLT.fermatLastTheorem` root the same block is
27 / 64,873 with prunable 35 / 95,884 (strategy §5.1). The two pin routes, their
duplication, the five K-citing lemmas and the PF/K fan-out are measured in
[riemann-roch-strategy.md](../../studies/riemann-roch-strategy.md) §4.1 and §5.4, with
the reproduction commands in its §6; the forward-cone restriction is in the D-S scout
§4.2. `HasCanonicalLocalResidueKStar`'s construction (the Cohen–Laurent /
`Lg37CompletionSection` prelude) is the **first work item** of the phase, not a
prerequisite of something deferred.

**Phase 4 — the applications.** The differentials ↔ cusp-forms transport
(`ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`
and the Hecke chain), then the per-file statements grouped by application
(`RationalFunctionField` ord computations, divisor class group / principal divisors,
`Pic0`/Jacobian, `RegularProlongation` residue calculus).

**Beyond RR.** Serre duality, the Weil pairing, `genusFF` — decide scope when the
engine's consumers are known.

**Decisions recorded.**

1. The algebraic-vs-analytic choice is settled: keep the algebraic engine; **port the
   residue-theorem block once** (both endings, one ℙ¹ core, one Tate agreement, one
   trace-completion commutation) and transcribe the pin's RR assembly against the K
   ending. The PF-plus-new-bridge alternative is rejected — see §3.
2. The canonical divisor stays phase 2's construction, not an RR consequence; the RR
   assembly only identifies it with the Weil/Kähler canonical divisor.
3. The weaker RR siblings need no separate "derive vs keep" work item. The port already
   owns the `ell` / index prelude, and the only purely derivable unported siblings
   inside the D-S cone are 59 lines
   (`degree_canonicalDivisor_eq_of_riemannRoch`,
   `ell_canonicalDivisor_eq_genus_of_riemannRoch`, `genus_eq_genusFF`), all supplied by
   the RR assembly; the larger flagged candidates are independent
   (`two_mul_genus_sub_two_eq_of_degree_canonical` is a ramification computation) or
   outside the cone. The derivation-vs-pin question of
   [riemann-roch-strategy.md](../../studies/riemann-roch-strategy.md) §4 is therefore
   closed by the assembly.

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
