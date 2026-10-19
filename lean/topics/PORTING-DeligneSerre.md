# The Deligne–Serre weight-one column — frontier, workflow and plan

The column ports `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` — the weight-one
mod-`ℓ` Galois-representation theorem — from the pin `anthropics/fermats-last-theorem@aa2d8b3`
(Lean `v4.33.1` / mathlib `db584cd6`) into the port library at mathlib `v4.34.0`. This note is
the column's state and plan: §1 what the port contains, §2 the frontier as it stands, §3 the
workflow the manager follows, §4 the shared ground (definitions, promotions, hubs) that is the
manager's own work, §5 the build economy, §6 verification, §7 what remains, §8 reproduce, §9
residuals. Every measurement is the pin's, read through `tools/deps`. The section numbers are
stable: work orders across the column cite §3 for the workflow and §7 for the gates.

The checker reads **10476 identical (774 promoted, 83 renamed), 0 mismatched, 0 missing, 42
own-proof declarations exempted, 294 registered-unwired declarations exempted (10812 checked)**. This column's recent landings: the
`TateFormal`/`TateSlots` definition layer, 9241 → 9304; the weight-4 Tate-slot engine and headline
façade (WORKORDER-F1), 9304 → 9318; the six `tateCurve`/Katz definition modules of WORKORDER-F2,
9318 → 9535 (+217); the `BridgeX` twin/triplet engine and headline façade (WORKORDER-F2),
9535 → 9540 (+5); and the `CohCarrier` Hecke–diamond definition layer
([deligneSerre/TOPIC-cohcarrier-comm-triplet.md](deligneSerre/TOPIC-cohcarrier-comm-triplet.md) §4–§6),
`CohCarrierLevel.lean` + `CohCarrierLower.lean`, 9786 → 9854 (+68) with both modules green,
then its Hecke–diamond commutation triplet engine + three-headline façade (WORKORDER-CT1),
9854 → **9857 (+3)**; and the D-S cone's `HahnSeries.isAlgClosed_rat` leaf, ported as a
**tier-3** mathlib supplement (`RingTheory/HahnSeries/IsAlgClosed.lean`, the generalized
Newton–Puiseux theorem, 67 public declarations, all registered in
[spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md); record:
[logs/hahn-series-alg-closed.md](../logs/hahn-series-alg-closed.md)) — no checker delta, since
the module is unlisted; and the Petersson adjointness of `T_p` on the nebentypus component,
`CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus` (1,230 pin lines, the leaf above the
nebentypus eigenbasis), 9857 → **9877 (+20)**: `peterssonOn` (+3), the fundamental-domain
ground (+16), the tier-1 headline (+1), with its 100-declaration engine tier-3 and registered
(record: [deligneSerre/TOPIC-petersson-hecke-adjointness.md](deligneSerre/TOPIC-petersson-hecke-adjointness.md)); and
the archimedean Casimir **definition layer**, the ground for the arch-derivative subject the
`--include-leaves` shelf shows 78 needed nodes of (33,726 raw `S_` lines): the pin's
`Def_LanglandsTunnell_ArchParam` (33 declarations) and `Def_AutomorphicForm_ArchDerivCasimir` (58,
the whole `archDerivAt`/`archCasimirAt`/`IsArchSmoothAt`/`ArchDir` API, which the port did not have
at all) homed whole at `LanglandsTunnell/ArchParam.lean` and
`AutomorphicForm/Adelic/ArchDerivCasimir.lean`, 9877 → **10104 (+91)** — measured against the tree
as found, which the note's 9877 had already left at 10013 by other columns' landings — and then its
first proof set, the real-place `CasCore` trio
([automorphicForm/WORKORDER-AC2-cascore-trio.md](automorphicForm/WORKORDER-AC2-cascore-trio.md)):
one listed module, `AutomorphicForm/Adelic/ArchCasimir.lean`, whose wire is exactly three headlines,
10104 → **10107 (+3)**, with the 128-declaration shared engine public and registered tier 3
([automorphicForm/TOPIC-arch-casimir.md](automorphicForm/TOPIC-arch-casimir.md),
[automorphicForm/WORKORDER-AC1-defs.md](automorphicForm/WORKORDER-AC1-defs.md)). The **centre-cut
pair** — the vanishing leaf
`AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre`
(902 pin lines) and its sibling
`AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre`
(892 pin lines) — landed together with the checker at **10239 identical**, one headline each (+1
per leaf). The two pin files share a 645-line block, ported once and public as the tier-3 engine
`AutomorphicForm/Adelic/Cusp/CentreCutEngine.lean` (964 lines, 49 declarations, registered); the
façades are `CentreCutVanishing.lean` (64 lines) and `CuspUnrealizable.lean` (59 lines). Records:
[logs/centre-cut-vanishing.md](../logs/centre-cut-vanishing.md),
[logs/centre-cut-sibling.md](../logs/centre-cut-sibling.md); orders:
[automorphicForm/WORKORDER-CMV-centre-cut-vanishing.md](automorphicForm/WORKORDER-CMV-centre-cut-vanishing.md),
[automorphicForm/WORKORDER-CCS-centre-cut-sibling.md](automorphicForm/WORKORDER-CCS-centre-cut-sibling.md).
The **centre-cut fundamental-domain trio** then landed on the shared slab prelude promoted public in
`PeterssonSlabPairing.lean`: the automorphy-transfer node
`AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre`
(325 pin lines, `Adelic/DetNormSlab.lean`) and the two measurable-fundamental-domain twins
`exists_measurableSet_isFundamentalDomain_subset_iUnion_{integralWindowed,centreCut}SiegelSet_of_coversModCentre`
(267/266, one module `Adelic/MeasurableFundamentalDomainCover.lean`); checker **10263 identical**
(+3 headlines, +21 promoted prelude declarations the checker can diff). The fourth `--ready` row,
the 234-line slab-integral bound, is deferred on the missing
`Def_AutomorphicForm_CuspidalSpectrumCarrier.lean` (carry-forward). Record:
[logs/centre-cut-fundamental-domain-trio.md](../logs/centre-cut-fundamental-domain-trio.md); order:
[automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md](automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md).
The **complex archimedean Casimir layer** then landed as Set B wave 0: the missing 196-line
`ArchDerivCasimirComplex` and 381-line `ArchDerivCasimirComplexAPI` definition pair (checker +78),
the 857-line complex engine `AutomorphicForm/Adelic/ArchCasimirComplex.lean` (96 declarations public
tier 3), and its first headline
`AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt` (+1); checker **10342
identical**, 294 registered-unwired exempted. `port_advise` found 0 substitutions and only 43
binder-spelling variants against the real `ArchCasimir.lean`; the two engines are architectural
mirrors (normalized similarity ≈0.38) because the complex half adds `archDelAt`/`archDelBarAt`,
`Del1`/`Del2`, the conjugate transport and `archCasimirBarAtComplex`, so the complex engine was
ported once as a separate tier-3 engine. Record:
[logs/arch-casimir-complex.md](../logs/arch-casimir-complex.md); order:
[automorphicForm/WORKORDER-ACC-arch-casimir-complex.md](automorphicForm/WORKORDER-ACC-arch-casimir-complex.md).
The **continuous norm section** then landed as the first `NumberField.TateGlobal` cut after the
`continuous_ideleNorm` hub: `NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq`
— a continuous monoid hom `ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ` splitting the idèle norm, with trivial
finite part — as the 239-line tier-3 engine `NumberField/TateGlobal/NormSection.lean` (25 public
declarations, at the pin's `FujisakiC3` names; the same block is re-proved in nine sibling `S_`
files) plus the 44-line listed façade `NumberField/TateGlobalNormSection.lean` (one headline,
checker **+1**, **10343 identical**), again with no existing module edited. The node is a graph
leaf with 57 whole-project dependents and lies on the shortest citation path to
`fermatLastTheorem`. Record: [logs/norm-section.md](../logs/norm-section.md); topic and order:
[numberTheory/tateGlobal/TOPIC-norm-section.md](numberTheory/tateGlobal/TOPIC-norm-section.md),
[numberTheory/tateGlobal/WORKORDER-T4-norm-section.md](numberTheory/tateGlobal/WORKORDER-T4-norm-section.md).
**GL₂ strong approximation over ℚ** then landed as the first *theorem* over the `AdelicLevel`
definition layer: `NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat` —
every finite idèle class has a rational representative modulo the integral level — as a
five-module tier-3 engine `NumberField/AdelicLevel/StrongApprox/{Elementary,Membership,Conjugation,Gauss,Approximation}.lean`
(45 public declarations, 1,136 lines) plus the 49-line listed façade
`NumberField/AdelicLevel/StrongApproxRat.lean`. This is the column's first **pure
transcription**: `port_advise` reports **0 substitutions**, so 874 of the 898 pin lines are new
mathematics, and none of the 45 names is re-proved anywhere else in the pin. Checker **+1**,
**10344 identical**; no existing module edited. Record:
[logs/gl2-strong-approximation.md](../logs/gl2-strong-approximation.md); topic and order:
[numberTheory/adelicLevel/TOPIC-gl2-strong-approximation.md](numberTheory/adelicLevel/TOPIC-gl2-strong-approximation.md),
[numberTheory/adelicLevel/WORKORDER-T5-gl2-strong-approximation.md](numberTheory/adelicLevel/WORKORDER-T5-gl2-strong-approximation.md).
The **`EisensteinGeneral` local twisted integral** then landed as the column's first
`EisensteinGeneral` cut: the five ready shelf rows of that namespace are one story — the local
integral of a twisted smooth function at one place — 2,134 raw `S_` lines of which 673 are
duplicate copies. The set opened with its **definition gate**,
`LanglandsTunnell/TateLocalConstantsAt.lean` (the pin's `Def_LanglandsTunnell_TateLocalConstantsAt`
whole, 21 declarations, +21; the five statements all quantify over `higherUnitsAt`), three
promotions out of `private` in `TateGlobal/WeylSmooth.lean` and `WeylShell.lean` (+3), and the
dedup that the gate forced — `WeylSmooth.lean` carried a second `higherUnitsAt` and now imports
the gate (−1). Then **Set A** (the ramified trio): two tier-3 engines
`EisensteinGeneral/LocalTwisted.lean` (527 lines, 25 declarations — the 486-line prelude the pin
writes twice, so 972 → 527 lines) and `LocalRamShells.lean` (265, 9), plus the 354-line listed
façade `LocalRam.lean` with three headlines (**+3**); and **Set B** (the unramified pair): the
single listed module `EisensteinGeneral/LocalUnr.lean` (408 lines, 18 declarations, **+18**),
listed whole with its two `S_` files because its machinery has no other consumer — the first set
in the column where most of the checker delta comes through the promoted-from-pin-private
fallback (702 → 718). Checker **10388 identical**, 0 mismatched / 0 missing. Records:
[logs/eisenstein-local-twisted-ram.md](../logs/eisenstein-local-twisted-ram.md),
[logs/eisenstein-local-twisted-unr.md](../logs/eisenstein-local-twisted-unr.md); topic and
orders: [numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md](numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md),
[numberTheory/eisensteinGeneral/WORKORDER-E1-local-twisted-ram.md](numberTheory/eisensteinGeneral/WORKORDER-E1-local-twisted-ram.md),
[numberTheory/eisensteinGeneral/WORKORDER-E2-local-twisted-unr.md](numberTheory/eisensteinGeneral/WORKORDER-E2-local-twisted-unr.md).
The **finite-adelic integral as an Euler product** then landed as the column's largest
`EisensteinGeneral` cut: `EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod`
(864 pin lines, 58 declarations, 839 net new) — the integral of `∏ᶠ v, h v (x v)` over the finite
adèles equals the Euler product of the normalized local integrals, given summable deviations from
`1`. It is homed as five engines (`EisensteinGeneral/Factorization/{ProductMeasure,Stratum,Measure,Integrability,Tprod}.lean`,
1,035 lines, 56 declarations) plus a 145-line listed façade, and — unlike every other engine in the
column — **all six modules are listed** with the pin `S_` file in `SOURCES`, so all **57**
declarations are statement-checked (**+57**, the column's biggest single wired delta; the
promoted-from-pin-private count moves 718 → 774). The only non-new declaration is a one-line alias
of `TateGlobal.ShellSupport.integralOff`. Checker **10445 identical**, 0 mismatched / 0 missing.
Record: [logs/eisenstein-factorization.md](../logs/eisenstein-factorization.md); topic and order:
[numberTheory/eisensteinGeneral/TOPIC-factorization.md](numberTheory/eisensteinGeneral/TOPIC-factorization.md),
[numberTheory/eisensteinGeneral/WORKORDER-E3-factorization.md](numberTheory/eisensteinGeneral/WORKORDER-E3-factorization.md).
The **nebentypus Hecke bound** `CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen`
(`‖a‖² < (p+1)² p^{k-2}` for `p ∤ M`) then landed as **P3** of the coset/Petersson set — and it
is the column's clearest dedup case: the pin's two `norm_sq` silos share their prelude, so **24
of the silo's 57 declarations were already in the tree** (in `ModularForms/Analytic/NormSqPow.lean`,
namespace `CuspForm.LiNormSq`), and two more (the `p`/`ℓ` variants of `geom_sum_root` and
`qParam_heckeDiag_smul`) are subsumed by the ported copies at the consumers — so the landing is
**≈614 net new lines / 30 declarations**, not 893. One listed module, `ModularForms/Analytic/NormSqLt.lean` (732 lines, namespace
`CuspForm.HeckeBoundGamma1`, importing the sibling's silo and `open`ing it so the pin's proofs
transcribe), checker **+31**, **10476 identical**. Record: [logs/normsq-lt.md](../logs/normsq-lt.md);
order and results:
[deligneSerre/WORKORDER-P3-normsq-lt.md](deligneSerre/WORKORDER-P3-normsq-lt.md); the set's topic
(now complete: P1/P2/P3) is
[deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md](deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md).
Each wired delta is exactly its new public surface, 0 mismatched / 0 missing. The 9542 → 9569 (+27) step is
the `NumberField.AdelicHeight` definition gate, the manager's own ground for the adelic-modulus
round
([numberTheory/adelicModulus/TOPIC-adelic-modulus.md](numberTheory/adelicModulus/TOPIC-adelic-modulus.md)),
not this column's; the remaining growth since the note's earlier figures (9569 → 9786) is other
columns' landings; the column's own history lives in `../logs/` and the work orders.

Companions:

- [../../math/019-deligne-serre-weight-one.md](../../math/019-deligne-serre-weight-one.md)
  — the mathematics: the theorem, the lifting, the assembly from residual data.
- [../../studies/deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md)
  — the effort measurement, the subject clusters and the two gates.
- [porting-playbook.md](../porting-playbook.md) — the rules; §2.1–§2.6 (planning),
  §3.1–§3.7 (execution, sets, the build ladder), §4 (faithfulness), §5 (sharing).
- The q-expansion layer's planning records:
  [functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md](functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md)
  and its successors
  [functionFieldGeneration/TOPIC-qexp-successors.md](functionFieldGeneration/TOPIC-qexp-successors.md),
  [functionFieldGeneration/TOPIC-qexp-successors-2.md](functionFieldGeneration/TOPIC-qexp-successors-2.md).
- Adjacent columns: [PORTING-Hecke.md](PORTING-Hecke.md), [PORTING-Level.md](PORTING-Level.md).
- The `NumberField` rows the target closure reaches but this column does not cut: the
  `continuous_ideleNorm` hub's port plan and landing record (the frontier's most connected
  `NumberField` leaf, 15 of the closure's nodes directly above it) is
  [numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md](numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md),
  and the next cut of the same family — the continuous splitting of the idèle norm — is
  [numberTheory/tateGlobal/TOPIC-norm-section.md](numberTheory/tateGlobal/TOPIC-norm-section.md)
  with [logs/norm-section.md](../logs/norm-section.md). The first *theorem* over the
  `AdelicLevel` layer, GL₂ strong approximation over ℚ, is
  [numberTheory/adelicLevel/TOPIC-gl2-strong-approximation.md](numberTheory/adelicLevel/TOPIC-gl2-strong-approximation.md)
  with [logs/gl2-strong-approximation.md](../logs/gl2-strong-approximation.md); its definition
  layer is [PORTING-AutomorphicForm.md](PORTING-AutomorphicForm.md). The `EisensteinGeneral`
  local twisted integral — the local factor computation of the Godement–Eisenstein series, five
  ready rows plus its definition gate — is
  [numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md](numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md)
  with [logs/eisenstein-local-twisted-ram.md](../logs/eisenstein-local-twisted-ram.md) and
  [logs/eisenstein-local-twisted-unr.md](../logs/eisenstein-local-twisted-unr.md); its global
  counterpart, the Euler-product factorization of the finite-adelic integral, is
  [numberTheory/eisensteinGeneral/TOPIC-factorization.md](numberTheory/eisensteinGeneral/TOPIC-factorization.md)
  with [logs/eisenstein-factorization.md](../logs/eisenstein-factorization.md).
- The mathematics of the Petersson adjointness proved in this column:
  [../../math/030-petersson-adjointness-of-hecke.md](../../math/030-petersson-adjointness-of-hecke.md).
  The coset/Petersson set's own topic — now complete, P1 the definition layer, P2 the newform
  eigenvalue, P3 the nebentypus bound — is
  [deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md](deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md),
  with [logs/normsq-lt.md](../logs/normsq-lt.md) for P3.
- The `WeierstrassCurve` ready shelf, its scoping and its set orders:
  [deligneSerre/TOPIC-weierstrass-ready-shelf.md](deligneSerre/TOPIC-weierstrass-ready-shelf.md).
- The `CohCarrier` Hecke–diamond commutativity triplet — the three `--include-leaves`
  rows, the 914-line development they share, and the two unported definition modules both
  pin files sit under:
  [deligneSerre/TOPIC-cohcarrier-comm-triplet.md](deligneSerre/TOPIC-cohcarrier-comm-triplet.md).
- The Γ₁/Nebentypus successor pair — the two `CuspForm` rows the shelf once showed, which are the
  lifting column's, not this column's:
  [deligneSerre/WORKORDER-S8-nebentypus.md](deligneSerre/WORKORDER-S8-nebentypus.md).
- The `ModularCurve` ready shelf's first cuts — the level-`N` function field and the modular
  polynomial:
  [modularCurve/TOPIC-levelN-and-modular-polynomial.md](modularCurve/TOPIC-levelN-and-modular-polynomial.md),
  [modularCurve/WORKORDER-A-levelN-field.md](modularCurve/WORKORDER-A-levelN-field.md),
  [modularCurve/WORKORDER-B1-phi-rows.md](modularCurve/WORKORDER-B1-phi-rows.md),
  [modularCurve/WORKORDER-B2-fibre-two.md](modularCurve/WORKORDER-B2-fibre-two.md),
  [modularCurve/WORKORDER-C2-x1-function-field.md](modularCurve/WORKORDER-C2-x1-function-field.md),
  [modularCurve/WORKORDER-D1-petersson.md](modularCurve/WORKORDER-D1-petersson.md),
  [modularCurve/WORKORDER-D2-period-map.md](modularCurve/WORKORDER-D2-period-map.md),
  [modularCurve/WORKORDER-E-levelN-qexp-bridge.md](modularCurve/WORKORDER-E-levelN-qexp-bridge.md).
- The weight-4 Tate-slot group the frontier's `--include-leaves` view once showed as fourteen
  `ModularCurve` leaves at ~1650 lines: its mathematics, dedup and port structure are
  [modularCurve/TOPIC-tate-slots-weight-four.md](modularCurve/TOPIC-tate-slots-weight-four.md), and
  the shared-engine order is
  [modularCurve/WORKORDER-F1-tate-slots-engine.md](modularCurve/WORKORDER-F1-tate-slots-engine.md).
- The `tateCurve` twin pair and the triplet lurking beside it — the three rows F1's step-6 re-read
  put on the shelf, five near-identical files sharing one `BridgeX` development:
  [modularCurve/TOPIC-tate-curve-twins.md](modularCurve/TOPIC-tate-curve-twins.md) and
  [modularCurve/WORKORDER-F2-tate-curve-twins.md](modularCurve/WORKORDER-F2-tate-curve-twins.md).
- The archimedean Iwasawa analytic core — the 13 `AutomorphicForm.{Complex,Real}Iwasawa` rows of
  §7's Gate 1 at the infinite place, ported as two deduped engine/façade waves:
  [automorphicForm/TOPIC-iwasawa-analytic-core.md](automorphicForm/TOPIC-iwasawa-analytic-core.md),
  its mathematics
  [../../math/028-iwasawa-decomposition-and-archimedean-estimates.md](../../math/028-iwasawa-decomposition-and-archimedean-estimates.md),
  and the orders
  [automorphicForm/WORKORDER-I1-complex-engine.md](automorphicForm/WORKORDER-I1-complex-engine.md),
  [automorphicForm/WORKORDER-I2-complex-successors.md](automorphicForm/WORKORDER-I2-complex-successors.md),
  [automorphicForm/WORKORDER-I3-real-engine.md](automorphicForm/WORKORDER-I3-real-engine.md).
- The archimedean `𝔰𝔩₂` / Casimir calculus — the other archimedean subject at the same places, and
  the one the `--include-leaves` reading prices highest after the ray-class hub: the definition
  layer, the 78-node / 33,726-line demand behind it, and the real-place `CasCore` trio that is its
  first proof set:
  [automorphicForm/TOPIC-arch-casimir.md](automorphicForm/TOPIC-arch-casimir.md),
  [automorphicForm/WORKORDER-AC1-defs.md](automorphicForm/WORKORDER-AC1-defs.md),
  [automorphicForm/WORKORDER-AC2-cascore-trio.md](automorphicForm/WORKORDER-AC2-cascore-trio.md).

## 1. What the port contains

The port holds the column's unconditional half, the `ModularCurve` q-expansion, function-field and
Frobenius layers, the analytic and period layer, the Tate-slots definition and weight-4 layers, and
the definition and hub ground the rest builds on. The dated records are in `../logs/` and, for the
`ModularCurve` sets, in the work order that produced them.

**The unconditional slice.** Everything that does not depend on the two automorphic gates — the
weight-one mod-`ℓ` lifting half and the assembly half. It takes the residual family as a
hypothesis, so it is stated without the ray-class input and without the automorphic layer; the
two gates attach to a fixed interface and can be ported later without reworking it. The consumer
wire test is `spec/DeligneSerreConsumer.lean`; the record is
[../logs/deligne-serre-port.md](../logs/deligne-serre-port.md) and the friction/promotion ledger
is [../logs/deligne-serre-friction.md](../logs/deligne-serre-friction.md).

**The coset-space Petersson layer, and the level-prime eigenvalue.** The definition layer
`ModularForms/Analytic/PeterssonCoset.lean` — `Nice`, the raw pairing `pair`, the slash
transfer and the relative-index machinery, 56 declarations, checker +56 — and the silo
`ModularForms/Analytic/NormSqPow.lean`, the level-prime bound `‖a‖² = ℓ^(k-1)` for a form new at
`ℓ`, 72 declarations, checker +72; the 18 statement-identical declarations the pin wrote twice
were moved out of the `PeterssonHecke` engine into the definition layer. Record:
[deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md](deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md),
order: [deligneSerre/WORKORDER-P2-normsq.md](deligneSerre/WORKORDER-P2-normsq.md).

**The `ModularCurve` q-expansion layer.** The Γ₀-rationality pair, the `X_H` relative-degree
bound, the JOneES finrank/index and residue-field rows, the Deuring-reduction /
constant-extension / Atkin–Lehner successors, and the `isAlgClosed` finrank bound, in
`functionFieldGeneration/SET-R-*`, `X1/*`, `XH/*` and `WeightOne/*`. The planning records are the
`TOPIC-qexp-*` notes.

**The `X_H`/`X₁` function field and Frobenius.** The `q`-expansion Frobenius inputs headline
`qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental`, appended to
`ModularCurve/Frobenius/QExpModL.lean` — the module already held its private machinery and its
`Fr* Fr_* = ℓ` sibling, so the append needed no new file and no promotion. The ten landed leaf
rows (`qExpansion_div_mem_laurentBaseChange_xHFunctionField`,
`isIntegral_jqNModC_of_modularPolynomialData`, `exists_gamma0_qExpansion_div_eq_jqNModC`,
`eisenstein4_cube_sub_mk_sq`, `diffQExp_x1FunctionFieldBar_injective`,
`modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero`,
`modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0`, `closure_elemSet_eq_top`,
`isCurveOver_x1FunctionFieldBar`, `essFiniteType_x1FunctionFieldBar`) sit in
`ModularCurve/X1/{QExpansionDiv,IntegralityJqNModC,Structure,FunctionFieldInclusion}.lean`, on the
definition modules `ModularCurve/Defs/{HeckeDifferential,SL2Elementary}.lean`,
`ModularCurve/X0/FunctionFieldFull.lean` and `AlgebraicCurve/Differential/PushPull.lean`, each
ported whole. The eleventh row is deferred (§7). Record:
[modularCurve/WORKORDER-C2-x1-function-field.md](modularCurve/WORKORDER-C2-x1-function-field.md).

**The analytic and period layer.** The pin's four `Def_AutomorphicForm_*` modules whole —
hyperbolic measure, fundamental-domain volume, the Siegel set cover and the Γ₀ fundamental set, in
`AutomorphicForm/`, keeping the pin's `FLT.*` namespaces — and the Petersson pairing
`ModularCurve/Analytic/PeterssonPairing.lean`, whose two headlines make the period pairing
perfect. The period map of a finite-index subgroup is
`ModularCurve/Period/{PeriodLatticeSpan,PeriodLatticeBoundary,ParabolicHoms,QExpansionDerivative}.lean`,
and the pin's `Def_ModularCurve_QExpansionDiff.lean` node is whole across
`Period/QExpansionDiff.lean` and `AlgebraicCurve/Differential/TraceDiff.lean`. Records:
[modularCurve/WORKORDER-D1-petersson.md](modularCurve/WORKORDER-D1-petersson.md),
[modularCurve/WORKORDER-D2-period-map.md](modularCurve/WORKORDER-D2-period-map.md).

**The level-`N` function field and the `Φ_N` rows.** `ModularCurve/LevelN/FunctionField.lean` is
the pin's 53-line definition module whole (`wp`, `fricke`, `jAnalytic`, `generators`, `ring`,
`jGen` and the membership lemmas), and `LevelN/{Prelude,FieldGalois,Places}.lean` hold the eight
rows — `isDomain_ring`, `slash_eq_self_of_mem_Gamma_of_mul_eq`,
`exists_monoidHom_algEquiv_fixedField_eq_adjoin`, `exists_algHom_laurentSeries_qExpansion`,
`exists_place_ord_neg_forall_smul_eq`, `exists_place_ord_sub_pos_forall_smul_eq`,
`exists_place_analyticOrderAt_eq_mul_ord`, `valuation_apply_smul_le_one_of_tendsto_div_smul`. The
six `Φ_N` rows sit in
`ModularCurve/ModularPolynomial{LeadingCoeff,UniquenessIrreducible,StarBank,FibreTwo}.lean`, on the
wave's `Defs/{ClassicalModularPolynomials,FibrePoly}.lean` (`phiTwo`/`phiThree`/`intFibre`, the
public `fibrePoly`, the `ReduceModBivar` block), and the level-`N` `q`-expansion bridge is the
deduped twin development in `ModularCurve/LevelN/QExpBridge.lean`. Records:
[modularCurve/WORKORDER-A-levelN-field.md](modularCurve/WORKORDER-A-levelN-field.md),
[modularCurve/WORKORDER-B1-phi-rows.md](modularCurve/WORKORDER-B1-phi-rows.md),
[modularCurve/WORKORDER-B2-fibre-two.md](modularCurve/WORKORDER-B2-fibre-two.md),
[modularCurve/WORKORDER-E-levelN-qexp-bridge.md](modularCurve/WORKORDER-E-levelN-qexp-bridge.md).

**The `WeierstrassCurve` layer.** The whole good-reduction definition chain —
`WeierstrassCurve/Reduction/{Point,TorsionIntegral,ReduceHom,ZeroComponent}.lean`, the pin's four
`Def_*` modules ported whole — and the eight ready-shelf nodes it gated: the exceptional
automorphisms in characteristics 2 and 3, full level structure and the division field, reduction
surjectivity on the prime-to-`p` torsion, the inertia-equivariant reduction, and the
Vélu-quotient `j`-map. Its scoping and set orders are
[deligneSerre/TOPIC-weierstrass-ready-shelf.md](deligneSerre/TOPIC-weierstrass-ready-shelf.md).

**The `TateFormal`/`TateSlots` definition layer.** The two pin `Definitions/` modules the
weight-4 slot cluster's fourteen `S_ModularCurve_*` leaves all import, ported whole (playbook
§2.3) at `ModularCurve/Defs/TateFormal.lean` (26 declarations — `tateB`, `tateA4`/`tateA6`,
`eisenstein6`, the `tatePowerSeries`/`tateLaurent` curves with their ellipticity instances, and
`laurentOfInt`) and `ModularCurve/Defs/TateSlots.lean` (37 declarations — `tateUnivX`/`tateUnivY`,
`slotFamily`/`slotSubst`, `tateBase`, the non-toric/toric and Vélu slot sets). The pin's
downstream consumers (`Def_ModularCurve_TatePoint`, `…_TateVeluRing`, `…_TateOrigin`,
`…_ShimuraGenerator`, `Theorems/Thm_ModularCurve_Delta_tatePowerSeries`) name the same
declarations, so the whole node is homed rather than only the block the `S_` files reach. Neither
pin module has a `Theorems/` wrapper, so both verify by name against their `Definitions/` files;
neither has a `private` declaration, so no promotion is owed. Both are appended last to
`SOURCES` / `PORT_FILES`.

**The weight-4 Tate-slot engine and headline façade.** The fourteen `S_ModularCurve_*` leaves the
frontier's `--include-leaves` view showed at ~1650 lines are one 1,671-net-line development written
fourteen times (23,094 raw lines, 112 shared names, ≈20,810 removable); it is ported once as the
tier-3 engine `ModularCurve/TateSlots/{Convergence,SlotCoeff}.lean` (537 + 1,293 lines, 38 + 81
public declarations, declaration parity exact, no build-time blow-up) and the fourteen public
headlines in the tier-1 façade `ModularCurve/TateSlots/CoefficientFormulas.lean`. The engine's fourteeen
kernels are public as `ModularCurve.TateSlots.<name>` with the pin `Theorems/` wrapper binders;
the façade states the wrappers verbatim. The engine stays tier 3 and is recorded in
[spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md); the façade is the checker wire (delta +14).
No existing module was edited. Mathematics, measurement and structure:
[modularCurve/TOPIC-tate-slots-weight-four.md](modularCurve/TOPIC-tate-slots-weight-four.md); the
order and its results:
[modularCurve/WORKORDER-F1-tate-slots-engine.md](modularCurve/WORKORDER-F1-tate-slots-engine.md).

**The `tateCurve` `BridgeX` layer and its definition chain.** The three `tateCurve` rows F1's
step-6 re-read put on the shelf are a **twin pair and a triplet** — five near-identical pin `S_`
files sharing one 1,338-line `ModularCurve.BridgeX` development (47 declarations in all five, 23
more in the pair only, 5 headlines). Ported once as the tier-3 engine
`ModularCurve/TateCurve/{Bridge,Slot}.lean` (839 + 674 lines, 50 + 25 public declarations, no
build-time blow-up), with the five public headlines in the tier-1 façade
`ModularCurve/TateCurve/QPow.lean`. Its six unported `Definitions/` modules are homed whole at
`Algebra/LaurentSeriesXAdic.lean`, `TateCurve/{QSeries,PointSeries}.lean`,
`ModularForms/KatzLevelOne.lean` and `ModularCurve/Defs/{KatzLevelP,KatzLevelPCusps}.lean` (217
declarations, checker +217). The engine stays tier 3 and is recorded in
[spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md). Mathematics and structure:
[modularCurve/TOPIC-tate-curve-twins.md](modularCurve/TOPIC-tate-curve-twins.md); the order and its
results:
[modularCurve/WORKORDER-F2-tate-curve-twins.md](modularCurve/WORKORDER-F2-tate-curve-twins.md).

**The archimedean Iwasawa analytic core.** The two gates of §7 take their input at the infinite
place from 13 `AutomorphicForm.{Complex,Real}Iwasawa` rows — the decomposition's compact factor and
the Fourier decay of its radial length. They are ported as the pre-gate wave the gates attach to:
the pin `Def_AutomorphicForm_ComplexIwasawa` (4 declarations) and the shared generic Fourier bound
(`M4aP3B.FourierDecay`, 2 declarations) homed as the definition layer, seven tier-3 engines
(`AutomorphicForm/Iwasawa/{Complex,Real}/{Core,Decay,UniformDecay,Continuation}.lean`, 5,818 lines)
holding the deduped development (10,378 raw `S_` lines → 5,256 net), and the two subject façades
`AutomorphicForm/Iwasawa/{Complex,Real}/Estimates.lean` (13 headlines) as the checker wire. Checker
9654 → 9673, 0 mismatched / 0 missing; the cone's `needed` falls 1,617 → 1,604 nodes and no Iwasawa
row remains in the demand. Topic, mathematics and orders: the companion bullet above.

**The centre-cut pair.** The vanishing leaf
`AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre`
rules out a continuous automorphic function supported on a centre-cut Siegel cover: if
`c ≤ 0 < d₁ < d₂` and the finite union of translates of `centreCutSiegelSet F c u d₁ d₂` covers
the centre, then `φ = 0`. Its sibling
`AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre` rules out an
arithmetic genuine cuspidal realization on the same cover. The two pin `S_` files share a
645-line / 47-declaration block byte-for-byte; it is ported once as the tier-3 engine
`AutomorphicForm/Adelic/Cusp/CentreCutEngine.lean` (964 lines, 49 public declarations, each with
`-- pin:` provenance), and the two façades `CentreCutVanishing.lean` (64 lines) and
`CuspUnrealizable.lean` (59 lines) hold one headline each. The first pass's 902-line module was
reduced when the sibling was cut; the engine's general `no_function_of_ne_zero` serves both
headlines, so the sibling's pin-specific `no_realization_of_ne_zero` is not ported. Checker
**10239 identical** (one headline each, +1 per leaf). Records:
[logs/centre-cut-vanishing.md](../logs/centre-cut-vanishing.md),
[logs/centre-cut-sibling.md](../logs/centre-cut-sibling.md); orders:
[automorphicForm/WORKORDER-CMV-centre-cut-vanishing.md](automorphicForm/WORKORDER-CMV-centre-cut-vanishing.md),
[automorphicForm/WORKORDER-CCS-centre-cut-sibling.md](automorphicForm/WORKORDER-CCS-centre-cut-sibling.md).

**The centre-cut fundamental-domain trio.** The next ready rows were the automorphy-transfer node
`AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre`
(325 pin lines) and the two twins
`AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_{integralWindowed,centreCut}SiegelSet_of_coversModCentre`
(267/266). They need the same fundamental-domain/slab prelude that `PeterssonSlabPairing.lean`
already carried `private`; the prelude was promoted once there (20 declarations, plus the 107-line
`exists_measurableSet_isFundamentalDomain_subset` and the 36/23-line `setLIntegral_fd_le_sum_mul` /
`cover_of_forall`), and the façades `Adelic/DetNormSlab.lean` and
`Adelic/MeasurableFundamentalDomainCover.lean` hold the three headlines. Checker **10263
identical** (+3 headlines, +21 promoted prelude declarations). The fourth `--ready` row, the
234-line `CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_…_ample`, is **not
actually ready**: it needs the unported 288-line
`Def_AutomorphicForm_CuspidalSpectrumCarrier.lean`, recorded in
[CARRY-FORWARD.md](../CARRY-FORWARD.md). Record:
[logs/centre-cut-fundamental-domain-trio.md](../logs/centre-cut-fundamental-domain-trio.md); order:
[automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md](automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md).

**The complex archimedean Casimir layer.** Set B of the arch-Casimir subject was blocked on two
unported pin `Definitions/` modules: `Def_AutomorphicForm_ArchDerivCasimirComplex` (196 lines / 32
declarations) and `…ComplexAPI` (381 / 46). Both were homed whole at
`AutomorphicForm/Adelic/ArchDerivCasimirComplex.lean` and `…ComplexAPI.lean` (checker +78), and the
first complex headline
`AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt` was ported as the 857-line
engine `AutomorphicForm/Adelic/ArchCasimirComplex.lean` (96 public declarations, tier 3,
registered; +1 headline). The engine is the complex mirror of the real `ArchCasimir.lean`: the
types are `ℂ` rather than `ℝ`, and the complex half adds the holomorphic/anti-holomorphic Del
operators, the conjugate transport and the second Casimir. `port_advise` reports 0 substitutions
and 43 binder-spelling variants; a normalized comparison is only ≈0.38 similar, so the
architectural duplication did not justify a generic `RCLike` rewrite of the landed real engine.
The remaining complex headlines are `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex`
(1,227) and `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` (133), then the 35-file
complex fan. Records:
[logs/arch-casimir-complex.md](../logs/arch-casimir-complex.md); order:
[automorphicForm/WORKORDER-ACC-arch-casimir-complex.md](automorphicForm/WORKORDER-ACC-arch-casimir-complex.md).

**The shared ground that edits existing modules.** The `ValuationSubring` residue block in
`NumberTheory/ValuationAtPlace.lean`; the `Gamma0Integral` promotion and its duplicate-block
collapse; the resolution of the `normFormulaAlong_of_elliptic` co-import collision (one public
copy; the character-free copy is named `normFormulaAlong_of_elliptic_cf`); the C1 append into
`ModularCurve/Frobenius/QExpModL.lean` — the one landing that edits a module rather than adds
one; and the wave that homed the shelf's definition layer, which also deduped `fibrePoly` out of
`Degree/PhiData.lean` into `Defs/FibrePoly.lean` at its public pin name. Registered in
[CARRY-FORWARD.md](../CARRY-FORWARD.md).

## 2. The frontier

```bash
cd tools/deps
# the canonical D-S cone read: --ds excludes the prunable complex-analytic subject
# (deligneSerre/PRUNABLE-complex-analytic.md) and --include-leaves shows the demand's
# graph leaves, which --ready and --hops drop
python3 frontier.py --ds --include-leaves --rank-by silo --top 0
python3 frontier.py --ds --rank-by silo --ready --top 0   # the ready shelf alone
```

The table below is the **default** (unexcluded, `union`) reading, kept for reference;
the `--ds` commands above are the ones to use for "what is left".

| quantity | value |
|---|---:|
| target closure | 2,308 nodes / 1,089,430 raw `S_` lines |
| frontier `F` (union) | 901 nodes / 517,169 |
| `F` inside the cone | 660 nodes / 412,941 |
| `needed` (unported demand, `F` terminal) | 1,635 nodes / 673,014 |
| `needed` (literal closure-minus-ported) | 1,648 nodes / 676,489 |
| **ready to port** (all premises available) | **67 nodes** |

The ready shelf by top-level namespace: `AlgebraicCurve` 24, `ModularCurve` 13, `CuspForm` 8,
`NumberField` 5, `AutomorphicForm` 4, `ModularForm` 3, `PeriodPair` 2, `LanglandsTunnell` 2,
`CohCarrier` 2, `EisensteinGeneral` 2, `CuspFormClass` 2. `WeierstrassCurve` no longer appears —
all eight shelf nodes are ported. The `ModularCurve` part is **13 nodes**, the column's own shelf:

| node | silo lines |
|---|---:|
| `ModularCurve.tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst` | 1,343 |
| `ModularCurve.tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd` | 1,343 |
| `ModularCurve.phiIrreducible_all` | 434 |
| `ModularCurve.exists_exp_eq_of_invariant_ne_zero_isParabolicHom` | 410 |
| `ModularCurve.SerreImage.contains_SL2` | 390 |
| `ModularCurve.qTwist_nonToricPoint_of_pow_eq_one` | 185 |
| `ModularCurve.LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand` | 165 |
| `ModularCurve.j_tateLaurent` | 144 |
| `ModularCurve.exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq` | 102 |
| `ModularCurve.ModularPolynomialData.natDegree_coeff_le` | 62 |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (mispriced, §7) | 36 |
| `ModularCurve.hasCanonicalDivisor_x1FunctionFieldBar` | 22 |
| `ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag` | 14 |

**The step-6 effect of the last landing.** WORKORDER-F1's engine and façade took the fourteen
~1650-line leaves off the demand and put **three successors** on the shelf, all reading the
slot-substitution engine it homed: the two `tateCurve_…_nonToricPoint_…` rows at 1,343 silo lines
each and `qTwist_nonToricPoint_of_pow_eq_one` (185). The first two are the largest `ModularCurve`
rows and the natural next cut; `phiIrreducible_all` (434) remains the standing candidate behind
them. The other ten rows predate the Tate-slot round. The `CuspForm`, `AlgebraicCurve`,
`PeriodPair`, `ModularForm` and `CohCarrier` rows are reached by the target closure but are not
`ModularCurve` rows, and are not this column's to cut; the `NumberField.TateGlobal` rows are cut
through their own topic notes (the `continuous_ideleNorm` hub and, now, the continuous norm
section — §1), and their remaining shelf rows are the two
`exists_norm_apply_eq_ideleNorm_rpow` cousins (§7).

**The two `tateCurve_…_nonToricPoint_…` rows are exact twins, and must be cut as one.**
`S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean` and its `_pointY_…_snd`
sibling are both 1,343 lines and differ by **8 diff lines**; normalized at the namespace stem, the
only difference is the final `solution` — `… = (nonToricPoint F p c j).1 := BridgeX.pointX_slot …`
against `… = (nonToricPoint F p c j).2 := BridgeX.pointY_slot …`. The 69 other declarations
(1,311 lines) are byte-identical at the same line numbers. `port_plan` reads 2,686 raw → **1,325
net new** / 72 groups, 0 substitutions. The order is the WORKORDER-E shape: write the shared
development once (`private`) and derive both public headlines from the two `BridgeX` conjuncts;
the checker delta is exactly +2.

**The readings differ, and the conservative one is the one to plan from.** The table above is the
default `union` name scan. `--frontier sources` (no name scan) gives `F` 756 nodes / 444,955, a
`needed` of 1,704 nodes / 708,235, and 61 ready candidates. The gap is the last-name blindness of
§9: a pin node whose last name matches a ported declaration of another namespace is priced as
ported. `port_advise` and `port_plan` never walk imports either, so an unported premise outside
the target files is invisible to them; both frontier readings stay in the loop.

**One ready row is mispriced.** `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` is
listed at 36 silo lines, but its premise
`ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` is unported and the `CuspForm` twin
cannot substitute — so it is a whole node, deferred to its own order (§7, §9). Under
`--frontier sources` the same query prices it at 10 needed nodes / 5,172 raw `S_` lines.

**A prunable subject sits on this shelf and is not this column's.** The complex-analytic
Jacobian / path-integral / Abel–Jacobi / `CellDissection` subject is in the target *closure*
(44 nodes / 30,570 lines on 2026-10-14) but is a second supply to a step the D-S route already
reaches by the differentials ↔ cusp-forms transport, so it is prunable — 205 nodes / 107,257
lines, a 186-node / 91,105-line saving on that tree. Read the frontier with it excluded —
`frontier.py --ds` is the one-flag form ([deligneSerre/PRUNABLE-complex-analytic.md](deligneSerre/PRUNABLE-complex-analytic.md),
`tools/deps/ds_prunable.py`) — or its leaves read as D-S work; its plan is RR phase 3
([algebraicCurve/TOPIC-cell-dissection.md](algebraicCurve/TOPIC-cell-dissection.md)).

**Not schedulable from this list.** The two gates of §7 remain in the unported demand but are not
ready; they must not be scheduled off a ready shelf.

## 3. The workflow

This is the loop the column runs. Steps 1–4 are the manager's; step 5 is the subagents'; step 6
closes.

**1. Read the frontier.** The canonical command above is `--ds --include-leaves` (`--ds` excludes
the prunable complex-analytic subject, `--include-leaves` surfaces the demand's graph leaves);
`--ready` narrows to the nodes whose whole demand is
themselves — every premise is already ported, so only the node's own proof is missing — and
`--rank-by silo` orders them by the raw `S_` lines of their **whole demand**, i.e. by how much
mathematics stands behind them, not by the size of their own file. This is demand, and it is the
only list to plan from. The `hops`/`used_by` columns choose *within* a cluster; they do not choose
the cluster. `--include-leaves` additionally surfaces the demand's graph leaves (no premises, so
they never reach `F`); that view prices a leaf at its whole file, so a cluster of near-identical
leaves — the Tate-slot fourteen were one — must be deduped by `port_advise` before it is believed.

**2. Cut a cluster by mathematics.** 3–6 ready nodes that tell one story in one layer — the
level-`N` place/valuation cluster, the `AlgebraicCurve` curve-and-divisor cluster, the `CuspForm`
Nebentypus cluster. Namespace and pin file are *not* the cut: one namespace can span several
layers, which is why the q-expansion head ran as several sets. The test is whether one sentence
states the cluster's subject without an "and".

**3. Scope the cluster with the tools.**

* `port_advise.py --target <node> … --json build/<cluster>_advise.json` — the substitution table
  (declarations already byte-identical in the port: import, never re-prove), the port-`private`
  rows (promote or re-derive), the **shared blocks** the target files have in common (the dedup:
  write once), the near-duplicate / binder-only rows, and the *suspect* type-only `def` matches the
  parser cannot judge (read both copies before applying any).
* `port_plan.py --json …` — the budget: raw lines, once-only dedup, boilerplate, **net new math
  lines**, declaration groups.
* `build_ladder.py --edit <host>` on **every** candidate host — the cascade each edit will force,
  in modules and lines.
* **Hand-check the import list.** `--ready` and `--with-defs` do not see import-only definitions:
  every `Definitions/Def_*.lean` a target `S_` file imports must be checked by hand against the
  port, declaration by declaration, and the target's proof's own definition uses checked too
  (`fltdata.proof_defs`) — a stub import can hide a live dependency. See §4(a).

**4. The manager does the shared ground — this is the point of the split.** Before any subagent
runs:

* **(a) the definition layer, whole node.** Home the pin `Def_*` module the cluster imports **in
  full** — every declaration with a consumer, not only the block the cluster reaches (playbook
  §2.3) — at the natural *theory* home rather than a new `Def_`-named file; promote out of
  `private` whatever the cluster must name. Checked against the pin, wiring appended to
  `SOURCES`/`PORT_FILES`.
* **(b) promotions and every other hub edit.** Any edit to an existing module is the manager's,
  not a subagent's: it is the only thing that re-elaborates the cone, so it is done once,
  deliberately, with the price known.
* **(c) dedup the scoping turned up.** A hub that carries the same private block twice, a copy
  that a promotion makes redundant — fold it into the same pass, because the wave is already
  being paid and deferring it pays nothing.

Each such edit is priced, applied, built at tier 1, checker-run, and followed by **one** wave
build; then the touched files freeze and no subagent may edit them.

**5. Divide into sets; dispatch and review in series.** One set = one mathematical story = one
module or a small group = one subagent = one work order. Sets run **one at a time**: parallel
`lake build`s contend on Lake's lock and cross-invalidate, so the second one looks like a blow-up
and both are slower. The one safe overlap is two sets with no shared prelude and disjoint
namespaces: they may write their modules in parallel if the shared checker wiring stays with the
manager and every build is serialized; the review order is still one set at a time. The manager
writes the work order, dispatches, and then reviews the tree *itself* before writing the next
order.

*Work-order template* (playbook §3.3): scope and what is explicitly not this set; pin sources
(`Theorems/` wrapper for the statement, `P2M/Sol/S_` for the proof); deliverable modules and the
public/`private` split; what is already in the port and must be reused; route with recorded
negatives; risks; the build-discipline block verbatim; the stop conditions; the report shape.
Every order carries the **hub prohibition**: a subagent that needs a `private` helper re-derives
it locally and reports it; one that believes a promotion is genuinely required **stops and
reports** with the declaration, host and `build_ladder.py --edit` price. The manager decides.

*Review checklist* after each set: checker `0 mismatched / 0 missing` with the `identical` delta
reconciled against the new public surface; tier 1 green and 0 warnings; no `sorry`/`admit`, no bare
`import Mathlib`; `#print axioms` on every headline `[propext, Classical.choice, Quot.sound]`; `git
status` showing only the set's files. The checker's mutation sensitivity is the instrument's own
test (`python3 spec/check_flt_statements.py --selftest`), run when the checker changes — not a
per-set manual mutation.

**6. Close out, then re-read the frontier.** Re-run step 1: the landed nodes leave the shelf and
their successors appear. Record the outcome in the work order and in the cluster's topic, name
the successors the landing unblocked, and cut the next cluster.

## 4. The shared ground

**(a) Definitions first, whole node, and check them by hand.** Nothing can be *stated* before the
pin `Def_*` modules the cluster imports exist in the port. They are leaves — cheap to build, no
cascade — and they are invisible to `frontier.py`'s readiness test, so the list is built by
reading each target `S_` file's `import` block and walking its `Definitions/Def_*.lean`
declarations against the port. **Home the whole module** (playbook §2.3): the closure the
cluster's proof reaches is the floor and the order, not the scope — the rest has consumers
elsewhere and `frontier.py` prices by file. A declaration with no consumer anywhere is the only
exclusion, and it needs a `grep -c` (excluding the pin's global `attribute [-simp]` preludes and
`p2m_export` rows) to justify. The partial-port failure this guards against is on the record:
`Def_ModularCurve_QExpansionDiff.lean` had its `thetaL` half ported against a set's needs while its
`QExpansionDiff` and `TraceDiff` halves, with no consumer in that set but pin consumers elsewhere,
were not — and `port_advise`'s per-target view did not show it.

**(b) `private` is a build tool, not a statement about mathematics.** A helper stays `private`
when it only adapts another theory, or is generic glue a consumer can re-derive in a few lines; it
is promoted when it carries mathematics another theory will state or reuse. A promoted
pin-`private` helper is renamed at the pin's name, and the checker verifies it through its
dotted-name fallback. The counterexample to avoid: a "promotion" of a declaration whose pin
statement is not the port's — the parser's type-only `def` matches are exactly this.

**(c) A hub edit is a wave, and the wave is the same price whether or not you also clean up in
it.** So: price it, do all of it at once, and only then freeze. A subagent never opens the
question; it reports and stops.

## 5. The build economy

* edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
  cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
  the low cap is what finds it. Diagnose it (`set_option diagnostics true` /
  `trace.Meta.synthInstance true` on that one declaration, in a scratch copy), fix the inference,
  re-run. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`. The edit loop
  writes no `.olean` and builds no dependent;
* `flock .lake/flt_build.lock timeout 300 lake build <module>` when a file is done (writes the
  `.olean`, builds dependencies, never dependents);
* **no bare whole-tree `lake build`** while a set is in flight; one at a milestone, with
  permission;
* every `lake build` serialized and bounded.

The wave that a hub edit forces can exceed the 300 s bound on a real compute
(`ModularPolynomialE4Cube` alone is ~280 s). That is not a blow-up: the tell is CPU time — high
user CPU with a timeout is real work and the target list should be re-run with a larger wall
bound; ~0 CPU wall-time is another agent's lock. A genuine blow-up is bisected, never re-run with
a bigger heartbeat cap.

## 6. Verification

```bash
cd lean
timeout 300 python3 spec/check_flt_statements.py        # 10476 identical / 0 / 0 / 42 own
flock .lake/flt_build.lock timeout 900 lake build       # the milestone build
timeout 180 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
python3 tools/deps/unwired_register.py --check          # tier-3 surface current
```

plus a `#print axioms` probe over the set's headlines and a `grep` sweep for
`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/heartbeat overrides. The checker's
`identical` delta must equal the new public surface exactly; anything else is a bug. Each work
order records its own numbers, measured on the tree it leaves, not copied from this note. The
checker's mutation sensitivity lives in the instrument:
`python3 spec/check_flt_statements.py --selftest`.

The checker's exemption list is keyed by **dotted name, never bare last name**: a bare
`"correspondence"` silently exempted two live declarations alongside its namesake, and dotting it
to `"AlgebraicCurve.Pic0.correspondence"` moved the count by +2 verified / −2 exemptions. That is
the same last-name blindness `frontier.py` shows on the `ModularForm`/`CuspForm` rename pairs
(§2, §9).

## 7. What remains

The unconditional slice stops where the automorphic input begins. Two gates remain, both on one
subject (the automorphic/adèlic `GL₂` layer, scout §2):

* **Gate 1 — the Rankin-type second-moment bound.**
  `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen`
  (764 needed nodes, 271 own `S_` lines), feeding
  `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd`
  (11 needed, 478 own).
* **Gate 2 — coefficient-ring finiteness by upper density.**
  `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen`
  (765 needed nodes, 248 own `S_` lines), feeding
  `DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le`
  (13 needed, 283 own).

Both reach the shared ray-class node `M4aTorus` (12,126 raw `S_` lines) by exactly one route —
`NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one` — and use only its continuation
conjunct, discarding the functional equation. Budget by the `S_`-line column, not by node count:
most of those nodes are self-contained against mathlib and show cost 1 in `frontier.py`. The
**converse cone** (`exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace`) is a separate
subject and a separate effort.

**The ready shelf** of §2 is 67 nodes, of which 13 are `ModularCurve` and the column's own. The
step-6 re-read after WORKORDER-F1 put the two `tateCurve_…_nonToricPoint_…` rows (1,343 each) and
`qTwist_nonToricPoint_of_pow_eq_one` (185) on it; the first two are the natural next cut and are
**exact twins** — one 1,325-net-line development with two headlines, the WORKORDER-E shape (§2) —
with `phiIrreducible_all` (434) behind them once a definition-layer check says so. The level-`N`
and `Φ_N` subjects and the level-`N` `q`-expansion bridge have landed, and their successor
`ModularCurve.LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand` (165) is on the shelf.

The **centre-cut pair** and the **fundamental-domain trio** have landed
([../logs/centre-cut-vanishing.md](../logs/centre-cut-vanishing.md),
[../logs/centre-cut-sibling.md](../logs/centre-cut-sibling.md),
[../logs/centre-cut-fundamental-domain-trio.md](../logs/centre-cut-fundamental-domain-trio.md)):
the pair shares the tier-3 `Cusp/CentreCutEngine.lean`, the trio shares the promoted slab prelude in
`PeterssonSlabPairing.lean`. The 234-line
`CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_…_ample` is deferred on the
unported `Def_AutomorphicForm_CuspidalSpectrumCarrier.lean`; the larger `coversModCentre` silo
(`exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre`, 3,038 lines)
is still behind the unit-factorizable chain recorded in [CARRY-FORWARD.md](../CARRY-FORWARD.md).

The **complex archimedean Casimir** wave has landed its definition pair and first headline
([../logs/arch-casimir-complex.md](../logs/arch-casimir-complex.md)); the next leaves of that
subject are `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` (1,227) and the
133-line `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne`, then the 35-file complex
fan of [TOPIC-arch-casimir.md](TOPIC-arch-casimir.md) §5 Set C.

The **Γ₁/Nebentypus pair** the shelf once showed at its head — the two `CuspForm` rows — is the
**lifting column's**, not this column's, and has landed there as
[deligneSerre/WORKORDER-S8-nebentypus.md](deligneSerre/WORKORDER-S8-nebentypus.md)
(`ModularForms/HeckeNebentypus{Existence,Fricke}.lean`, checker +2, deduped onto the promoted
`CuspForm.HeckeEigenNebentypus` API).

The **continuous norm section** has landed ([../logs/norm-section.md](../logs/norm-section.md)):
the tier-3 engine `NumberField/TateGlobal/NormSection.lean` now homes the 25 declarations nine
pin `S_` files re-prove, so the family's remaining cuts import it rather than copy it. The next
two rows of that family are the cousins
`NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow` (236 silo lines, 42 project
dependents) and `RatIdele.exists_norm_apply_eq_ideleNorm_rpow` (312, 7) — "the absolute value of
a continuous idèle-class character is a power of the norm", 496 net new lines for the pair, with
an `expUnit`/`expUnit_*` block they share with each other. They are their own order:
[numberTheory/tateGlobal/TOPIC-norm-section.md](numberTheory/tateGlobal/TOPIC-norm-section.md)
§5, §7.

**GL₂ strong approximation over ℚ** has landed too ([../logs/gl2-strong-approximation.md](../logs/gl2-strong-approximation.md)):
the five-module engine `NumberField/AdelicLevel/StrongApprox/` puts the `AdelicLevel` vocabulary
to work for the first time (874 of 898 pin lines were new, 0 substitutions). Its successors are
the level-`N` variant `NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat`
(397 pin lines; demand now 3 nodes / ≈720 raw `S_` lines), then
`AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` — the adelic cover the
centre-cut subject of §1 needs at ℚ — and two `AutomorphicForm` coset/isotypic nodes. None is
ready; the level-`N` row is the next cut of that family.

The **`EisensteinGeneral` local twisted integral** is complete on the ready shelf: five headlines
landed (three ramified, two unramified) over a shared engine and one definition gate
([numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md](numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md)
§6). The family's remaining rows are `EisensteinGeneral.LocalUnr.integral_twisted_eq` (601 pin
lines — the general unramified formula, of which the landed vanishing row is the special case;
it needs two unported `LanglandsTunnell` rows, 249 raw lines) and the `LocalCorrection` pair
(173 lines, not ready). The five headlines' consumers — the `AutomorphicForm`
Godement–Eisenstein local-factor assembly — are not this column's.

The **factorization** node (the global counterpart: `∏ᶠ` integral = Euler `∏'`) has landed too
([logs/eisenstein-factorization.md](../logs/eisenstein-factorization.md)); its successor
`EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq` (185 pin
lines) needs two unported `NumberField` rows (420 raw `S_` lines) before it is ready.

**Deferred to its own order** is the C2 row
`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`. Its one substantive step is the
unported premise `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, and the chain behind
it is ≈4.8k raw / ≈2.1k `S_` lines; the ported `CuspForm` twin cannot stand in for it because the
cuspidal subspace does not span the Eisenstein part. The row is documented in
`X1/IntegralityJqNModC.lean`'s docstring and open in [CARRY-FORWARD.md](../CARRY-FORWARD.md).

## 8. Reproduce

```bash
cd tools/deps
# the D-S cone, canonical: --ds targets the weight-one headline and excludes the
# prunable complex-analytic subject (deligneSerre/PRUNABLE-complex-analytic.md §4;
# tools/deps/ds_prunable.py), --include-leaves shows the demand's graph leaves that
# --ready/--hops drop
python3 frontier.py --ds --include-leaves --rank-by silo --top 0
# ... the conservative (no name-scan) reading, and the ready shelf / needed alone
python3 frontier.py --ds --include-leaves --frontier sources --top 0
python3 frontier.py --ds --rank-by silo --ready --top 0
python3 frontier.py --ds --top 0

# scope one cluster (step 3): advise → plan → price
python3 port_advise.py --target <node> --target <node> --json build/cluster_advise.json
python3 port_plan.py --json build/cluster_advise.json
python3 build_ladder.py --edit FLTForHuman/<host>.lean

# the gates
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --top 0
```

The checker wiring convention (append the `Theorems/` wrapper and, where it is not already
listed, the `S_` file to `SOURCES`; the module to `PORT_FILES`; both last) is in every work order
and in the friction log.

The checker's mutation sensitivity is its own unit test, run when the checker changes rather than
on every set:

```bash
cd lean
python3 spec/check_flt_statements.py --selftest
```

## 9. Residuals

* **The norm-section engine.** `NumberField/TateGlobal/NormSection.lean` is tier 3 and its 25
  declarations have exactly one importer today (the façade); their intended consumers are the
  eight `normQ` siblings, unported, which must import it rather than copy it
  ([numberTheory/tateGlobal/TOPIC-norm-section.md](numberTheory/tateGlobal/TOPIC-norm-section.md)
  §3, §5). Two of the 25 (`norm_ringEquiv{,Real,Complex}*_symm`) duplicate an inline argument in
  `TateGlobal/ArchNorm.lean` and a public copy in
  `AutomorphicForm/Adelic/WeylIntegrable/LatticeEstimates.lean`; `ArchNorm.lean` is the natural
  home if `AutomorphicForm` ever needs them from here (≈45 s hub wave, not owed).
* **The GL₂ strong-approximation engine.** `NumberField/AdelicLevel/StrongApprox/*.lean` is tier 3
  with 45 declarations and one importer (the façade); the intended consumers are the headline's
  5 whole-project dependents, unported. Two of its names collide *by spelling only* with other pin
  declarations (`exists_common_denominator` with six `ModularCurve` PD-pairing files, `detUnit`
  with a `ℝˣ`-valued `private def` in an `AutomorphicForm` silo), so neither is a home to share;
  recorded so a later `port_advise` run does not read them as duplicates. The five-module split
  is the layout, not a promise: merging them changes no statement.
* **The local twisted-integral engine.** `EisensteinGeneral/LocalTwisted.lean` +
  `LocalRamShells.lean` are tier 3 (34 declarations) with one importer each (the façade, and Set
  B's module); their intended other consumer is the `AutomorphicForm` Godement–Eisenstein
  local-factor assembly, unported. The two `untwisted` definitions (5-arg ramified in
  `TwistedSmoothLocal`, 3-arg unramified in `TwistedUnramifiedLocal`) are deliberately *not*
  unified: their statements differ, and a `Set B` proof that opened both would tie on
  `untwisted` — the ambiguity is recorded in the log.
* **Two wiring lessons from the factorization landing**, both now in the checker's comments: a
  listed `S_` file shadows its own `Theorems/` wrapper for last-name matching unless the wrapper is
  listed **first** (the headline's pin-private twin inherits its binders from a section variable, so
  the two texts differ); and a pin spelling the port seems to lack may already exist as a port-only
  alias elsewhere (`AdelicBox.integralFinteAdeles` is such an alias, in
  `NumberTheory/AdelicHaar/PlaceMeasure.lean`), so grep for the alias before declaring a name
  unspellable. The factorization set also carries the column's one file-level
  `set_option linter.style.haveILetI false` (six modules, 24 load-bearing `haveI` sites) — a
  candidate for narrowing.
* **Register.** The weight-4 engine (`TateSlots/{Convergence,SlotCoeff}.lean`) is tier 3: built and
  importable, not in `PORT_FILES`, with its 119 public declarations carrying `-- pin:` provenance
  in [spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md) (78 modules / 1,906 public / 1,618 with a
  pin original). Only the façade `TateSlots/CoefficientFormulas.lean` is diffed.
* `locKer`/`adjoinRoot'` are public in `DeligneSerre/Lifting.lean` with no consumer today (kept
  per the pin).
* The private `det_eq` copies in `Gamma1Vanishing.lean`/`HeckeEigenNebentypus.lean` are
  statement-identical to the public `ModularForm.HeckeRepresentatives.det_eq`; the one
  un-promoted dedup candidate.
* **`Gamma1_le_of_dvd` is homed (2026-10-18).** mathlib has no order lemma for `Gamma1`, the pin
  re-declares the fact in 12 files and uses it at 135 sites, and the port carried five copies. The
  wave [logs/gamma1-le-of-dvd-home.md](../logs/gamma1-le-of-dvd-home.md) added the tier-3 mathlib
  supplement `NumberTheory/ModularForms/CongruenceSubgroupOrder.lean`
  (`CongruenceSubgroup.Gamma1_le_of_dvd`, the general `{m n}` shape — "the API lemma every consumer
  wants" — plus the `Gamma0` companion), deleted the three `private` copies (`DeligneSerre/Lifting.lean`
  ×2 including the `Gamma0` one, `WeightOne/IntegralWeightOneForm.lean`,
  `WeightOne/Gamma0Integral.lean`) and turned the three checker-listed copies into one-line wrappers
  at their pin binders (`ModularCurve/X1/Defs.lean`, `Analytic/NormSqLt.lean`,
  `WeightOne/RationalityDvd.lean` as `Gamma1_le_of_dvd'`). The checker is unchanged at 10,476 / 0 / 0;
  the wave also cleared `Lifting.lean`'s 18 `haveILetI` warnings by taking Lean's own
  `haveI`→`have` suggestion at every site. The next tenant of the same home is `Gamma_le_Gamma1`
  (public in `CuspForm.LiNormSq` — that copy must stay, it is the pin's — and `private` in
  `WeightOne/Gamma1IntegralBasis.lean` and `…/Gamma0Integral.lean`).
* The `Gamma0Integral.lean` prelude still exists `private` in its two sibling namespaces
  (`…GammaNBounded`, `…X1BoundedDenominators`); `GammaNBounded`'s `IsRat` is a *different
  formulation*, not a copy, and was deliberately left.
* The two gates of §7 are deferred by design, behind the fixed interface the unconditional slice
  leaves.
* The subject-A modules carry **15 narrow `set_option linter.* false in`** suppressions (13
  `unusedSectionVars`, 1 `style.haveILetI`, 1 `unusedVariables`), each on the individual
  declaration rather than file-wide. They are not stylistic: Lean auto-includes `[NeZero N]` in
  those signatures because the *value* uses it while the *type* does not, the linter then calls it
  unused, and `omit [NeZero N] in` is refused (`cannot omit referenced section variable`). The pin
  sets the same options file-wide in six of the eight `S_` files and 192 other port modules do the
  same, so this is house style narrowed, not a new licence — but a work order's "no
  `set_option linter.*` suppression" line should say so. Recorded in
  [CARRY-FORWARD.md](../CARRY-FORWARD.md).
* `frontier.py --ready` resolves names by last name, so a pin node that shares a last name with a
  ported declaration of another namespace is priced as ported. The known instance is the
  `ModularForm`/`CuspForm` rename pair of §7's deferred row — 10 needed nodes / 5,172 raw `S_`
  lines under `--frontier sources`, 1 / 36 under the default `union`. Read the pin node itself
  before trusting `ready` for such a pair, price the pin's `Theorems/` imports too, not only its
  `Definitions/` ones, and re-run both frontier readings: `port_advise` and `port_plan` never walk
  imports, so an unported premise outside the target files is invisible to them.
