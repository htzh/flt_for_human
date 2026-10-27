# The Deligne–Serre weight-one column — frontier, workflow and plan

The column ports `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` — the weight-one
mod-`ℓ` Galois-representation theorem — from the pin `anthropics/fermats-last-theorem@aa2d8b3`
(Lean `v4.33.1` / mathlib `db584cd6`) into the port library at mathlib `v4.34.0`. This note is
the column's state and plan: §1 what the port contains, §2 the frontier as it stands, §3 the
workflow the manager follows, §4 the shared ground (definitions, promotions, hubs) that is the
manager's own work, §5 the build economy, §6 verification, §7 what remains, §8 reproduce, §9
residuals. Every measurement is the pin's, read through `tools/deps`. The section numbers are
stable: work orders across the column cite §3 for the workflow and §7 for the gates.

**This note is not a landing log.** The dated record of a landing — the checker and build readings,
the per-module tables, what it moved and what it deferred — lives in [../logs/](../logs/) under that
landing's own name, and in the work order and topic that produced it. §1 names module homes and
points at those records; it does not copy their numbers. A reading copied into this note goes stale
the moment another column lands (§6), and a work order measures on the tree it leaves.

**Status.** The column's unconditional slice is complete, together with the definition and
infrastructure ground listed in §1. What remains is the two automorphic gates of §7, which sit
behind a fixed interface and can be ported without reworking what is there.

The checker is **`spec/check_port.py` alone**, one module at a time, wired by the module's own
`spec-pin:` header over the shared statement parser **`spec/lean_parser.py`** (§6). Declaration-level
exceptions live in `spec/decl_markers.tsv`, never in the Lean source.

Companions:

- [../../math/019-deligne-serre-weight-one.md](../../math/019-deligne-serre-weight-one.md)
  — the mathematics: the theorem, the lifting, the assembly from residual data.
- [../../studies/deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md)
  — the effort measurement, the subject clusters and the two gates.
- [porting-playbook.md](../porting-playbook.md) — the rules; §2.1–§2.6 (planning),
  §3.1–§3.7 (execution, sets, the build ladder), §4 (faithfulness), §5 (sharing).
- [TOPIC-dedup-refactoring.md](TOPIC-dedup-refactoring.md) — the dedup phase of a new cut: what to
  import, promote, append or write locally against the port that already exists, why copy counts are
  not the criterion, what the checker's direction makes free, and the FR1 worked example.
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
- The `AlgebraicCurve` local-parameter leaves — the finite cover as the `Fam` engine, the
  24-lemma prelim block the three `localParam` `S_` files share, and the family's charted-space
  capstone:
  [algebraicCurve/TOPIC-localParam-finite-cover.md](algebraicCurve/TOPIC-localParam-finite-cover.md),
  [algebraicCurve/WORKORDER-LP1-localParam-finite-cover.md](algebraicCurve/WORKORDER-LP1-localParam-finite-cover.md).
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
- The any-field `Φ_p` splitting and the at-slot roots it exposes — the two char-`p` nodes
  `PhiGen.splits_prime{,_at_slot}_of_isPrimitiveRoot`, one pin development shipped in two
  byte-identical 607-line files, homed once at
  `ModularCurve/PhiGenSplitsAnyField.lean` (489 lines, 9 public declarations) as the any-field twin
  of `PhiGenSplits.lean`/`PhiSlotRoots.lean`, whose statements it is not an instance of (they spend
  `Algebra ℚ K`; its proof *calls* `splits_of_prime` through the integral cyclotomic order
  `ℤ[ζ_p]`). Its ground was a definition-layer refactor: `Defs/TS.lean` generalised to the pin's
  `jqModC` spelling at `[Field K]` and wired, `coeffEmb L jq = jqModC L` moved down to
  `Defs/JqCoeff.lean`. Records: [logs/ts-general-field.md](../logs/ts-general-field.md),
  [logs/phigen-splits-any-field.md](../logs/phigen-splits-any-field.md); order:
  [modularCurve/WORKORDER-GS1-phigen-splits-any-field.md](modularCurve/WORKORDER-GS1-phigen-splits-any-field.md).
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
- The archimedean **type-span** leaf — the `--include-leaves` demand's rank-#2 row, ported as a
  façade over the shared `Q09` engine, and its `finiteDimensional_span_translates_of_mem_archCutSubmodule`
  successor (now ready at 184 lines):
  [automorphicForm/WORKORDER-ATS-arch-type-span.md](automorphicForm/WORKORDER-ATS-arch-type-span.md),
  [logs/arch-type-span.md](../logs/arch-type-span.md). The engine's own planning note is
  [automorphicForm/TOPIC-archTestFactor-family.md](automorphicForm/TOPIC-archTestFactor-family.md).
- The **matrix-group right-finite supplement** — `U(2)`/`O(2)`, the pin's twin pair ported as one
  faithful development over a shared evaluation-combination prelude, and the pricing of the rest of
  the `Matrix.`-namespace demand in the cone:
  [deligneSerre/TOPIC-matrixgroup-rightfinite.md](deligneSerre/TOPIC-matrixgroup-rightfinite.md),
  [deligneSerre/WORKORDER-MG1-right-finite-supplement.md](deligneSerre/WORKORDER-MG1-right-finite-supplement.md),
  [deligneSerre/TOPIC-matrix-family-in-cone.md](deligneSerre/TOPIC-matrix-family-in-cone.md),
  [deligneSerre/WORKORDER-MG2-matrix-family.md](deligneSerre/WORKORDER-MG2-matrix-family.md),
  [logs/matrixgroup-rightfinite.md](../logs/matrixgroup-rightfinite.md),
  [logs/matrix-family-four.md](../logs/matrix-family-four.md).
- The **mathlib-like leaf families of the cone** — the 179 self-contained leaves that carry no FLT
  import, grouped by the frontier's own family preamble, with the free-group family priced as one
  engine + four headlines, and the preamble's one-to-three-node families split into 43 ready and 11
  blocked (nine of them one ready leaf away), plus the nine-pair wave that landed from it:
  [deligneSerre/TOPIC-ds-leaf-families.md](deligneSerre/TOPIC-ds-leaf-families.md),
  [deligneSerre/WORKORDER-MG3-ds-leaf-families.md](deligneSerre/WORKORDER-MG3-ds-leaf-families.md),
  [logs/ds-leaf-families-wave1.md](../logs/ds-leaf-families-wave1.md),
  [logs/ds-leaf-families-wave2.md](../logs/ds-leaf-families-wave2.md). The re-scoped cut that
  the criterion actually admits — 37 nodes / 3,641 lines / 7 families, all ready and gate-free — is
  [deligneSerre/TOPIC-phase3-small-supplements.md](deligneSerre/TOPIC-phase3-small-supplements.md),
  whose two smallest families (`PowerSeries`, `Module.End`) landed 2026-10-20 as five modules and
  66 statement-checked declarations: orders
  [deligneSerre/WORKORDER-PH3A-module-end-eigenspace.md](deligneSerre/WORKORDER-PH3A-module-end-eigenspace.md)
  and
  [deligneSerre/WORKORDER-PH3B-powerseries-coefficients.md](deligneSerre/WORKORDER-PH3B-powerseries-coefficients.md),
  record [logs/phase3-module-end-and-powerseries.md](../logs/phase3-module-end-and-powerseries.md).
  The note repriced those two families from 5 nodes / 522 lines to **8 / 1,724** — the three rows it
  had missed are 1,202 of the 1,724 lines. The same phase's `Algebra` and `CongruenceSubgroup`
  families followed the same day: orders
  [deligneSerre/WORKORDER-PH3C-algebra-norm-and-integrality.md](deligneSerre/WORKORDER-PH3C-algebra-norm-and-integrality.md),
  [deligneSerre/WORKORDER-PH3D-congruence-subgroup-lattice.md](deligneSerre/WORKORDER-PH3D-congruence-subgroup-lattice.md),
  record [logs/phase3-algebra-and-congruence-subgroup.md](../logs/phase3-algebra-and-congruence-subgroup.md)
  — including the **reversal of the note's `CongruenceSubgroup` exclusion**, which had rejected
  five mathlib-shaped nodes on a subject smell without reading their statements.
- The **mathlib-first check for supplements, and the survey behind it** — first the habit (name /
  concept / statement `rg` over mathlib `v4.34.0`, with the three traps: trailing-name collisions, a
  more general mathlib lemma, a pin `import Mathlib` hiding the library), then the one-off study of the
  pin's 2,723 clean-import unported `S_` files (538,498 raw lines) outside the D-S cone: the subject
  families, the ten hand-read supplements with mathlib-mirroring homes and verified gaps (the 57-line
  `ValuationSubring` residue-field pair at 124 + 197 consumers is the cheapest), the FLT-flavoured
  ~135k lines that are *not* supplements, and the dedup cases:
  [TOPIC-mathlib-supplements.md](TOPIC-mathlib-supplements.md).
- The `HeckeIntegralSeam` **coset seam** — the explicit `q_v + 1`-coset decomposition of the Hecke
  double coset at a finite place, its three-module `LocalLanglands` definition gate, and the public
  engine its `_principalLevel` sibling will import:
  [automorphicForm/WORKORDER-HS1-hecke-coset-seam.md](automorphicForm/WORKORDER-HS1-hecke-coset-seam.md),
  [logs/hecke-coset-seam.md](../logs/hecke-coset-seam.md). The adelic definition layer it sits on
  is [PORTING-AutomorphicForm.md](PORTING-AutomorphicForm.md) (`D3`–`D6`: `levelOne`,
  `finiteAdelicGL2Subgroup`, `heckeGen`, `localEmbed`, `finEmbed`).
- The `Place` **separating-uniformiser twin** — a uniformiser (or a tame-order element) is a
  separating element, the ready pair ported as two headlines over the promoted Frobenius-subfield
  engine, with the criterion *called* rather than re-proved:
  [algebraicCurve/WORKORDER-SU1-separable-uniformiser.md](algebraicCurve/WORKORDER-SU1-separable-uniformiser.md),
  [logs/separating-uniformiser.md](../logs/separating-uniformiser.md). Its AC neighbours are
  [algebraicCurve/TOPIC-t1-ord-interface.md](algebraicCurve/TOPIC-t1-ord-interface.md) (the `ord`
  interface it is stated over) and
  [algebraicCurve/TOPIC-t9-transcendence.md](algebraicCurve/TOPIC-t9-transcendence.md) (its two
  premises).

## 1. What the port contains

The port holds the column's unconditional half, the `ModularCurve` q-expansion, function-field and
Frobenius layers, the analytic and period layer, the Tate-slots definition and weight-4 layers, and
the definition and hub ground the rest builds on. Each subject below names its module homes and its
record; the readings that go with the landing are in the record.

**The unconditional slice.** Everything that does not depend on the two automorphic gates — the
weight-one mod-`ℓ` lifting half and the assembly half. It takes the residual family as a hypothesis,
so it is stated without the ray-class input and without the automorphic layer; the two gates attach
to a fixed interface and can be ported later without reworking it. The consumer wire test is
`spec/DeligneSerreConsumer.lean`; the record is
[../logs/deligne-serre-port.md](../logs/deligne-serre-port.md) and the friction/promotion ledger is
[../logs/deligne-serre-friction.md](../logs/deligne-serre-friction.md).

**The coset-space Petersson layer, and the level-prime eigenvalue.** The definition layer
`ModularForms/Analytic/PeterssonCoset.lean` — `Nice`, the raw pairing `pair`, the slash transfer and
the relative-index machinery, 56 declarations — and the silo `ModularForms/Analytic/NormSqPow.lean`,
the level-prime bound `‖a‖² = ℓ^(k-1)` for a form new at `ℓ`, 72 declarations; the 18
statement-identical declarations the pin wrote twice were moved out of the `PeterssonHecke` engine
into the definition layer. Topic and order:
[deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md](deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md),
[deligneSerre/WORKORDER-P2-normsq.md](deligneSerre/WORKORDER-P2-normsq.md).

**The `ModularCurve` q-expansion layer.** The Γ₀-rationality pair, the `X_H` relative-degree bound,
the JOneES finrank/index and residue-field rows, the Deuring-reduction / constant-extension /
Atkin–Lehner successors, and the `isAlgClosed` finrank bound, in `functionFieldGeneration/SET-R-*`,
`X1/*`, `XH/*` and `WeightOne/*`. The planning records are the `TOPIC-qexp-*` notes.

**The `X_H`/`X₁` function field and Frobenius.** The `q`-expansion Frobenius inputs headline
`qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental`, appended to
`ModularCurve/Frobenius/QExpModL.lean` — the module already held its private machinery and its
`Fr* Fr_* = ℓ` sibling, so the append needed no new file and no promotion. The ten landed leaf rows
(`qExpansion_div_mem_laurentBaseChange_xHFunctionField`,
`isIntegral_jqNModC_of_modularPolynomialData`, `exists_gamma0_qExpansion_div_eq_jqNModC`,
`eisenstein4_cube_sub_mk_sq`, `diffQExp_x1FunctionFieldBar_injective`,
`modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero`,
`modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0`, `closure_elemSet_eq_top`,
`isCurveOver_x1FunctionFieldBar`, `essFiniteType_x1FunctionFieldBar`) sit in
`ModularCurve/X1/{QExpansionDiv,IntegralityJqNModC,Structure,FunctionFieldInclusion}.lean`, on the
definition modules `ModularCurve/Defs/{HeckeDifferential,SL2Elementary}.lean`,
`ModularCurve/X0/FunctionFieldFull.lean` and `AlgebraicCurve/Differential/PushPull.lean`, each
ported whole. The eleventh row is deferred (§7). Order:
[modularCurve/WORKORDER-C2-x1-function-field.md](modularCurve/WORKORDER-C2-x1-function-field.md).

**The analytic and period layer.** The pin's four `Def_AutomorphicForm_*` modules whole —
hyperbolic measure, fundamental-domain volume, the Siegel set cover and the Γ₀ fundamental set, in
`AutomorphicForm/`, keeping the pin's `FLT.*` namespaces — and the Petersson pairing
`ModularCurve/Analytic/PeterssonPairing.lean`, whose two headlines make the period pairing
perfect. The period map of a finite-index subgroup is
`ModularCurve/Period/{PeriodLatticeSpan,PeriodLatticeBoundary,ParabolicHoms,QExpansionDerivative}.lean`,
and the pin's `Def_ModularCurve_QExpansionDiff.lean` node is whole across
`Period/QExpansionDiff.lean` and `AlgebraicCurve/Differential/TraceDiff.lean`. Orders:
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
deduped twin development in `ModularCurve/LevelN/QExpBridge.lean`. Orders:
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
neither has a `private` declaration, so no promotion is owed.

**The weight-4 Tate-slot engine and headline façade.** The fourteen `S_ModularCurve_*` leaves the
frontier's `--include-leaves` view showed at ~1650 lines are one 1,671-net-line development written
fourteen times (23,094 raw lines, 112 shared names, ≈20,810 removable); it is ported once as the
tier-3 engine `ModularCurve/TateSlots/{Convergence,SlotCoeff}.lean` (537 + 1,293 lines, 38 + 81
public declarations, declaration parity exact, no build-time blow-up) and the fourteen public
headlines in the tier-1 façade `ModularCurve/TateSlots/CoefficientFormulas.lean`. The engine's
fourteeen kernels are public as `ModularCurve.TateSlots.<name>` with the pin `Theorems/` wrapper
binders; the façade states the wrappers verbatim. The engine stays tier 3 and is recorded in
[spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md); the façade is the checker wire. No existing
module was edited. Mathematics, measurement and structure:
[modularCurve/TOPIC-tate-slots-weight-four.md](modularCurve/TOPIC-tate-slots-weight-four.md); the
order: [modularCurve/WORKORDER-F1-tate-slots-engine.md](modularCurve/WORKORDER-F1-tate-slots-engine.md).

**The `tateCurve` `BridgeX` layer and its definition chain.** The three `tateCurve` rows F1's
step-6 re-read put on the shelf are a **twin pair and a triplet** — five near-identical pin `S_`
files sharing one 1,338-line `ModularCurve.BridgeX` development (47 declarations in all five, 23
more in the pair only, 5 headlines). Ported once as the tier-3 engine
`ModularCurve/TateCurve/{Bridge,Slot}.lean` (839 + 674 lines, 50 + 25 public declarations, no
build-time blow-up), with the five public headlines in the tier-1 façade
`ModularCurve/TateCurve/QPow.lean`. Its six unported `Definitions/` modules are homed whole at
`Algebra/LaurentSeriesXAdic.lean`, `TateCurve/{QSeries,PointSeries}.lean`,
`ModularForms/KatzLevelOne.lean` and `ModularCurve/Defs/{KatzLevelP,KatzLevelPCusps}.lean` (217
declarations). The engine stays tier 3 and is recorded in
[spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md). Mathematics and structure:
[modularCurve/TOPIC-tate-curve-twins.md](modularCurve/TOPIC-tate-curve-twins.md); order:
[modularCurve/WORKORDER-F2-tate-curve-twins.md](modularCurve/WORKORDER-F2-tate-curve-twins.md).

**The archimedean Iwasawa analytic core.** The two gates of §7 take their input at the infinite
place from 13 `AutomorphicForm.{Complex,Real}Iwasawa` rows — the decomposition's compact factor and
the Fourier decay of its radial length. They are ported as the pre-gate wave the gates attach to:
the pin `Def_AutomorphicForm_ComplexIwasawa` (4 declarations) and the shared generic Fourier bound
(`M4aP3B.FourierDecay`, 2 declarations) homed as the definition layer, seven tier-3 engines
(`AutomorphicForm/Iwasawa/{Complex,Real}/{Core,Decay,UniformDecay,Continuation}.lean`, 5,818 lines)
holding the deduped development (10,378 raw `S_` lines → 5,256 net), and the two subject façades
`AutomorphicForm/Iwasawa/{Complex,Real}/Estimates.lean` (13 headlines) as the checker wire. No
Iwasawa row remains in the demand. Topic, mathematics and orders: the companion bullets above.

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
headlines, so the sibling's pin-specific `no_realization_of_ne_zero` is not ported. Records:
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
`Adelic/MeasurableFundamentalDomainCover.lean` hold the three headlines. The fourth `--ready` row,
the 234-line `CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_…_ample`, is **not
actually ready**: it needs the unported 288-line `Def_AutomorphicForm_CuspidalSpectrumCarrier.lean`,
recorded in [CARRY-FORWARD.md](../CARRY-FORWARD.md). Record:
[logs/centre-cut-fundamental-domain-trio.md](../logs/centre-cut-fundamental-domain-trio.md); order:
[automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md](automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md).

**The complex archimedean Casimir layer.** Set B of the arch-Casimir subject was blocked on two
unported pin `Definitions/` modules: `Def_AutomorphicForm_ArchDerivCasimirComplex` (196 lines / 32
declarations) and `…ComplexAPI` (381 / 46). Both were homed whole at
`AutomorphicForm/Adelic/ArchDerivCasimirComplex.lean` and `…ComplexAPI.lean`, and the first complex
headline `AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt` was ported as the
857-line engine `AutomorphicForm/Adelic/ArchCasimirComplex.lean` (96 public declarations, tier 3,
registered). The engine is the complex mirror of the real `ArchCasimir.lean`: the types are `ℂ`
rather than `ℝ`, and the complex half adds the holomorphic/anti-holomorphic Del operators, the
conjugate transport and the second Casimir. `port_advise` reports 0 substitutions and 43
binder-spelling variants; a normalized comparison is only ≈0.38 similar, so the architectural
duplication did not justify a generic `RCLike` rewrite of the landed real engine. The remaining
complex headlines are `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` (1,227)
and `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` (133), then the 35-file complex
fan. Record: [logs/arch-casimir-complex.md](../logs/arch-casimir-complex.md); order:
[automorphicForm/WORKORDER-ACC-arch-casimir-complex.md](automorphicForm/WORKORDER-ACC-arch-casimir-complex.md).

**The Poisson-summation pair closed the `ZLattice` deferral** (§9's last parked item): the 563-line
`SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace` and the two `ZLattice` headlines (229 + 221 pin
lines) as `Analysis/Fourier/PoissonSummationPi.lean` (613 lines, 31 wired + 7 `own:`) and
`PoissonSummationZLattice.lean` (293 lines, 2 wired). The deferral was not a slow proof: three
declarations blew the diagnostic **in their statements**. A locally bound `hf` — "every lattice
translate is summable in sup-norm on every compact", written inline in all six `PeriodizeLift`
declarations — made `isDefEq` unfold the norm on a restricted `ContinuousMap`
(`ContinuousMap.instNorm = dist x 0`, `sInf`, `Finset.sum`); naming that type `LocSum` removed the
unfolding and put both modules back in the low single-digit seconds (§5). The set is the column's
first **registered deviation set**: 7 `own:` rows in `spec/decl_markers.tsv` (the six binders and
`LocSum`; the statements stay defeq to the pin's). Record:
[logs/poisson-summation-statements.md](../logs/poisson-summation-statements.md).

**The `Representation` family closed whole** — six ready nodes / 2,351 raw pin lines, cut by size
and subject as the family note's §7.5 priced it. The five small mathlib-shaped leaves landed as five
mathlib-mirrored modules
(`RepresentationTheory/{Burnside,InvariantPairing,CompactGroup,SubrepresentationExtension}.lean`,
`LinearAlgebra/Matrix/SubfieldBasis.lean`; 21 wired), and the 1,692-line descent development as
three `GaloisRep/Deformation/` modules (`Charpoly`, `Cocycle`, `FiniteDescent`; 103 wired) — eight
modules, 2,893 port lines, 124 checked declarations. The mathlib-first audit recorded a negative for
every declaration, with mathlib supplying ingredients only (`Matrix.map_injective`, Schur, Jacobson
density, Haar averaging, `toMatrix`/trace dictionary, the `FiniteField` Frobenius/norm API); two
helpers in `RepresentationTheory/BrauerNesbitt.lean` were promoted for the Burnside module and now
diff through the pin-private fallback. The family is complete. Records:
[logs/representation-leaves.md](../logs/representation-leaves.md),
[logs/descent-charpoly.md](../logs/descent-charpoly.md); orders:
[WORKORDER-R2-representation-leaves.md](deligneSerre/WORKORDER-R2-representation-leaves.md),
[WORKORDER-R1-descent-charpoly.md](deligneSerre/WORKORDER-R1-descent-charpoly.md).

**The remaining surface, by module home.** One line per set, no numbers — the module is the entry
point, the record is where the landing is described:

- the **`localParam` family** — `Place/FiniteCover.lean` (the `Fam` engine) with `Place/OrdCalculus.lean`
  beneath it, then `Place/{BranchUniqueness,MeroRealize,LocalParamDatum}.lean` and the four premise
  leaves `Place/{LaurentSeriesModel,TranscendentalOfOrdNeZero}.lean`,
  `IsCurveOver/FinitenessTransfer.lean`, `Analysis/PowerSeries/EisensteinAlgSeries.lean`
  ([logs/localParam-family.md](../logs/localParam-family.md));
- the **`Place` separability pair** — `Place/SeparableUniformiser.lean`, two headlines over the
  promoted Frobenius-subfield engine ([logs/separating-uniformiser.md](../logs/separating-uniformiser.md));
- the **`HeckeIntegralSeam` coset seam** — the engine `Adelic/HeckeCosetSeam.lean`, its gate
  `RepTheory/LocalLanglands/{IntegralSubgroup,IntegralSubgroupOpen,HeckeCosetLocal}.lean`, the
  coset-sum append to `HeckeCosetSystem.lean`, and the `_principalLevel` near twin
  ([logs/hecke-coset-seam.md](../logs/hecke-coset-seam.md));
- the **matrix-group right-finite supplement** — `Analysis/MatrixGroup/{Unitary,Orthogonal}RightFinite.lean`
  over the shared `LinearAlgebra/Dual/EvalSpan.lean`
  ([logs/matrixgroup-rightfinite.md](../logs/matrixgroup-rightfinite.md));
- the **four ready `Matrix.` rows** — `LinearAlgebra/Matrix/{SimultaneousEigenbasis,SL2Generation,SpecialLinearGroupHermite}.lean`
  and `Analysis/MatrixGroup/SpecialUnitary2.lean` ([logs/matrix-family-four.md](../logs/matrix-family-four.md));
- the **mathlib-like leaf families** — wave 1's eighteen modules (which also homed
  `Def_AlgebraicCurve_ConstantReduction`, `Def_AlgebraicCurve_RegularProlongation`,
  `Def_HeckeCharacter_FiniteOrder` and `Def_ModularCurve_OmegaOf` whole) and its phase 2's
  twenty-nine, including the `Def_Compat_Mathlib430` block-D gate
  ([logs/ds-leaf-families-wave1.md](../logs/ds-leaf-families-wave1.md),
  [logs/ds-leaf-families-wave2.md](../logs/ds-leaf-families-wave2.md)); phase 3's four families are
  `LinearAlgebra/Eigenspace/{Sl2Strings,MultiplicityOne}.lean`,
  `RingTheory/PowerSeries/{Saturation,GaloisDescent,CoeffMem}.lean`,
  `RingTheory/IntegralClosure/FunctionField.lean`, `RingTheory/Norm/Elementary.lean` and
  `NumberTheory/ModularForms/CongruenceSubgroupLattice.lean`
  ([logs/phase3-module-end-and-powerseries.md](../logs/phase3-module-end-and-powerseries.md),
  [logs/phase3-algebra-and-congruence-subgroup.md](../logs/phase3-algebra-and-congruence-subgroup.md));
- the **`Rat*` definition gates and their two nodes** — `LanglandsTunnell/StandardLocalConstantsAt.lean`
  and `NumberTheory/RatIdele/Normalizer.lean` as gates, `NumberTheory/RatAdele/DenseRange.lean` and
  `NumberTheory/RatIdele/ClassCharNorm.lean` as nodes
  ([logs/rat-def-gates.md](../logs/rat-def-gates.md), [logs/rat-nodes.md](../logs/rat-nodes.md));
- the **`q`-expansion trio and the free-group family** — `NumberTheory/ModularForms/QExpansionCoeff.lean`
  plus `Combinatorics/SimpleGraph/Transversal.lean`,
  `GroupTheory/{FreeDoubleCoset,FreeGroup/KuroshRank,FreeGroup/SpecialLinearGroupGenerators}.lean` and
  the three `BassSerre`/`ModularGroup` modules ([logs/qexp-and-freegroup.md](../logs/qexp-and-freegroup.md));
- the **Fricke trace** `ModularForms/HeckeFrickeTrace.lean`, the **Fricke reciprocity** of the
  `q`-expansion as `ModularForms/Level/Gamma1Slash.lean` + `ModularForms/FrickeReciprocity.lean`
  ([logs/hecke-fricke-trace.md](../logs/hecke-fricke-trace.md),
  [deligneSerre/WORKORDER-FR1-fricke-reciprocity.md](deligneSerre/WORKORDER-FR1-fricke-reciprocity.md)),
  and the **Gauss regular prolongation** of the `q`-expansion valuation
  ([logs/qexp-regular-prolongation.md](../logs/qexp-regular-prolongation.md));
- the **degeneracy-cover degree and the Hecke compositum** — the `RelIndex` ground
  (`Analytic/AnalyticAtCusp.lean`, `RelIndex/{Hermite,LevelRaise,RatioField}.lean`) under the two
  façades `RelIndex/{LeRelrank,LeRelIndex}.lean`, then `ModularCurve/HeckeCompositum.lean` with both
  headlines ([logs/relindex-relrank.md](../logs/relindex-relrank.md),
  [logs/hecke-compositum.md](../logs/hecke-compositum.md));
- the **`q`-expansion definition-layer re-homing** — the pin `Def_ModularCurve_X1` predicate at
  `ModularCurve/X1/Integral.lean` and its blocks in `ModularCurve/X1/Defs.lean`
  ([logs/qexp-definition-layer-homes.md](../logs/qexp-definition-layer-homes.md));
- the **archimedean type-span leaf** — `AutomorphicForm/Adelic/Cusp/ArchTypeSpan.lean`, a façade over
  the shared `Q09` engine `RepTheory/TypeReproducer.lean`
  ([logs/arch-type-span.md](../logs/arch-type-span.md));
- the **composite-silo correction** — `NumberTheory/ModularForms/Gamma0Three.lean` and
  `ModularCurve/Numerics/NuThree.lean` made public out of the composite host
  `ModularForms/WeightOne/EisensteinChiNegThree.lean` ([logs/phantom-landings.md](../logs/phantom-landings.md));
- the **`GeneralLinearGroup` card bound** (set MG4) and the four `Matrix.SpecialLinearGroup` free-group
  rows ([logs/matrix-gl2-count.md](../logs/matrix-gl2-count.md)).

**The shared ground that edits existing modules.** The `ValuationSubring` residue block in
`NumberTheory/ValuationAtPlace.lean`; the `Gamma0Integral` promotion and its duplicate-block
collapse; the resolution of the `normFormulaAlong_of_elliptic` co-import collision (one public
copy; the character-free copy is named `normFormulaAlong_of_elliptic_cf`); the C1 append into
`ModularCurve/Frobenius/QExpModL.lean` — the one landing that edits a module rather than adds
one; and the wave that homed the shelf's definition layer, which also deduped `fibrePoly` out of
`Degree/PhiData.lean` into `Defs/FibrePoly.lean` at its public pin name. Registered in
[CARRY-FORWARD.md](../CARRY-FORWARD.md).

**The pole at the cusp, and the prime non-adjoin twin.** These two sets were placement and
transcription passes, not new mathematics, and they are the column's clearest cases of a statement
authority other than the `S_` text. The three `j`-pole headlines
`ModularCurve.coeff_jqModC_pow_self` / `coeff_jqModC_pow_of_lt` / `coeff_jqModC_neg_one` (`j(q) =
q⁻¹·u`, `u(0) = 1`, hence `ord j = -1` and `j` transcendental — the valuation input to every degree
and pole count in the q-expansion layer) were stated in the port **only `private`**, twice over, and
were three of the register's orphan phantoms. They now have their one home, *The pole at the cusp*
in `ModularCurve/Defs/JqCoeff.lean`, beside the `jqModC` they are about, together with the
`jqModC_pow` pole/unit factorisation they read off; the four copies the listing named are deleted
and their modules import the home. The trio is stated at its `Theorems/` **wrappers' binders**,
because the wrapper is the checker's statement authority: the pin's `S_` text spells them with
section variables, which the checker's hash does not equate.

The two `jqNModC` headlines — `jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne` and
`jqNModC_prime_not_mem_adjoin_of_charZero`, "`j(q^p)` is not in `K(j(q))`" — are one development
written twice in the pin (the two `S_` files are 593 lines each, 574 byte-identical), and it is
ported once: the cyclotomic-conjugate engine `ModularCurve/Degree/JqCyclotomicConjugates.lean`
(519 lines, 24 declarations at the pin's names) and the node `ModularCurve/Degree/PrimeNonAdjoin.lean`
(166 lines, the engine plus the two headlines at their wrappers' binders). The mathematics: `j(q)`
is transcendental, so `K[j(q)]` is a polynomial ring and integrally closed, while the monic modular
relation `Φ_p(j(q), j(q^p)) = 0` makes `j(q^p)` integral over it — so an element of the fraction
field that is integral **is** a polynomial, and no polynomial in `j(q)` takes the value `j(q^p)` by
the `q^-p`-coefficient obstruction. `Defs/JqCoeff.lean` gains the pole's exact order,
`order_jqModC` (222 lines), and `ModularPolynomialStarBank.lean` drops its fourteen `private`
prelude copies for the import (266 → 123 lines). The set's one unavoidable drift is registered as
two `own:` rows, `phiAtSeed_TS_eval` and `phiAtSeed_TS_eval_symm`: the port's `TS` (`Defs/TS.lean`)
is the `ℚ`-model spelling and carries an `Algebra ℚ K` binder, while the pin's per-file `W1.TS` is
over an arbitrary field — `Algebra ℚ K` is not synthesizable from `[Field K]`, so the two are
stated one hypothesis stronger, and the two `TS` spellings agree by `coeffEmb K jq = jqModC K`. The
frontier rows for both headlines read **needed 0**, "target is ported"; the order is
[modularCurve/WORKORDER-JQ1-prime-non-adjoin.md](modularCurve/WORKORDER-JQ1-prime-non-adjoin.md).

**Two transcription lessons from the SET-R-C repair, both worth carrying into any work order.** The
`JOneES` finrank/index module `ModularCurve/X1/FunctionFieldDegree.lean` silently stopped
elaborating when an unrelated landing added a *general* `ModularCurve.coeffEmb_intSeriesC` to
`JqIntegralRatios.lean`: the proof's `simp only [...]` names the lemma unqualified while the module
`open`s a namespace that holds a `.map`-spelled copy, and an unqualified name resolves to the
enclosing namespace **before** an `open`ed one — so the bare name became the general lemma, the goal
kept `intSeriesC ℂ …` unexpanded, and `simp` reported "made no progress". The repair is one token
(`intSeriesC` joins the `simp only` list); nothing else moved. The rule: **when a proof's unqualified
name has a same-named declaration in the module's own namespace, qualify it or state the form the
step needs**, and read a `simp made no progress` in a busy namespace as this symptom, not as a
deleted hypothesis. That is also why the two `coeffEmb_intSeriesC` spellings are two declarations,
not a duplicate: a "dedup" of the pair was tried, and the next wave build caught it, because the
`S_`:782 `.map` copy has a consumer that names it qualified — each copy is faithful to its own `S_`
file. And the same module came up to standard in the same pass: three **file-wide** linter
suppressions removed, six `haveI` → `have`, four `omit` insertions, and one statement binder
narrowed rather than renamed (renaming it would change the statement the checker diffs). Neither
checker compiles — the frozen registry and `check_port` both diff text — so a statement-reading
gate cannot see a broken proof; only a build can. The other duplicates in that area — the
`monomialSpan` induction re-derived in `X1/FunctionFieldDegree.lean`, and
`X1/FunctionFieldBaseChange.lean`'s `private` valuation block — are an open item in
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
them. The other ten rows predate the Tate-slot round. The `CuspForm`,
`PeriodPair`, `ModularForm` and `CohCarrier` rows are reached by the target closure but are not
`ModularCurve` rows, and are not this column's to cut; the `NumberField.TateGlobal` rows are cut
through their own topic notes (the `continuous_ideleNorm` hub and, now, the continuous norm
section — §1), and their remaining shelf rows are the two
`exists_norm_apply_eq_ideleNorm_rpow` cousins (§7).

**The `AlgebraicCurve` rows are now being cut too**, through their own AC-homed notes: the
`localParam` family's first leaf, `AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex`,
landed on 2026-10-19 (§1) and the rest of the family followed the same day — the branch
uniqueness, the local parameter with its meromorphic-order dictionary, and the four leaves those
rest on — so the charted-space capstone
`Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` (1,576 silo lines) now lacks
only its own assembly, with `Place.exists_forall_ord_eq_finset` (291) ready beside it. The `--ds` ready shelf itself read
**85 candidates** at that landing (the 67 in §7 predates four other columns' landings). The
`Place` **separability pair** followed on 2026-10-20 (§1): a uniformiser is a separating element,
and so is an element of nonzero tame order — one module, two headlines, over a three-declaration
promotion in the Frobenius-subfield engine; it put the `ordDiff` rows on the ready shelf (§7).

**The different's homes (2026-10-27).** `Genus/DegreeIdentity.lean` had grown to 2,048 lines
holding four subjects. It is now four modules, each on the wire and each with its own
`spec-pin:` block: `Genus/DegreeIdentity.lean` (3 ok — the degree identity),
`Differential/Different.lean` (1 ok — the different is effective),
`Place/OrbitCardinality.lean` (8 ok — the Galois orbit/stabiliser dictionary, whose
seven-declaration prelude `toSemilinear`/`placeAction`/`smul_place_def`/
`mem_fiberOver_iff_mem_orbit`/`card_stabilizer_*`/`inertiaDeg_eq_one_of_deg_eq_one` is
public as the pin declares it, since the wild bound consumes it), and
`Genus/HurwitzBound.lean` (2 ok — the two Hurwitz line bounds). Corpus after the split:
**6,638 ok / 0 mismatch / 0 missing / 32 own, 306 modules, 500 exempt**; `dedup` 0 on all
four (`Differential/Different.lean` reports only its engine-plus-headline pair, 10 lines, the
pin's own two-declaration structure and kept), `move_dead` 0 except one recorded false positive
(below). The only in-tree importer
of the old module, `ModularCurve/LevelN/GenusFF.lean`, now imports the two homes it uses.

The slice is scoped in
[deligneSerre/TOPIC-different-wild-bound.md](deligneSerre/TOPIC-different-wild-bound.md): Wave A
is the six algebraic-curve nodes (the wild bound at `needed == 1`, the equality chain at
`needed == 6`), Wave B the three modular consequences (138 and 54 nodes of modular demand), and
the price of Wave A is ≈1,640 net new lines over 108 declarations.

The ready `ordDiff` rows now have a home with no promotion left to pay:
`Differential/Different.lean` takes `Place.ordDiff_D_eq_ord_sub_one` (178 ln, 8
declarations, nothing to reuse) and `Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois`
(899 ln, 62 declarations, 793 net new lines; its seven-declaration prelude is the orbit
module's public block). `port_advise` finds 65 lines already in the port and no duplicate
copies inside the slice.

**Instrument note.** `move_dead` reads the orbit module's `embAction` (12 lines) as dead.
It is not: the `MulAction` instance is found by instance search inside `MulAction.orbit` /
`MulAction.stabilizer` on `Emb`, so the name-based liveness test cannot see its use —
deleting it breaks the build. The same caution as `dedup`'s shape tier applies in reverse:
check the call sites before acting.

**The demand's leaves are the other shelf, and its rank-#2 row has landed.** `--ready` and `--hops`
drop graph leaves (a leaf has `needed == 1` and can never reach `F`), so the automorphic demand's
biggest self-contained rows appear only under `--include-leaves` or in a direct query. The
archimedean type-span leaf
`AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`
— 813 silo lines, `used_by` 3 cone / 9 project — was rank #2 there behind the ray-class hub and
landed 2026-10-20 (§1, WORKORDER-ATS); the leaf shelf drops 445 → **444** candidates and its head
moves to `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen` (807). The leaf's own
successor `AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule` (184) is now
on the `--ready` shelf — the same principle at the whole cut, and the next cut of the family. The
standing count after the same day's later landings is **348** candidates (§1, WORKORDER-PH3A–PH3D and
the phantom-landings refactor: `Module.End`, `PowerSeries`, `Algebra` and `CongruenceSubgroup` — ten
modules, 155 declarations — which emptied four namespace rows of the demand), and the FR1 set (§1)
takes the `UpperHalfPlane` Fricke row off it: `frontier.py --ds --target` reads `needed 0 / 0 lines`
and *"target is ported"*, so one leaf and its 1,307 raw `S_` lines are gone. Caveat, and it is the one
the next cut must not ignore: `frontier.py` counts `private` declarations as ported, so 23 pin headlines
the port states only privately are missing from that shelf
([CARRY-FORWARD.md](../CARRY-FORWARD.md), homing note §10).

**The leaf shelf's next two rows were the `Matrix.` pair, and they have landed** (§1, WORKORDER-MG1):
the shelf reads **442 → 440** and loses 1,550 raw lines, and the `Matrix.`-namespace demand goes
**11 nodes / 4,519 lines → 9 / 2,969**. The family's remainder is priced together in
[deligneSerre/TOPIC-matrix-family-in-cone.md](deligneSerre/TOPIC-matrix-family-in-cone.md) — four
ready leaves (970 net new, +73, WORKORDER-MG2), the
`GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le` row
(1,242) behind its own `ModularCurve.SerreImage.contains_SL2` premise (390), and four
`Matrix.SpecialLinearGroup` free-group rows that are **not ready** (686 own lines behind 3,275 raw
lines of `Monoid.CoprodI` / `SimpleGraph` / `Subgroup` premises) and are another column's subject.

**The two `tateCurve_…_nonToricPoint_…` rows are exact twins, and must be cut as one.**
`S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean` and its `_pointY_…_snd`
sibling are both 1,343 lines and differ by **8 diff lines**; normalized at the namespace stem, the
only difference is the final `solution` — `… = (nonToricPoint F p c j).1 := BridgeX.pointX_slot …`
against `… = (nonToricPoint F p c j).2 := BridgeX.pointY_slot …`. The 69 other declarations
(1,311 lines) are byte-identical at the same line numbers. `port_plan` reads 2,686 raw → **1,325
net new** / 72 groups, 0 substitutions. The order is the WORKORDER-E shape: write the shared
development once (`private`) and derive both public headlines from the two `BridgeX` conjuncts.

**The readings differ, and the conservative one is the one to plan from.** The table above is the
default `union` name scan. `--frontier sources` (no name scan) gives `F` 837 nodes / 519,647, a
`needed` of 1,438 nodes / 542,136, and 85 ready candidates (2026-10-19). Both readings now count a
module wired by its own
`spec-pin:` header as ported — `frontier.py` reads those headers into the `sources` tier — so the
new wire's handoff does not drop a landing out of the conservative reading. The gap is the last-name blindness of
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
closes. The step-by-step recipe — the exact commands, what each figure means, the homing rule and
the instrument failures the last two passes hit — is
[deligneSerre/TOPIC-scoping-a-ds-set.md](deligneSerre/TOPIC-scoping-a-ds-set.md).

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
  (declarations the port already has: import, never re-prove), the port-`private` rows (promote or
  re-derive), the **shared blocks** the target files have in common (the dedup: write once), the
  near-duplicate / binder-only rows, and the *suspect* type-only `def` matches the parser cannot
  judge (read both copies before applying any). **Read the substitution table by shape, not by
  text**: it reports two tiers — the checker's byte-identical tier, and the *shape* tier (same
  conclusion, same hypothesis list, once section variables, instance arguments and bound names are
  normalised). The shape tier is the reuse answer: the pin writes one lemma many ways
  (`mem_of_ord_nonneg` occurs in 33 distinct texts across 263 files), and the port's copies were
  homed from the `Theorems/` wrappers, so a byte scan under-reports systematically. Its `residue`
  list names the few the shape tier cannot settle (one side keeps the variable in a file-level
  `variable`); read those two texts. A *restated* lemma must still use the pin's own text shape, or
  `check_port.py` reports a `MISMATCH` — importing is the normal move.
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
  `private` whatever the cluster must name. Checked against the pin; a new module is wired by its
  own `spec-pin:` header (§6) and **not** by an entry in the frozen `SOURCES`/`PORT_FILES`.
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

*Review checklist* after each set: `spec/check_port.py --force` on the set's modules with **0
mismatched / 0 missing** and every public declaration accounted for (matched, or recorded in
`spec/decl_markers.tsv` as a `pin:`/`own:` entry) — no in-source per-declaration marker is added;
`--all` (or `--changed`) green over the whole wired surface, whose counts are the progress metric;
tier 1 green and 0 warnings; no `sorry`/`admit`, no bare `import Mathlib`; `#print axioms` on
every headline `[propext, Classical.choice, Quot.sound]`; `git status` showing only the set's
files. `spec/old_check_stmts.py` is the frozen registry, not run as a gate and never appended to
(§6). The checker is cache-aware and `--force` re-checks one module from scratch, which is the
per-set gate. The statement instrument itself — `norm`, the declaration regex, the hash — is
shared with `spec/old_check_stmts.py`, so its mutation sensitivity is still exercised by
`python3 spec/old_check_stmts.py --selftest` when that parser changes, not per set.

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
* **to isolate a slow declaration, never re-elaborate a file.** The quick recipe, in order of
  preference: (i) `import` the module that already owns the declaration (its olean is the prelude) and
  restate only the target, proof pasted — the probe then costs that proof alone; (ii) in a scratch copy,
  stub the prelude with `sorry` (keep the statements, replace the proofs) and elaborate the one target;
  (iii) cut at *section* boundaries only, deleting a whole section's proofs rather than truncating the
  file — a truncated file fails to elaborate at all, which burns a long run and answers nothing. Every
  probe is a ≤ 60 s turn; if a probe cannot finish in that, the probe is wrong, not the file. One long
  *profiled* run per module is the sanctioned exception — `set_option profiler true` at the library cap
  gives the per-declaration split (elaboration vs typeclass inference vs tactics) and the module's total,
  once, after which the isolation above takes over;
* **a timeout is not automatically a slow proof.** Stub the suspect declaration's *proof* with `sorry`
  and re-probe at the low cap: if the statement still times out, the cost is a term in the type, and
  no proof-level change (pinning a search argument, a local `letI`, a reshaped tactic block) can move
  it. First instance: the now-landed `ZLattice` pair's three `PeriodizeLift` declarations, each far
  over the 200k diagnostic (one alone still timed out at 1M) — all of it the argument check of a
  hypothesis whose type contains the norm on a restricted `ContinuousMap` (`isDefEq` unfolds `dist x 0`
  and its `BoundedContinuousFunction` machinery); naming that hypothesis type once brought the whole
  614-line module to ~6 s at 20k hearts and a 5.5 s build. The fix was a name, not a pinned instance —
  full bisection, mechanism and the 7 registered `own:` rows:
  [logs/poisson-summation-statements.md](../logs/poisson-summation-statements.md);
* **the register of open build-time issues is [logs/build-time-issues.md](../logs/build-time-issues.md)**
  (the owed `ResidueSumQExpansion` rework, the resolved `ZLattice` blocker, the tree's incomplete
  oleans, the lock/memory rules, and the `/usr/bin/time` measurement trap). Read it before any
  build-heavy wave;
* **the cap is a diagnostic, not the build budget.** The library's own setting is the lakefile's
  `maxHeartbeats 4000000`, so a declaration whose measured cost is **arithmetic defeq** rather than
  instance synthesis (`Add.add`/`Nat.rec` unfolding from a large expression) may exceed the 200,000
  edit-loop budget and still be correct and green at tier 1. The rule for that case: **no `set_option`
  of any kind**, the pin's own bump, the bisection and the diagnosis recorded in the module header, and
  the tier-1 `lake build` as the gate. First instance:
  `EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow` (pin 4,000,000; port
  300k–400k; `lake build` 31 s, WORKORDER-MG3). Deferral is reserved for a proof that no longer
  **closes** at any budget — the `HeckeCosetSeam.of_dvd` case;
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
python3 spec/check_port.py --changed                    # the new per-module wire (the registry)
python3 spec/check_port.py --force <the set's module>   # one module, every public declaration
python3 spec/check_port.py --all                        # the whole wired surface
flock .lake/flt_build.lock timeout 900 lake build        # the milestone build
timeout 180 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
python3 spec/unwired_register.py --check                # tier-3 surface current
```

plus a `#print axioms` probe over the set's headlines and a `grep` sweep for
`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/heartbeat overrides.

**One checker, one wire per module** (playbook §4). A set's new module carries `spec-pin:` lines —
the pin file per source, the `Theorems/` wrapper for a statement and the `P2M/Sol/S_` file for a
transcribed proof — and is verified by `spec/check_port.py`, which matches on the statement hash:
a faithful but renamed copy verifies, a same-name statement that differs is a `MISMATCH`, and an
engine's internal declarations are checked, not only its headline. Declaration-level exceptions
are `pin:`/`own:` entries in **`spec/decl_markers.tsv`**, keyed by `(module, full declaration
name)`; the source carries no marker for new work, and the grandfathered in-source `-- pin:`/
`-- own:` comments are still read where they exist. `spec/old_check_stmts.py` is the frozen
registry of the grandfathered `PORT_FILES`/`SOURCES` set, **not run as a gate**: do not append to
it, and do not expect its 10473 to move. Each work order records its own numbers, measured on the
tree it leaves, not copied from this note.

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

**The ready shelf** of §2 read 85 candidates on 2026-10-19 (67 when this note was last
refreshed), of which 13 are `ModularCurve` and the column's own. The
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
fan of [automorphicForm/TOPIC-arch-casimir.md](automorphicForm/TOPIC-arch-casimir.md) §5 Set C.

The **archimedean type-span leaf** has landed too
([../logs/arch-type-span.md](../logs/arch-type-span.md), WORKORDER-ATS): it was the demand's
rank-#2 high-impact leaf, it is a façade over the shared `Q09` engine
(`RepTheory/TypeReproducer.lean`), and it put its successor
`AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule` — the same principle at
the whole archimedean cut, 184 silo lines, `used_by` 6 cone / 7 project — on the ready shelf. The
family's third row,
`CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous`, still needs three
nodes / 369 lines; the seven other consumers are the `CuspidalConstituent` cut-weight and
isotypic-cut rows of §2.

The **matrix-group right-finite pair** has landed too (§1, WORKORDER-MG1) as a mathlib supplement,
and it moved the `Matrix.`-namespace remainder onto the shelf: the four ready leaves of
`Matrix.exists_bijective_transpose_mulVec_of_adjoin_intCast` (765), `…specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag`
(114), `…SpecialLinearGroup.closure_diagonal_unipotent_weyl_eq_top` (86) and
`…exists_specialLinearGroup_mul_upperTriangular` (76) are WORKORDER-MG2 (970 net new, +73); the
`GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le` row
(1,242) is ready only with `ModularCurve.SerreImage.contains_SL2` (390, the column's own §2 shelf
row) and is set MG4 (the older rows call it MG3; 1,611 net new, +53), **landed 2026-10-20** as a full
dispatch (record: [logs/matrix-gl2-count.md](../logs/matrix-gl2-count.md)); the four `Matrix.SpecialLinearGroup` free-group rows landed 2026-10-20. All three cuts are priced in
[deligneSerre/TOPIC-matrix-family-in-cone.md](deligneSerre/TOPIC-matrix-family-in-cone.md).

The **Hecke coset seam** has landed (§1, WORKORDER-HS1) with its definition gate — the three
`LocalLanglands` `Definitions/` modules the port had never homed — and its 39-line well-definedness
row has landed as an append to `RepTheory/LocalLanglands/HeckeCosetSystem.lean` (addendum §9 of the
order). **The `HeckeIntegralSeam.` namespace is out of the D-S demand entirely.** The
`_principalLevel` near twin has landed as well (addendum §10): outside the cone, but banked now
because it re-proves the same engine — with the engine public it cost 11 restated declarations and
45 imports. What the family still holds, all outside the cone and cut when a column needs it:
`exists_isHeckeCosetSystem_integralSubgroup_diagPi` (35),
`IsHeckeCosetSystem.exists_bijective_forall_exists_mul_eq_mul_of_mem` (72),
`IsHeckeCosetSystem.sum_apply_mul_prod_ofFn_eq_of_mem` (111),
`exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq` (137), and
`exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd` (957 pin lines, the same engine under
`v ∣ N`, which is now a small module on the public engine). The first consumer to become ready is
`AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup`
(229).

The `Place` **separability pair** has landed too (§1, WORKORDER-SU1): a uniformiser at a place
is a separating element, and so is an element of nonzero tame order
([../logs/separating-uniformiser.md](../logs/separating-uniformiser.md)). It put four rows on the
ready shelf — the top one is
`AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable` (576 silo lines, 5 of its 6 cone nodes
ported), then `Place.diffCoeff_smul_D_of_ord_eq_one` (28), `Place.diffCoeff_smul_D_eq_of_ord_eq_one`
(26) and `AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable` (20). The first three were
one development — the coefficient against a uniformiser and its integrality — and have landed
(2026-10-24) as an absorption into the already-ported
`AlgebraicCurve/Differential/Generation.lean`, which was handed over to the new checker in the same
edit; record: [algebraicCurve/TOPIC-diffCoeff-integrality.md](algebraicCurve/TOPIC-diffCoeff-integrality.md).
`frontier.py --ds --ready` reads 1,206 → 1,203 needed nodes, and the next row of the family is
`Place.ord_diffCoeff_D_nonneg_of_perfectField` (17 ln). `isCurveOver_of_transcendental_of_isSeparable`
(20) is still on the shelf and is not a premise of the three.

The **local-parameter family** is complete (§1): the finite cover
([logs/localParam-finite-cover.md](../logs/localParam-finite-cover.md)), the branch uniqueness,
the local parameter with its meromorphic-order dictionary, and the four leaves those rest on
([logs/localParam-family.md](../logs/localParam-family.md)). Its capstone is the charted-space
node `AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` ("the
places of a complex function field form a compact Riemann surface", 1,576 silo lines), which now
lacks only its own assembly; beside it sit
`Place.connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex` (679),
`Place.exists_forall_ord_eq_finset` (291, ready) and `Place.exists_ord_eq_one`. The family's own
prelim blocks are *not* reproduced: the port imports one copy of each, at its theory home
(`Place/OrdCalculus.lean`, 19 declarations after the re-home) — see
[logs/localParam-family.md](../logs/localParam-family.md) §1 and §3.5.

The **Γ₁/Nebentypus pair** the shelf once showed at its head — the two `CuspForm` rows — is the
**lifting column's**, not this column's, and has landed there as
[deligneSerre/WORKORDER-S8-nebentypus.md](deligneSerre/WORKORDER-S8-nebentypus.md)
(`ModularForms/HeckeNebentypus{Existence,Fricke}.lean`, deduped onto the promoted
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

**The `Algebra` and `CongruenceSubgroup` rows left the demand at 1,239 nodes / 475,631 lines.**
Their successors are measured with `frontier.py --target`: the `AlgebraicCurve` function-field rows
that consume the integral-closure and denominator nodes, and the Hecke/coset rows that consume the
congruence-subgroup ones (`ModularCurve.finrankAlong_heckeAlphaHBar_of_dvd`,
`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary`,
`ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`, each 1,5xx–1,6xx lines of
remaining demand at the time of the landing). The `CongruenceSubgroup` row is now **empty**: its fifth node,
`CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three`, was not a port but a **lift** — 35 of its 40
declarations were already in the tree, byte-identical and `private`, in `EisensteinChiNegThree.lean` —
and it landed as `NumberTheory/ModularForms/Gamma0Three.lean` (40 wired) with the host importing it
([logs/phantom-landings.md](../logs/phantom-landings.md)). The dependent wave (51 modules / ≈413 s) is
owed and deliberately unbuilt; [logs/build-time-issues.md](../logs/build-time-issues.md) §3b.

**The `Module.End` and `PowerSeries` families left four near-ready successors and emptied two
frontier rows.** Measured with `frontier.py --target` before and after the landing (§1, WORKORDER-
PH3A/PH3B): the archimedean string-basis consumer
`AutomorphicForm.exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex` drops **4 nodes /
2,530 lines → 3 / 2,064** (it now lacks three `AutomorphicForm` nodes and nothing else); the
**Gauss regular-prolongation row**
`ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC` drops **2 / 1,284 →
1 / 853**, and its two `_residue` siblings are reached through the same node;
`ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem` drops **2 / 116 → 1 / 78**;
`ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion` **5 / 2,977 → 4 / 2,791** and
`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary` **6 / 1,617 → 5 / 1,576**. The
multiplicity-one consumer `CuspForm.nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one`
is still 51 nodes out and stays banked. The frontier's `Module.` and `PowerSeries.` namespace rows
are gone; the leaf shelf reads **358** candidates and the demand **1,248 nodes / 476,792 raw `S_`
lines**.

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

The checker wiring convention is the per-module one: a module carries `spec-pin:` lines in its
leading `/- … -/` block naming the pin files that verify it (the `Theorems/` wrapper for a
headline, the `P2M/Sol/S_` file for a transcribed engine). Declaration-level exceptions — a rename,
a source outside the header, a tier-2 statement — are `pin:`/`own:` entries in
**`spec/decl_markers.tsv`**, keyed by `(module, full declaration name)`; the Lean source carries
**no** per-declaration marker for new work (the grandfathered in-source comments still work).
Nothing is appended to `spec/old_check_stmts.py`: that file is now only the frozen registry and
the shared parser. `spec/statement_db.py build` makes the pin corpus (`tmp/flt-statements/`,
git-ignored) that the checker reads; `spec/statement_db.py show <name>` prints a pin signature
with its `file:line`.

The statement instrument's mutation sensitivity is its own unit test — the parser and hash are
shared with `spec/old_check_stmts.py`, so run it when that parser changes rather than on every
set:

```bash
cd lean
python3 spec/old_check_stmts.py --selftest
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
* **The `Q09` engine now has a second pin-silo consumer.** `RepTheory/TypeReproducer.lean` (tier 3,
  registered) is the home of the `TypePiece`…`MultiPlace` engine that the pin writes into both
  `S_AutomorphicForm_exists_isArchTestFactor_…` and
  `S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`;
  the arch-type-span landing ([logs/arch-type-span.md](../logs/arch-type-span.md)) imports it and
  re-proves nothing. Two consequences for later work: (i) the remaining eight consumers of that
  leaf will find the engine there, not in their own silos; (ii) their proofs rely, as the pin does,
  on `archTypeSubmoduleAt` being *definitionally* `typeSubmodule (rowIsometryInclAt₀ F w) τ.ρ`
  (`hcut := rfl`), so a wrapper around that definition would turn a `rfl` into a proof obligation.
* **The matrix-group twin is parallel by construction.** `Analysis/MatrixGroup/{Unitary,Orthogonal}RightFinite.lean`
  are ≈80 % identical (898 diff lines, 33 hunks) because the pin writes the `ℝ` development as the
  `ℂ` one without conjugation, and the port keeps the pin's text. The generic `[RCLike 𝕜]` statement
  — which after the base-field normalization is *one* sentence, since `Matrix.orthogonalGroup` is
  mathlib's `abbrev` for `unitaryGroup` — is the natural revision, not a cleanup: it would wire 2
  headlines instead of 96 statements and leave ≈45 declarations in the tier-3 register. The route
  was priced and declined on 2026-10-20 (topic §7). The shared
  `LinearAlgebra/Dual/EvalSpan.lean` lemma has no mathlib counterpart (a recorded negative from
  `Mathlib/LinearAlgebra/Dual/`) and exactly two importers today.
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
  `WeightOne/RationalityDvd.lean` as `Gamma1_le_of_dvd'`). The same wave cleared
  `Lifting.lean`'s `haveILetI` warnings by taking Lean's own `haveI`→`have` suggestion at every
  site. The next tenant of the same home is `Gamma_le_Gamma1`
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
* **The frontier and the new wire.** `frontier.py`'s `sources` tier reads the frozen checker's
  `SOURCES` *and* the `spec-pin:` headers of the port tree (2026-10-19), so a module handed over from
  `PORT_FILES` is ported in both readings; the `names` tier had always seen it (it scans
  `lean/FLTForHuman`). Neither reading has any per-declaration "ported" flag: the unit is the pin
  *node*, so the pin's
  hundreds of copies of one lemma (263 for `mem_of_ord_nonneg`) stay in the demand as nodes of their
  own even when the port homes the lemma once — the landing only makes each of them cheaper.
* `frontier.py --ready` resolves names by last name, so a pin node that shares a last name with a
  ported declaration of another namespace is priced as ported. The known instance is the
  `ModularForm`/`CuspForm` rename pair of §7's deferred row — 10 needed nodes / 5,172 raw `S_`
  lines under `--frontier sources`, 1 / 36 under the default `union`. Read the pin node itself
  before trusting `ready` for such a pair, price the pin's `Theorems/` imports too, not only its
  `Definitions/` ones, and re-run both frontier readings: `port_advise` and `port_plan` never walk
  imports, so an unported premise outside the target files is invisible to them.
* **Protocol migration.** The per-module wire (`spec-pin:` header + `spec/check_port.py`, with
  `spec/decl_markers.tsv` for declaration-level exceptions) is current in
  [porting-playbook.md](../porting-playbook.md) §4, in this note's §3/§6/§8 and in the tooling
  (`tools/deps`, `spec/unwired_register.py`). The **older column notes and work orders still
  describe the retired "append to `PORT_FILES`/`SOURCES`" route** — they are the record of how those
  landings were wired, not instructions; a new set follows §6. The **573** modules still owned by the
  frozen registry are the migration backlog, and each moves when it is edited for another reason
  (playbook §4) — the Frobenius-subfield host moved that way on 2026-10-20, and the four q-expansion
  definition-layer modules on 2026-10-21 (§1).
* **The `of_dvd` seam sibling is scoped and deferred.** `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd`
  (957 pin lines, 55 declarations) is the family's last large row and sits outside the cone. It
  drags in **no modules** (every dependency is inside `HeckeCosetSeam`'s closure; its five extra
  `Definitions/` imports are inert), but its residual — 13 declarations / ≈320 lines — is dominated
  by a 153-line covering lemma that carries `set_option maxHeartbeats 3200000 in` in the pin and
  whose entrywise matrix steps no longer close under mathlib `v4.34.0`. That is proof development
  under the no-heartbeat-raise rule, so it waits for its own order (WORKORDER-HS1 addendum §11; a
  compiling draft is parked at `lean/tmp/HeckeCosetSeamDvd.draft.lean`).
