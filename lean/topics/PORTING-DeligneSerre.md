# The Deligne–Serre weight-one column — frontier, workflow and plan

The column ports `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` — the weight-one
mod-`ℓ` Galois-representation theorem — from the pin `anthropics/fermats-last-theorem@aa2d8b3`
(Lean `v4.33.1` / mathlib `db584cd6`) into the port library at mathlib `v4.34.0`. This note is
the column's state and plan: §1 what the port contains, §2 the frontier as it stands, §3 the
workflow the manager follows, §4 the shared ground (definitions, promotions, hubs) that is the
manager's own work, §5 the build economy, §6 verification, §7 what remains, §8 reproduce, §9
residuals. Every measurement is the pin's, read through `tools/deps`. The section numbers are
stable: work orders across the column cite §3 for the workflow and §7 for the gates.

The checker reads **9540 identical (656 promoted, 83 renamed), 0 mismatched, 0 missing, 38
own-proof declarations exempted (9578 checked)**. This column's recent landings: the
`TateFormal`/`TateSlots` definition layer, 9241 → 9304; the weight-4 Tate-slot engine and headline
façade (WORKORDER-F1), 9304 → 9318; the six `tateCurve`/Katz definition modules of WORKORDER-F2,
9318 → 9535 (+217); and the `BridgeX` twin/triplet engine and headline façade (WORKORDER-F2),
9535 → 9540 (+5). Each delta is exactly its new public surface, 0 mismatched / 0 missing. The
remaining growth since the note's earlier figures is other columns' landings; the column's own
history lives in `../logs/` and the work orders.

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
- The `WeierstrassCurve` ready shelf, its scoping and its set orders:
  [deligneSerre/TOPIC-weierstrass-ready-shelf.md](deligneSerre/TOPIC-weierstrass-ready-shelf.md).
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
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
```

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
`PeriodPair`, `ModularForm`, `NumberField` and `CohCarrier` rows are reached by the target closure
but are not `ModularCurve` rows, and are not this column's to cut.

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

**Not schedulable from this list.** The two gates of §7 remain in the unported demand but are not
ready; they must not be scheduled off a ready shelf.

## 3. The workflow

This is the loop the column runs. Steps 1–4 are the manager's; step 5 is the subagents'; step 6
closes.

**1. Read the frontier.** The command above. `--ready` keeps only the nodes whose whole demand is
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
reconciled against the new public surface; a one-token mutation test (exactly one more
`mismatched`, reverted); tier 1 green and 0 warnings; no `sorry`/`admit`, no bare `import
Mathlib`; `#print axioms` on every headline `[propext, Classical.choice, Quot.sound]`; `git
status` showing only the set's files.

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
timeout 300 python3 spec/check_flt_statements.py        # 9318 identical / 0 / 0 / 38 own
flock .lake/flt_build.lock timeout 900 lake build       # the milestone build
timeout 180 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
python3 tools/deps/unwired_register.py --check          # tier-3 surface current
```

plus a `#print axioms` probe over the set's headlines, a `grep` sweep for
`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/heartbeat overrides, and the one-token
mutation test on a headline. The checker's `identical` delta must equal the new public surface
exactly; anything else is a bug. Each work order records its own numbers, measured on the tree it
leaves, not copied from this note.

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

The **Γ₁/Nebentypus pair** the shelf once showed at its head — the two `CuspForm` rows — is the
**lifting column's**, not this column's, and has landed there as
[deligneSerre/WORKORDER-S8-nebentypus.md](deligneSerre/WORKORDER-S8-nebentypus.md)
(`ModularForms/HeckeNebentypus{Existence,Fricke}.lean`, checker +2, deduped onto the promoted
`CuspForm.HeckeEigenNebentypus` API).

**Deferred to its own order** is the C2 row
`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`. Its one substantive step is the
unported premise `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, and the chain behind
it is ≈4.8k raw / ≈2.1k `S_` lines; the ported `CuspForm` twin cannot stand in for it because the
cuspidal subspace does not span the Eisenstein part. The row is documented in
`X1/IntegralityJqNModC.lean`'s docstring and open in [CARRY-FORWARD.md](../CARRY-FORWARD.md).

## 8. Reproduce

```bash
cd tools/deps
# the frontier (step 1), both readings
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --frontier sources --ready --top 0

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

## 9. Residuals

* **Register.** The weight-4 engine (`TateSlots/{Convergence,SlotCoeff}.lean`) is tier 3: built and
  importable, not in `PORT_FILES`, with its 119 public declarations carrying `-- pin:` provenance
  in [spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md) (78 modules / 1,906 public / 1,618 with a
  pin original). Only the façade `TateSlots/CoefficientFormulas.lean` is diffed.
* `locKer`/`adjoinRoot'` are public in `DeligneSerre/Lifting.lean` with no consumer today (kept
  per the pin).
* The private `det_eq` copies in `Gamma1Vanishing.lean`/`HeckeEigenNebentypus.lean` are
  statement-identical to the public `ModularForm.HeckeRepresentatives.det_eq`; the one
  un-promoted dedup candidate.
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
