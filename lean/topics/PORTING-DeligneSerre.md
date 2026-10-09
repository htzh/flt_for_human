# The Deligne–Serre weight-one column — frontier, workflow and plan

**Status (2026-10-08).** The unconditional 54-node slice shipped 2026-09-29 (§1).
The column has since taken four more clusters off the same frontier — the
q-expansion head, its two successor sets, and the definition layer and hub work
under them — using the workflow of §3. The checker is at **7218 identical
(313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (7254 checked)**, and
the `DeligneSerre` target's ready shelf is **83 nodes** (§2).

This note is the column's plan, not its history: §1 what has shipped, §2 the
frontier as it stands, §3 the workflow the manager follows, §4 the shared ground
(definitions, promotions, hubs) that is the manager's own work, §5 the build
economy, §6 verification, §7 what remains. Everything is measured against the pin
`anthropics/fermats-last-theorem@aa2d8b3` with `tools/deps`; the port's mathlib is
`v4.34.0`.

Companions:

- [../../math/019-deligne-serre-weight-one.md](../../math/019-deligne-serre-weight-one.md)
  — the mathematics: the theorem, the lifting, the assembly from residual data.
- [../../studies/deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md)
  — the effort measurement, the subject clusters, and the two gates (§1, §3.1).
- [porting-playbook.md](../porting-playbook.md) — the rules; §2.1–§2.6 (planning),
  §3.1–§3.7 (execution, sets, the build ladder), §4 (faithfulness), §5 (sharing).
- The current head's planning record:
  [functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md](functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md)
  and its successors
  [functionFieldGeneration/TOPIC-qexp-successors.md](functionFieldGeneration/TOPIC-qexp-successors.md),
  [functionFieldGeneration/TOPIC-qexp-successors-2.md](functionFieldGeneration/TOPIC-qexp-successors-2.md).
- Adjacent columns: [PORTING-Hecke.md](PORTING-Hecke.md), [PORTING-Level.md](PORTING-Level.md).
- The `WeierstrassCurve` ready shelf — eight nodes, four stories, and the good-reduction
  definition gate:
  [deligneSerre/TOPIC-weierstrass-ready-shelf.md](deligneSerre/TOPIC-weierstrass-ready-shelf.md);
  its first set, dispatched 2026-10-08:
  [deligneSerre/WORKORDER-W1-automorphisms.md](deligneSerre/WORKORDER-W1-automorphisms.md).

## 1. What has shipped

**The unconditional slice (2026-09-29).** Everything that does not depend on the
two automorphic gates — the weight-one mod-`ℓ` lifting half plus the assembly half,
54 nodes, 55 new modules, ≈15,200 written lines, checker `2058 → 2552` at the time,
milestone build 4,805 jobs, consumer wire test `spec/DeligneSerreConsumer.lean`.
The slice takes the residual family as a hypothesis, so it lands without the
ray-class input or the automorphic layer. The after-the-fact record is
[../logs/deligne-serre-port.md](../logs/deligne-serre-port.md); the running
friction/promotion ledger is
[../logs/deligne-serre-friction.md](../logs/deligne-serre-friction.md).

**The q-expansion column (2026-10-08).** The frontier's head moved to the
`ModularCurve` q-expansion cluster; it has run as:

| set | subject | modules | checker |
|---|---|---|---:|
| prerequisite | the promotion pass (82 declarations, JOneES block + hub rows) | `X1/FunctionField.lean` + 3 hubs | 6520 → 6602 |
| [SET-R-A](functionFieldGeneration/SET-R-A.md) | the Γ₀-rationality pair, engine once | `WeightOne/RationalityDvd.lean` (1,204) | 6602 → 6652 |
| [SET-R-B](functionFieldGeneration/SET-R-B.md) | the `X_H` relative-degree bound | `XH/Relrank.lean` (1,153) | 6652 → 6798 |
| [SET-R-C](functionFieldGeneration/SET-R-C.md) | the JOneES tail: finrank/index + residue field | `X1/FunctionFieldDegree.lean` (690), `X1/FunctionFieldResidue.lean` (1,027) | 6798 → 6904 |
| hub edit | `Gamma0Integral` promotion + duplicate-block collapse | that hub | 6904 → 6920 |
| [SET-R-D](functionFieldGeneration/SET-R-D.md) | the three successors: Deuring reduction, constant extension, Atkin–Lehner | `Defs/QExpValuationReduction.lean` (601), `X1/FunctionFieldIsAlgClosed.lean` (405), `X1/IsIntegralAtkinLehner.lean` (484) | 6920 → 6975 |
| definition layer | the `ValuationSubring` residue block, homed publicly | `NumberTheory/ValuationAtPlace.lean` | 6975 → 6979 |
| [SET-R-E](functionFieldGeneration/SET-R-E.md) | the `isAlgClosed` finrank bound; the two Atkin–Lehner exchanges | `X1/FunctionFieldFinrankIsAlgClosed.lean` (154), `X1/AtkinLehnerExchange.lean` (2,110) | 6979 → 7218 |

Every set is: one work order, one subagent, reviewed by the manager before the
next; no existing module edited by a subagent; nothing committed by an agent.

**The `WeierstrassCurve` shelf opens (2026-10-08).** The column's first two sets off the ready
shelf described in §2, and the first ones outside the q-expansion cluster.
[SET-W1](deligneSerre/WORKORDER-W1-automorphisms.md) is the exceptional automorphisms of the
supersingular curves in characteristics 2 and 3, plus the point-transport prelude the two
headlines share: three new modules, 1,520 written lines, checker **7218 → 7231** identical.
[SET-W2](deligneSerre/WORKORDER-W2-division-fields.md) is full level structure and the
division field: two new modules under `WeierstrassCurve/Torsion/`, 910 written lines, checker
**7231 → 7233**, the two headlines composed in the consumer's `Zone W2`. Story D followed on
2026-10-08: its `stepCurve` half ([W3](deligneSerre/WORKORDER-W3-stepcurve.md), 298 lines) and,
after a manager refactor wave removed a co-import collision (§2), its `zmultiples` half
([W3b](deligneSerre/WORKORDER-W3b-zmultiples.md), 468 lines) landed at checker **7234** and
**7247**. All are warning-free, axioms clean (`[propext, Classical.choice, Quot.sound]`), no
existing module edited — apart from the two refactor/definition hub appends the manager owns —
and nothing committed.

Both landings were depth, not breadth. After W1 the frontier went 812 → **814** nodes and the
ready shelf 83 → **81**; after W2 it went to **F 816 / needed 1,711 / ready 79** — in each case
nothing new entered, because the successors (`exists_j_eq_zero_torsion_basis_…`,
`…_of_order_four`, `natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two`,
`ord_census_qExpFunctionFieldC_gammaH_of_char_three`, and the 85k-line `ModularCurve` moduli
nodes) each still need other unported `WeierstrassCurve` nodes. The four shelf nodes left are
stories D (Vélu-quotient `j`) and C (good reduction, gated — §2).

## 2. The current frontier

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
```

| quantity | value |
|---|---:|
| target closure | 2,308 nodes / 1,089,430 raw `S_` lines |
| frontier `F` | 812 nodes / 425,264 |
| `needed` (unported demand) | 1,715 nodes / 752,548 |
| **ready to port** (`needed == 1`) | **83 nodes** |

The ready shelf by top-level namespace: `ModularCurve` 32, `AlgebraicCurve` 23,
`CuspForm` 10, `WeierstrassCurve` 8, `PeriodPair` 2, `ModularForm` 2,
`CuspFormClass` 2, `CohCarrier` 2, `AutomorphicForm` 2. The head by silo is
`WeierstrassCurve.exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two`
(988 `S_` lines), then the `ModularCurve.LevelN.*` group
(`exists_place_ord_neg_forall_smul_eq` 891,
`valuation_apply_smul_le_one_of_tendsto_div_smul` 820,
`exists_algHom_laurentSeries_qExpansion` 602,
`exists_place_ord_sub_pos_forall_smul_eq` 521,
`exists_monoidAlgebra_algEquiv_fixedField_eq_adjoin` 472, …) — a level-`N` cluster.

**The `WeierstrassCurve` cut (2026-10-08).** The eight ready `WeierstrassCurve.*` nodes were
scoped as four mathematical stories — the exceptional automorphisms of the supersingular
curves in characteristics 2 and 3 (1,412 lines), full level structure and division fields
(910), the Serre–Tate good-reduction mechanism (786), and the Vélu-quotient `j`-map (760) —
at **3,868 raw `S_` lines → 3,586 net new math lines**, all mutually independent. Six of the
eight are statement-ready; the good-reduction pair is gated behind the unported
`TorsionIntegral → ReduceHom → ZeroComponentReduction` definition chain, which is a manager
wave, not a set. The first two sets (the characteristic-2 and characteristic-3 automorphisms
with their shared point-transport prelude; then full level structure and the division field)
**landed 2026-10-08** as
[deligneSerre/WORKORDER-W1-automorphisms.md](deligneSerre/WORKORDER-W1-automorphisms.md) and
[deligneSerre/WORKORDER-W2-division-fields.md](deligneSerre/WORKORDER-W2-division-fields.md) —
checker 7218 → 7231 → 7233 identical, 0/0, warning-free — and the shelf then read **F 816 /
needed 1,711 / ready 79** (§1). The remaining stories follow one set at a time, reviewed
between. **Story D closed 2026-10-08**: its `stepCurve` half landed as
[WORKORDER-W3](deligneSerre/WORKORDER-W3-stepcurve.md) (`Velu/StepCurveSubgroup.lean`, 298
lines), and its `zmultiples` half — parked by the co-import collision of §5.1 — was unblocked by
a manager refactor wave (one hub edit renaming the character-free `normFormulaAlong_of_elliptic`
in `Velu/RestrictAlong.lean` to `…_cf`, measured blast radius: ~100 of 101 references resolve to
the `Engine` copy, so the other had one user; one `OWN_PROOFS` entry; one wave build of 9,352
jobs / 65.6 s) and landed as
[WORKORDER-W3b](deligneSerre/WORKORDER-W3b-zmultiples.md) (`Velu/CyclicQuotientJInjective.lean`,
468 lines). **Every remaining `WeierstrassCurve` shelf node is now gated on the W4 definition
wave alone** — `exists_inertia_equivariant_reduction_of_variableChange_eq_map` (601) and
`exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero` (185) — whose stages 2–4 are paused and
handed off (resume at the order's §1a). Story C still waits on that wave. Scoping, the blocker,
the refactor, the wave plan and the reproduce recipe:
[deligneSerre/TOPIC-weierstrass-ready-shelf.md](deligneSerre/TOPIC-weierstrass-ready-shelf.md).
Story C's definition wave is now scoped and **started, then paused for hand-off**: its used block
is 88 of 145 declarations / 2,081 raw pin lines over four stages
([WORKORDER-W4](deligneSerre/WORKORDER-W4-definition-wave.md), **resume at §1a**), of which
**stage 1 landed 2026-10-08** — the pin `Def_WeierstrassCurve_ReductionMap.lean` used block,
complete: nine public declarations in `WeierstrassCurve/Reduction/Point.lean` plus four
`ValuationSubring` rows appended to `NumberTheory/ValuationAtPlace.lean`, one wave, checker
7233 → **7246**, 9,353 jobs / 51.8 s. Stages 2–4 (the remaining **1,923 raw lines**: the
`TorsionIntegral` estimate chain, `ReduceHom`, `ZeroComponentReduction`) are handed to a new
session; the wave hangs off just **17 entry points**, tabulated in the order. Scoping, the
blocker, the refactor, the wave plan and the reproduce recipe:
[deligneSerre/TOPIC-weierstrass-ready-shelf.md](deligneSerre/TOPIC-weierstrass-ready-shelf.md).

The two gates of §7 are still in the unported demand but are not ready; they are
not on this list and must not be scheduled from it.

## 3. The workflow

This is the loop the column now runs. Steps 1–4 are the manager's; step 5 is the
subagents'; step 6 closes.

**1. Read the frontier.** The command above. `--ready` keeps only the nodes whose
whole demand is themselves — every premise is already ported, so only the node's
own proof is missing — and `--rank-by silo` orders them by the raw `S_` lines of
their **whole demand**, i.e. by how much mathematics stands behind them, not by
the size of their own file. This is demand, and it is the only list to plan from.
The `hops`/`used_by` columns choose *within* a cluster; they do not choose the
cluster.

**2. Cut a cluster by mathematics.** 3–6 ready nodes that tell one story in one
layer — the Γ₀-rationality pair; the `X_H` relative-degree bound; the JOneES
tail; the Atkin–Lehner exchange. Namespace and pin file are *not* the cut: the
first q-expansion head was one namespace but three different layers, which is why
it ran as three sets. The test is whether one sentence states the cluster's
subject without an "and".

**3. Scope the cluster with the tools.**

* `port_advise.py --target <node> … --json build/<cluster>_advise.json` — the
  substitution table (declarations already byte-identical in the port: import,
  never re-prove), the port-`private` rows (promote or re-derive), the **shared
  blocks** the target files have in common (the dedup: write once), the
  near-duplicate / binder-only rows, and the *suspect* type-only `def` matches the
  parser cannot judge (read both copies before applying any).
* `port_plan.py --json …` — the budget: raw lines, once-only dedup, boilerplate,
  **net new math lines**, declaration groups.
* `build_ladder.py --edit <host>` on **every** candidate host — the cascade each
  edit will force, in modules and lines.
* **Hand-check the import list.** `--ready` and `--with-defs` do not see
  import-only definitions: every `Definitions/Def_*.lean` a target `S_` file
  imports must be checked by hand against the port, declaration by declaration
  (§4a).

**4. The manager does the shared ground — this is the point of the split.** Before
any subagent runs:

* **(a) the definition layer.** Home whatever definitions the cluster's pin
  `Def_*` imports need and the port lacks, at the natural *theory* home rather
  than a new `Def_`-named file; promote out of `private` whatever the cluster must
  name. Checked against the pin, wiring appended to `SOURCES`/`PORT_FILES`.
* **(b) promotions and every other hub edit.** Any edit to an existing module is
  the manager's, not a subagent's: it is the only thing that re-elaborates the
  cone, so it is done once, deliberately, with the price known.
* **(c) dedup the scoping turned up.** A hub that carries the same private block
  twice, a copy that a promotion makes redundant — fold it into the same pass,
  because the wave is already being paid and deferring it pays nothing.

Each such edit is priced, applied, built at tier 1, checker-run, and followed by
**one** wave build; then the touched files freeze and no subagent may edit them.
Worked examples: the `Gamma0Integral` promotion of sixteen rows *and* the
collapse of the seventeen-row duplicate block in the same edit (module 2,349 →
2,253 lines, rebuild 36 s → 15 s); the `ValuationSubring` residue block homed in
`NumberTheory/ValuationAtPlace.lean`, which removed the last `private`
re-derivation from a landed module.

**5. Divide into sets; dispatch and review in series.** One set = one mathematical
story = one module or a small group = one subagent = one work order. Sets run
**one at a time**: parallel `lake build`s contend on Lake's lock and
cross-invalidate, so the second one looks like a blow-up and both are slower. The
manager writes the work order, dispatches, and then reviews the tree *itself*
before writing the next order.

*Work-order template* (playbook §3.3): scope and what is explicitly not this set;
pin sources (`Theorems/` wrapper for the statement, `P2M/Sol/S_` for the proof);
deliverable modules and the public/`private` split; what is already in the port and
must be reused; route with recorded negatives; risks; the build-discipline block
verbatim; the stop conditions; the report shape. Every order carries the
**hub prohibition**: a subagent that needs a `private` helper re-derives it
locally and reports it; one that believes a promotion is genuinely required
**stops and reports** with the declaration, host and `build_ladder.py --edit`
price. The manager decides.

*Review checklist* after each set: checker `0 mismatched / 0 missing` with the
`identical` delta reconciled against the new public surface; a one-token mutation
test (exactly one more `mismatched`, reverted); tier 1 green and 0 warnings; no
`sorry`/`admit`, no bare `import Mathlib`; `#print axioms` on every headline
`[propext, Classical.choice, Quot.sound]`; `git status` showing only the set's
files.

**6. Close out, then re-read the frontier.** Re-run step 1: the landed nodes leave
the shelf and their successors appear. Record the outcome in the work order (§8)
and in the cluster's topic, name the successors the landing unblocked, and cut the
next cluster.

## 4. The shared ground

**(a) Definitions first, and check them by hand.** Nothing can be *stated* before
the pin `Def_*` modules the cluster imports exist in the port. They are leaves —
cheap to build, no cascade — and they are invisible to `frontier.py`'s readiness
test, so the list is built by reading each target `S_` file's `import` block and
walking its `Definitions/Def_*.lean` declarations against the port. If only a
block of a pin definition module is needed (the common case), home that block and
record the rest as unported.

**(b) `private` is a build tool, not a statement about mathematics.** A helper
stays `private` when it only adapts another theory, or is generic glue a consumer
can re-derive in a few lines; it is promoted when it carries mathematics another
theory will state or reuse. A promoted pin-`private` helper is renamed at the
pin's name, and the checker verifies it through its dotted-name fallback. The
counterexample to avoid: a "promotion" of a declaration whose pin statement is not
the port's — the parser's type-only `def` matches are exactly this, and they are
how the X_H topic went wrong twice.

**(c) A hub edit is a wave, and the wave is the same price whether or not you
also clean up in it.** So: price it, do all of it at once, and only then freeze.
A subagent never opens the question; it reports and stops.

## 5. The build economy

* edit loop `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`
  (writes no `.olean`, builds no dependent);
* `flock .lake/flt_build.lock timeout 300 lake build <module>` when a file is done
  (writes the `.olean`, builds dependencies, never dependents);
* **no bare whole-tree `lake build`** while a set is in flight; one at a milestone;
* every `lake build` serialized and bounded; never raise the heartbeat cap.

The wave that a hub edit forces can exceed the 300 s bound on a real compute
(`ModularPolynomialE4Cube` alone is ~280 s). That is not a blow-up: the tell is
CPU time — high user CPU with a timeout is real work and the target list should be
re-run with a larger wall bound; ~0 CPU wall-time is another agent's lock. A
genuine blow-up is bisected, never re-run with a bigger heartbeat cap.

## 6. Verification

```bash
cd lean
timeout 300 python3 spec/check_flt_statements.py        # 7218 identical / 0 / 0 / 36 own
flock .lake/flt_build.lock timeout 900 lake build       # the milestone build
timeout 180 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
```

plus a `#print axioms` probe over the set's headlines, a `grep` sweep for
`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/heartbeat overrides, and
the one-token mutation test on a headline. The checker's `identical` delta must
equal the new public surface exactly; anything else is a bug. Per-set numbers are
in the work orders' §8.

## 7. What remains

The slice stopped where the automorphic input begins; two gates remain, both on
one subject (the automorphic/adèlic `GL₂` layer, scout §2):

* **Gate 1 — the Rankin-type second-moment bound.**
  `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen`
  (775 new nodes), feeding
  `…isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd`.
* **Gate 2 — coefficient-ring finiteness by upper density.**
  `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen`
  (783 new nodes), feeding `…exists_natCard_range_le_of_charpoly_frobenius_mem_…`.

Both also reach the shared ray-class node `M4aTorus.completedRayL_fe` by exactly
one route — `NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one` — and
use only its continuation conjunct, discarding the functional equation; behind
that interface the pair is 21 nodes / 8,265 lines. Budget by the `S_`-line column,
not by node count: most of those nodes are self-contained against mathlib and show
cost 1 in `frontier.py`. The **converse cone**
(`exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace`, 421 nodes) is a
separate subject and a separate effort.

Because the slice takes the residual family as a hypothesis and states the gates
as explicit hypotheses, both remainders attach to a fixed interface: they can be
ported later without reworking what shipped.

## 8. Reproduce

```bash
cd tools/deps
# the frontier (step 1)
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
# scope one cluster (step 3): advise → plan → price
python3 port_advise.py --target <node> --target <node> --json build/cluster_advise.json
python3 port_plan.py --json build/cluster_advise.json
python3 build_ladder.py --edit FLTForHuman/<host>.lean
# the gates
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --top 40
```

The checker wiring convention (append the `Theorems/` wrapper *and*, where it is
not already listed, the `S_` file to `SOURCES`; the module to `PORT_FILES`; both
last) is in every work order and in the friction log.

## 9. Residuals

* `locKer`/`adjoinRoot'` are public in `DeligneSerre/Lifting.lean` with no consumer
  today (kept per the pin).
* The private `det_eq` copies in `Gamma1Vanishing.lean`/`HeckeEigenNebentypus.lean`
  are statement-identical to the public `ModularForm.HeckeRepresentatives.det_eq`;
  the one un-promoted dedup candidate.
* The `Gamma0Integral.lean` prelude still exists `private` in its two sibling
  namespaces (`…GammaNBounded`, `…X1BoundedDenominators`); `GammaNBounded`'s
  `IsRat` is a *different formulation*, not a copy, and was deliberately left.
* `Definitions/Def_WeierstrassCurve_ReductionMap.lean`'s Weierstrass reduction half
  (`reducePoint`, `equation_residue`, …) is unported; only its `ValuationSubring`
  block was needed.
* The deferred half as in §7, by design.
