# The Deligne–Serre weight-one column — frontier, workflow and plan

The column ports `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` — the weight-one
mod-`ℓ` Galois-representation theorem — from the pin `anthropics/fermats-last-theorem@aa2d8b3`
(Lean `v4.33.1` / mathlib `db584cd6`) into the port library at mathlib `v4.34.0`. This note is
the column's state and plan: §1 what the port contains, §2 the frontier as it stands, §3 the
workflow the manager follows, §4 the shared ground (definitions, promotions, hubs) that is the
manager's own work, §5 the build economy, §6 verification, §7 what remains, §8 reproduce, §9
residuals. Every measurement is the pin's, read through `tools/deps`. The section numbers are
stable: work orders across the column cite §3 for the workflow and §7 for the gates.

The checker reads **7370 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 37
own-proof declarations exempted (7407 checked)**, and the milestone whole-tree build is green
(9,359 jobs).

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

## 1. What the port contains

The port holds the column's unconditional half, the q-expansion layer, and the definition and hub
ground the rest builds on. This is the state; the dated records are in `../logs/`.

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

**The `WeierstrassCurve` layer.** The whole good-reduction definition chain —
`WeierstrassCurve/Reduction/{Point,TorsionIntegral,ReduceHom,ZeroComponent}.lean`, the pin's four
`Def_*` modules ported whole — and the eight ready-shelf nodes it gated: the exceptional
automorphisms in characteristics 2 and 3, full level structure and the division field, reduction
surjectivity on the prime-to-`p` torsion, the inertia-equivariant reduction, and the
Vélu-quotient `j`-map. The shelf is empty; its scoping and set orders are
[deligneSerre/TOPIC-weierstrass-ready-shelf.md](deligneSerre/TOPIC-weierstrass-ready-shelf.md).

**The shared ground that edits existing modules.** The `ValuationSubring` residue block in
`NumberTheory/ValuationAtPlace.lean`; the `Gamma0Integral` promotion and its duplicate-block
collapse; and the resolution of the `normFormulaAlong_of_elliptic` co-import collision (one public
copy; the character-free copy is named `normFormulaAlong_of_elliptic_cf`), registered in
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
| frontier `F` | 820 nodes / 429,132 |
| `needed` (unported demand, `F` terminal) | 1,707 nodes / 748,680 |
| **ready to port** (all premises available) | **75 nodes** |

The ready shelf by top-level namespace: `ModularCurve` 32, `AlgebraicCurve` 23, `CuspForm` 10,
`PeriodPair` 2, `ModularForm` 2, `CuspFormClass` 2, `CohCarrier` 2, `AutomorphicForm` 2.
`WeierstrassCurve` no longer appears on it — all eight shelf nodes are ported (§1). The head by
silo is the `ModularCurve.LevelN.*` place/valuation cluster, then the modular-polynomial and
`CuspForm` Nebentypus rows:

| node | silo lines |
|---|---:|
| `ModularCurve.LevelN.exists_place_ord_neg_forall_smul_eq` | 891 |
| `ModularCurve.LevelN.valuation_apply_smul_le_one_of_tendsto_div_smul` | 820 |
| `ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion` | 602 |
| `ModularCurve.LevelN.exists_place_ord_sub_pos_forall_smul_eq` | 521 |
| `ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin` | 472 |
| `ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare` | 724 |
| `CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke` | 667 |
| `CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen` | 591 |

The two gates of §7 remain in the unported demand but are not ready; they are not on this list
and must not be scheduled from it.

## 3. The workflow

This is the loop the column runs. Steps 1–4 are the manager's; step 5 is the subagents'; step 6
closes.

**1. Read the frontier.** The command above. `--ready` keeps only the nodes whose whole demand is
themselves — every premise is already ported, so only the node's own proof is missing — and
`--rank-by silo` orders them by the raw `S_` lines of their **whole demand**, i.e. by how much
mathematics stands behind them, not by the size of their own file. This is demand, and it is the
only list to plan from. The `hops`/`used_by` columns choose *within* a cluster; they do not choose
the cluster.

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
`p2m_export` rows) to justify.

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

* edit loop `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`
  (writes no `.olean`, builds no dependent);
* `flock .lake/flt_build.lock timeout 300 lake build <module>` when a file is done (writes the
  `.olean`, builds dependencies, never dependents);
* **no bare whole-tree `lake build`** while a set is in flight; one at a milestone;
* every `lake build` serialized and bounded; never raise the heartbeat cap.

The wave that a hub edit forces can exceed the 300 s bound on a real compute
(`ModularPolynomialE4Cube` alone is ~280 s). That is not a blow-up: the tell is CPU time — high
user CPU with a timeout is real work and the target list should be re-run with a larger wall
bound; ~0 CPU wall-time is another agent's lock. A genuine blow-up is bisected, never re-run with
a bigger heartbeat cap.

## 6. Verification

```bash
cd lean
timeout 300 python3 spec/check_flt_statements.py        # 7370 identical / 0 / 0 / 37 own
flock .lake/flt_build.lock timeout 900 lake build       # the milestone build
timeout 180 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
```

plus a `#print axioms` probe over the set's headlines, a `grep` sweep for
`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/heartbeat overrides, and the one-token
mutation test on a headline. The checker's `identical` delta must equal the new public surface
exactly; anything else is a bug. Each work order records its own numbers.

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
  (14 needed, 283 own).

Both reach the shared ray-class node `M4aTorus` (12,126 raw `S_` lines) by exactly one route —
`NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one` — and use only its continuation
conjunct, discarding the functional equation. Budget by the `S_`-line column, not by node count:
most of those nodes are self-contained against mathlib and show cost 1 in `frontier.py`. The
**converse cone** (`exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace`) is a separate
subject and a separate effort.

Both remainders attach to the fixed interface the slice leaves, so they can be ported without
reworking what is there.

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
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --top 0
```

The checker wiring convention (append the `Theorems/` wrapper *and*, where it is not already
listed, the `S_` file to `SOURCES`; the module to `PORT_FILES`; both last) is in every work order
and in the friction log.

## 9. Residuals

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
