# The Vélu port, second plan: the remaining slice, the boundary, and V1

**Status: measured 2026-10-05 against the present port; supersedes the budget and
phase list of [TOPIC-port-plan.md](TOPIC-port-plan.md) §1.4/§5.** The four plan
headlines, the explicit-Vélu column, the H5 engine and the torsion promotion are
landed, so the plan's own numbers and name lists are now stale in three ways
(§1, §2). This file re-baselines them, puts the far end of the subject **out of
scope**, and cuts the next wave **V1** whose work orders are
[TOPIC-V1-ready-columns.md](TOPIC-V1-ready-columns.md). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §2 (plan), §2.4 (dedup),
§2.6 (scout), §3.4 (sets/review), §3.5 (build ladder), §3.7 (order), §4
(faithfulness). Dated record: [../../logs/velu-port.md](../../logs/velu-port.md).

## 0. Decision in one paragraph

The block is no longer "42 nodes / 26.7 k lines of Vélu". What is left is **36
nodes / 29,580 raw `S_` lines / 16,135 net new**, and most of its mass sits behind
a **boundary** that is not Vélu at all: the `PeriodPair` uniformization ladder
(gating the Mazur chain), the `fullKernelHom`/reduction columns (gating the Ribet
chain), and the modular-polynomial bijection at the far end. So: (1) **V1** is the
part with no unported prerequisites — the order-two column, the odd-order
discriminant identity, and the quotient-`j` column, ≈7.0 k written across three
new-module sets, detailed in the companion topic; (2) **V2** is the two cheap
gateways plus the Ribet-side completion, ≈2–3 k, to be scoped after V1; (3) the
**boundary set** (§2) is tracked, priced and *not ported here* — it is a different
subject, and the plan should stop claiming it.

## 1. Re-baselined budget

Fresh run of the plan's own instrument (§5) over the nodes the port does not yet
provide. The node filter shrinks as homes land, so this is the honest remaining
figure:

| quantity | pre-port (plan §1) | plan §1.4 | **now** |
|---|---:|---:|---:|
| nodes | 47 | 42 | **36** |
| raw `S_` lines | 91,442 | 47,509 | **29,580** |
| distinct declaration groups | 1,930 | 1,282 | 905 |
| once-cost after dedup | 42,970 | 30,647 | 19,178 |
| — already in the port | 2,984 | 3,973 | 3,043 |
| **net new mathematics** | 39,986 | 26,674 | **16,135** |

Two corrections to how the plan reads this budget:

- **The H5 landing also paid for its consumers' preludes.** The dedup is
  declaration-granular, so a node whose pin file inlines the H5 engine now shows a
  small net: `exists_pointEnd_eq_of_mem_isogenyEndSubring` reads 3,672 raw span but
  ~1.26 k of it is already declared in `IsogenyEndDatum/Engine.lean`, leaving
  **701** net. Re-running the instrument is what surfaces this; reading the old
  table does not.
- **The mass is still concentrated, and where it sits moved.** Four nodes are
  8.8 k of the 16.1 k: the discriminant identity (3,546), the two base-change
  headlines (1,414 + 1,433) and `exists_intermediateField_countable…` (2,416).
  All four are in V1 or V3, not at the far end.

### 1.1 The readiness metric this plan now uses

Raw size does not order the remaining work; **the node's unported closure does**.
For each remaining node the run reports
`ucl = Σ pin lines over (closure(node) \ port)`, i.e. what still has to be written
before it can land. The cut below is by `ucl`, not by layer:

| `ucl` | node | net | verdict |
|---:|---|---:|---|
| 0 | `veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow` | 3,546 | **V1** |
| 0 + small | the order-two identities and `exists_addMonoidHom_coe_eq_veluPointMap2` | 1,507 | **V1** |
| 0 + 188 | `cyclicQuotientJ_{variableChange_eq,baseChange_map_eq…}` | 554 | **V1** |
| 269 (in port under other names) | `exists_pointEnd_eq_of_mem_isogenyEndSubring` | 701 | V2 |
| 3,076 | `exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq` | 454 | V2 |
| 2,386 (itself) | the base-change trio | 3,713 | V3 |
| 5,610 | `exists_pointHom_comp_eq_of_ker_le_of_isCentred` | 325 | boundary-gated |
| 17,818 | `aeval_j_diag_eq_zero_of_finrankAlong_eq` | 289 | boundary-gated |
| 77,743 / 141 nodes | `bijOn_cyclicQuotientJ_isRoot_modularPolynomial…` | 1,082 | parked (far end) |

The three "cheap" nodes with five-figure closures are the ones the old phase list
would have dispatched next. They are not cheap.

## 2. Scope: what this port is not

### 2.1 The boundary set

These nodes are on the FLT root path but have large unported closures that belong
to **other subjects**. They are recorded here, priced, and **out of scope for this
port**; a consumer that needs one stops at the boundary and reports (§3.7).

| node | pin lines | why it is not this port |
|---|---:|---|
| `WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq` | 289 (net) / 647 raw | its closure is the **`PeriodPair` uniformization ladder** (§2.2) |
| `WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j` | 57 | consumes the above; **not in the Deligne–Serre cone**, so in no plan list |
| `WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add` | 4,316 | the place-level `algEquiv` column |
| `WeierstrassCurve.exists_fullKernelHom` | 904 | the full-kernel/reduction entrance; consumes V1-SET-1 and V1-SET-2 |
| `WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` | 178 | drags `Def_…_ReduceHom` (489) ← `TorsionIntegral` (1,233) ← `ReductionMap` |
| `ModularCurve.modularPolynomial_rootMultiplicity_jQuotVelu_eq_one` and its consumers | — | the modular-curve side; downstream of the boundary |

### 2.2 The `PeriodPair` ladder (the Mazur gate)

The `ucl`-17.8 k closure of `aeval_j_diag_eq_zero_of_finrankAlong_eq` is dominated
by, in order, `WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq`
(2,684), `PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`
(2,673), `WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem`
(2,288), `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient`
(2,021) and `PeriodPair.isUniformization_toPoint` (1,493). That is a
uniformization/lattice subject with its own vocabulary, and it is what separates the
landed H5 work from the Mazur chain. **Decision: not this port.** The port records
it as the trigger for a future `PeriodPair` subject; if it is wanted, it is scoped
as its own topic with its own budget, not as a "289-line Phase D node".

### 2.3 Three gap classes the slice filter misses (standing rule)

The slice is `closure(DeligneSerre…) ∩ {`WeierstrassCurve.*` nodes matching a Vélu
name regex} \ port`. Three classes of real prerequisite fall outside it, each of
which has now cost a re-scope:

1. **Definition modules the slice never counted** — `Def_WeierstrassCurve_VeluOrderTwo`
   (49), `…_VeluPointMap2` (117), `…_VeluQuotientJInvariant` (92),
   `…_VeluVariableChange` (112), `…_VeluEquivariance` (200),
   `…_CyclicQuotientJ` (207), `…_VariableChangePointEquiv` (160). V1 carries ≈700
   of these (measured by referenced fraction, §4.2).
2. **Off-regex nodes inside the cone** — `WeierstrassCurve.Affine.Point.vcInvFun_add`
   (188), `ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi` (298),
   `AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy`
   (85). These are in the Deligne–Serre cone but do not match
   `startswith('WeierstrassCurve.')` plus the regex.
3. **FLT-path nodes outside the Deligne–Serre cone** — `exists_fullKernelHom`,
   `…_of_not_isIntegral_j`, `exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add`.
   Precedents: `Def_DualIsogenyAPI` and `addX_addY_specialize_at_place`.

**Rule for the next re-measure:** a work order's source list is the route closure
of its deliverable over *all three* classes, not the tool's node list. Price a node
by its `ucl`, never its raw size.

## 3. The waves

| wave | contents | ≈ written | status |
|---|---|---|---|
| **V1** | the three ready columns: order-two, discriminant, quotient-`j` | **7,370 measured** | **landed 2026-10-05** |
| **V2** | the two gateways (`exists_pointEnd_eq_of_mem_isogenyEndSubring` 701 → `exists_sq_lt_four_mul…` 454) and the Ribet-side completion (`exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples` 25, `exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed` 97 + its separable-principal-divisors and genus-one-gate closure) | ≈2–3 k | outline only |
| **V3 / parked** | H6 base-change (3,713, demoted: no out-of-slice consumer until the `PeriodPair` gate opens); the two deferred H5 vocabulary nodes with their boundary closures; the far-end modular-polynomial bijection (`bijOn_cyclicQuotientJ…`, `exists_equiv_addSubgroup…`) | — | parked |
| **boundary** | §2.1, §2.2 | — | out of scope |

Why V2 is not "next" in the same breath as V1: the Mazur gateways are cheap and
unblocked, but after them the Mazur chain stops at the `PeriodPair` gate, and the
Ribet-side completion needs the separable principal-divisors layer. Both are
scoped *after* V1 so their orders can be written against the modules that then
exist (playbook §0.2).

Why H6 is demoted: the base-change trio's consumers are **all in the slice** and
reach FLT only through `aeval_j_diag…` (parked). Porting it now buys nothing on the
root path. It stays in V3, behind the gate decision.

## 4. V1 in outline

V1 is the part of the slice with **no unported prerequisite node** plus its
measured definition layer. Three sets, one mathematical story each, all delivered
as **new modules** (so no library cascade):

| set | story | new modules | ≈ written |
|---|---|---|---|
| V1-SET-1 | the order-two quotient and its point map | `Velu/OrderTwo.lean`, `Velu/OrderTwoMap.lean` | 1.73 k |
| V1-SET-2 | the discriminant of the odd-order Vélu quotient | `Velu/Equivariance.lean`, `Velu/Discriminant.lean`, `Velu/CyclicCount.lean` | 4.27 k |
| V1-SET-3 | the quotient `j`: model independence and base change | `WeierstrassCurve/VariableChangePoint.lean`, `Velu/CyclicQuotientJ.lean` | 1.05 k |

**V1 landed 2026-10-05** — all three sets, 7,370 written lines across seven new
modules, no library cascade. Checker `5572 → 5699 identical / 0 mismatched /
0 missing` (312 promoted, 36 own-proof); whole-tree build green (9,289 jobs, 14.1 s
warm); consumer exit 0; `#print axioms` clean on all five headlines. The close-out,
the per-set review and the friction are in
[TOPIC-V1-ready-columns.md](TOPIC-V1-ready-columns.md) §10 and
[../../logs/velu-port.md](../../logs/velu-port.md); the four findings that reshape
what V2 should do are:

- a definition module's **imports** are part of its source list
  (`Def_…_VeluVariableChange` pulled `Def_…_VariableChangePointEquiv`, which no
  order had assigned);
- a referenced-fraction table does not say what the port **already has** — the
  `map_velu*` block was already public in `Velu/Formula.lean`, and SET-2's first
  build shipped eight silent duplicates before it was caught by name;
- the cost of an identity column is its `linear_combination` count, not its line
  count (SET-1's 1,952 lines were ~50× slower to build than SET-2's 4,365);
- the binding knob for those identities is the pin's **`maxRecDepth`, not
  `maxHeartbeats`**.

The detailed work orders — scope, pin sources with line ranges, declaration list,
route with recorded negatives, stop-early risks, build discipline and verification —
are in [TOPIC-V1-ready-columns.md](TOPIC-V1-ready-columns.md) §4–§6; the SET-2 and
SET-3 orders carry in-place amendments made from the previous set's review
(playbook §3.3).

### 4.1 What V1 buys

- **SET-1** closes the order-two column and lands `exists_addMonoidHom_coe_eq_veluPointMap2`
  (1,292 net), the point map that the out-of-cone `fullKernelHom` fan-out (11 nodes)
  consumes.
- **SET-2** lands the single largest remaining item, the discriminant identity
  (3,546), which is the largest unported prerequisite of `exists_fullKernelHom` and
  the arithmetic reason `E/⟨Q⟩` stays elliptic; plus the ψ-counting pair.
- **SET-3** makes `cyclicQuotientJ` well-defined: invariant under a variable change
  and compatible with base change. These are the two lemmas that let every later
  consumer treat the quotient `j` as a function on the moduli problem.

### 4.2 The definition layer, measured by referenced fraction

Porting a definitions file is not the default (playbook §2.1). The referenced
fractions, measured by grepping each definition module's declarations against the
`S_` files of the nodes that import it:

| module | decls | referenced | V1 treatment, as landed |
|---|---:|---|---|
| `Def_…_VeluOrderTwo` | 8 | 4/8, 3/8 | ported whole into `Velu/OrderTwo.lean` (49) |
| `Def_…_VeluPointMap2` | 13 | 5/13 | ported whole into `Velu/OrderTwo.lean` (117) — the working part is not separable |
| `Def_…_VeluQuotientJInvariant` | 14 | 1/14 (`Δ_mul_j`) | only `Δ_mul_j` ported; the rest is a ℚ worked example, and it went to the consumer as a numeric zone |
| `Def_…_VeluVariableChange` | 8 | 4/8 | ported whole into `Velu/Equivariance.lean` (112) |
| `Def_…_VeluEquivariance` | 13 | **1/13** | **already public in `Velu/Formula.lean`** (H4 work) — imported, 0 written |
| `Def_…_VariableChangePointEquiv` | 19 | 6/19 | unassigned in the plan; **found by SET-2 reading the imports** of `VeluVariableChange`, ported core into `Velu/Equivariance.lean`; SET-3 imports it |
| `Def_…_CyclicQuotientJ` | 52 public, not 46 | 33/52, 31/52 | ported into `Velu/CyclicQuotientJ.lean` (207); the referenced-fraction regex cannot see the six `@[simp]` `xVeluCurve_aᵢ` projections the checker's `attrs` group does |
| `Def_…_VeluBundledMap` | 8 | **0/8** | **skipped** (verified 0 references) |

Total definition layer as landed ≈ 485 written, against 1,426 raw. The two rows
that moved the number are the ones the table alone could not see: a module's
**imports** are part of its source list (`VariableChangePointEquiv`), and a
referenced fraction says nothing about what the port **already has**
(`VeluEquivariance` → 0). Grep the port by name before transcribing a definition
module.

## 5. Reproduce

```bash
cd tools/deps
python3 frontier.py --selfcheck | tail -1

# the current slice: nodes the port does not yet provide
python3 - <<'PY' > build/velu_nodes2.txt
import frontier, re
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
ds = fr.closure(pay.pid('DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen'))
rx = re.compile(r'[Vv]elu|cyclicQuotient|cyclicKernels|isAddCyclic|IsogenyEnd|IsogenyHom|OddOrderSummingSet|ker_pointMap|veluFieldHom|veluFunctionFieldHom|veluQuotient|velu_map_equation')
print(','.join(pay.qual(i) for i in ds
               if i not in front and pay.qual(i).startswith('WeierstrassCurve.')
               and rx.search(pay.qual(i).split('.', 1)[1])))
PY
python3 port_advise.py --nodes "$(cat build/velu_nodes2.txt)" --json build/velu_advise2.json
python3 port_plan.py --json build/velu_advise2.json --json-out build/velu_plan2.json
```

The `ucl` column is recomputed with:

```python
# per remaining node: unported closure in pin lines
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
for i in rem:
    un = [n for n in fr.closure(i) if n not in front and n != i]
    ucl = sum(pay.lines(n) for n in un)
```

The 2026-10-05 run is in `tools/deps/build/velu_plan2.{txt,json}` (untracked, like
the toolchain); the plan's §1 numbers are the pre-port run of the same instrument.
Re-pin before re-measuring: both the node filter and the sibling/overlap ratios
move with the port and the pin.

## 6. Build economy

V1 is deliberately **new-files-only**: three new modules under
`WeierstrassCurve/Velu/`, appended to `PORT_FILES`/`SOURCES` in `spec/` (which is
outside the libraries) and exercised by new zones of
`spec/WeierstrassCurveConsumer.lean` (also outside). No library module is edited, so
`lake build <module>` re-elaborates one file and its dependencies and cascades
nowhere; the only whole-tree build is the V1 milestone gate (playbook §3.5, §3.7).
The one rule that keeps this true: **a worker who reaches an unported prerequisite
stops at the boundary and reports** rather than editing a closed module.
