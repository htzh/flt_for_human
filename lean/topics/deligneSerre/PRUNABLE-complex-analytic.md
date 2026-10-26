# The D-S prunable set — the complex-analytic Jacobian / path-integral / Abel–Jacobi / CellDissection subject

**Status (2026-10-14): recorded; do not schedule this subject off a D-S ready shelf.**

**Why this file exists.** The Deligne–Serre frontier lists this subject on its ready
shelf because every node of it is in the target's *closure* — but the D-S column does
not port it. The subject is a **second, redundant supply** to a step the D-S route
already reaches by the differentials ↔ cusp-forms transport, so it is prunable
(§2). This file is the canonical definition so a frontier read can exclude it in one
flag and the shelf does not resurface it.

The subject's port plan lives in
[../algebraicCurve/TOPIC-cell-dissection.md](../algebraicCurve/TOPIC-cell-dissection.md)
(the RadialRegion / CellDissection cluster, RR column phase 3); this file is only the
D-S-side exclusion.

## 1. The set

Let `R_DS` be the nodes of the D-S root cone whose qualified name contains one of

* `CellDissection`
* `pathIntegral`
* `abelJacobi`
* `pathPeriodLattice`

or is one of the four `Pic0.*complex` nodes (the only part not expressible as a
substring):

```
AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_complex
AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_of_chartedSpace_complex
AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex
AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_genus_complex
```

Measured 2026-10-25 (the 2026-10-14 set, unchanged): **44 nodes / 30,570 lines** (all
still unported):

| family | nodes |
|---|---:|
| `abelJacobi` | 19 |
| `CellDissection` | 11 |
| `pathIntegral` | 7 |
| `Pic0.*complex` | 4 |
| `pathPeriodLattice` | 3 |

Membership is defined by the name patterns, not by a frozen list: as the port grows the
set's *unported* part shrinks, but the exclusion stays correct. A one-day attempt to
narrow the `abelJacobi` substring (2026-10-25) was reverted — see §7, which records what
it found and why the breadth is kept.

## 2. Payout

`prunable(R_DS) = closure(root) \ closure(root with R_DS deleted)` — the nodes only
reachable through the subject — is **205 nodes / 107,257 lines** (port-independent; it
agrees with `deligne-serre-weight-one-scout.md` §4.2). On the 2026-10-25 tree the prune
moves the D-S forward target from **1359 / 530,935** unpruned to **1177 / 441,332**
pruned — a saving of **182 nodes / 89,603 lines**; `AlgebraicCurve.` falls 251 / 95,728
to 184 / 48,515. (The 2026-10-14 tree read 1,588 / 623,825 to 1,402 / 532,720 — a saving
of 186 / 91,105; the scout read 201 / 103,660 on its own, smaller, tree. Only the
`prunable` figure is stable across trees.)

## 3. Why it is prunable

The step the subject's route feeds,
`ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm`, cites two
independent supplies for the same job:

* `ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`
  — the differentials ↔ cusp-forms transport, the route the D-S/RR columns port; and
* `AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero`
  — supplied by the Abel–Jacobi / path-integral / `CellDissection` route, i.e. `R_DS`.

Port the transport, drop the second supply, and the whole subject falls away at a
**13-node rewiring frontier** (the kept nodes whose proofs directly cite it). The
scout puts it plainly: "that transport is the bottleneck, not RR itself"
([deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md)
§4.2). Note the `24 nodes / 56,383 lines` figure in
[PORTING-RR.md](../PORTING-RR.md) §3 is the *residue* block
(`residueTheorem | tateAgreement | residueTrace`), which has since been ported — 0
unported in the cone — not this subject.

## 4. How to exclude it (the switch)

The set is promoted to `tools/deps/ds_prunable.py` (`TARGET`, `PATTERNS`, `EXTRA`,
`removed(pay, cone)`, `LABEL`), and `frontier.py` carries a default D-S switch that
targets the headline and avoids the set in one flag:

```bash
cd tools/deps
python3 frontier.py --ds --ready --rank-by silo --top 0   # the D-S ready shelf
python3 frontier.py --ds --top 0                          # the needed/prunable read
python3 ds_prunable.py                                    # the set and its payout
```

`--ds` is exactly the manual form — `--target` defaults to `TARGET`, the four
substring patterns are `--remove`d and the four `Pic0.*complex` names `--also`ed:

```bash
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --remove CellDissection --remove pathIntegral --remove abelJacobi --remove pathPeriodLattice \
  --also AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_complex \
  --also AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_of_chartedSpace_complex \
  --also AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex \
  --also AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_genus_complex \
  --ready --rank-by silo --top 0
```

`--remove` is a **substring** match and `--also` an exact name (see
`prune.py`'s `nodes_matching`), which is why the four `Pic0.*complex` rows are listed
explicitly rather than as a regex.

This is the reading to use whenever the D-S frontier is asked what is left. Without
it, the subject's leaves appear on the ready shelf (that is how
`AlgebraicCurve.RadialRegion.exists_rect_sixArcs` was first picked up) and read as D-S
work. Verified 2026-10-14: `--ds --ready --rank-by silo --top 0` lists 87 candidates
and no node of the subject.

## 5. Regeneration

`python3 ds_prunable.py` prints the set and its payout; the same numbers come from:

```bash
cd tools/deps
python3 - <<'PY'
import ds_prunable, frontier
fr = frontier.Frontier(); pay = fr.pay
root = pay.pid(ds_prunable.TARGET)
R = ds_prunable.removed(pay, fr.closure(root))
print('R', len(R), pay.total_lines(R),
      'prunable', len(pay.prunable(root, R)), pay.total_lines(pay.prunable(root, R)))
PY
```

## 6. Pointers

* the subject's plan: [../algebraicCurve/TOPIC-cell-dissection.md](../algebraicCurve/TOPIC-cell-dissection.md)
* the route/mechanism: [deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md) §4.2
* the prune machinery: `tools/deps/prune.py`, `tools/deps/frontier.py` (`--remove`, `--also`, `--scenario`)
* the D-S frontier, both readings: [PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2

## 7. The 2026-10-25 trial — narrowed for a day, reverted

A D-S read of `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` surfaced the
ambiguity: `abelJacobi` names both the complex-analytic **supply** (the divisor/vector with
path periods, the period lattices) and an **algebraic** family
(`AlgebraicCurve.Pic0.abelJacobiCard_genus` and its `…FF_of_frobenius` cousins) stating
`Nat.card (Pic0.torsion K F p) = p ^ (2 * genus K F)`. A bare substring caught both, so
`--ds` priced that pair at **1 node / 327 lines** — its only numerical premise avoided.

The set was narrowed for a day to the analytic spellings with `EXTRA` emptied. What that
bought and cost, measured:

| read | restored (2026-10-14 set) | narrowed |
|---|---:|---:|
| avoided R, D-S cone | 44 / 30,570 | 39 / 29,881 |
| avoided R, Fermat cone | 140 / 74,620 | 49 / 32,634 |
| D-S forward target | 1177 / 441,332 | 1184 / 442,175 |
| `AlgebraicCurve.` demand | 184 / 48,515 | 190 / 49,249 |
| the pair under `--ds` | 1 / 327 | 71 / 20,526 |

**What the experiment found — the reason the narrowing was reverted, and kept here.**

1. **The subject has two independent halves.** The Riemann-surface route (cell dissection,
   path integrals, Abel–Jacobi divisor/vector, the complex uniformization
   `Pic0 ℂ F ≃+ (Fin g → ℂ) ⧸ L`) and the **modular period route**
   (`periodAlongOf`/`periodLatticeOf`, `ComplexPlaceDictionary{,Of}`, the Hecke-equivariant
   quotient) each prove the same uniformization, for different classes of curves, and their
   interfaces are disjoint.
2. **The D-S column has both proofs of the torsion finiteness.** The pair
   (`moduleFinite[_and_free]_padicInt_tateModule_j{One,jH}`) is the first;
   `ModularCurve.finite_torsion_jOne` (80 lines, from `periodLatticeOf`/`periodAlongOf`, no
   pruned premise) is the second. So the prune is a **rewiring assumption** — it prices the
   D-S column along the modular supply — and the pinned chain cites both.
3. **Therefore the breadth is not the bug.** Narrowing it does not repair anything: it
   makes the D-S column pay the redundant route (+7 nodes / +843 lines) while the released
   nodes' own premises are still the pruned analytic supply (11 such citations). The set is
   restored to the 2026-10-14 definition, and the subject is treated **in its own right**
   from here — its structure and four porting options are in
   [../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md).

What survives from the experiment as a permanent finding: the subject's outbound interface
is one statement with **fan-in one**, its arithmetic hub `abelJacobiCard_genus` has
**fan-in twelve**, and both halves are wide bodies with narrow mouths — recorded with the
numbers in the structure note.
