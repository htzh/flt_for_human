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

Measured 2026-10-14: **44 nodes / 30,570 lines** (all still unported):

| family | nodes |
|---|---:|
| `abelJacobi` | 19 |
| `CellDissection` | 11 |
| `pathIntegral` | 7 |
| `Pic0.*complex` | 4 |
| `pathPeriodLattice` | 3 |

Membership is defined by the name patterns, not by a frozen list: as the port grows
the set's *unported* part shrinks, but the exclusion stays correct.

## 2. Payout

`prunable(R_DS) = closure(root) \ closure(root with R_DS deleted)` — the nodes only
reachable through the subject — is **205 nodes / 107,257 lines** (port-independent; it
agrees with `deligne-serre-weight-one-scout.md` §4.2). On the 2026-10-14 tree the
prune moves the D-S forward target from **1,588 / 623,825** unpruned to
**1,402 / 532,720** pruned — a saving of **186 nodes / 91,105 lines**. (The scout read
201 / 103,660 on its own, smaller, tree; only the `prunable` figure is stable.)

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
