# V1 — the ready columns: order-two, discriminant, quotient-`j`

**Status: landed 2026-10-05** — all three sets green; see §10 for the close-out and
[../../logs/velu-port.md](../../logs/velu-port.md) for the dated record. The work
orders below are kept as written (with SET-3's §6.2 amendment and the SET-1
findings folded into §5.5), so the scoping can be judged against what happened.
This file is the work orders for wave V1 of
[TOPIC-port-plan-v2.md](TOPIC-port-plan-v2.md) §4. Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §0.2 (staffing), §2.1/§2.4
(measure, dedup), §3.3–§3.5 (work order, sets, build ladder), §3.7 (order), §4
(faithfulness).

V1 is the part of the remaining slice whose every prerequisite is **already in the
port**, plus the definition modules its `S_` files import. It is delivered as **new
modules only**; no existing library module is edited, so no set cascades.

| set | story | new modules | ≈ written |
|---|---|---|---|
| **SET-1** | the order-two quotient and its point map | `WeierstrassCurve/Velu/OrderTwo.lean`, `…/Velu/OrderTwoMap.lean` | 1.73 k |
| **SET-2** | the discriminant of the odd-order Vélu quotient | `WeierstrassCurve/Velu/Equivariance.lean`, `…/Velu/Discriminant.lean`, `…/Velu/CyclicCount.lean` | 4.27 k |
| **SET-3** | the quotient `j`: model independence and base change | `WeierstrassCurve/VariableChangePoint.lean`, `…/Velu/CyclicQuotientJ.lean` | 1.05 k |

Sequence: SET-1 → review → SET-2 → review → SET-3 → milestone. Sets are run one at
a time, one subagent each (playbook §0.2); the manager writes each order against the
modules that then exist and reviews the tree between sets.

## 1. What V1 is, measured

Node net-new is the fresh re-measurement ([TOPIC-port-plan-v2.md](TOPIC-port-plan-v2.md)
§1.1); `ucl` is the node's unported closure in pin lines — **zero for every V1
node**, which is what makes V1 dispatchable today.

| node | net | `ucl` | set |
|---|---:|---:|---|
| `veluQuotient2_cFour` | 5 | 0 | 1 |
| `Delta_eq_veluGx_sq_mul_velu2QuadDisc` | 9 | 0 | 1 |
| `veluQuotient2_Delta_eq` | 9 | 0 | 1 |
| `velu2_tangent_addX_cleared_identity` | 44 | 0 | 1 |
| `velu2_secant_negAddY_cleared_identity` | 29 | 0 | 1 |
| `velu2_tangent_negAddY_cleared_identity` | 25 | 0 | 1 |
| `veluGx_ne_zero_of_two_torsion` | 5 | 15 | 1 |
| `velu2QuadDisc_ne_zero_of_two_torsion` | 5 | 15 | 1 |
| `veluQuotient2_j` | 11 | 92 | 1 |
| `veluQuotient2_Delta_ne_zero` | 7 | 54 | 1 |
| `isElliptic_veluQuotient2_of_isElliptic` | 4 | 70 | 1 |
| `exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero` | 62 | 81 | 1 |
| `exists_addMonoidHom_coe_eq_veluPointMap2` | 1,292 | 143 | 1 |
| `isOddVeluSet_oddOrderSummingSet` | 106 | 0 | 2 |
| `veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow` | 3,546 | 0 | 2 |
| `veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq` | 7 | 3,566 | 2 |
| `exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero` | 53 | 3,968 | 2 |
| `ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi` | 298 | 0 | 2 |
| `AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy` | 85 | 0 | 2 |
| `cyclicQuotientJ_variableChange_eq` | 302 | 188 | 3 |
| `cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed` | 252 | 0 | 3 |
| `WeierstrassCurve.Affine.Point.vcInvFun_add` | 188 | 160 | 3 |

**The definition layer** (measured by referenced fraction, §2.1 of the plan): ≈700
written, not the 1,426 raw of the eight candidate modules. `Def_…_VeluEquivariance`
is referenced 1/13 (one lemma) and `Def_…_VeluBundledMap` 0/8 — neither file is
ported.

**Corrected V1 budget: ≈7.0 k written** = 6,344 node net + ≈700 definition layer.
The plan's old slice counted neither the definition modules nor the three off-regex
nodes (`vcInvFun_add`, the two counting lemmas), which are 571 of the node net.

## 2. Module DAG, namespaces, and the checker wiring

```
WeierstrassCurve/Velu/Defs.lean                    (existing, H2 vocabulary)
  ├─ WeierstrassCurve/VariableChangePoint.lean        SET-3   vcFun/vcInvFun, vcInvFun_add
  ├─ WeierstrassCurve/Velu/OrderTwo.lean              SET-1   order-two defs + identities
  │    └─ WeierstrassCurve/Velu/OrderTwoMap.lean      SET-1   the order-two point map
  ├─ WeierstrassCurve/Velu/Equivariance.lean          SET-2   VeluVariableChange + map_velu*
  │    └─ WeierstrassCurve/Velu/Discriminant.lean     SET-2   the discriminant identity
  │         └─ WeierstrassCurve/Velu/CyclicCount.lean SET-2   ψ-counting + enumeration
  └─ WeierstrassCurve/Velu/CyclicQuotientJ.lean       SET-3   cyclicQuotientCurve/J + j lemmas
       (imports VariableChangePoint)
```

Namespace rules: every declaration keeps the pin's name and namespace
(`WeierstrassCurve.…`, `WeierstrassCurve.Affine.Point.…`, `ZMod.…`,
`AddCommGroup.…`), so the checker's last-name match keeps working. Module headers
state the subject, the pin source and what they assume from lower modules.

Checker wiring, per set, at the two spec files only (never a library module):

- `spec/check_flt_statements.py`: append the set's new modules to `PORT_FILES`
  **last**; append the `Theorems/Thm_<stem>.lean` statement sources to `SOURCES`
  **last** (the wrapper is the statement authority).
- `spec/WeierstrassCurveConsumer.lean`: add one zone per new module with a real,
  executed cross-module composition (no `#check`, no `sorry`), plus one `#eval`/
  `norm_num` numeric check where the mathematics is concrete.

## 3. Build discipline (copy into every work order)

> `lake env lean <opts> <file>` is the edit loop, with `<opts>` =
> `-DmaxHeartbeats=4000000 -DautoImplicit=false` (without them the check runs at the
> default cap and lies about heavy modules); `lake build <module>` when a file is
> done; **one** `lake build` per wave; the full build at the milestone. Bound every
> build (`timeout 60` / `90` / `300`), serialize every `lake build` with `flock`
> (the lock lives in the workspace at `lean/.lake/flt_build.lock`, never `/tmp`),
> and time it: high user CPU with a timeout is a real blow-up to bisect, ~0 CPU is
> contention. Never raise `maxHeartbeats`. Import specifically — never
> `import Mathlib` in a library module.

Per set, the concrete loop:

```bash
cd lean
# edit loop, per declaration (writes no .olean, no cascade)
timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>
# module done
timeout 90 flock .lake/flt_build.lock bash -c 'time lake build <module>'
# the cheap faithfulness gate at every module close
python3 spec/check_flt_statements.py
```

Then `#print axioms` on each headline must be
`[propext, Classical.choice, Quot.sound]`; no `sorry`. Iterate a hard declaration in
a gitignored `Scratch*.lean`, not by rebuilding the module. **A worker who reaches
an unported prerequisite stops at the boundary and reports** rather than editing a
closed module or weakening a statement.

## 4. SET-1 work order — the order-two quotient

### 4.1 Scope

Port the order-two quotient column of the Vélu block: the vocabulary
(`veluQuotient2`, `velu2QuadDisc`, `velu2X/YNum`, `velu2X/Y`, `veluPointMap2`), the
order-two identities, the nonvanishing/discriminant corollaries, the enumeration of
the three 2-torsion quotients, and the point map
`exists_addMonoidHom_coe_eq_veluPointMap2`. The order-two quotient is the kernel
`{0, (x₀,y₀)}` with `veluGy x₀ y₀ = 0`; the pin's formulas are the `S = {(x₀,y₀)}`
case of §2 of the plan's subject, written in the form `(x-x₀)^{-1}` rather than
`(x-x₀)^{-2}` because `-Q = Q`.

**Not this set:** the odd-order case, `cyclicQuotientJ`, the discriminant identity
of SET-2, and the reduction column.

### 4.2 Source (pin)

Statements verbatim from the `Theorems/` wrappers; proofs from the `S_` files.

- `Definitions/Def_WeierstrassCurve_VeluOrderTwo.lean` (49 lines): `veluQuotient2`
  and its `a₁…a₆`/`b₂` projection lemmas, `velu2QuadDisc` and
  `velu2QuadDisc_def`/`velu2QuadDisc_eq_disc_cofactor`/`map_velu2QuadDisc`.
- `Definitions/Def_WeierstrassCurve_VeluPointMap2.lean` (117 lines): `velu2XNum`,
  `velu2YNum`, `velu2XNum_eq_mul`, `velu2_equation_cleared_four`,
  `velu2X`, `velu2Y`, `velu2X_eq_div`, `velu2Y_eq_div`, `velu2_map_equation`,
  `velu2_map_nonsingular`, `veluPointMap2`, `veluPointMap2_zero`,
  `veluPointMap2_some_of_eq`, `veluPointMap2_some_of_ne`.
- `Definitions/Def_WeierstrassCurve_VeluQuotientJInvariant.lean:17–18`: `Δ_mul_j`
  only (the one declaration the importing `S_` files reference).
- Node proof bodies (line counts; the `solution` line is the headline):
  `S_WeierstrassCurve_veluQuotient2_cFour.lean` 11 (7),
  `…_Delta_eq_veluGx_sq_mul_velu2QuadDisc.lean` 15 (7),
  `…_veluQuotient2_Delta_eq.lean` 15 (7),
  `…_velu2_tangent_addX_cleared_identity.lean` 53 (15),
  `…_velu2_secant_negAddY_cleared_identity.lean` 39 (11),
  `…_velu2_tangent_negAddY_cleared_identity.lean` 36 (12),
  `…_veluGx_ne_zero_of_two_torsion.lean` 12 (8),
  `…_velu2QuadDisc_ne_zero_of_two_torsion.lean` 12 (8),
  `…_veluQuotient2_j.lean` 21 (11),
  `…_veluQuotient2_Delta_ne_zero.lean` 16 (10),
  `…_isElliptic_veluQuotient2_of_isElliptic.lean` 11 (8),
  `…_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero.lean` 73 (26),
  `…_exists_addMonoidHom_coe_eq_veluPointMap2.lean` 1,438 (1,428).
  All under `P2M/Sol/`.

The headline signatures to land (from the wrappers):

```lean
theorem WeierstrassCurve.veluQuotient2_cFour :
    (W.veluQuotient2 x₀ y₀).c₄ = W.c₄ + 240 * W.veluGx x₀ y₀

theorem WeierstrassCurve.veluQuotient2_Delta_eq (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).Δ = W.veluGx x₀ y₀ * W.velu2QuadDisc x₀ ^ 2

theorem WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point,
      ⇑φ = veluPointMap2 h2 hQ hgy hΔ
```

(the full list of wrappers is in §4.6.)

### 4.3 Deliverable

Two new modules, `WeierstrassCurve/Velu/` namespace `WeierstrassCurve`:

1. **`FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean`** — imports
   `FLTForHuman.WeierstrassCurve.Velu.Defs`. Carries the vocabulary of §4.2 and the
   nodes `veluQuotient2_cFour`, `veluQuotient2_Delta_eq`,
   `Delta_eq_veluGx_sq_mul_velu2QuadDisc`, the `velu2_*_cleared_identity` trio,
   `veluGx_ne_zero_of_two_torsion`, `velu2QuadDisc_ne_zero_of_two_torsion`,
   `veluQuotient2_j`, `veluQuotient2_Delta_ne_zero`,
   `isElliptic_veluQuotient2_of_isElliptic`,
   `exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero`. Public surface: the
   wrapper names plus the vocabulary; purely local proof helpers stay `private`.
2. **`FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean`** — imports `OrderTwo`.
   Carries `exists_addMonoidHom_coe_eq_veluPointMap2` and its proof-local helpers
   (`private`). This is the set's wire test.

Register both in `PORT_FILES` (append last) and the thirteen wrappers in `SOURCES`
(append last).

### 4.4 Route, with recorded negatives

- mathlib has **no** `veluQuotient2`, `velu2QuadDisc`, `veluPointMap2`, and no
  Vélu at all (checked 2026-10-04, re-check before writing).
- The pin's `Δ_mul_j` (`Δ * j = c₄³`) follows from mathlib's
  `WeierstrassCurve.j = Δ'⁻¹ * c₄³` by `eq_div_iff`-style manipulation; record the
  exact mathlib spelling used.
- mathlib supplies the group law used by the `velu2_*_cleared_identity` trio:
  `WeierstrassCurve.Affine.addX`, `…slope`, `…negY`, `…Equation`; the trios are
  polynomial identities, so the pin's proof shape (`linear_combination` with a
  coefficient polynomial) transcribes, with the coefficient polynomial copied
  verbatim.
- `velu2_equation_cleared_four` is the order-two analogue of
  `velu_singleton_equation_cleared`; the port already has the latter in
  `Velu/Defs.lean` — read it for the transcription idiom (it is the same file the
  earlier set landed).
- `exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero` enumerates the three
  roots of the 2-division polynomial with nonvanishing quotient discriminant; the
  `veluGx_ne_zero`/`velu2QuadDisc_ne_zero` pair is what makes each of the three
  survive, so land those two first inside the set.

### 4.5 Stop-early risks (stop and report, do not push)

- `velu2_equation_cleared_four` or a `velu2_*_cleared_identity` times out at the
  4,000,000 cap even after the scratch gate. **Scout first**: prototype the
  smallest one (`velu2_tangent_negAddY_cleared_identity`) in `Scratch.lean` and
  report the time before writing the rest of the module.
- `veluPointMap2` needs a `dif_pos`/`dif_neg` split on `x = x₀`; if the
  `Nonsingular` proof obligation under `some` does not elaborate with the pin's
  `velu2_map_nonsingular`, stop and report the goal.
- Any statement in §4.2 whose wrapper text differs from the `S_` file's `solution`
  text: **the wrapper wins**; report the difference rather than choosing.

### 4.6 Verification

- `lake env lean` clean on both modules; `lake build` each.
- `python3 spec/check_flt_statements.py` → `0 mismatched / 0 missing`; record the
  `identical` before → after delta, and reconcile it against the new public surface.
- Consumer: extend `spec/WeierstrassCurveConsumer.lean` with a zone per module — at
  minimum a concrete `veluQuotient2` computation on a curve with 2-torsion, a
  `#print axioms`-clean use of `veluQuotient2_Delta_eq` in a composition with
  `Velu/Defs.lean`, and a use of `exists_addMonoidHom_coe_eq_veluPointMap2` as a
  genuine `→+`.
- `#print axioms` on `exists_addMonoidHom_coe_eq_veluPointMap2` and on
  `veluQuotient2_Delta_eq`: `[propext, Classical.choice, Quot.sound]`; no `sorry`.

## 5. SET-2 work order — the discriminant of the odd-order quotient

### 5.1 Scope

Port the odd-order discriminant column: the summing-set predicate, the identity

`Δ(W.veluQuotient S) · (∏_{P∈S} u_P)^4 = Δ(W)^{2n+1}`,

its nonvanishing corollary, the ψ-counting lemmas it consumes, and the enumeration
of the cyclic kernels with nonsingular quotient. **Not this set:** the order-two
column (SET-1), the quotient-`j` column (SET-3), and anything consuming
`exists_fullKernelHom` (out of scope, boundary).

### 5.2 Source (pin)

- Definition layer (new file, §5.3.1):
  `Definitions/Def_WeierstrassCurve_VeluVariableChange.lean` (112 lines, whole file:
  `vcInvEmbedding`, `variableChange_velu{Gy,Gx,T,U,W,TSum,WSum}`) — the `S_` file
  references 4/8 of its declarations; and
  `Definitions/Def_WeierstrassCurve_VeluEquivariance.lean` **lines 1–60 only**
  (`map_velu{Gx,Gy,T,U,W}` + `map_veluTSum`, `map_veluWSum`; the file's other 12
  declarations are referenced 0/13 by these targets and `VeluBundledMap` is
  referenced 0/8 — do not port them).
- Node proof bodies:
  `P2M/Sol/S_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet.lean` 173 (146);
  `…_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean` 3,566 (3,548)
  — **the headline**, 203 `private` helpers;
  `…_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq.lean` 19
  (13);
  `…_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero.lean` 70 (18);
  and the two counting nodes
  `Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean`,
  `Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy.lean`.
- The identity's `S_` file also uses the ported `Velu/Formula.lean` public
  `exists_some_of_ne_zero` and `veluGy_ne_zero_of_two_nsmul_ne_zero`; import them,
  do not re-derive.

### 5.3 Deliverable

Three new modules:

1. **`FLTForHuman/WeierstrassCurve/Velu/Equivariance.lean`** — the definition layer
   of §5.2 (both files' parts), statements verbatim. Imports
   `FLTForHuman.WeierstrassCurve.Velu.Defs` only.
2. **`FLTForHuman/WeierstrassCurve/Velu/Discriminant.lean`** — imports
   `Equivariance`; `isOddVeluSet_oddOrderSummingSet`, the identity
   `veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow`, and
   `veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq`.
3. **`FLTForHuman/WeierstrassCurve/Velu/CyclicCount.lean`** — imports
   `Discriminant` and the port's `Algebra/ZModTorsion.lean`; the two counting
   lemmas and `exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero`.

Register all three in `PORT_FILES` and the four wrappers (+ the two counting
wrappers) in `SOURCES`, appended last. **Also append the `Definitions/` files or
file ranges that this set ports to `SOURCES`** — a vocabulary block has no
wrapper, and SET-1's friction was 26 vocabulary declarations reading
`MISSING IN FLT` until the three `Definitions/` entries were added
(`Def_…_VeluVariableChange.lean` whole, `Def_…_VeluEquivariance.lean:1–60`).

SET-1 has landed and is not a prerequisite here: `Velu/OrderTwo.lean` carries
`veluQuotient2`/`velu2QuadDisc`/`veluPointMap2` and `Velu/OrderTwoMap.lean` the
order-two point map, both public and checker-verified. SET-2 imports **neither**
(the odd-order column goes through `Velu/Defs.lean`); SET-3 imports `OrderTwo`.

Prerequisites confirmed present in the port before dispatch:
`Velu/Formula.lean`'s `exists_some_of_ne_zero`, `Velu/OddOrder.lean`'s
`veluGy_ne_zero_of_two_nsmul_ne_zero`, `ModularCurve/Defs/Jq.lean`'s
`dedekindPsi` and `ModularCurve`'s `dedekindPsi_prime`,
`Algebra/ZModTorsion.lean`'s
`nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`, and
`Elliptic/TorsionZMod.lean`'s `nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`.

### 5.4 Route, with recorded negatives

- mathlib has no `Vélu`, no `velu2QuadDisc`, no `veluQuotient`; the identity is
  pure polynomial/`Finset` algebra over the pin's own vocabulary, which SET-1 and
  `Velu/Defs.lean` already provide.
- The port already has `ModularCurve.dedekindPsi` and `ModularCurve.dedekindPsi_prime`
  (in `ModularCurve/`); import them rather than re-deriving ψ.
- The counting pair is the generic `ZMod`/`AddCommGroup` statement the port's
  torsion promotion partly covers: `Algebra/ZModTorsion.lean` has
  `AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`, and
  `Elliptic/TorsionZMod.lean` has the `E[n] ≅ (ℤ/n)²` wrapper. Read both first; if
  the counting lemma is a corollary of the promoted classification, prove it that
  way and record the route.
- The `S_` file's own `private` prologue (203 helpers: `chord_prod`, `double_x`,
  `coordsOrZero_*`, `fold2`/`unfold2`, `nsmul_injOn_Icc`, `pack_esymm*`, …) is
  self-contained; transcribe it in the pin's line order, which is a valid
  topological order.

### 5.5 Stop-early risks

**Known from SET-1 (measured, 2026-10-05), so plan for it rather than rediscover it:**

- The binding knob on these identities is **`maxRecDepth`, not `maxHeartbeats`**.
  SET-1's scout of `velu2_tangent_negAddY_cleared_identity` failed at 53 s with
  `maximum recursion depth reached` (default 1000, inside `field_simp`); the pin
  carries `maxRecDepth 8000`, which the port keeps. All of the pin's
  `maxHeartbeats` bumps (8 M–160 M) were dropped and every SET-1 node closed at the
  frozen 4,000,000. So: keep a pin `maxRecDepth` bump where the pin has one, never
  raise `maxHeartbeats`, and scout the heaviest identity before writing the module.
- **These modules are heavy.** SET-1 measured `lake env lean` 5 m 21 s /
  `lake build` 248 s on its 524-line vocabulary module, and 7 m 49 s / 552 s on its
  1,428-line headline, with a 12 m 47 s wave build. Budget the same order here: work
  in bounded declaration batches in `ScratchSet2.lean`, keep the edit loop off the
  module file, and expect multi-minute `lake env lean` runs.

- **The identity is 3,546 net lines with 203 private helpers.** Budget the set as
  two halves — the identity, then its consumers — and if the first half is not
  closed when the agent's budget runs low, **stop and report at that boundary**;
  the consumers (`Discriminant.lean`'s `_ne_zero`, `CyclicCount.lean`) become a
  follow-up order rather than being half-written.
- `variableChange_veluTSum`/`map_veluQuotient` may need a `Finset.map` injectivity
  argument spelled differently in `v4.34.0`; if the pin's `hf.prodMap hf` does not
  elaborate, report the goal rather than weakening `Function.Injective f`.
- If `exists_enum_cyclicKernels_…` needs a `Fintype`/`Finset` enumeration lemma that
  is not in the port, stop and report — do not invent a weaker `Nonempty` form.
- **Statements come from the wrappers, and the checker reads the declaration's own
  text**: 8 of SET-1's 13 wrappers hoist binders into file-level `variable`s while
  the `S_` files inline them, and all 8 mismatched until each wrapper's `variable`
  prelude was spliced onto the `S_` proof. Expect the same on every node here.

### 5.6 Verification

- `lake env lean` clean per module; `lake build` per module; then **one** wave
  `lake build` for the three-module wave at the manager's gate.
- Checker `0 mismatched / 0 missing` with the `identical` delta recorded.
- Consumer zones: a concrete `#eval`-style check of the ψ-count for a small `N`, a
  composition using `isOddVeluSet_oddOrderSummingSet` with `Velu/Formula.lean`, and
  a use of `veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq`.
- `#print axioms` on the identity and on the enumeration:
  `[propext, Classical.choice, Quot.sound]`; no `sorry`.

## 6. SET-3 work order — the quotient `j`

### 6.1 Scope

Port the quotient-`j` column: the cyclic-quotient vocabulary
(`absSum`/`xVeluCurve`/`xVeluX`/`twoVeluCurve`/`twoVeluX`/`kernelXSet`/`stepCurve`/
`cqjIterate`/`cyclicQuotientCurve`/`cyclicQuotientJ` and the `xVeluT/U/W` block), the
variable-change point equivalence it is stated with, and the two well-definedness
lemmas: invariance under a variable change, and compatibility with base change to
an algebraically closed field. Plus `WeierstrassCurve.Affine.Point.vcInvFun_add`
(the point-map additivity that `cyclicQuotientJ_variableChange_eq` consumes, 188
lines, an off-subject prerequisite carried per the `ucl` rule).

**Not this set:** the `reduceHom`/residue node
`exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` — its
definitional closure is the reduction subtree (`Def_…_ReduceHom` 489 ←
`TorsionIntegral` 1,233 ← `ReductionMap`), and it is **out of scope** here
([TOPIC-port-plan-v2.md](TOPIC-port-plan-v2.md) §2.1).

### 6.2 Source (pin)

- `Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean` (160 lines):
  **already ported** — SET-2 landed the core (`vcX`, `vcY`, `vcXInv`, `vcYInv`,
  `equation_variableChange_iff`, `nonsingular_variableChange_iff`, `vcFun`,
  `vcInvFun`, `vcFun_leftInverse`, `vcFun_rightInverse`) publicly in
  `FLTForHuman/WeierstrassCurve/Velu/Equivariance.lean`, because
  `Def_…_VeluVariableChange` imports it. **Import that module; do not redeclare
  the core.** The `variableChangeEquiv`/`equivOfVariableChangeEq` tail is not
  needed.
- `Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean` (207 lines, 46 decls):
  referenced 33/46 and 31/46 — port the file.
- `P2M/Sol/S_WeierstrassCurve_Affine_Point_vcInvFun_add.lean` 188 (184).
- `P2M/Sol/S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.lean` 315 (298).
- `P2M/Sol/S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.lean`
  264 (254).

### 6.3 Deliverable

Two new modules, both under `Velu/` (the variable-change point vocabulary now lives
in `Velu/Equivariance.lean`, so its additivity node follows it rather than opening a
new area directory for one declaration):

1. **`FLTForHuman/WeierstrassCurve/Velu/VariableChangePoint.lean`** — imports
   `FLTForHuman.WeierstrassCurve.Velu.Equivariance`; carries
   `WeierstrassCurve.Affine.Point.vcInvFun_add` and its proof-local helpers
   (`private`). This is the one off-subject prerequisite in V1, carried by the `ucl`
   rule; its header says so and names its pin source.
2. **`FLTForHuman/WeierstrassCurve/Velu/CyclicQuotientJ.lean`** — imports
   `VariableChangePoint` and `Velu/Defs.lean`; the `Def_…_CyclicQuotientJ` content
   and the two `cyclicQuotientJ_*` lemmas. This is the set's wire test.

Register both in `PORT_FILES`; append the three wrappers **and the
`Def_…_CyclicQuotientJ.lean` definition source** to `SOURCES`, appended last.

### 6.3.1 Route, with recorded negatives

- mathlib has no `cyclicQuotientJ`/`cyclicQuotientCurve`; `absSum` over a possibly
  infinite set (`absSum_of_finite`/`absSum_of_infinite`) has no mathlib analogue —
  it is the pin's "sum over the finite kernel, 0 if infinite" device.
- `Def_…_CyclicQuotientJ` imports `VeluOrderTwo` and `VeluPointMap2` (SET-1's
  `OrderTwo.lean`): SET-3 therefore **imports SET-1's modules**, which is part of
  the hand-off (§7).
- The `map_velu*` commutation block is **already public in `Velu/Formula.lean`**
  (landed with the H4 work, and re-matched by SET-2's checker delta as a promotion
  against the pin's public copy). Import it; do not port
  `Def_…_VeluEquivariance`'s block again — SET-2's first build produced 8 silent
  cross-module duplicates that way.
- `stepCurve`/`stepX` branch on `ℓ = 2` vs `ℓ ≠ 2` (the 2-torsion quotient is the
  order-two one); the `ℓ = 2` branch refers to the order-two vocabulary from SET-1.

### 6.4 Stop-early risks

- `cqjIterate` is defined by recursion over `N.primeFactorsList`; if `v4.34.0`'s
  `Nat.primeFactorsList` API has drifted, report the goal rather than redefining the
  iteration.
- `cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed` quantifies over two
  algebraically closed `R`-algebras `A → B`; if the `Point.map` instance diamonds
  bite, use the pin's instance style and record it in `instance-friction.md` rather
  than weakening the statement.
- **Statements come from the wrappers and the checker reads the declaration's own
  text** (SET-1: 8/13 mismatched until the wrapper's `variable` prelude was
  spliced onto the `S_` proof). Also: the checker's tracker is naive about a dotted
  `end A.B` (it pops one frame) — `Discriminant.lean`'s headlines read as
  `WeierstrassCurve.WeierstrassCurve.…` in the tracker while Lean's name is
  single-level; matching is unaffected, so **do not reshape the file to please the
  tracker**.

### 6.5 Verification

- `lake env lean` clean per module; `lake build` per module.
- Checker `0 mismatched / 0 missing` with the delta recorded.
- Consumer zones: a `cyclicQuotientJ` computation on a concrete curve with a
  `zmultiples` subgroup, a composition with `Velu/MapEquation.lean`, and a
  `#print axioms`-clean use of the base-change lemma.
- `#print axioms` on both `cyclicQuotientJ_*` lemmas:
  `[propext, Classical.choice, Quot.sound]`; no `sorry`.

## 7. Hand-off: what V2 inherits

Fixed by V1, so V2's orders can name them instead of re-deriving:

- vocabulary, under the pin's names: `veluQuotient2`, `velu2QuadDisc`, `velu2X/YNum`,
  `velu2X/Y`, `veluPointMap2`, `map_veluQuotient`, `variableChange_velu*`,
  `cyclicQuotientCurve`, `cyclicQuotientJ`, `xVeluT/U/W`;
- the headline `exists_addMonoidHom_coe_eq_veluPointMap2 : … →+ …` and the
  discriminant identity, both public and checker-verified;
- `Velu/Equivariance.lean` as the home of the base-change commutation of Vélu data —
  V2's `exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples` and the
  `fullKernelHom` column import it rather than copying;
- build budget: every V1 module is a leaf, so V2's first builds start from a warm
  tree; the estimated V2 budget is ≈2–3 k written (plan §3).

Hand-off written the other way as well: **V1 does not port** the reduction column,
`exists_fullKernelHom`, or anything under the `PeriodPair` gate; a V2/V3 worker that
needs one stops and reports, and the manager re-scopes.

## 8. Risk register

| risk | mitigation | status |
|---|---|---|
| a `velu2_*_cleared_identity` or the discriminant identity blows the cap | scout the smallest identity in `Scratch.lean` first (SET-1 §4.5); SET-2 splits at the identity/consumer boundary | open — gate |
| the definition layer is bigger than the referenced-fraction estimate | the estimate is measured (§1); each work order names the *exclusions* (`VeluBundledMap` 0/8, `VeluEquivariance`'s tail 12/13, `VeluQuotientJInvariant` 13/14) | measured |
| a checker match flips because a wrapper's binders differ from the `S_` file | statements from the wrappers, `SOURCES` appended last; `#check @` probe the headlines | usual |
| the counting lemmas duplicate the torsion promotion | read `Algebra/ZModTorsion.lean` first; if the counting lemma is a corollary, prove it that way and record the route | planned |
| `Point.vcInvFun_add` (188) is off-subject and drags `VariableChangePointEquiv` | it is in V1 by the `ucl` rule; SET-3 carries it in its own module with a header saying so | planned |
| a set wants to extend an existing module | forbidden: every V1 deliverable is a new file; extend `spec/` only | settled |

## 9. Reproduce

The node list, the per-node net and the `ucl` column are reproduced by
[TOPIC-port-plan-v2.md](TOPIC-port-plan-v2.md) §5; the referenced-fraction table by

```python
# referenced fraction of a pin Definitions module against the S_ files of its targets
import re
def decls(f):
    t = open(f, encoding='utf-8', errors='replace').read()
    return re.findall(r'^(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?'
                      r'(?:def|theorem|lemma|structure|abbrev|class|instance)\s+'
                      r'([A-Za-z_][A-Za-z0-9_\'\.]*)', t, re.M)
ds = decls('Definitions/Def_WeierstrassCurve_VeluEquivariance.lean')
txt = open('P2M/Sol/S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean').read()
used = [d for d in ds if re.search(r'(?<![A-Za-z0-9_\'])' + re.escape(d.split('.')[-1]) + r'(?![A-Za-z0-9_\'])', txt)]
print(len(used), '/', len(ds), used)
```

Node source line numbers were read from
`Theorems/Thm_<stem>.lean` (statement line) and `P2M/Sol/S_<stem>.lean` (line count
and `solution` line); they move with a re-pin.

## 10. V1 close-out

**Landed 2026-10-05**, three sets run in series with a manager review between each.
Seven new modules, 7,370 written lines against the ≈7.0 k estimate; **no existing
library module edited**, so no set cascaded and the only whole-tree build was the
milestone.

| set | modules | written | `lake build` (wave) |
|---|---|---:|---:|
| SET-1 | `Velu/OrderTwo.lean`, `Velu/OrderTwoMap.lean` | 1,952 | 12 m 47 s |
| SET-2 | `Velu/Equivariance.lean`, `Velu/Discriminant.lean`, `Velu/CyclicCount.lean` | 4,365 | 95 s |
| SET-3 | `Velu/VariableChangePoint.lean`, `Velu/CyclicQuotientJ.lean` | 1,053 | 11 s |

Milestone: checker `5611 → 5699 identical` (the three sets' deltas reconcile as
+39 / +33 / +55, = the new public surfaces), `0 mismatched / 0 missing`, 312
promoted, 36 own-proof; whole-tree build green (9,289 jobs, 14.1 s warm); consumer
679 lines exit 0; `#print axioms` clean on all five headlines.

**The four findings that outlived the wave.** (1) A definition module's *imports*
are part of its source list: `Def_…_VeluVariableChange` pulled
`Def_…_VariableChangePointEquiv`, which no order had assigned; SET-2 ported it and
SET-3 imports it. (2) A referenced-fraction table does not say what the port
*already has*: the `map_velu*` block was already public in `Velu/Formula.lean`, and
SET-2's first build shipped eight silent duplicates before the agent grepped by
name. (3) The cost of an identity column is its `linear_combination` count, not its
line count: SET-1 (1,952 lines) was 50× slower to build than SET-2 (4,365 lines).
(4) The binding knob for those identities is the pin's `maxRecDepth`, not
`maxHeartbeats`; every pin heartbeat bump was dropped and all nodes closed at the
frozen cap.

**Refactor item for V2** (files frozen this wave): `Discriminant.lean` and
`VariableChangePoint.lean` each carry a `private` copy of the `vcInvFun_add` helper
chain; promote one public and delete the other.
