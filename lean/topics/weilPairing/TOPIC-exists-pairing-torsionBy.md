# Topic: the Weil pairing on `E[n]` from `weilPairing0`

**Status: scoped, not started (2026-10-10).** Cone **43 nodes / 5,993 raw `S_`
lines**, 4 of them already ported; **needed 39 / 4,038**. Pin
`anthropics/fermats-last-theorem@aa2d8b3`, port mathlib `v4.34.0`. Checker
baseline at scoping: **7,630 identical (313 promoted, 83 renamed), 0 mismatched,
0 missing, 38 own (7,668 checked)**.

**Why `topics/weilPairing/`, not `deligneSerre/`, `algebraicCurve/` or
`level/`.** The target is a `WeierstrassCurve.*` node — 35 of its 39 needed nodes
are `WeierstrassCurve.*`, and its own proof constructs the pairing from
`weilPairing0` on the affine curve — so it is neither an `AlgebraicCurve` nor a
`ModularCurve` development. Its **consumers** are the Mazur/Ribet level-lowering
column (`isResiduallyModularOfLevel_*`, `mazurRealizationFamily_*`,
`exists_isGoodPrimeFor_*`, `exists_hasLowerLevelTorsion_*`), reached through
`WeierstrassCurve.det_galoisRepModuleEnd_frobenius_eq`. That column is **entirely
unported and unscoped** (no port module and no `topics/` or `studies/` file names
those nodes), so the pairing cannot be scoped "inside" it. This is the
[`charLFrobenius`](../charLFrobenius/TOPIC-qexp-frobenius-modl.md) situation
again — a foundational node that a later column only *consumes* — and it gets its
own directory, mirroring the modules already landed under
`FLTForHuman/WeierstrassCurve/`.

**Audience.** A session taking the elliptic-curve Weil pairing: the valuation
dictionary on `weilFun`/`weilNum`, the four law lemmas of `weilPairing0`, and the
reduction that turns an alternating bi-multiplicative form on `(W⁄K).Point` into
the pairing on `E[n]`. Read [porting-playbook.md](../../porting-playbook.md) §0.2
(staffing), §2.1 (measure the cone), §2.2–§2.3 (route and whole nodes), §3.1–§3.5
(modules, sets, build ladder) and §4 (faithfulness);
[CARRY-FORWARD.md](../../CARRY-FORWARD.md) §Deferred API before budgeting the
`FunctionFieldPullback` slice (§5).

**Goal** (the pin wrapper's statement, verbatim; pin `aa2d8b3`):

```lean
theorem WeierstrassCurve.exists_pairing_torsionBy {F K : Type*} [Field F] [Field K]
    [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hnK : (n : K) ≠ 0) :
    ∃ e : Submodule.torsionBy ℤ (W⁄K).Point n → Submodule.torsionBy ℤ (W⁄K).Point n → Kˣ,
      (∀ P P' Q, e (P + P') Q = e P Q * e P' Q) ∧
      (∀ P Q Q', e P (Q + Q') = e P Q * e P Q') ∧
      (∀ P, e P P = 1) ∧
      (∀ (σ : K ≃ₐ[F] K) P Q, ((e (σ • P) (σ • Q) : Kˣ) : K) = σ (e P Q)) ∧
      (∀ P, (∀ Q, e P Q = 1) → P = 0)
```

The pin produces `e` as a bare function with five of the six `IsWeilPairing`
laws (right-nondegeneracy instead of the bundled `nondegenerate`); the
existential `HasWeilPairing` follows by `nondegenerate : ∃ P Q, B P Q ≠ 1`
derived from the left-nondegeneracy. The port's interface is
`FLTForHuman/WeierstrassCurve/WeilPairing.lean`.

## 1. What is pinned

Every statement comes from the pin:

- wrapper:
  [Theorems/Thm_WeierstrassCurve_exists_pairing_torsionBy.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_pairing_torsionBy.lean)
- proof:
  [P2M/Sol/S_WeierstrassCurve_exists_pairing_torsionBy.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_exists_pairing_torsionBy.lean)
  (88 lines, **2 declarations**: `WeilPairing.exists_pairing_torsionBy_of_laws`,
  the general reduction, and `solution`, the target; see the appendix)
- definitions (both already ported):
  [Definitions/Def_GaloisRep_WeilPairing.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_WeilPairing.lean)
  → `WeilPairing.lean`;
  [Definitions/Def_EllipticCurve_WeilPairingFun.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_WeilPairingFun.lean)
  → `WeilPairingFun.lean`.

The pin's `S_` file imports, besides `P2M.Util`, exactly nine theorem wrappers —
the four `weilPairing0` laws, `eq_zero_of_forall_transEquiv_eq`,
`valuation_mulPull_le_of_ne_zero`, `valuation_weilFun`,
`exists_transEquiv_weilFun_eq`, and `CoordinateRing_isDedekindDomain` (all listed
in §4). The checker diffs every port statement by name; the port transcribes at
the pin's names, so no `OWN_PROOFS` entry should be needed.

## 2. The measured cone

```bash
cd tools/deps
python3 frontier.py --target WeierstrassCurve.exists_pairing_torsionBy --top 0 --list
```

| reading | nodes | raw `S_` lines |
|---|---:|---:|
| port cone (target closure) | 43 | 5,993 |
| frontier `F` inside the cone | 4 | 1,955 |
| **needed (`F` terminal)** | **39** | **4,038** |
| needed (literal) | 39 | 4,038 |

By namespace: `WeierstrassCurve.` 35 / 3,631, `IntermediateField.` 1 / 147,
`IsDedekindDomain.` 2 / 176, `Valuation.` 1 / 84. The target sits one hop above
`F`; the demand histogram is `1:10, 2:3, 3:4` by hops.

**Content vs raw.** These are dense `S_` proof files with no `p2m_*` prelude of
note; budget content at ≈85–90 % of raw, i.e. ~3,400–3,650 content lines. The
largest single files are `valuation_placeOf_neg_transEquiv_algebraMap` (336) and
`FunctionField.eq_valuationSubring_of_X_not_mem` (260) — both place/valuation
lemmas on the function field, not new mathematics.

## 3. What is already paid (do not re-derive)

The four ported nodes inside the cone, with their backing `S_`/`Thm_` lines:

| node | lines | port home |
|---|---:|---|
| `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain` | 187 | `WeierstrassCurve/Place/CoordinateRingDedekind.lean` |
| `WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed` | 376 | `Elliptic/TorsionZMod.lean` |
| `WeierstrassCurve.card_torsion_of_isAlgClosed` | 1,335 | `Elliptic/TorsionCard.lean` |
| `WeierstrassCurve.Affine.fibSet_finite` | 57 | `WeierstrassCurve/FibSetFinite.lean` |

and, below them, the entry points this cone consumes (all landed, checker-clean):

- `WeilPairing.lean` — `IsWeilPairing`, `HasWeilPairing`;
- `WeilPairingFun.lean` — `placeIdeal`/`fibSet`/`fibIdeal`/`weilNum`/`weilFun`/
  `weilPairing0`;
- `Place/PointPlace.lean` — `Point.xc`/`yc`, `placeOf`, `transEquiv` (a *partial*
  port of `Def_EllipticCurve_FunctionFieldPullback`, §5);
- `FibSetFinite.lean` — `torsion_finite`, `card_torsion_toFinset`,
  `fibSet_finite'`, `fibSet_finite`.

The target's own proof is therefore **assembly**: `WeilPairing.exists_pairing_torsionBy_of_laws`
applied to `weilPairing0`, with the four law lemmas quoted and nondegeneracy from
`eq_zero_of_forall_transEquiv_eq` on `weilFun`.

## 4. The needed set, by route group

Four groups, cut on the mathematical object (playbook §2.1); each can be a set.

### G1 — coordinate-ring / function-field local algebra (10 nodes, 1,138 raw)

| node | lines |
|---|---:|
| `IntermediateField.finrank_fieldRange_le_of_adjoin_pair_eq_top` | 147 |
| `IsDedekindDomain.HeightOneSpectrum.exists_eq_span_singleton_of_map_eq` | 142 |
| `IsDedekindDomain.HeightOneSpectrum.valuation_eq_exp_neg_count` | 34 |
| `Valuation.eq_comap_of_valuationSubring_le_comap` | 84 |
| `WeierstrassCurve.Affine.CoordinateRing.isPrincipal_prod_XYIdeal_zpow_iff` | 17 |
| `WeierstrassCurve.Affine.CoordinateRing.natDegree_norm_eq_finsum_count` | 185 |
| `WeierstrassCurve.Affine.FunctionField.adjoin_X_Y_eq_top` | 76 |
| `WeierstrassCurve.Affine.FunctionField.eq_valuationSubring_of_X_not_mem` | 260 |
| `WeierstrassCurve.Affine.FunctionField.exists_eq_algebraMap_of_valuation_eq_one` | 87 |
| `WeierstrassCurve.Affine.FunctionField.exists_valuation_eq_exp_natDegree_norm` | 106 |

These are the `Place` ↔ `ValuationSubring` ↔ `HeightOneSpectrum` dictionary on
the base-changed curve: the port already carries the generic
`AlgebraicCurve.Place` bridge (`Defs/Place.lean`), so check each against the port
before pricing (playbook §2.1 "sweep by name and by `#check`").

### G2 — the `[n]`-fibre, division polynomials and `MulGood` (10 nodes, 599 raw)

| node | lines |
|---|---:|
| `WeierstrassCurve.Affine.Point.exists_zsmul_some_eq_some_baseChange` | 101 |
| `WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff` | 28 |
| `WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff` | 44 |
| `WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div` | 100 |
| `WeierstrassCurve.Affine.evalEval_psi_sq` | 29 |
| `WeierstrassCurve.Affine.ncard_fibSet` | 70 |
| `WeierstrassCurve.Affine.sum_eq_zero_of_forall_mem_iff_smul_eq_zero` | 102 |
| `WeierstrassCurve.Affine.zsmul_genericPoint_good` | 60 |
| `WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic` | 44 |
| `WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq` | 21 |

The division-polynomial half (`evalEval_psi_sq`, `zsmul_some_eq_some_div`,
`two_smul_some_eq_zero_iff`, `Psi2Sq_ne_zero_of_isElliptic`,
`natDegree_Phi_sub_C_mul_PsiSq`) may be partly paid by the Velu port's ψ
development in `WeierstrassCurve/Velu/`; `zsmul_genericPoint_good` is
`MulGood`-shaped and re-enters the deferred pullback node (§5).

### G3 — the valuation of `weilFun`/`weilNum` (14 nodes, 1,688 raw)

| node | lines |
|---|---:|
| `WeierstrassCurve.Affine.valuation_weilNum` | 186 |
| `WeierstrassCurve.Affine.weilNum_ne_zero` | 22 |
| `WeierstrassCurve.Affine.valuation_weilFun` | 17 |
| `WeierstrassCurve.Affine.weilFun_ne_zero` | 21 |
| `WeierstrassCurve.Affine.valuation_transEquiv_weilFun` | 157 |
| `WeierstrassCurve.Affine.valuation_transEquiv_le` | 119 |
| `WeierstrassCurve.Affine.valuation_transEquiv_le_self` | 200 |
| `WeierstrassCurve.Affine.valuation_placeOf_smul_of_algEquiv` | 158 |
| `WeierstrassCurve.Affine.valuation_placeOf_neg_transEquiv_algebraMap` | 336 |
| `WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_smul` | 72 |
| `WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq` | 24 |
| `WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq` | 150 |
| `WeierstrassCurve.Affine.valuation_mulPull_le_of_ne_zero` | 114 |
| `WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le` | 112 |

This is the heart: the divisor of `weilFun` is `n[P] − n[0]`, translation by an
`n`-torsion point multiplies it by a constant of `Kˣ` (the `exists_transEquiv_weilFun_eq`
route), and non-vanishing off the `[n]`-fibre gives the nondegeneracy input.

### G4 — the `weilPairing0` laws (4 nodes, 525 raw)

| node | lines |
|---|---:|
| `WeierstrassCurve.Affine.weilPairing0_add_left` | 37 |
| `WeierstrassCurve.Affine.weilPairing0_add_right` | 110 |
| `WeierstrassCurve.Affine.weilPairing0_self` | 146 |
| `WeierstrassCurve.Affine.weilPairing0_galois` | 232 |

plus the target `WeierstrassCurve.exists_pairing_torsionBy` (88).

**Total: 1,138 + 599 + 1,688 + 525 + 88 = 4,038.** ✔

## 5. The deferred `FunctionFieldPullback` node re-enters here

Two needed nodes are stated in the pin's `Def_EllipticCurve_FunctionFieldPullback`
vocabulary, which the port has **not** carried beyond the `PointPlace.lean`
slice:

- `valuation_mulPull_le_of_ne_zero` (G3, 114) names `mulPull`;
- `zsmul_genericPoint_good` (G2, 60) is `WeierstrassCurve.Affine.MulGood`, whose
  definition sits in the same node.

So this cone is on the [CARRY-FORWARD.md](../../CARRY-FORWARD.md) §Deferred API
entry: before G2/G3, port `Def_EllipticCurve_FunctionFieldPullback` **whole** —
`genericX`/`genericY`, `genericPoint`, `pointHom`/`pointPull`, `transPull`,
`negPull`/`negEquiv`, `MulGood`/`mulPull` and their lemmas. That node is 1,218
lines with ≈90 declarations; it is a prerequisite, not part of this cone, and its
own measurement is a separate prerequisite order. Expect to re-run
`port_advise.py --target Definitions/Def_EllipticCurve_FunctionFieldPullback.lean`
for its dedup against `Velu/Engine.lean` (the port's `translationAlgEquivOf` and
`genericPoint` may already supply part of it).

## 6. Route and set decomposition

Three sets, one work order each, reviewed between (playbook §3.4). Set A is
independent of the deferred node; Set B is the deferred prerequisite; Set C is
the laws and the target wire test.

- **Set A — the fibre/torsion counting (G2 minus `MulGood`, ~540 raw).** New leaf
  module(s) next to `FibSetFinite.lean`. Independent of §5; check the Velu ψ
  development first.
- **Set B — the deferred pullback dictionary (§5), then G1 (1,138 raw + 1,218-node
  prerequisite).** Port the node whole; G1 follows it.
- **Set C — G3 then G4 then the target (~2,300 raw).** Ends with
  `exists_pairing_torsionBy` as the wire test, then the `#print axioms` and the
  consumer zone.

Hand-offs: Set B's `mulPull`/`MulGood` are the fixed names Set C imports; Set A's
`ncard_fibSet`/`fibSet_finite` feed G3's valuation computations. Do not split a
node between sets.

## 7. The consumer cone (why this topic lives here)

`exists_pairing_torsionBy` has one consumer, the auxiliary
`hasWeilPairing_of_isAlgClosed` in the `S_` file of
`WeierstrassCurve.det_galoisRepModuleEnd_frobenius_eq` (252 lines; wrapper
`det ρ(Frob_ℓ) = ℓ mod p`), which feeds
`det_galoisRepModuleEnd_eq_of_isWeilPairing` — the "determinant is the cyclotomic
character, from the six laws" argument of [base/007](../../../base/007-weil-pairing.md)
§2. That node's own cone is 46 nodes / 6,361 raw, **needed 42 / 4,406**, and its
consumers are four nodes of the Mazur/Ribet level-lowering column:

| consumer | lines |
|---|---:|
| `ModularCurve.mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt` | 302 |
| `WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf` | 1,125 |
| `WeierstrassCurve.exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five` | 753 |
| `WeierstrassCurve.exists_isGoodPrimeFor_not_dvd_apOfModel_sub_of_galoisRepIsIrreducible` | 418 |

Those reach `FreyPackage.level_lowering_*` → `FreyPackage.no_frey_package` →
`FLT.fermatLastTheorem`. The level-lowering node alone closes over **12,474
nodes / 4,093,412 raw `S_` lines** — i.e. the whole remaining Frey/Serre/patching
column — and none of it is ported or scoped. That is why the pairing is its own
directory and the level-lowering column is a **separate, future** topic: this
cone is the foundational half, and §7 is the hand-off pointer, not the budget.

## 8. Risk register and verification

Named risks, in the order they bite:

- **The deferred pullback node (§5)** is on the critical path. This is the one
  genuine gate; resolve it before pricing G2/G3. Mitigation: port the node whole
  in Set B; do not re-land `mulPull` privately in the consumers (it would create
  the file-granular shadow the register warns about).
- **Instance drift on `(W⁄K)`.** The pin's `S_` files carry
  `haveI : (W⁄K).IsElliptic := by dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance`
  and `haveI : IsDedekindDomain (W⁄K).CoordinateRing`; the port needs the same
  bricks (playbook §6). The `weilPairing0` laws already required them.
- **`weilPairing0_galois` (232) and `valuation_placeOf_neg_transEquiv_algebraMap`
  (336) are the two heartbeat candidates.** Bisect by milestone, not by
  declaration.
- **Division-polynomial overlap with Velu.** `evalEval_psi_sq` and
  `Point.zsmul_some_eq_some_div` may be re-derivations of landed `Velu/` API;
  check by `#check` before transcribing (the cone's `needed` figure is a node
  count and cannot see this).
- **No `p2m_*` scaffolding** in this `S_` file, so raw ≈ content; budget by the
  named risks, not by lines (playbook §2.5).

Verification (copy into each work order):

> `timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
> `lake build <module>` per finished file; one `lake build` per wave; serialize
> with `flock`. Checker `0 mismatched / 0 missing`; a
> `spec/WeilPairingConsumer.lean` zone per set; `#print axioms` on
> `exists_pairing_torsionBy`; no `sorry`.

## Appendix — the `S_` file's two declarations

`P2M/Sol/S_WeierstrassCurve_exists_pairing_torsionBy.lean` (88 lines):

- `WeilPairing.exists_pairing_torsionBy_of_laws` (lines 25–65) — the general
  reduction: an alternating bi-multiplicative Galois-equivariant form `e₀` on
  `(W⁄K).Point`, restricted to the `n`-torsion, gives the target existential. The
  left-nondegeneracy in the conclusion comes from right-nondegeneracy `hndR` plus
  the skew-symmetry `e₀ T S = (e₀ S T)⁻¹` proved from alternation applied to
  `S + T` (the `hskew` block).
- `solution` (line 67) — applies the reduction to `weilPairing0 W K n`, quoting
  the four law lemmas, and discharges `hndR` with
  `eq_zero_of_forall_transEquiv_eq` + `valuation_mulPull_le_of_ne_zero` +
  `valuation_weilFun` + `exists_transEquiv_weilFun_eq` + `transEquiv_weilFun`.
  Port name: `WeierstrassCurve.exists_pairing_torsionBy` (the wrapper's name,
  per the port's `solution` → wrapper convention).
