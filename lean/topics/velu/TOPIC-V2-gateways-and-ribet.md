# V2 — the two Mazur gateways and the Ribet-side completion

**Status: landed and verified 2026-10-06** — both sets green; see §9 for the
close-out, §4 for the SET-1 landing note and §6 for the hand-off. The work orders
below are kept as written (with the SET-2 amendments made at the SET-1 review gate,
§5–§6, and the review corrections in §9), so the scoping can be judged against what
happened. This is wave
V2 of [TOPIC-port-plan-v2.md](TOPIC-port-plan-v2.md) §3. V1 landed 2026-10-05
([TOPIC-V1-ready-columns.md](TOPIC-V1-ready-columns.md) §10); the four findings of
that close-out are folded into the orders below. Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §0.2 (staffing), §2 (plan),
§2.4 (dedup), §3.3–§3.5 (order, sets, build ladder), §3.7 (order, boundary), §4
(faithfulness). Record: [../../logs/velu-port.md](../../logs/velu-port.md).

V2 is the part of the remaining slice the plan cut as cheap: the two Mazur
gateways, then the Ribet-side completion of the odd-order Vélu quotient. It is
delivered as **new files only**, plus **one** small reconciliation in an existing
leaf module. No library module with dependents is edited, so no set cascades.

| set | story | modules | ≈ written |
|---|---|---|---|
| **SET-1** | the two Mazur gateways (the `IsogenyEndDatum` columns) | `WeierstrassCurve/Place/CoordinateRingDedekind.lean`, `Elliptic/TorsionCardLight.lean`, `WeierstrassCurve/IsogenyEndDatum/PointEndSubring.lean`, `WeierstrassCurve/IsogenyEndDatum/CharPolySquare.lean` | 1.2 k |
| **SET-2** | the Ribet-side completion (the odd-order point map) | `FieldTheory/SeparableOfCoprime.lean`, `AlgebraicCurve/PrincipalDivisors/SeparableRatFunc.lean`, `WeierstrassCurve/PrincipalDivisorsSeparable.lean`, `WeierstrassCurve/Isogeny/PointMapSurjective.lean`, `WeierstrassCurve/Velu/PointMapOddOrder.lean` + the `Velu/RestrictAlong.lean` reconciliation | 0.4 k |

Sequence: SET-1 → manager review → SET-2 (order amended in place against the tree
that then exists) → manager review → milestone. One subagent per set, never two at
once (playbook §0.2, §3.4).

## 1. What V2 is, re-measured 2026-10-06

The plan's §1.1 table was measured 2026-10-05, **before V1 landed**. The fresh run
(`§8`) now reports **17** remaining nodes (V1's 19 are gone), and the four V2
targets are the same four the plan names. `ucl` is the node's unported closure in
pin lines.

| node | own `S_` | `ucl` | set |
|---|---:|---:|---|
| `WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring` | 2,745 | 269 | 1 |
| `WeierstrassCurve.Affine.IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq` | 503 | 3,076 | 1 |
| `WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples` | 34 | 351 | 2 |
| `WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed` | 185 | 2,655 | 2 |

The `ucl` figures are **upper bounds**, and this re-measurement shows why: the
graph does not see (a) that a closure member's mathematics is already in the port
under another name, nor (b) the pin's definitional imports. Both corrections are
measured below; they are the reason V2 is ≈1.6 k written and not ≈3 k.

### 1.1 What the port already has (name sweep, 2026-10-06)

For each target `S_` file, every declaration name was extracted and grepped in
`FLTForHuman/`:

| target `S_` file | declarations | present | absent |
|---|---:|---:|---:|
| `…exists_pointEnd_eq_of_mem_isogenyEndSubring` | 143 | 117 | 26 |
| `…exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq` | 19 | 1 | 18 |
| `…exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples` | 1 | 1 | 0 |
| `…exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed` | 7 | 4 | 3 |

The gateway's 117 present names come from `IsogenyEndDatum/Engine.lean`, which was
landed (H5) as the port of **two other** pin `S_` files — the `dualEndData` and
`restrictAlong_placeOfPoint_eq_add` files, already in `SOURCES`. The gateway's own
`S_` file is not in `SOURCES`; it is where its 26 missing declarations' pin
statements live.

Closure members whose mathematics is already in the port **under another name**
(verify by `grep`/`#check` before writing anything):

| pin closure member (`ucl` lines) | what the port already has |
|---|---|
| `CoordinateRing.isDedekindDomain` (187) | the scoped instance `CoordinateRing.instIsDedekindDomain` and `isDedekindDomain_of_Δ_ne_zero`, `Place/Dictionary.lean:321–327` |
| `CoordinateRing.exists_eq_XYIdeal` (82) | `CoordinateRing.exists_eq_XYIdeal_of_isMaximal` (`Place/Dictionary.lean:170`) + `XYIdeal_ne_bot`/`XYIdeal_isMaximal` (`:335`, `:341`); only the `IsPrime`-to-`IsMaximal` step is new |
| `card_torsion_of_isAlgClosed_light` (12) | `FLTForHuman.Elliptic.card_torsion_of_isAlgClosed`, `Elliptic/TorsionCard.lean:1167` |
| `card_torsionBy_eq_sq_of_isAlgClosed` (12) | the above, at `K := F` |
| `finite_torsionBy_of_natCast_ne_zero` (38) | `private finite_torsionBy_aux`, `IsogenyEndDatum/DualEndData.lean:58` |
| `AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable` (1,246) | the **public** `Divisor.pushforwardNormFormula`, `AlgebraicCurve/PrincipalDivisors/Transcendence.lean:371` (same statement plus `[CharZero F]`); the char-free proof is private in two modules |
| `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable` (911) | `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`, `AlgebraicCurve/PrincipalDivisors/IsSeparable.lean:182` — same statement up to binder explicitness |
| `AlgebraicCurve.normFormulaAlong_of_separableAlong` (24) | `private kw_normFormulaAlong_of_separableAlong_cf`, `WeierstrassCurve/Velu/RestrictAlong.lean:1768` |
| `WeierstrassCurve.Affine.pointMapOfPushforward_surjective` (58) | `pointMapOfPushforward_surjective_of_separableAlong'`, `WeierstrassCurve/Isogeny/NatCard.lean:454` — the same body with `hsep` explicit |
| the `pushforwardNormFormula`/`_ne_zero` separable tail | `AlgebraicCurve/PrincipalDivisors/IsSeparable.lean` (the two separable headlines) |

Two recorded negatives (do not repeat the searches):

- **`finite_torsionBy_of_natCast_ne_zero` is not ported on purpose.** No V2 proof
  calls the pin name, and the mathematics is `private` in `DualEndData.lean:58`; a
  future consumer promotes it in one line. Do not add it to V2.
- **The `reduceHom` node's fresh `ucl` reads 0 and is still out of scope.**
  `WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom`
  reads `ucl = 0` because its closure is `Definitions/`, which the node graph does
  not carry; `grep` finds `reduceHom`/`ReduceHom`/`TorsionIntegral`/`ReductionMap`
  at **0** hits in the port. The plan's §2.1 park stands.

### 1.2 The definition layer: nothing to port

Every `Definitions/` module the four targets import is already in `SOURCES` and
ported: `Def_Isogeny_ConditionalCurrency` (225), `Def_WeierstrassCurve_GenusOnePlaceGateCentred`
(40), `Def_DualIsogenyAPI` (316), `Def_WeierstrassCurve_Velu`, `Def_WeierstrassCurve_OddOrderSummingSet`,
`Def_WeierstrassCurve_VeluQuotientMap` (74), `Def_WeierstrassCurve_VeluPointMap` (86).
V2 has **no** definition-layer work (contrast V1's ≈700 written).

### 1.3 Budget

| set | node net | closure net-new | definitions | ≈ written | measured |
|---|---:|---:|---:|---:|---:|
| SET-1 | 1,155 (701 + 454) | ≈70 (the coordinate-ring pair + the two torsion aliases) | 0 | **1.2 k** | **1,134** (4 modules) + 178 consumer |
| SET-2 | 122 (25 + 97) | ≈230 (the char-free HPD pair, `of_coprime_finrank_expChar`, `normFormulaAlong_of_separableAlong`, the two headlines' own bodies) | 0 | **0.4 k** | — |
| | | | | **≈1.6 k** | |

SET-1 measured 1,134 written lines against the ≈1.2 k estimate (module heads
`83 + 55 + 416 + 580`), plus the 178-line consumer and a 39-line additive
reconciliation held for SET-2. The plan's "≈2–3 k" holds with margin. The
AC/Hecke measured written÷content ratios (1.0–1.45, playbook §2.5) are not applied:
these are transcription sets, and V1's own ratio was ≈1.0.

## 2. Module DAG, namespaces, and the checker wiring

```
WeierstrassCurve/Place/Dictionary.lean                  (existing)
  └─ WeierstrassCurve/Place/CoordinateRingDedekind.lean     SET-1   the shared pair
Elliptic/TorsionCard.lean                               (existing, NOT in PORT_FILES)
  └─ Elliptic/TorsionCardLight.lean                         SET-1   the two aliases
WeierstrassCurve/IsogenyEndDatum/Engine.lean            (existing, H5)
  └─ WeierstrassCurve/IsogenyEndDatum/PointEndSubring.lean   SET-1  gateway 1
WeierstrassCurve/IsogenyEndDatum/DualEndData.lean       (existing, H5)
  └─ WeierstrassCurve/IsogenyEndDatum/CharPolySquare.lean    SET-1  gateway 2
       (imports PointEndSubring, CoordinateRingDedekind, TorsionCardLight)

WeierstrassCurve/Isogeny/NatCard.lean                   (existing)
  └─ WeierstrassCurve/Isogeny/PointMapSurjective.lean        SET-2
WeierstrassCurve/Velu/RestrictAlong.lean                (existing, 0 library dependents)
  └─ (reconciliation: two promotions to the pin names)      SET-2
AlgebraicCurve/PrincipalDivisors/IsSeparable.lean       (existing)
  ├─ AlgebraicCurve/PrincipalDivisors/SeparableRatFunc.lean  SET-2   1-line alias
  └─ WeierstrassCurve/PrincipalDivisorsSeparable.lean        SET-2   the HPD pair
        └─ WeierstrassCurve/Velu/PointMapOddOrder.lean        SET-2   the two headlines
```

Namespaces: every declaration keeps the pin's name and namespace
(`WeierstrassCurve.…`, `WeierstrassCurve.Affine.…`, `WeierstrassCurve.Affine.CoordinateRing.…`,
`WeierstrassCurve.Affine.IsogenyEndDatum.…`, `ModularCurve.…`, `AlgebraicCurve.…`,
`Algebra.IsSeparable.…`), so the checker's last-name match keeps working. Module
headers state the subject, the pin source with its raw URL, and what they assume
from lower modules.

Checker wiring, per set, at the two spec files only (never a library module):

- `spec/check_flt_statements.py`: append the set's new modules to `PORT_FILES`
  **last**; append the pin statement sources to `SOURCES` **last** — the
  `Theorems/Thm_<stem>.lean` wrapper for every headline *and* every non-`solution`
  declaration, and the pin `S_` file for the helper declarations that the wrappers
  do not carry. The wrapper is the statement authority (playbook §4.1).
- `spec/<X>Consumer.lean`: see §2.1 — SET-1 gets a **new** consumer file, SET-2
  extends the existing one.

### 2.1 The consumer split, forced by a name collision

`WeierstrassCurve.Affine.normFormulaAlong_of_elliptic` is declared **twice** in the
port — in `IsogenyEndDatum/Engine.lean` (the H5 copy, `[IsAlgClosed F] [CharZero F]`)
and in `Velu/RestrictAlong.lean` (the H4 char-free copy with an explicit `hsep`).
Lean cannot import the two files into one environment (verified: `lake env lean` on
a file importing both fails with *environment already contains
`WeierstrassCurve.Affine.normFormulaAlong_of_elliptic`*). SET-1's modules import the
Engine cone; SET-2's import the RestrictAlong cone. Therefore:

- SET-1's zones go in a **new** `spec/IsogenyEndDatumConsumer.lean`, because it must
  import the Engine cone and the existing `spec/WeierstrassCurveConsumer.lean` must
  **not** gain an Engine import.
- SET-2's zones extend the **existing** `spec/WeierstrassCurveConsumer.lean`
  (which already imports `Velu/RestrictAlong.lean`).

Do **not** fix the collision inside V2 (no rename of a frozen public name): record
it in the friction log and [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md) as a
refactor-round candidate. The checker is text-based and already matches both copies
against their respective pin `S_` files, so the collision costs nothing until two
modules need both cones.

## 3. Build discipline and the measured costs

> **Build discipline (copy into each work order).** `lake env lean <opts> <file>`
> is the edit loop, with `<opts>` = `-DmaxHeartbeats=4000000 -DautoImplicit=false`
> (without them the check runs at the default cap and lies about heavy modules);
> `lake build <module>` when a file is done; **one** `lake build` per wave; the
> full build at the milestone. Bound every build (`timeout 60` / `90` / `300` /
> `180`), serialize every `lake build` with `flock` (the lock lives in the project
> at `lean/.lake/flt_build.lock`, never `/tmp`), and time it: high user CPU with a
> timeout is a real blow-up to bisect, ~0 CPU is contention. Never raise
> `maxHeartbeats`; this project's global cap is already 4,000,000. Import
> specifically — never `import Mathlib` in a library module.

Measured 2026-10-06 on the warm tree, for the two cones (this is the fixed
`lake env lean` cost of a *tiny* file before any work — the big `.olean`s are
loaded, not re-elaborated):

| cone | fixed edit-loop cost | why |
|---|---:|---|
| SET-1 (`Engine` + `DualEndData` + `RestrictAlongAdd` + `Vocabulary` + `Place/Dictionary`) | **1 m 37 s** | `DualEndData.olean` 8.1 MB, `Engine`/`RestrictAlongAdd` 4.3 MB each; `user` 5 s, `sys` 23 s |
| SET-2 (`Velu/RestrictAlong` + `GenusOnePlaceGateCentred` + `PrincipalDivisors` + `IsSeparable`) | **8.6 s** | one 2,109-line module cone, no 8 MB olean |

Consequences, binding:

1. **SET-1 must iterate in batches, never per declaration.** Put a *bounded block*
   of declarations in the module (or a `tmp/scratch*.lean` importing only what the
   block needs), check once, then extend. `tmp/` is gitignored; V1 left
   `tmp/build_set1.py`-style drivers there. A 700-line module checked once costs
   ≈2 min on top of the 1 m 37 s floor; checked 50 times it costs hours.
2. **Never `lake build` in the edit loop** (playbook §3.5). `lake build <module>`
   writes the `.olean` and builds *dependencies*, never dependents.
3. **The whole wave edits each module once.** Every V2 deliverable except the
   RestrictAlong reconciliation is a new file, so the cascade is empty; the one
   `lake build` per set is `lake build <the set's modules>` followed by the
   milestone whole-tree build.
4. **The RestrictAlong reconciliation is the wave's only existing-file edit.**
   Measured cascade: **0 library modules, ≈25 s** (`Velu/RestrictAlong.lean` has no
   library importer; only `spec/WeierstrassCurveConsumer.lean` restates). Compare
   `Transcendence.lean`, the other home of the same private proof: **52 modules /
   ≈405 s**. That measurement is why the reconciliation goes in
   `Velu/RestrictAlong.lean`.

Baseline for the progress metric (2026-10-06, warm tree):

```
$ python3 spec/check_flt_statements.py
5750 statements identical (312 promoted from pin-private declarations), 0 mismatched,
0 missing, 36 own-proof declarations exempted (5786 port declarations checked)
$ flock .lake/flt_build.lock bash -c 'time lake build'      # 9294 jobs, green, 13.6 s
$ timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/WeierstrassCurveConsumer.lean
exit 0 (61 s)
```

## 4. SET-1 work order — the two Mazur gateways

**Status: landed and reviewed 2026-10-06.** Four new modules (1,134 written lines)
plus a 178-line `spec/IsogenyEndDatumConsumer.lean`. Checker `5750 → 5796 identical`
(+46: 46 genuinely new public declarations — the `promoted → ok` flip of
`IsogenyEndDatum.pointEnd_eq_geomMorph_sub_geomMorph_zero` contributes 0, since
`promoted` is a subset of `identical`), promoted `312 → 311`, `0 mismatched /
0 missing`; whole-tree build green (9298 jobs, 12.7 s — no cascade); consumer exit 0
(1 m 10 s); `#print axioms` clean on all seven headlines. The order below is kept
as written; the review's corrections are in §6 and §9.

Two findings from this set:
(a) **A third module-import collision of the §2.1 family**: `GenusOnePlaceGateCentred.lean`'s
`Place/RRSpace.lean` (`scoped instance instInfinitePlace`, line 444) cannot be
imported alongside `IsogenyEndDatum/Engine.lean` (plain `instInfinitePlace`, line 90),
so the SET-1 consumer takes the three gate instances as hypotheses instead of
discharging them from `exists_genusOnePlaceGate_isCentred_and_abelTheorem`; and
(b) the §4.2 table missed one pin-public name, `coe_isogenyEndSubmonoid` (landed),
and one already-present name, `KwIsogenyEndAddDatumSupply` (`Engine.lean:228`).

### 4.1 Scope

Port the two unconditional `IsogenyEndDatum` columns the plan cut as V2's
gateways: (a) every nonzero endomorphism of the formal group's end ring is the
`pointEnd` of some isogeny datum (`exists_pointEnd_eq_of_mem_isogenyEndSubring`,
2,745 raw / 701 net, 143 declarations of which 117 are already in the port), and
(b) its number-theoretic consumer: the trace/norm of a non-integral endomorphism
spans binary quadratic forms of negative discriminant
(`exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq`, 503 raw / 454 net).
Plus the two prerequisites that are shared with SET-2 and the port does not
provide at the pin names: the coordinate-ring Dedekind/`XYIdeal` pair, and the two
generic elliptic-torsion aliases (a). No definition module is involved (§1.2).

**Not this set:** anything under the `PeriodPair` uniformization gate
(`aeval_j_diag_eq_zero_of_finrankAlong_eq`), the base-change trio, the
`exists_intermediateField_countable…` node, the `fullKernelHom`/`reduceHom`
columns, and the far-end modular-polynomial bijection. A worker that reaches an
unported prerequisite outside this set **stops at the boundary and reports**
rather than editing a closed module or weakening a statement (playbook §3.7).

### 4.2 Source (pin)

Statements verbatim from the `Theorems/` wrappers; proofs from the `S_` files,
adapted to mathlib `v4.34.0`. Every path below is relative to the pin root
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/>).

**The shared coordinate-ring pair** (new module 1):

- `Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean:19` +
  `P2M/Sol/S_…_isDedekindDomain.lean` 187 (the whole 187-line file is the pin's route
  to the instance; the port already has an equivalent route, so only the statement is
  transcribed):

  ```lean
  theorem WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain
      {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic] :
      IsDedekindDomain W.toAffine.CoordinateRing
  ```

- `Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.lean:9` +
  `P2M/Sol/S_…_exists_eq_XYIdeal.lean` 82 (the pin's wrapper declares it as
  `P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal`; the checker
  matches by last name, so the port declares it at the undecorated name):

  ```lean
  theorem P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal
      {K : Type*} [Field K] {W : Affine K} [IsAlgClosed K]
      {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] :
      ∃ a b : K, W.Equation a b ∧ P = XYIdeal W a (C b)
  ```

  Proof route: the pin's `isMaximal_of_isPrime_of_ne_bot` (its 4 lines, absent from
  the port) then the ported `exists_eq_XYIdeal_of_isMaximal`.

**The two torsion aliases** (new module 2), both `WeierstrassCurve.…`:

- `Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light.lean:9` +
  `P2M/Sol/S_…_light.lean` 12 (the pin's proof is one line:

  ```lean
  theorem WeierstrassCurve.card_torsion_of_isAlgClosed_light
      {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
      [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ}
      (hn : (n : K) ≠ 0) :
      Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2
  ```

  Spell the base change with the `⁄` notation exactly as above — the port's
  `FLTForHuman.Elliptic.card_torsion_of_isAlgClosed` spells it `W.baseChange K` and
  is **not** in `PORT_FILES`, so it is not a text reference for the checker.
- `Theorems/Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed.lean:11` +
  `P2M/Sol/S_…_card_torsionBy….lean` 12: the same at `K := F`. It is consumed by
  gateway 2.

**Gateway 1** (new module 3): `Theorems/Thm_…_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean:19`
(statement) + `P2M/Sol/S_…pointEnd….lean` 2,745 (`solution` at 2732). The headline:

```lean
theorem WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (ψ : AddMonoid.End W.Point) (hψ : ψ ∈ isogenyEndSubring W hNs) (hne : ψ ≠ 0) :
    ∃ D : IsogenyEndDatum W, D.pointEnd (hNs D) = ψ
```

The pin's `solution` body is short and names its own dependencies:

```lean
  have hadd : ModularCurve.KwIsogenyEndAddDatumSupply W := …
  exact ModularCurve.kw_isogenyEndDatumOfNonzeroEnd_of_addDatumSupply W hadd ψ hψ hne
```

The **26 declarations absent from the port** (line spans in the pin `S_` file; the
names are pin-public, and the checker needs them declared at those names):

| span | name | note |
|---:|---|---|
| 1 | `instFactNatPrime2_s13e2` | `Fact (Nat.Prime 2)`; same for 3 and 7 (`instFactNatPrime3/7_s13e2`) |
| 50 | `KwIsogenyEndDatumOfNonzeroEnd` | the datum `abbrev` the headline produces |
| 9 | `InertiaDegComp` | check against the port's `inertiaDegAlong_comp` |
| 96 | `one_mem_range_pointEnd` | |
| 14 | `restrictInclusionAlong` | check `AlgebraicCurve/Defs/RestrictAlongAPI.lean` |
| 6 | `restrictResidueMapAlong` | idem |
| 91 | `Divisor.pushforwardAlong_pushforwardAlong'` | the port has the unprimed sibling (present); check whether the pin's two are binder-only variants — if so port **one** general lemma (playbook §2.4) |
| 62 | `geomMorph_compDatum` | |
| 28 | `pushforwardAlongHom_comp_apply` | |
| 4 | `isIntegral_comp_` | |
| 23 | `comp_pointEnd` | |
| 14 | `mul_mem_range_pointEnd` | |
| 9 | `isogenyEndSubmonoid` | |
| 5 | `submonoid_closure_range_pointEnd` | |
| 6 | `coe_submonoid_closure_range_pointEnd` | |
| 60 | `mem_isogenyEndSubring_iff_mem_addSubgroup_closure` | |
| 8 | `geomMorph_add_geomMorph_zero` | |
| 7 | `geomMorph_sub` | |
| 57 | `compDatum_pointEnd` | |
| 37 | `es1a4_negDatum_pointEnd` | the `es1a4_negDatum` datum itself is already in `Engine.lean` |
| 8 | `kw_neg_mem_range_pointEnd` | |
| 22 | `kw_zero_or_mem_range_pointEnd_of_mem_addSubgroup_closure` | |
| 36 | `kw_isogenyEndDatumOfNonzeroEnd_of_addDatumSupply` | |

`KwIsogenyEndAddDatumSupply` (`abbrev`, span 50 at line 486) and the two
`ModularCurve.…` names keep the pin's `ModularCurve` namespace.

**Gateway 2** (new module 4): `Theorems/Thm_…_exists_sq_lt_four_mul….lean:23` +
`P2M/Sol/S_…sq_lt_four_mul….lean` 503 (`solution` at 494). The headline:

```lean
theorem WeierstrassCurve.Affine.IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    [GenusOnePlaceGate.IsCentred W]
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (D₀ : IsogenyEndDatum W)
    (hD₀ : ¬ ∃ m : ℤ, ∀ P : W.Point, D₀.pointEnd (hNs D₀) P = m • P) :
    ∃ t n : ℤ, t ^ 2 < 4 * n ∧
      ∀ a b : ℤ, b ≠ 0 → ∃ D : IsogenyEndDatum W,
        (finrankAlong F D.ι : ℤ) = a ^ 2 + t * a * b + n * b ^ 2
```

Its `S_` file's 18 missing declarations are a self-contained pure-algebra prelude
(namespace `Ws13S7`) followed by the dual-end-data argument; 18/19 are absent from
the port, so transcribe the file in its own order (a valid topological order):

`mem_bot_addMonoidEnd_iff` (7), `dd_charPoly_eq` (5),
`dd_intLinComb_norm_pos_of_disc_neg` (9), `dd_intLinComb_norm_pos_of_b_eq_zero` (7),
`dd_intLinComb_norm_pos_of_disc_neg_of_ne_zero` (11),
`binaryQuadForm_pos_of_neg_disc` (7),
`linearIndependent_one_of_quadCharPoly_neg_disc` (48),
`charZero_addMonoidEnd_point` (28), `intCast_addMonoidEnd_point_injective` (5),
`finrankAlong_pos` (9), `finrankAlong_datum_pos` (3),
`isogenyEndSubring_mul_left_cancel` (29),
`sq_eq_intCast_nonneg_isSquare` (47), `dualEndData_disc_neg_of_notBot` (113),
`s7_exists_dualEndData_dual_mem_and_intLinComb_norm_pos` (29),
`dd_norm_trace_unique` (48), `s7_dualEndData_norm_eq_finrankAlong` (10),
`s7_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq` (45).
It also consumes `card_torsionBy_eq_sq_of_isAlgClosed` (module 2) and the ported
`exists_dualEndData_dual_mem_and_norm_eq_finrankAlong` (`DualEndData.lean:3921`).

### 4.3 Deliverable

Four new modules, all under their pin namespaces:

1. **`FLTForHuman/WeierstrassCurve/Place/CoordinateRingDedekind.lean`** — imports
   `FLTForHuman.WeierstrassCurve.Place.Dictionary`. Declares
   `CoordinateRing.isDedekindDomain` and
   `CoordinateRing.exists_eq_XYIdeal` (public, pin statements); the
   `IsPrime → IsMaximal` helper is `private`.
2. **`FLTForHuman/Elliptic/TorsionCardLight.lean`** — imports
   `FLTForHuman.Elliptic.TorsionCard`. Declares
   `WeierstrassCurve.card_torsion_of_isAlgClosed_light` and
   `WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed`.
3. **`FLTForHuman/WeierstrassCurve/IsogenyEndDatum/PointEndSubring.lean`** — imports
   `FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Engine` and
   `CoordinateRingDedekind`. Carries the 26 declarations of §4.2 and the headline.
   Public: the headline and the pin-public names of §4.2; everything new-local stays
   `private`.
4. **`FLTForHuman/WeierstrassCurve/IsogenyEndDatum/CharPolySquare.lean`** — imports
   `PointEndSubring`, `FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DualEndData` and
   `FLTForHuman.Elliptic.TorsionCardLight`. Carries the 18-declaration prelude and
   the headline. This is the set's wire test.

Register the four in `PORT_FILES` (append last) and the pin sources of §4.2 in
`SOURCES` (append last, wrappers before their `S_` files):

```
    "Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.lean",
    "Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light.lean",
    "Theorems/Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean",
```

Then add a zone per module to **`spec/IsogenyEndDatumConsumer.lean`** (new; see
§2.1). Each zone must be a real, executed cross-module composition — no `#check`,
no `sorry`; deleting any one module must make the file fail. Suggested zones:

- the coordinate-ring pair at a concrete elliptic curve over `AlgebraicClosure ℚ`
  (reuse the consumer's `W1 : y² = x³ + 1` idiom), including an
  `exists_eq_XYIdeal`-produced prime and `IsDedekindDomain W1.toAffine.CoordinateRing`;
- the two torsion aliases, with a numeric `#eval`/`norm_num` check (`n = 3` gives
  `9`) and at least one use in a composition with
  `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`;
- gateway 1 with `hNs` **discharged** from the ported
  `IsogenyEndDatum.normFormulaAlong_auto` and the ported genus-one gate
  (`exists_genusOnePlaceGate_isCentred_and_abelTheorem`), and `ψ` a nonzero element
  of `isogenyEndSubring W hNs` (for instance `ψ = 1` realised through the ported
  `idDatum`), concluding `∃ D, D.pointEnd (hNs D) = ψ`;
- gateway 2 stated in hypothesis form (playbook §4.2: the non-integrality
  hypothesis has no concrete witness in the port), plus one non-vacuity `example`
  for the pure-algebra prelude (`mem_bot_addMonoidEnd_iff`,
  `binaryQuadForm_pos_of_neg_disc` at concrete integers) that needs no gate
  instances.

### 4.4 Route, with recorded negatives

- mathlib has **no** `IsogenyEndDatum`, no `isogenyEndSubring`, no `pointEnd`, no
  `FiniteAlong`/`NormFormulaAlong`, no `GenusOnePlaceGate`/`AbelTheorem`, no
  `DualEndData`: all FLT vocabulary. What mathlib supplies is `Ideal.isMaximal_…`,
  `IsLocalization.AtPrime`, `IsDiscreteValuationRing.TFAE`, `Submodule.torsionBy`,
  `Algebra.norm` — the ported modules already wrap them.
- The 117 names the gateway `S_` file shares with the H5 files are **already
  public** (mostly in `Engine.lean`). Import, do not redeclare. Where the pin's
  local copy differs from the port's public one, **the port's statement wins** and
  the difference is recorded (V1 finding 2).
- `CoordinateRing.isDedekindDomain`: the port's proof route is
  `isDedekindDomain_of_Δ_ne_zero` (`Place/Dictionary.lean:321`), not the pin's
  `isDedekindDomain_of_isAlgClosed'`; both are landed and green. Transcribe the
  *statement* only, and prove it from the port's route.
- `CoordinateRing.exists_eq_XYIdeal`: the non-maximal case is new; the pin's
  `isMaximal_of_isPrime_of_ne_bot` is 4 lines
  (`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap` + `IsPrime.to_maximal_ideal`).
  `P2M.Dup.…exists_eq_XYIdeal`'s statement is the wrapper's; keep the `P2M.Dup.`
  prefix off the Lean name (the checker matches the last name) but spell the
  binders exactly as the wrapper.
- The two torsion aliases are one-liners over
  `FLTForHuman.Elliptic.card_torsion_of_isAlgClosed` (`TorsionCard.lean:1167`),
  which takes `W.baseChange K`; the pin spells `W⁄K`. The `⁄` notation is
  available in the port (`DualEndData.lean:75`). Do not re-prove the count.
- The gateway `S_` file sets `maxHeartbeats` up to `25600000` and
  `synthInstance.maxHeartbeats` `1600000`; the port's global cap is `4000000` and
  the pin's bumps are **dropped**. There is **no** `maxRecDepth` bump in this file
  (unlike V1 SET-1). If a declaration blows the frozen cap, supply the explicit
  instance / restructure the proof rather than raising it (playbook §6).
- `Divisor.pushforwardAlong_pushforwardAlong'` (91): the port has the unprimed
  `Divisor.pushforwardAlong_pushforwardAlong` publicly. Diff the two pin
  statements first; if they differ only by binders, port **one** and derive the
  other, and record the drop with `grep -c`.

### 4.5 Stop-early risks (stop and report, do not push)

- **`ord_polyToFunctionField_pos_iff`-class declarations.** The pin's file carries
  a `maxHeartbeats 25600000` block; the ported `Engine.lean` already contains the
  hard `ord`/`place` machinery, so the gateway module should mostly *import*, but if
  a new declaration (the `ord_nonneg_of_mem`/`mem_of_ord_nonneg` family, or
  `isFinitePlace_of_mem`) exceeds the frozen cap after the batch gate, stop and
  report which one with its `lake env lean` time.
- **`es1a4_negDatum_*`/`one_mem_range_pointEnd` are kernel-heavy identites.** Scout
  the smallest one (`kw_neg_mem_range_pointEnd`, 8 lines) in a `tmp/scratch` block
  and report the time before writing the whole module.
- **A statement in §4.2 whose wrapper text differs from the `S_` file's copy: the
  wrapper wins**; report the difference rather than choosing.
- **Any pull toward `aeval_j_diag_eq_zero_of_finrankAlong_eq`, the base-change trio,
  or the `PeriodPair` ladder**: that is the boundary (§4.1). Stop and report.
- **Gateway 2's `dualEndData_disc_neg_of_notBot`** (113 lines) may be present in
  `DualEndData.lean` under a different name; if the port's version is stronger or
  differently bound, stop and report the two statements rather than weakening one.

### 4.6 Verification

- `lake env lean` clean per module; `lake build` per module; then one wave
  `lake build` over the four modules (bounded, `flock`ed).
- `python3 spec/check_flt_statements.py` → `0 mismatched / 0 missing`; record the
  `identical` before → after delta (baseline `5750`) and reconcile it against the
  new public surface. A mismatch is a bug, not a drift to accept.
- The checker's own sanity probe: mutate one token in a transcribed statement,
  expect exactly `N identical / 1 mismatched / 0 missing`, revert (playbook §4).
- `spec/IsogenyEndDatumConsumer.lean` exit 0.
- `#print axioms` on `exists_pointEnd_eq_of_mem_isogenyEndSubring` and
  `exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq`:
  `[propext, Classical.choice, Quot.sound]`; no `sorry`.
- `grep -c` of every declaration dropped as already-present or binder-only, with
  the reason, in the friction log.

## 5. SET-2 work order — the Ribet-side completion

**Status: landed and reviewed 2026-10-06.** Five new modules (537 written lines) plus
the **+39 / −0** additive reconciliation in `Velu/RestrictAlong.lean`. Checker
`5796 → 5805 identical` (+9: 2 reconciliation + 7 prerequisites/headlines),
promoted unchanged `311 → 311`, `0 mismatched / 0 missing`; whole-tree build green
(9,303 jobs, 12.3 s — the +5 module jobs and no cascade); `spec/WeierstrassCurveConsumer.lean`
exit 0; `#print axioms` clean on all four headlines; the one-token mutation probe
gave exactly `5804 / 1 / 0` and reverted clean. The order below is kept as written,
with the §5.2 reconciliation amendment made at the SET-1 gate.

### 5.1 Scope

Complete the Ribet side of the odd-order Vélu column: the two point-map headlines
for `E/⟨Q⟩` with `addOrderOf Q = 2n+1` — that the descended function-field
homomorphism has kernel exactly `zmultiples Q`
(`exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples`, 34 raw), and
the explicit point map with the `veluX`/`veluY` coordinates
(`exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed`, 185 raw) — together with
the four prerequisites the port lacks at the pin names: the separate-principal-
divisors interface (`Divisor.pushforwardNormFormula_of_isSeparable`,
`normFormulaAlong_of_separableAlong`, `hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable`),
the generic separable-coprime lemma (`Algebra.IsSeparable.of_coprime_finrank_expChar`),
the characteristic-free function-field principal-divisors pair, and the point-map
surjectivity wrapper.

**Not this set:** the definition layer (§1.2 — all ported), the `fullKernelHom`
column, `WeierstrassCurve.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add`,
the modular-polynomial bijection, and the `exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom`
reduction column (§1.1 negative). A worker that reaches an unported prerequisite
outside this set stops at the boundary and reports.

### 5.2 Source (pin)

**Target 3** — `Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples.lean:34`
+ `P2M/Sol/S_…_ker_eq_zmultiples.lean` 34 (`solution` at 10):

```lean
theorem WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
    {Q : W.toAffine.Point} {n : ℕ} (hord : addOrderOf Q = 2 * n + 1)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    [(W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine] :
    ∃ (ι : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      AlgebraicCurve.finrankAlong F ι = 2 * n + 1
        ∧ ∀ hN : AlgebraicCurve.NormFormulaAlong F ι hfin,
            (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
              = AddSubgroup.zmultiples Q
```

Its whole proof is 8 lines: it destructures the **already-ported**
`WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq`
(`Velu/RestrictAlong.lean`) and drops the three extra conjuncts. Net cost ≈10 lines.

**Target 4** — `Theorems/Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed.lean:24`
+ `P2M/Sol/S_…oddOrderSummingSet….lean` 185 (`solution` at 89):

```lean
theorem WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0)
    (Q : W.toAffine.Point) (hQord : addOrderOf Q = p) :
    let S := W.oddOrderSummingSet Q (p / 2)
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h')
```

Its proof names exactly five prerequisites (§5.4): the ported restrictAlong
headline, the two function-field principal-divisors instances, the genus-one gate
(ported), `normFormulaAlong_of_separableAlong`, `of_coprime_finrank_expChar`. The
`S_` file has 7 declarations; 4 are present in the port
(`inertiaDegAlong_eq_one'`, `pushforwardAlong_single_eq'`, `pointMapOfPushforward_apply'`
and the port's `…_of_separableAlong'` idiom); the three absent primed helpers
(`pushforwardAlongDegZero_pointDivisor'`, `pushforwardAlongHom_pointClass'`,
`pointMapOfPushforward_eq_of_seam'`) are the same three names already public
**unprimed** in `WeierstrassCurve/Isogeny/NatCard.lean` — import them and use the
port's names; do not redeclare the primed copies unless a statement genuinely
differs, and record either way.

**The prerequisite nodes** (pin `S_` line counts; statements from the wrappers):

| node | wrapper | `S_` | port status |
|---|---|---:|---|
| `AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable` | 9 | 1,246 | port's public `Divisor.pushforwardNormFormula` (`Transcendence.lean:371`) has `[CharZero F]`; the char-free proof is private in `Velu/RestrictAlong.lean:1749` |
| `AlgebraicCurve.normFormulaAlong_of_separableAlong` | 9 | 24 | `private kw_normFormulaAlong_of_separableAlong_cf`, `Velu/RestrictAlong.lean:1768` |
| `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable` | 13 | 911 | port's `…_of_isSeparable` (`IsSeparable.lean:182`) is the same statement, different binder spelling |
| `Algebra.IsSeparable.of_coprime_finrank_expChar` | 8 | 24 | absent |
| `WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_two_ne_zero_or` | 13 | 147 | absent; its proof is `isSeparable_yCoord_of_or` + `algebra_isSeparable_ratFunc_functionField_of_or` + the ported `hasPrincipalDivisors_of_finiteDimensional_of_isSeparable` |
| `WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic` | 12 | 34 | absent; 1-line corollary of the previous + `two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero` (which is absent too — 12 lines) |
| `WeierstrassCurve.Affine.pointMapOfPushforward_surjective` | 18 | 58 | port's `…_of_separableAlong'` (`NatCard.lean:454`) is the body; the pin derives `hsep` from `Algebra.IsSeparable.of_integral` |

**The reconciliation** (the wave's only existing-file edit) — in
`FLTForHuman/WeierstrassCurve/Velu/RestrictAlong.lean`:

- **Add** a public `AlgebraicCurve.normFormulaAlong_of_separableAlong`, at the pin's
  binders exactly as `Theorems/Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong.lean`
  (`{K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') [HasPrincipalDivisors K F'] (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)`),
  proved by the existing private `kw_normFormulaAlong_of_separableAlong_cf`
  (line 1776) with the `[HasPrincipalDivisors K F']` instance supplied.
- **Add** a public `AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable`
  at the pin wrapper's binders
  (`{K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']`),
  proved by the existing private `Divisor.pushforwardNormFormula_of_finiteDimensional`
  (line 1749), which is *hypothesis-free* and so already stronger; the pin's
  `[HasPrincipalDivisors K F']` is carried in the statement and unused in the proof.
- **Leave both privates in place.** They stay the char-free proof bodies and their
  only callers are inside this file (verified 2026-10-06: `pushforwardNormFormula_of_finiteDimensional`
  is called once, at line 1783; `kw_normFormulaAlong_of_separableAlong_cf` once, at
  line 1806), so this is **purely additive — no rename and no caller edits**.
  `private ord_norm_eq_sum_fiberOver` (line 1713) stays private.

The section variables in scope at line 1567 are `{K F F'} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']`; the public wrappers add `[HasPrincipalDivisors K F']` (the second) and make `φ`/`hfin`/`hsep` explicit (the first).

Measured cascade of this edit: **0 library modules / ≈25 s** (§3, rule 4). It is the
only library file V2 edits; do it in one pass and do not reopen it.

### 5.3 Deliverable

Five new modules plus the reconciliation:

1. **`FLTForHuman/FieldTheory/SeparableOfCoprime.lean`** — the pin's
   `Algebra.IsSeparable.of_coprime_finrank_expChar` (24 lines; the pin's proof is a
   transcription). Imports only mathlib.
2. **`FLTForHuman/AlgebraicCurve/PrincipalDivisors/SeparableRatFunc.lean`** — the
   one-line alias `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable`
   from the ported `hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`
   (`AlgebraicCurve/PrincipalDivisors/IsSeparable.lean:182`). Its own module because
   the namespace is `AlgebraicCurve`, not `WeierstrassCurve`.
3. **`FLTForHuman/WeierstrassCurve/PrincipalDivisorsSeparable.lean`** — the
   characteristic-free function-field pair:
   `WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_two_ne_zero_or`
   and `WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic`. Imports
   `FunctionFieldQuadratic`, `FunctionFieldFinite`, `PrincipalDivisors` and
   `AlgebraicCurve/PrincipalDivisors/IsSeparable`; `isSeparable_yCoord_of_or` and
   `algebra_isSeparable_ratFunc_functionField_of_or` are transcribed from the pin's
   147-line `S_` file, the rest is the port's generic separable transfer.
   `two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero` is `private`.
4. **`FLTForHuman/WeierstrassCurve/Isogeny/PointMapSurjective.lean`** — the pin's
   `WeierstrassCurve.Affine.pointMapOfPushforward_surjective`, proved from the
   ported `pointMapOfPushforward_surjective_of_separableAlong'` (`NatCard.lean:454`)
   by supplying `hsep` from `Algebra.IsSeparable.of_integral`. If the ported lemma's
   binders do not line up, stop and report the two statements rather than weakening
   either.
5. **`FLTForHuman/WeierstrassCurve/Velu/PointMapOddOrder.lean`** — the two headlines
   of §5.2, both public, plus their proof-local helpers (`private`). This is the
   set's wire test. Imports `Velu/RestrictAlong` (for the restrictAlong headline),
   `GenusOnePlaceGateCentred`, `WeierstrassCurve/PrincipalDivisorsSeparable` and
   `FieldTheory/SeparableOfCoprime`.

Register the five modules (and only these) in `PORT_FILES`, appended last; append
the eight wrappers and the two headline `S_` files to `SOURCES`, appended last,
wrappers first. `Velu/RestrictAlong.lean` is already in `PORT_FILES`, so its two
promoted declarations are picked up without a wiring change; the two new wrapper
entries are what lets the checker diff them.

Then extend **`spec/WeierstrassCurveConsumer.lean`** with one zone per new module —
real executed compositions, no `#check`, no `sorry`:

- the char-free HPD pair at a concrete curve in **both** characteristics: the
  consumer's `W1` over `AlgebraicClosure ℚ`, and a curve with `a₁ ≠ 0` over a
  characteristic-2 or -3 field (or over `ZMod 3` / `ZMod 2` with `IsElliptic`
  discharged by `norm_num` on `Δ`), so the `(2 : F) ≠ 0 ∨ a₁ ≠ 0 ∨ a₃ ≠ 0` branch is
  genuinely exercised;
- `Algebra.IsSeparable.of_coprime_finrank_expChar` at a concrete coprime pair
  (e.g. a rank-1 extension with `q = 2`);
- `Divisor.pushforwardNormFormula_of_isSeparable` / `normFormulaAlong_of_separableAlong`
  composed with `exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq`
  (hypothesis form where the gate instances cannot be discharged);
- `pointMapOfPushforward_surjective` on the ported restrictAlong datum;
- the two headlines in hypothesis form, plus one `#print axioms`-clean use of
  target 3's kernel statement.

Do **not** add an `IsogenyEndDatum`/`Engine` import to this file: the
`normFormulaAlong_of_elliptic` collision (§2.1) forbids it. SET-1's zones live in
the new `spec/IsogenyEndDatumConsumer.lean`.

### 5.4 Route, with recorded negatives

- mathlib has no `HasPrincipalDivisors`, no `FiniteAlong`/`NormFormulaAlong`/`SeparableAlong`,
  no `normFormulaAlong`; all FLT vocabulary, already ported in
  `AlgebraicCurve/Defs/Correspondence.lean` and `Defs/PushPull.lean`.
- `Algebra.IsSeparable.of_coprime_finrank_expChar`: mathlib `v4.34.0` has
  `Algebra.IsSeparable.of_integral`, `PerfectField`-based separability, and
  `ExpChar`; the pin's proof is a short transcription over `ExpChar.exists`.
  **Pre-verified 2026-10-06** (manager `#check` probe): every name the pin's 24-line
  proof uses exists at the expected type in `v4.34.0` —
  `Field.finSepDegree_eq_finrank_iff`, `separableClosure.isPurelyInseparable`,
  `IsPurelyInseparable.finrank_eq_pow`, `Field.finInsepDegree`,
  `Field.finSepDegree_mul_finInsepDegree`, `Nat.Coprime.eq_one_of_dvd`,
  `Nat.Coprime.pow_left`, `expChar_of_injective_algebraMap` — so the transcription
  should go through with only binder-level tweaks.
- The pin's `hasPrincipalDivisors_functionField_of_two_ne_zero_or` calls
  `hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable`; the port calls
  the same-content `hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`
  (imported). Use the port's, not module 2's alias, to avoid a cycle.
- `isSeparable_yCoord_of_or` is the set's one piece of genuinely new mathematics
  (≈47 lines): the derivative of the `y`-quadratic is nonzero under
  `2 ≠ 0 ∨ a₁ ≠ 0 ∨ a₃ ≠ 0`. Check the pin's `linear_combination`-style steps
  against `v4.34.0` (`linear_combination`, `Polynomial.coeff_derivative`,
  `minpoly.dvd`, `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`).
  **Pre-verified 2026-10-06** (manager `#check` probe): the pin's whole glue chain
  has ported counterparts at the expected types —
  `WeierstrassCurve.Affine.adjoin_yCoord_eq_top`, `…finiteDimensional_ratFunc_functionField`,
  `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`,
  `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`,
  `…isIntegral_yCoord`, `…aeval_yCoord_weierstrassQuadratic`, `…weierstrassQuadratic_monic`,
  `…weierstrassQuadratic_sub_degree_lt`, `Polynomial.coeff_derivative`,
  `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`, `minpoly.dvd`,
  `IntermediateField.topEquiv`, `AlgEquiv.Algebra.isSeparable`. Use the port's
  `hasPrincipalDivisors_of_finiteDimensional_of_isSeparable` (E-binder form) with
  `E := W.FunctionField`, not module 2's alias, to avoid an import cycle.
- `pointMapOfPushforward_surjective`: the only new content beyond the ported
  `…_of_separableAlong'` is the `hsep` derivation
  (`Algebra.IsSeparable.of_integral`), which needs
  `charZero_of_injective_algebraMap` for the intermediate field — see the pin's
  58-line file.
- The pin's target-4 proof calls `Algebra.IsSeparable.of_coprime_finrank_expChar`
  with `q = ExpChar.exists F`; the port's `ExpChar`/`CharP.cast_eq_zero_iff` API is
  the one to use (check `#check @ExpChar.exists`). `omega` closes the odd-order
  arithmetic in the pin; keep it if it elaborates.

### 5.5 Stop-early risks

- **The reconciliation edit is the one place V2 can cascade.** It is purely
  additive (two public wrappers over existing privates, no rename) in a file with 0
  library dependents; if the agent finds itself needing to edit any *other*
  existing module, it stops and reports (playbook §3.7: a worker who reaches a
  closed file reports, it does not reopen it).
- **The primed helpers.** If `pushforwardAlongDegZero_pointDivisor'`,
  `pushforwardAlongHom_pointClass'` or `pointMapOfPushforward_eq_of_seam'` differ
  from the port's unprimed names by more than binders, stop and report the two
  statements; do not weaken either.
- **The two headlines' gate instances.** Target 4's proof constructs
  `GenusOnePlaceGate`/`IsCentred`/`AbelTheorem` for both curves from the ported
  `exists_genusOnePlaceGate_isCentred_and_abelTheorem` and supplies
  `HasPrincipalDivisors` from module 3. If the instance resolution for
  `(W.veluQuotient S).toAffine` stalls, use explicit `haveI`/`letI` as the pin does
  and record it in [../../instance-friction.md](../../instance-friction.md)
  (`spec/InstanceFriction.lean`); do not weaken the statement.
- **Statement/`variable` hoisting.** The checker reads the declaration's own text;
  V1's SET-1 had 8/13 wrappers hoist binders into file-level `variable`s while the
  `S_` files inline them. Expect the same here: take each binder from the wrapper,
  use the `S_` file for the body.
- **The `#eval`/numeric zone in the consumer**: if a concrete `ZMod 2`/`ZMod 3`
  curve's `IsElliptic` does not fall to `norm_num`/`decide`, use a hypothesis-form
  zone and record it; do not invent a weaker statement in a library module.

### 5.6 Verification

- `lake env lean` clean per module; `lake build` per module; then one wave build
  over the reconciliation + the five modules (bounded, `flock`ed).
- `python3 spec/check_flt_statements.py` → `0 mismatched / 0 missing`; record the
  `identical` delta. The reconciliation is expected to move it by +2 (the two AC
  promotions) and the four aliases by +4; reconcile the rest against the two
  headlines' public surface.
- `spec/WeierstrassCurveConsumer.lean` exit 0 (extends the existing zones; the file
  was 61 s / exit 0 before).
- `#print axioms` on both headlines and on
  `hasPrincipalDivisors_functionField_of_two_ne_zero_or`:
  `[propext, Classical.choice, Quot.sound]`; no `sorry`.
- `grep -c` of every declaration dropped (the primed trio, the two big AC closure
  members landed as aliases) with the reason, in the friction log.

## 6. Hand-off: what SET-2 inherits from SET-1

**SET-1 landed and passed the manager review on 2026-10-06** (four new modules,
1,134 written lines; checker `5750 → 5796 identical`, 0 mismatched / 0 missing,
promoted 312 → 311; whole-tree build green 9298 jobs / 12.7 s, i.e. **no cascade**;
`spec/IsogenyEndDatumConsumer.lean` 178 lines, exit 0 / 1 m 10 s; `#print axioms`
clean on all seven headlines). The review confirmed: every pin-public name of the
gateway `S_` files landed at its pin name; the only drops are the three pin
`scoped instance instFactNatPrime{2,3,7}_s13e2` (invisible to the checker's
`DECL_RE` and unnecessary — mathlib supplies `Fact (Nat.Prime 2)`), the
pin-`private` primed `Divisor.pushforwardAlong_pushforwardAlong'` (a one-line
instance of the port's public general lemma in `WeilExchange/Transport.lean:141`)
and the pin-`private` `IsogenyEndDatum.comp`.

Fixed by SET-1, so SET-2's order names them instead of re-deriving:

- **`FLTForHuman/WeierstrassCurve/Place/CoordinateRingDedekind.lean`** (83 lines)
  carries `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain` and
  `…exists_eq_XYIdeal` (public, checker-verified). **Target 4's proof uses the
  former three times** — import it, do not redeclare;
- **`FLTForHuman/Elliptic/TorsionCardLight.lean`** (55 lines) carries
  `WeierstrassCurve.card_torsion_of_isAlgClosed_light` and
  `…card_torsionBy_eq_sq_of_isAlgClosed`; SET-1's gateway 2 consumes them, SET-2
  does not need them;
- **`FLTForHuman/WeierstrassCurve/IsogenyEndDatum/PointEndSubring.lean`** (416) and
  **`…/CharPolySquare.lean`** (580) are SET-1's gateways; they import the Engine /
  `DualEndData` cone, which SET-2 must **not** import (the
  `normFormulaAlong_of_elliptic` collision, §2.1). Nothing in SET-2 depends on them;
- the `IsogenyEndDatum` cone (`Engine`, `DualEndData`, `RestrictAlongAdd`,
  `Vocabulary`) is now fully checked at the pin names, so SET-2's
  `normFormulaAlong_of_separableAlong` promotion can rely on the port's names;
- build budget: every SET-1 module is a leaf, so SET-2's first builds start from a
  warm tree. SET-2's cone loads in ≈8.6 s; SET-1's in ≈1 m 37 s. The checker's
  baseline for SET-2 is **5796 identical / 311 promoted / 0 mismatched / 0 missing**.

Written the other way as well: **SET-2 does not port** the `fullKernelHom` column,
the `reduceHom`/reduction column, the `aeval_j_diag` node, or the far-end
modular-polynomial bijection; a worker that needs one stops and reports, and the
manager re-scopes.

The manager writes/amends SET-2's order against the tree that exists at the SET-1
review gate (playbook §3.4), and folds any SET-1 finding into §5 in place, marking
it as an amendment (the V1 precedent).

## 7. Risk register

| risk | mitigation | status |
|---|---|---|
| the 1 m 37 s SET-1 edit-loop floor is paid per declaration | batch blocks per check; never `lake build` in the loop; `tmp/` scratch drivers | measured; SET-1 landed at that cost |
| gateway 1's 26 declarations are more than seam glue | the missing-span table sums to ≈688 lines; scout the smallest identity first (§4.5) | **cleared** — 416 written, no cap problem |
| a "missing" name is present under a different name | the §1.1 sweep; `grep -c`/`#check` before writing; record every drop | **cleared** — `KwIsogenyEndAddDatumSupply` was the one already-present name |
| gateway 2's `dualEndData_disc_neg_of_notBot` duplicates ported math | diff the two statements; if binder-only, port one | **cleared** — landed as its own declaration, 580 lines |
| the RestrictAlong reconciliation cascades | measured 0 library modules / 25 s; the alternative home cascades 52 modules / 405 s | **confirmed** — +39/−0, zero library cascade |
| the promotion's statement text flips a checker match | the pin wrapper is appended to `SOURCES` **after** the existing entries, and the promoted binders are copied from it verbatim | **cleared** — +2 identical, promoted unchanged |
| SET-1's consumer cannot import SET-2's cone | separate spec files (§2.1); the collision is recorded, not fixed | settled — and a **second** collision (`instInfinitePlace`) found in SET-1 |
| target 4's instance walls (`veluQuotient S` gate instances) | explicit `haveI`/`letI` as the pin does; `instance-friction.md` entry | resolved inside the module; the consumer uses hypothesis form only for SET-1's gate (collision) |
| a set wants to extend an existing module | forbidden except the one RestrictAlong reconciliation; extend `spec/` only | held — only `Velu/RestrictAlong.lean` edited beyond `spec/` |
| the checker's one-token probe is left undone | the manager runs it at the milestone | **done** — `5804 / 1 / 0`, reverted |

## 8. Reproduce

```bash
cd tools/deps
python3 frontier.py --selfcheck | tail -1

# the remaining slice after V1 (2026-10-06: 17 nodes)
python3 - <<'PY' > build/velu_nodes3.txt
import frontier, re
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
ds = fr.closure(pay.pid('DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen'))
rx = re.compile(r'[Vv]elu|cyclicQuotient|cyclicKernels|isAddCyclic|IsogenyEnd|IsogenyHom|OddOrderSummingSet|ker_pointMap|veluFieldHom|veluFunctionFieldHom|veluQuotient|velu_map_equation')
print(','.join(pay.qual(i) for i in ds
               if i not in front and pay.qual(i).startswith('WeierstrassCurve.')
               and rx.search(pay.qual(i).split('.', 1)[1])))
PY
python3 port_advise.py --nodes "$(cat build/velu_nodes3.txt)" --json build/velu_advise3.json
python3 port_plan.py --json build/velu_advise3.json --json-out build/velu_plan3.json

# per-node ucl and the unported closure members
python3 - <<'PY'
import frontier
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
for q in open('build/velu_nodes3.txt').read().strip().split(','):
    i = pay.pid(q); un = [n for n in fr.closure(i) if n not in front and n != i]
    print(sum(pay.lines(n) for n in un), pay.lines(i), q)
    for n in sorted(un, key=lambda n: -pay.lines(n))[:8]:
        print('   ', pay.lines(n), pay.qual(n))
PY

# the cascade of the one existing-file edit, and of the alternative homes
python3 build_ladder.py --edit FLTForHuman/WeierstrassCurve/Velu/RestrictAlong.lean
python3 build_ladder.py --edit FLTForHuman/AlgebraicCurve/PrincipalDivisors/Transcendence.lean
```

The name sweep of §1.1 is a declaration-name extraction per pin `S_` file followed
by `grep -rqw <name> --include=*.lean lean/FLTForHuman`.

The 2026-10-06 run is in `tools/deps/build/velu_{nodes3.txt,advise3.json,plan3.txt,plan3.json}`
(untracked, like the toolchain). Re-pin before re-measuring.

## 9. Close-out

**Landed and verified 2026-10-06**, two sets run in series with a manager review
between them. Nine new modules and one additive reconciliation; **no library module
with dependents was edited**, so no set cascaded and the only whole-tree builds were
the two milestone gates.

| set | modules (lines) | spec | `lake build` (wave) | checker |
|---|---|---:|---:|---|
| SET-1 | `Place/CoordinateRingDedekind` 83, `Elliptic/TorsionCardLight` 55, `IsogenyEndDatum/PointEndSubring` 416, `IsogenyEndDatum/CharPolySquare` 580 | consumer 178 (new) | green | +46 |
| SET-2 | `FieldTheory/SeparableOfCoprime` 54, `AC/PrincipalDivisors/SeparableRatFunc` 46, `WeierstrassCurve/PrincipalDivisorsSeparable` 181, `Isogeny/PointMapSurjective` 56, `Velu/PointMapOddOrder` 200, `Velu/RestrictAlong` +39/−0 | consumer +166 | green | +9 |

**Milestone.** Checker `5750 → 5805 identical` (SET-1 +46, SET-2 +9; promoted
`312 → 311`; the SET-1 `promoted → ok` flip of
`IsogenyEndDatum.pointEnd_eq_geomMorph_sub_geomMorph_zero` contributes nothing to
`identical`, since `promoted` is a subset of it), `0 mismatched / 0 missing`,
36 own-proof exempted, 5,841 port declarations checked. Whole-tree `lake build`
green: **9,303 jobs / 12.3 s** against the pre-V2 9,294 / 13.6 s — exactly +9 jobs,
i.e. the nine new leaves and **zero cascade**. Consumer `spec/IsogenyEndDatumConsumer.lean`
exit 0 (71 s) and `spec/WeierstrassCurveConsumer.lean` exit 0 (63 s). `#print axioms`
on all eleven V2 headlines is `[propext, Classical.choice, Quot.sound]`; no `sorry`.
The checker's one-token mutation probe was run by the manager on
`CoordinateRingDedekind.exists_eq_XYIdeal` (`P ≠ ⊥` → `P ≠ ⊤`): exactly
`5804 identical / 1 mismatched / 0 missing`, reverted to `5805 / 0 / 0`.

Measured against the plan's ≈2–3 k: **1,671 written** in library modules
(1,134 + 537) plus 344 consumer lines and the 39-line additive reconciliation.

**The four findings that outlived the wave.**

1. **`ucl` overstates, and it is the *port's* names it cannot see.** Three of V2's
   closure members whose `ucl` read 1,246 / 911 / 58 lines were already in the port
   under other names (`Divisor.pushforwardNormFormula` minus `[CharZero F]`,
   `hasPrincipalDivisors_of_finiteDimensional_of_isSeparable` with different binder
   spelling, `pointMapOfPushforward_surjective_of_separableAlong'`), and the shared
   "269-line" coordinate-ring pair cost ≈15 lines. The plan's ≈1.6 k estimate was
   right; a `ucl`-only budget would have been ≈4 k. **Sweep the port by name and by
   statement before pricing any closure member.**
2. **Co-import collisions are a class, and the node graph cannot see them.** Three
   pairs of library modules cannot be imported into one environment
   (`normFormulaAlong_of_elliptic` in `Engine`/`RestrictAlong`; `instInfinitePlace`
   in `Engine`/`Place/RRSpace`), none of which shows up in any tool. They cost the
   consumers real tests (SET-1's zone 3 states the gate instances as hypotheses; the
   two efforts' consumers had to live in separate spec files). Registered in
   [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md); the fix is a refactor round.
3. **The reconciliation belongs in the file with no dependents.** The same
   promotion costs **39 lines / 0 library modules / ≈25 s** in
   `Velu/RestrictAlong.lean` and **≈405 s** (52-module cascade) in
   `Transcendence.lean`. `tools/deps/build_ladder.py --edit <file>` answered that
   before a line was written; it should be run for every candidate home.
4. **A definitions file's *imports* are its source list; the checker's regex is not.**
   V1's finding recurs in a new form: the pin's three `scoped instance
   instFactNatPrime{2,3,7}` are invisible to the checker's `DECL_RE` (140 vs 144
   declarations in the gateway `S_` file), and `isIntegral_comp_ι` was nearly
   mis-swept because a name-extraction regex without Greek letters truncates it.
   A name sweep is an aid, not an authority; the checker's own `raw_declarations` is.

**Deviations from the plan, all recorded.** V2 skipped the definition layer entirely
(nothing to port, §1.2) — the plan's "≈700 written" definition estimate was V1's.
SET-1's consumer is a **new** spec file (the collision), and SET-1's gateway-1 module
imports `Vocabulary.lean` beyond the order's list because the pin's `solution` calls
`IsogenyEndDatum.exists_pointEnd_eq_add`. SET-2's `SOURCES` gained **9** wrappers,
not the order's "eight" (7 prerequisites + 2 headlines); `PrincipalDivisorsSeparable`
keeps its own private copy of `two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero`
rather than importing `RestrictAlong` (the DAG forbids it).

**Refactor items carried forward** (files frozen this wave):
`Velu/RestrictAlong.lean` and `IsogenyEndDatum/Engine.lean` each carry a public
`normFormulaAlong_of_elliptic`, and `Place/RRSpace.lean`'s `scoped instance
instInfinitePlace` collides with `Engine.lean`'s plain one; keep one of each so the
cones can meet. `PrincipalDivisors/Transcendence.lean` still carries a second private
char-free norm formula beside the now-public home in `Velu/RestrictAlong.lean`.
