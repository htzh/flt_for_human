# SET MC-4 — M6 + M5: the period lattice's Hecke-diamond stability, and the Galois action on the Hecke operators

**Status: scoped and landed (2026-10-27); all six rows are green.** The definition gate came from
the MC definition wave; the manager's lane is the two legacy migrations and one 27-line row; the
other five rows are four worker orders. Measured: **84 checked declarations `ok`, 0 mismatch, 0
missing, 1 pre-existing `own`** across the six modules, axioms clean, zero warnings, 0 dedup
clusters, and a five-zone consumer at 0 errors. `needed` moved by exactly the six rows (§7). This is the `ModularCurve` ready shelf's **MC-4**
([TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §1), the fourth of the seven orders and the first of
the gated ones: story **M6** (the period lattice) and story **M5** (the Galois action on the Hecke
operators). It follows the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) and the
definition wave that unblocked it
([WORKORDER-MCDEF-definition-wave.md](WORKORDER-MCDEF-definition-wave.md), modules D1–D4).

The shelf priced MC-4 as 6 rows / 1,405 silo / ≈1,670 net with a **438-line** definition gate
(`PeriodOf` 21 + `HeckeOpForms` 158 + `X1HeckeModule` 203 + `XHOperators` 56). Two corrections are
this brief's first findings:

1. **the gate is landed and was 335 pin lines, not 438**: `PeriodOf`'s 21 lines are **not** a gate
   for either M6 row (the port's `EichlerShimura/PeriodOf.lean` already names everything the two
   rows use — the declaration-level audit of the def wave, §0.1 there), and `CuspForm_Gamma1HeckeOperators`'s
   32 lines were already ported (MC-7's finding);
2. **one `X₁` row is the manager's**: `heckeOperatorOneBar_comm_diamondOneBar` is 15 net lines and
   its home `X1/DiamondLift.lean` had to migrate off `PORT_FILES` anyway, so the manager landed
   both in one touch (§2). Four worker orders remain.

| figure | value |
|---|---:|
| MC-4 rows | 6 / 1,405 silo |
| net new math lines (six rows, per-row `port_advise`) | **≈1,161** |
| definition gate landed (D1–D4 of the def wave) | 4 modules, 60 declarations |
| manager lane | **2 legacy migrations** (`X1/DiamondLift.lean`, `XH/DiamondLift.lean`) + **1 row** (17 ok / 0 / 0) |
| worker orders | **4** (a 464, b 350, c 272, d 265+27) |
| homes | 2 existing insertions (`Period/…`), 2 insertions into the wave's own def modules, 1 migrated legacy |

## 0. The six rows

Read from the corrected shelf (2026-10-27, after the def wave; `needed` **1,004 / 398,972**, MC
ready **15 / 4,163**, `--selfcheck` **PASS**) — the six rows are the MC-4 block of that shelf:

| story | row (`ModularCurve.` dropped) | silo | prem | home | order |
|---|---|---|---:|---|---|
| M6 | `periodLatticeOf_gammaH_heckeDiamondStable` | 464 | 5 | `Period/HeckeStability.lean` (insert) | **MC-4a** |
| M6 | `exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup` | 350 | 6 | `Period/PeriodLatticeBasis.lean` (insert) | **MC-4b** |
| M5 | `JOne.galois_smul_heckeAlgOne_smul` | 272 | 1 | `X1/HeckeModule.lean` (insert — the def home) | **MC-4c** |
| M5 | `galois_smul_genOpH_comm` | 265 | 1 | `XH/Operators.lean` (insert — the def home) | **MC-4d** |
| M5 | `heckeOperatorHAlong_diamondHBar_comm` | 27 | 2 | `XH/DiamondLift.lean` (migrated legacy) | **MC-4d** |
| M5 | `heckeOperatorOneBar_comm_diamondOneBar` | 27 | 2 | `X1/DiamondLift.lean` (migrated legacy) | **landed** (§2) |

All six are `needed = 1`, `premises_pruned = 0`, `leaf = false`; **no row cites another row of the
set**, so the orders are independent. The MC block's leaves (32 rows / 6,797) are the shelf's second
programme and are not cut here.

### 0.1 The premises, verified in the port

Every premise of every row is ported — checked by name (`tools/`-free `grep`/declaration index) on
this tree, since the frontier's readiness is the claim being trusted:

| premise (`Thm_` wrapper) | port module |
|---|---|
| `ModularForm.heckeU_slash_eq_self_of_mem_GammaH`, `…heckeU_add_slash_slash_eq_self_of_mem_GammaH` | `ModularForms/HeckeInvariance.lean` |
| `CuspForm.stableT` / `stableU` / `stableD` | `ModularCurve/Period/HeckeStability.lean` |
| `exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup` | `Period/PeriodLatticeBasis.lean` |
| `finrank_parabolicHoms_le_two_mul_finrank_cuspForm_…`, `Period.exists_basis_parabolicHoms_of_isAddTorsionFree` | `Period/ParabolicHomsBasis.lean` |
| `ModularCurve.periodMapOf_mem_parabolicHoms` | `Period/ParabolicHoms.lean` |
| `periodMapOf_apply_eq_periodOf` | `ModularForms/EichlerShimura/ExistsEquivariantPrimitive.lean` |
| `CuspForm.finiteDimensional_of_isArithmetic` | `ModularForms/WeightOne/Basic.lean` |
| `AlgebraicCurve.SemilinearAut.pic0_correspondence_smul` (SET 7's AC row) | `AlgebraicCurve/WeilExchange/GaloisRamification.lean` |
| `exists_algEquiv_intertwinesAlong_diamondAutBar` | `ModularCurve/X1/DiamondLift.lean` |
| `exists_algEquiv_intertwinesAlong_diamondAutHBar` | `ModularCurve/XH/DiamondLift.lean` |

**The four "gates" of the definition wave are all in place**: D1's `CuspForm.{diamondLinH,heckeULinH,heckeTLinH}`
(464), D2's `HeckeAlgOne` + `heckeModuleOneBar` (272), D3's `diamondHBar`/`genOpH` (265 and the
27-line XH row), D4's `CohCarrier.Gen` (265's statement). No other definition is missing.

### 0.2 The manager's lane

- **The definition gate**: landed by the MC definition wave (D1–D4), 121 checked declarations
  `ok`. This brief does not re-price it; it *corrects* its MC-4 share: `PeriodOf`'s petersson block
  is not needed by either M6 row (§0.2 of the def wave), and `CuspForm_Gamma1HeckeOperators`'s 32
  lines are the H2 pair (FR-0052).
- **No promotion is needed.** No declaration of the four gated modules is `private` where a row
  needs it public: the rows' statements name only public surface.
- **Two legacy migrations: `X1/DiamondLift.lean` and `XH/DiamondLift.lean`.** Its home for MC-4e is demanded by the subject
  (the diamond lift is the row's engine) and it was on `PORT_FILES`. Per recipe §4 the wave pays the
  migration in the same touch: it now carries a four-line `spec-pin:` wire (its own `Thm_` wrapper
  and comparable `S_` copy, plus MC-4e's pair) and **`check_port` owns it: 17 ok / 0 mismatch / 0
  missing**. Its `PORT_FILES` row is replaced by a `MIGRATED` comment; its `SOURCES` rows stay.
  The second is forced by the import direction (§2.1): MC-4d's 27-line `XH` row consumes the diamond
  lift, and the port's `XH/DiamondLift.lean` *imports* `XH/Operators.lean` — so the row cannot live
  in `Operators`, and its home is the lift module, migrated here rather than by the worker
  (**16 ok / 0 mismatch / 0 missing** on the untouched module; the row adds two `spec-pin:` lines).
- **One row landed here**: `heckeOperatorOneBar_comm_diamondOneBar` (15 net lines, the `X₁` twin of
  MC-4d's 27-line `XH` row) — its proof is the pin's twelve lines over
  `SemilinearAut.pic0_correspondence_smul` and `exists_algEquiv_intertwinesAlong_diamondAutBar`, and
  it is the cheapest proof that the wave's new definitions `heckeOperatorOneBar` (D2's module home)
  and `diamondOneBar` compose. Checker: **17 ok / 0 / 0**.

### 0.3 The pricing, per row

`port_advise` per row (`port_plan`'s net = declaration lines − duplicates − boilerplate − already
in the port):

| order | row | raw `S_` | decl lines | boilerplate | in port | **net** |
|---|---|---:|---:|---:|---:|---:|
| MC-4a | 464 | 464 | 440 | 24 | 0 | **416** |
| MC-4b | 350 | 350 | 318 | 32 | 0 | **286** |
| MC-4c | 272 | 272 | 254 | 18 | 16 | **220** |
| MC-4d | 265 | 265 | 245 | 20 | 16 | **209** |
| MC-4d | 27 (XH) | 27 | 15 | 12 | 0 | **15** |
| — | 27 (X₁) | 27 | 15 | 12 | 0 | **15** (landed) |
| | **total** | **1,405** | | | | **≈1,161** |

The 272/265 rows' 16 "already in port" lines are the pin preludes the def wave and earlier sets
landed (`heckeOperatorOneBar_apply`, `heckeDiamondGenBar*`, `HeckeInputsOneBar*`); `port_advise`'s
`1 suspect` substitution on each is the parser's type-only `def` match and needs the hand read the
worker does anyway.

## 1. What each row is

**464 — `periodLatticeOf_gammaH_heckeDiamondStable`.** Three conjuncts: the `ℤ`-lattice
`periodLatticeOf (GammaH M H)` is stable under the `dualMap` of `heckeTLinH 2 hℓ hℓM`, of
`heckeULinH 2 q` (`q ∣ M`), and of `diamondLinH 2 d`. The pin (`S_…_periodLatticeOf_gammaH_heckeDiamondStable`)
is 464 lines: a `PeriodLatticeHStableProof` engine (primitive/derivative lemmas, the
`periodAlongOf`-vs-`periodOf` dictionary, the slash-invariance of the period) plus three short
assemblies. The three headlines it consumes are `CuspForm.stableT/U/D` (this module's own), so the
home `Period/HeckeStability.lean` is above all of them and is the module that discharges the
stability hypotheses.

**350 — `exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup`.**
One `∃`: a `ℤ`-linear equivalence `parabolicHoms ℤ Γ ℤ ≃ Module.Dual ℤ (periodLatticeOf Γ)` whose
value on `periodOf Γ δ` is `ψ (ofMul δ)` — the period lattice is the `ℤ`-dual of the parabolic
homs, i.e. the Eichler–Shimura period pairing is perfect. The pin's `main` is `CpairK2Of`'s
assembly over its six premises; the port's premise modules are all `Period/…` and the row's home is
the basis module.

**272 — `JOne.galois_smul_heckeAlgOne_smul`.** With `letI := heckeModuleOneBar M`, a Galois element
`σ` commutes with every `t : HeckeAlgOne` acting on `J₁(M)`: `σ • (t • x) = t • (σ • x)`. The pin
proves it by reducing `t` (`MvPolynomial.induction_on`), using `heckeModuleOneBar_smul_def`, then
the X₁ Hecke/diamond commutations (`heckeOperatorOneBar_apply`, `diamondOneBar_apply`) through
`pic0_correspondence_smul`. **Instance-sensitive**: the statement is a `letI`, so transcribe the
`letI` shape and follow `heckeModuleOneBar_smul_def` / `_smul_of_not`.

**265 — `galois_smul_genOpH_comm`.** `σ • (genOpH M H S g P) = genOpH M H S g (σ • P)`: the
`X_H` generator operator commutes with the Galois action, by cases on `g : CohCarrier.Gen M S`
(`T`/`U` via `heckeOperatorHAlong`, `dia` via `diamondHBar`).

**27 (XH) — `heckeOperatorHAlong_diamondHBar_comm`.** `heckeOperatorHAlong` commutes with
`diamondHBar`, through `exists_algEquiv_intertwinesAlong_diamondAutHBar` and
`pic0_correspondence_smul`; the `¬ HeckeInputsHAlong` case is `simp`.

**27 (X₁) — landed (§0.2).**

## 2. Homes, and the import direction

| order | home | above every premise? | why |
|---|---|---|---|
| a | `Period/HeckeStability.lean` (insert) | yes — it is the module of `CuspForm.stableT/U/D` and imports `HeckeInvariance` | the subject *is* the stability of the period lattice; no module is above the three stability theorems and the period API |
| b | `Period/PeriodLatticeBasis.lean` (insert) | yes — it hosts the basis theorem and imports the other five premises' modules | the period/parabolic-homs dictionary |
| c | `X1/HeckeModule.lean` (insert) | yes — the def home; its own `heckeModuleOneBar` is the statement's instance | the row is *about* the `HeckeAlgOne`-module it defines |
| d | `XH/Operators.lean` (insert, 265) **and** `XH/DiamondLift.lean` (insert, 27; migrated) | 265: yes — the def home (`genOpH`, `diamondHBar`), imports `XH/HeckeOperator`. 27: no for Operators (§2.1) — its home is the lift module, which imports Operators and therefore sits above both | the `X_H` operator vocabulary; the commutation consumes the lift |
| e | `X1/DiamondLift.lean` (migrated) | yes — it hosts the diamond lift and now imports `X1/HeckeModule` | the row is the lift's corollary |

### 2.1 The one import-direction correction

The 27-line `XH` row consumes `exists_algEquiv_intertwinesAlong_diamondAutHBar`, and in this port that
declaration lives in `XH/DiamondLift.lean`, which **imports** `XH/Operators.lean` (the pin has both
in one `Def_` module, so the pin never faces the question). Putting the row in `Operators` would be
the cycle `Operators → DiamondLift → Operators`; the row's home is therefore the **lift** module, the
exact analogue of MC-4e's X₁ row. This is the recipe's FR-0037/0038 failure mode caught by the
worker before writing — the acyclicity table above was wrong for that row and is corrected here
(FR-0059).

All the other homes were checked for acyclic import edges (`X1/HeckeModule` imports `X1/HeckeOperator`
and `X1/Diamond` only; `XH/Operators` imports `XH/HeckeOperator`, `ModularForms/CohCarrier/Inst`,
`Defs/Laurent`, `WeightOne/Gamma0Integral`). **The four worker orders touch disjoint files**, so
they run concurrently (only the build lock is shared).

## 3. The four orders

| order | row | home | silo | net | workorder |
|---|---|---|---:|---:|---|
| **MC-4a** | 464 | `Period/HeckeStability.lean` | 464 | 416 | [WORKORDER-MC4a-period-lattice-stability.md](WORKORDER-MC4a-period-lattice-stability.md) |
| **MC-4b** | 350 | `Period/PeriodLatticeBasis.lean` | 350 | 286 | [WORKORDER-MC4b-period-dual-equivalence.md](WORKORDER-MC4b-period-dual-equivalence.md) |
| **MC-4c** | 272 | `X1/HeckeModule.lean` | 272 | 220 | [WORKORDER-MC4c-galois-hecke-module.md](WORKORDER-MC4c-galois-hecke-module.md) |
| **MC-4d** | 265 + 27 | `XH/Operators.lean` + `XH/DiamondLift.lean` | 292 | 224 | [WORKORDER-MC4d-genop-galois-comm.md](WORKORDER-MC4d-genop-galois-comm.md) |

## 4. Traps, per order

**MC-4a.** (i) The pin's `PeriodLatticeHStableProof` engine defines `IsPrimitive` and its
`add`/`sum` lemmas locally; the port has no `IsPrimitive` (it is scaffolding, `private` at most).
(ii) `clamp01`, `clamp01_of_mem`, `segmentPoint`, `segmentPath`, `continuous_segmentPath`,
`periodAlong` are ported in `ModularForms/EichlerShimura/PeriodIntegral.lean` — import, do not
restate (this is the `port_advise` "already in port" 0 the tool reports because it is
name-anchored; check by hand). (iii) The pin's `p2m_export`/`p2m_open` lines are P2M scaffolding,
not Lean. (iv) The three `Stable*` theorems the row consumes are this module's own; do not re-prove
them.

**MC-4b.** (i) The pin's `CpairK2Of` engine is substantial; its `main` is the assembly. (ii) The
statement is the pin's `∃ EV …` and must be transcribed as written, including the
`⟨periodOf Γ δ, periodOf_mem_periodLatticeOf Γ δ⟩` subtype term. (iii) The `attribute [-instance]`/
`[-simp]` preludes of the pin's wrapper and `S_` file are **not** reproduced (the port keeps those
global; see `ModularForms/CohCarrier/CommTriplet.lean`'s header). (iv) `haveI : Γ.FiniteIndex :=
hΓ.finiteIndex` is how the pin starts — the port's `IsCongruenceSubgroup` API may need
`CongruenceSubgroup.IsCongruenceSubgroup.finiteIndex`.

**MC-4c.** (i) `heckeModuleOneBar` is an `@[implicit_reducible]` `Module` instance behind
`Classical.dec` and `if h : HeckeDiamondCommuteBar M`; the statement's `letI := heckeModuleOneBar M`
means the elaboration must respect the instance, so transcribe with the pin's `letI` and use
`heckeModuleOneBar_smul_def` (not `rfl`). (ii) The pin's engine has `coeffMap_qExpand_comm`,
`intertwines_alpha`/`intertwines_beta` and the `JOne`-level `galois_smul_*` blocks — the last is the
row; keep the engine `private` unless the wire calls it public. (iii) `omit [NeZero ℓ] in` appears
in the pin's engine; keep it where the pin has it (it is not a suppression).

**MC-4d.** (i) `heckeOperatorHAlong` has `_eq`/`_of_not`; the `¬ HeckeInputsHAlong` branch is
`simp` with `heckeOperatorHAlong_of_not`. (ii) `diamondHBar_apply` unfolds to
`SemilinearAut.ofAlgAut … • x`; the interchange with `heckeOperatorHAlong` is
`pic0_correspondence_smul` at the `heckeBetaHBar`/`heckeAlphaHBar` pair (the pin's order: beta
first). (iii) The 265 row is by cases on `CohCarrier.Gen`; `genOpH_T`/`_U`/`_dia` are the
`rfl`-lemmas that discharge each case. (iv) `NeZero ℓ` is supplied by `Fact ℓ.Prime` in the
statement — do not re-derive.

## 5. Gates, per order

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; every added public
   declaration `ok` (private helpers are exempt and stay private). No `spec/decl_markers.tsv` row
   from a worker.
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake build` under `flock`/`timeout`; silent at the project cap; **no**
   `set_option maxHeartbeats` and no linter suppression added by the order (the two legacy modules
   `X1/DiamondLift.lean` and, to a lesser degree, `Period/HeckeStability.lean` carry pre-existing
   options — do not extend them, and report if a new declaration needs one);
4. `dedup.py --within --tier shape` on the module: 0 clusters, or the cluster recorded as the
   pin's own wrapper-over-engine shape;
5. the module's `spec-pin:` block gains exactly its own `Thm_` wrapper and `S_` copy;
6. the worker appends nothing to `logs/frictions.md` directly — frictions come back in the report
   and the manager records them.

### 5.1 What the workers found (recorded, all fixed in-wave)

Four brief defects surfaced while the orders ran; each is the kind of thing the next brief of this
column must carry:

1. **The import-direction inversion** (§2.1, FR-0059) — the 27-line `XH` row cannot live in
   `XH/Operators.lean`, whose subject it is, because `XH/DiamondLift` imports `Operators`. The
   rule: when the pin's `Def_` module is split, the row's home is the *highest* of the split
   modules, whatever the subject says.
2. **`Period/HeckeStability.lean` did not reach the period API.** MC-4a's brief claimed the period
   dictionary was already in the home module's closure; it was not, and the order added
   `import FLTForHuman.ModularForms.EichlerShimura.PeriodOf` in the same touch. A brief's closure
   claim is a first cut (recipe §4) and must be checked with `grep '^import'` on the home, not
   assumed from the premise list.
3. **The `check_port` per-row delta is +1, not +2.** One ported declaration satisfies a
   `Thm_`-wrapper/`S_`-copy pair (their statements are textually identical), so a module's row
   count grows by one per pin headline, not per wired source. Only the manager's forecast is
   affected.
4. **`linter.style.haveILetI` and the pin's literal `haveI`.** Where the port's proof needs to
   introduce an instance that the pin introduces with the `haveI` tactic, the term-mode
   `exact haveI : … := …` is the unsuppressed spelling (MC-4c used it; `X1/DiamondLift.lean`
   instead carries the pre-existing option). New declarations must not add the option.

**The consumer zone for the set** (`spec/ModularCurveMC4Consumer.lean`, manager-written): the three
stability conjuncts of 464 composed with `periodOf_mem_periodLatticeOf` and `Submodule.span`; the
350 equivalence applied to `periodOf` and composed with `periodMapOf_apply_eq_periodOf`; the 272
statement specialised to `t = heckeGenOne ℓ` and `t = diamondGen d` through
`heckeModuleOneBar_heckeGenOne_smul`/`_diamondGen_smul`; and the 265/27 commutations composed with
`genOpH_dia`/`genOpH_T`. Its error count is the deliverable metric.

## 6. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc4.json
python3 frontier.py --selfcheck
for row in periodLatticeOf_gammaH_heckeDiamondStable \
  exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup \
  JOne.galois_smul_heckeAlgOne_smul galois_smul_genOpH_comm \
  heckeOperatorHAlong_diamondHBar_comm heckeOperatorOneBar_comm_diamondOneBar; do
  python3 port_advise.py --nodes ModularCurve.$row --json build/mc4-$row.json
  python3 port_plan.py --json build/mc4-$row.json
done
cd ../lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/DiamondLift.lean
```

## 7. What this set does not do

- **The MC block's leaves (32 / 6,797)** and the leaves programme's definition gates
  (`PeriodHomPair`, `Pic0Congr`, `ComplexPlaceDictionaryOf`, `X0ModL`) — the shelf's second
  programme; the leaves' `periodAlongOf_eq_neg_conj_…` and `periodAlongOf`-adjacent rows are the
  natural companions of MC-4a/4b but are not cut here.
- **`PeriodOf`'s petersson block** and the pin's `Def_CuspForm_Petersson` — deferred by the def wave
  (§0.2 there) and not needed by MC-4; they come back with the `L-other` leaves.
- **`ModularCurve_XH`'s Jacobian block** (`torsionGaloisRep` and the Tate pair) — the M9 successors'
  surface, deferred with `TateModule`.
- **No tree build, no promotion.** The wave's only surface beyond the rows is the `X1/DiamondLift`
  migration.

## 7. The landing — measured (2026-10-27, all six rows in)

| figure | before | after | delta |
|---|---:|---:|---:|
| instrument `needed` | 1,004 / 398,972 | **998 / 397,567** | **−6 / −1,405** |
| ready, all namespaces | 75 / 15,689 | **70 / 14,308** | −5 / −1,381 |
| `ModularCurve` ready shelf | 15 / 4,163 | **10 / 2,782** | −5 / −1,381 |
| `ModularCurve` leaves | 32 / 6,797 | 32 / 6,797 | 0 |
| leaves, all namespaces | 294 / 71,671 | 294 / 71,671 | 0 |
| frontier F | 1,408 / 727,998 | **1,415 / 729,584** | +7 / +1,586 |
| `--selfcheck` | PASS | **PASS** | — |

The −6 / −1,405 is exactly the six rows (`464 + 350 + 272 + 265 + 27 + 27 = 1,405`); the frontier
gained the same six nodes plus one further pin declaration the wave's engines made ported (the
+1 / +181 that separates +1,586 from +1,405). **The ready shelf lost five rows and gained one**:
`ModularCurve.rep_tateModule_jOne_comm` (24) entered.

**That entry is a false ready, and the next brief must exclude it.** Its statement is
`TateModule.rep p (JOne M) …` composed twice — it names `TateModule`/`TateModule.rep` from the pin's
`Def_EllipticCurve_TateModule` (69 declarations, absent from the port) and, through the same file,
D2's deferred `rationalHeckeRepOne`/`RationalTateModule`. It reads `needed = 1` because its *graph
premises* are ported (one of them MC-4c's `JOne.galois_smul_heckeAlgOne_smul`); its *vocabulary* is
not, so it cannot be written. It is the padic-Tate-module topic's row
([TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md) T1/T2) and the withheld pair's
neighbourhood — the same FR-0049 shape the recipe §0 warns about, caught here by the def-wave
audit rather than by `--ready`.

The set's own deliverables: **four new row modules' worth of proof** —
`Period/HeckeStability.lean` 90 → 576 (27 private engine declarations + the headline),
`Period/PeriodLatticeBasis.lean` 374 → 715 (21 private engine declarations + the headline),
`X1/HeckeModule.lean` 226 → 499 (14 private engine declarations + the headline),
`XH/Operators.lean` 161 → 259 (11 private engine declarations + the headline),
`XH/DiamondLift.lean` 386 → 411 (the 27-line commutation),
`X1/DiamondLift.lean` 389 → 411 (the 27-line commutation, the manager's) — **six modules edited, no
new module**, 2 legacy migrations paid, no promotion, no `set_option` added anywhere, no
`spec/decl_markers.tsv` row written (the one `own` row in `PeriodLatticeBasis` pre-dates the set).

Consumer zone: `spec/ModularCurveMC4Consumer.lean` (five zones: `stable`, `dual`, `module`, `genop`,
`comm`) — **0 errors**.

**What the next pass reads.** The MC ready shelf is 10 / 2,782: the MC-5 block (403, 390, 224, 220),
the MC-6 block (384, 322), the three first-wave successors (611, 168, 36) and the false ready (24).
MC-5 opens on 403/390/224/220 — and the 24 row is excluded with the reason above.
