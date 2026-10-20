# The D-S cone's leaf families — wave 1 (the nine pairs), landed

**Status: phase 1 closed 2026-10-20.** Three coding groups, **18 new modules, 6,291 port lines,
323 statement-checked declarations**, no existing module edited, nothing promoted, nothing registered.
Checker **2111 → 2434 ok** (+323, exactly the wired count), 0 mismatched / 0 missing, 4 own, **78
modules**; axioms `[propext, Classical.choice, Quot.sound]`; 0 warnings in every module. **28 of the
31 priced nodes landed** (+ the bonus `theta_mul`); the `ZLattice` pair (3 nodes / 1,321 pin lines) is deferred with its drafts
parked and its two hotspots diagnosed (see §5). Order and scope:
[topics/deligneSerre/WORKORDER-MG3-ds-leaf-families.md](../topics/deligneSerre/WORKORDER-MG3-ds-leaf-families.md);
pricing: [topics/deligneSerre/TOPIC-ds-leaf-families.md](../topics/deligneSerre/TOPIC-ds-leaf-families.md) §7.

Build-time issues left open by this wave — the owed `ResidueSumQExpansion` shape rework,
the parked `ZLattice` draft, the tree's olean gaps and the lock/memory rules — are in
[build-time-issues.md](build-time-issues.md).

## 1. What landed

| group | modules | port lines | wired | pin lines (nodes) |
|---|---|---:|---:|---:|
| **A** — `Polynomial`, `Int`, `IsAlgClosed`, `GaussProlongation` (+ the two gate modules) | 7 | 2,071 | 76 | 1,403 (11) + 211 gate |
| **B** — `EisensteinSeries`, `ZMod`; `AddCommGroup`+`CohCarrier` | 5 | 2,202 | 153 | 1,590 (7 of 10) |
| **C** — `HeckeCharacter`; `omegaRow_T2` (+ `theta_mul`) | 6 | 2,018 | 94 | 1,798 (11) |
| **total** | **18** | **6,291** | **323** | 5,002 + 359 gate |

Group A: `AlgebraicCurve/{ConstantReduction 192/14, RegularProlongation 136/7, GaussProlongation 369/10}`,
`FieldTheory/TranscendentalAdjoin 303/3`, `NumberTheory/{SquarefreeValues 406/9, UnimodularLift 140/5,
ValuationSubring/ChevalleyExtension 525/28}`.
Group B: `NumberTheory/ZModPowerTsum 143/7`, `ModularForms/Eisenstein/{ConstTermCubeIntegral 254/6,
ResidueSumQExpansion 319/1}`, `Algebra/TorsionByCoordinates 715/41`,
`ModularForms/CohCarrier/TorsionOrbit 771/98`.
Group C: `HeckeCharacter/{FiniteOrder 58/3, Equality 754/7}`, `ModularForms/QCoeffLevelOne 459/28`,
`ModularCurve/{Defs/OmegaOf 125/4, Period/ThetaMul 70/1, OmegaRowT2 553/51}`.

## 2. The definition gates

Five were owed; **four were homed whole and verbatim, one is deferred**:

| pin gate | pin lines | port | verdict |
|---|---:|---|---|
| `Def_AlgebraicCurve_ConstantReduction` | 127 | 192 lines, 14 public | 14 ok |
| `Def_AlgebraicCurve_RegularProlongation` (with the 3-decl `toRegularProlongation` bridge) | 84 | 136, 7 | 7 ok |
| `Def_HeckeCharacter_FiniteOrder` | 30 | 58, 3 | 3 ok |
| `Def_ModularCurve_OmegaOf` | 94 | 125, 4 | 4 ok |
| `Def_ModularCurve_EigenformIdeal` | 24 | — | **deferred** (its three declarations are defined via `eigenIdeal`/`EigenformSupport`/`EichlerShimuraDataReduced` of the port-blocked `Def_HeckeGalois_EichlerShimura`; `omegaRow_T2` references none of them) |

`ConstantReduction` was added to the gate at the group's finding and the manager's decision: it is a pin
**hub** (1,944 importers) and the `toRegularProlongation` bridge is named in a dozen `Theorems/`
wrappers' `attribute [-simp]` preludes, so omitting either would have left the gate incomplete in the
§4(a) sense. Gate consumption is honest and recorded: the `GaussProlongation` pair uses only the
`RegularProlongation` structure and `smul_const_ne_zero`; `ConstantReduction` is consumed by the bridge
alone; `IsFiniteOrderHeckeChar` and `omegaOf` are homed-and-diffed but unconsumed by the proofs landed
here.

## 3. One extra landing, and two deferred items

* **`ModularCurve.theta_mul`** (185 pin lines, its own `Theorems/` wrapper, outside the D-S cone) was the
  one declaration `omegaRow_T2`'s proof lacked; it landed as `ModularCurve/Period/ThetaMul.lean`
  (70 lines, 1 wired). Its only ingredient, `theta_coeff`, was already public in
  `ModularCurve/Period/QExpansionDerivative.lean`; its pin imports are unused by the proof and were not
  carried.
* **`ZLattice` pair deferred** (§5). **`Def_ModularCurve_EigenformIdeal` deferred** (CARRY-FORWARD).

## 4. Heartbeats: the cap is a diagnostic, not the build budget

`EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow` needs **300k–400k**
hearts (bisected: 300k fails in `h6`, 400k passes; the pin sets 4,000,000). The diagnosis is arithmetic
defeq, not instance synthesis: `Add.add` 304,515 unfoldings, `HAdd.hAdd` 266,601, `HMul.hMul` 208,538,
`Nat.rec` 193,653, and no class-instance counter of note. The library builds at the lakefile's
`maxHeartbeats 4000000` (tier-1 3,764 jobs / 31 s), so the module is green; **no `set_option` was added**,
and the pin's bump, the bisection and the diagnosis are in the module header. The one cut taken inside
the 40-minute rework box (0 minutes used) was factoring the `sigmaAntidiagonalEquivProd` summability out
of `h6`/`hfin` into one `have hsigma`, which moved the file from *failing at 400k* to *passing*.
**The rework is still owed** — recorded in the module header and below.

## 5. The deferred `ZLattice` pair, and what was learned

`SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace` (563) + the two `ZLattice` nodes (229 + 221) were
drafted (614 + 293 port lines, sorry-free) and parked at `lean/tmp/mg3-zlattice-drafts/`; they are not in
the library because the `SchwartzMap` module could not be elaborated inside 2 minutes — measured at
**~110 % CPU, over 4 minutes**, against the column's ~120 s defect band. What the group did establish,
and what the next order must start from:

* the hotspot `periodizeLiftFun`: `Function.surjInv toUnitAddTorus_surjective z` spends minutes inferring
  `surjInv`'s implicit function argument from a *proof term*; pinning `(f := toUnitAddTorus)` on the four
  `Function.surjInv` and the one `Function.surjInv_eq` makes the prefix elaborate in seconds (minimal
  proof kept: `lean/tmp/pi_G.lean`);
* at least one further hotspot remains in the `Schwartz`/`Euclidean` half (prefix bisection reached
  266/312 fast, 323/329/365 slow pre-fix, 440/470/520/565/613 untested);
* the pin itself sets `maxHeartbeats 16000000` on the `PeriodizeLift` section and 3,200,000 file-wide, so
  its declarations exceed 200k by the pin's own admission;
* the `ZLattice` draft deliberately does *not* re-declare the 12 `PiPoissonSummation` helpers that the
  two pin `S_` files duplicate verbatim — that dedup is the design call to review when the pair is
  picked up.

## 6. Tool and tree findings worth keeping

* **The `end A.B` trap, caught.** The pin's `end K2Seam3.SqfreeSieve` closes one scope for the checker's
  namespace tracker, not two; the port's two headlines matched by hash while sitting in the wrong
  namespace. Written as two bare `end`s (playbook §7, now with a concrete instance).
* **`scoped instance` is parser-invisible** to both checkers: two transcribed `scoped instance`s in
  `SquarefreeValues` are faithful but not wired (78 port declarations, 76 wired).
* **Missing oleans**: `ModularForms/Level/Degeneracy`, then `ConstTermCubeIntegral`, `TorsionByCoordinates`
  and `TorsionOrbit` had to be built by the manager; the tree's oleans are not complete.
* **`/usr/bin/time` under-reports** a grandchild's CPU when the command is `timeout … lake env lean`:
  `user 0.4 s` on a 110 s, 110 %-CPU elaboration. Measure with `ps` on the `lean` process.
* **The build lock can be held for 40+ minutes** by another session's build; a queued `lake build` waits
  silently. Check the lock before blaming the compiler, and keep one compile at a time — the box is also
  memory-tight (7.9 GB, swap in use).
* **The "unavoidable" lints were suppressible, and the line between the two repairs is the statement.**
  Everywhere a warning can be removed *without touching the checked statement* it was removed at the
  source: `omit [NeZero …] in` (15 in `ChevalleyExtension`, 28 in `TorsionOrbit` where it works, 15 in
  `TorsionByCoordinates`), `haveI`→`have`, `dif_pos`/`if_neg`→`dite_eq_*`/`ite_eq_*`,
  `Set.mem_setOf_eq`→`Set.mem_ofPred_eq`, the `kw_`/`Kw` name strip, and the pin's own suppressions
  kept verbatim (`ConstantReduction.IsGood`). The **seven residual** warnings are the case where the
  source and the statement are the same text:
  `TorsionByCoordinates.exists_isUnit_Q` has an unused `hp : p.Prime` binder *inside its hypothesis
  type*, so the only source fix (`_hp`, or dropping it) rewrites the statement — the group verified that
  route and the checker answers `40 ok / 1 mismatch`; and six `TorsionOrbit` declarations have
  `[NeZero M]` **auto-included** because the *value* uses it (`ZMod.natCast_zmod_val`, `val_nsmul_V`)
  while the *type* does not, so `omit [NeZero M] in` breaks the proof rather than the warning. For those
  seven the repair is a **declaration-scoped** `set_option linter.unusedVariables false in` /
  `…unusedSectionVars false in` — the pin's own file-wide options, narrowed to one declaration, with the
  statement untouched (both modules still diff 41 / 98 ok afterwards). The column already documents this
  shape (note §9: the 15 narrow suppressions in the subject-A modules are the same auto-included-instance
  case). A statement deviation with a `decl_markers.tsv` entry is the only alternative, and it trades a
  verifiable statement for a cosmetic linter win.

## 7. Drift applied (per module, condensed)

`ResidueSumQExpansion`: `Set.mem_setOf_eq`→`Set.mem_ofPred_eq` (:80,:107), `if_pos`/`if_neg`→
`ite_eq_left`/`ite_eq_right` (7 sites), `boole_mul`'s literals no longer matching (:310,:317), the
`Nat.succPNat_coe` split before `hw` (:305–307), the `hsigma` factor, one trailing `rfl`.
`TorsionByCoordinates`: `import Mathlib.Algebra.Field.ZMod` added (:61), `inv_mul_cancel₀`→`simp [hγb]`
(:302), `simp [coe_resT, h…]` (:622,:624,:626), 15 `omit [NeZero …] in`, two `haveI`→`have`.
`TorsionOrbit`: `Equiv.setCongr`→`Set.equivOfEq` (:705), 28 `omit [NeZero M] in`, one `Set.mem_setOf_eq`,
one proof-internal `fun s s' h`→`fun _s _s' h`. `ZModPowerTsum`/`ConstTermCubeIntegral`/
`HeckeCharacter/{FiniteOrder,Equality}`/`QCoeffLevelOne`/`OmegaRowT2`: the `Set.mem_setOf_eq`,
`dif_pos`/`dif_neg`, `zero_le'`, `ENat.coe_le_coe`, `if_neg`, `haveI`→`have` families (full list in each
module header). `GaussProlongation`: bare `residue A`→`IsLocalRing.residue A` (4 sites, the new
`RegularProlongation.residue` projection shadows it), `Polynomial.finset_sum_coeff`→`finsetSum_coeff`
(3), `if_pos`→`ite_eq_left`. `SquarefreeValues`: seven generated `kw_`/`Kw` names stripped (the checker's
name guard rejects a residual `kw`; `norm` erases both forms, so the statement still diffs).
`UnimodularLift`: `Prime.not_unit`→`Prime.not_isUnit`, one unreachable `first` branch collapsed.
`TranscendentalAdjoin`: five `haveI`→`have`; the pin's `synthInstance.maxHeartbeats 800000` dropped (it
elaborates inside 200,000). `ChevalleyExtension`: `dif_pos`→`dite_eq_left` (2), one `Set.mem_setOf_eq`,
eleven `haveI`→`have`, two `letI`→`let`. `ConstantReduction`: no proof drift; the pin's own
`linter.unusedVariables false in` on `IsGood` carried verbatim (dropping or `_R`-renaming the binder
`MISMATCH`es).

## 8. What remains

* **`ZLattice` pair** — 3 nodes / 1,321 pin lines, drafts parked, hotspots diagnosed (§5). It needs the
  isolate-and-low-cap iteration *before* it lands; see CARRY-FORWARD.
* **`ResidueSumQExpansion`'s declaration** — the 40-minute shape rework is owed (300k–400k hearts today).
* **MG3 phase 2** — the 34 free-standing one-to-three-node families, 46 nodes / 9,344 raw lines / ~596
  wired (order §5). Not started.
* **Set MG4** (the `GeneralLinearGroup.exists_natCard_le_…` row behind `ModularCurve.SerreImage.contains_SL2`,
  1,611 net new, +53) — priced in
  [TOPIC-matrix-family-in-cone.md](../topics/deligneSerre/TOPIC-matrix-family-in-cone.md), not dispatched.
