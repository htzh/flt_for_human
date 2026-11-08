# SET-AF27 — the `L²`-continuity of right convolution

**Status: LANDED 2026-11-07** — one order, one new module, three headlines; the manager transcribed
the first proof and an agent the other two. §6 records the landing and the re-read.

**3 rows / 426 silo / 79 net new math lines (`port_plan`) / 7 declaration groups**, of which **297 of
the 376 declaration lines are already in the port**. This is the smallest set of the column and by far
the most composition-heavy: what is new is three proofs, not three developments.

| row | silo | prem | block | what it says |
|---|---|---:|---|---|
| `AutomorphicForm.norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 0 | leaf | `‖rightConv K φ f g‖ ≤ ‖f‖₂ · ‖φ‖₂((· * g) '' tsupport f)` — the Young/Hölder bound on the support of `f` |
| `AutomorphicForm.exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain` | 209 | 1 | *off-shelf* | for factorizable `f`, compact `Kc` and `ε > 0` a neighbourhood `V` of `1` with `‖rightConv φ f (g * h) - rightConv φ f g‖ ≤ ε ‖φ‖₂(Φ₀)` — uniform continuity of the convolution orbit |
| `MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le` | 139 | 0 | leaf | an equicontinuous, pointwise bounded family on a tight finite measure space has a finite `ε`-dense subset in the `eLpNorm` distance (Arzelà–Ascoli) |

## 0. The read (SET-AF26's post-landing read)

| figure | value |
|---|---|
| `needed [F terminal]` | **784 nodes / 330,301 lines** |
| `needed [literal]` | 796 / 333,766 |
| frontier F | 1,632 / 797,075 |
| ready block | **69 / 22,193** — 41 `AutomorphicForm` / 16,054 |
| leaves block | **210 / 54,362** — 45 `AutomorphicForm` / 9,242 |
| `AutomorphicForm` demand | 293 / 130,006 |
| withheld | 4 (prunable, not this column's) |
| `--selfcheck` | PASS |

## 1. Why this cut — and why it is small

After AF26 the AF shelf's return column is empty (best row 576 → 552) and its ready block holds no
large coherent subject: every remaining big block is behind an unported gateway. What *was* ready and
coherent is this trio — the `L²`-continuity package that the compact-operator chain needs, whose three
premises `285` names together:

`isCompactOperator_lift_rightConv_comp_cuspSubcarrier` (285, off-shelf) is missing **6** premises after
AF26; three of them are exactly this set (`norm_rightConv_le_eLpNorm_…` 78,
`exists_nhds_one_forall_norm_rightConv_mul_sub_…` 209, the equicontinuity lemma 139), and the other
three are big (`1,165`, `1,781`, `119`). So the set removes half the gateway's deficit for 426 silo.

**The set is below the recipe's 1,100–1,400-line band and the brief says so** (the SET-AF10 precedent):
79 net lines do not justify a 1,500-line dispatch by themselves; the order is sized to the work, and
the manager took the first proof. It is dispatched rather than done inline because the two remaining
bodies are 348 lines of pin text.

## 2. The price

| figure | value |
|---|---|
| raw `S_` lines | 426 |
| declaration lines | 376 |
| — duplicate copies | 0 |
| — boilerplate | 50 |
| distinct declaration groups | 7 |
| already in the port (vetted) | **297** |
| **net new math lines** | **79** |

6 trusted substitutions, 0 suspect; no definition gate; `twin_scan`: `new` three times.

## 3. Home

**One new module, `Adelic/RightConvLpContinuity.lean`**, above `Adelic/RightConvolution.lean`,
`Adelic/FactorizableTestFn.lean`, `Adelic/LsXi.lean` and SET-AF26's `Adelic/LsXiBound.lean` (the mass
bound the 209 proof consumes). The generic `MeasureTheory` headline is homed here because this module
is its only consumer — a `MeasureTheory/` supplement would be the home the day a second consumer
appears.

## 4. The cut, and the gates

One order, against the checker-green scaffold
(**3 ok / 0 mismatch / 0 missing**), which carries the three `attribute [local instance]` lines and the
`Filter`/`Topology` opens the two headlines need. No legacy module, no definition gate, no cascade.

## 5. Forecast

| figure | before | after |
|---|---|---|
| `needed [F terminal]` | 784 / 330,301 | **781 / 329,875** |
| `needed [literal]` | 796 / 333,766 | **793 / 333,340** |
| frontier F | 1,632 / 797,075 | **1,635 / 797,501** |
| ready block | 69 / 22,193 | **69 / 22,193** (untouched: one leaf, one off-shelf row, one leaf) |
| leaves block | 210 / 54,362 | **208 / 54,145** (2 leaves out: 217) |
| `AutomorphicForm` demand | 293 / 130,006 | **290 / 129,719** |
| rows readied | — | **0** (the 285 gateway goes from 6 to 3 missing premises) |

## 6. The landing

| part | who | result |
|---|---|---|
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` (pin 78) | manager | transcribed in one pass, elaborates clean (no v4.34 drift beyond the local instances) |
| the 209 and 139 headlines, plus the pin's three helper lemmas | agent | landed; final module **459 lines / 7 declarations** |

| gate | result |
|---|---|
| `check_port --force` | **6 ok / 0 mismatch / 0 missing / 0 own** (3 headlines + the pin's 3 S_-file helpers) |
| build (single module, flock) | success, 3,745 jobs, 6.3 s |
| axioms (3 headlines) | `[propext, Classical.choice, Quot.sound]` each |
| `dedup --within` | 7 declarations, **0 clusters / 0 removable** |
| `move_dead` | 0 declarations / 0 lines |
| consumer `spec/AutomorphicFormSetAF27Consumer.lean` | **0 errors / 0 warnings** (134 lines, three zones) |

**The re-read is exact on five of the six rows** and off by one node on the sixth:

| figure | before | forecast | actual |
|---|---|---|---|
| `needed [F terminal]` | 784 / 330,301 | 781 / 329,875 | **781 / 329,875** ✓ |
| `needed [literal]` | 796 / 333,766 | 793 / 333,340 | **793 / 333,340** ✓ |
| frontier F | 1,632 / 797,075 | 1,635 / 797,501 | **1,635 / 797,501** ✓ |
| ready block | 69 / 22,193 | 69 / 22,193 | **69 / 22,193** ✓ |
| leaves block | 210 / 54,362 | 208 / 54,145 | **208 / 54,145** ✓ |
| `AutomorphicForm` demand | 293 / 130,006 | 290 / 129,719 | **291 / 129,719** (nodes, see below) |
| rows readied | — | 0 | **0** ✓ |

The one slip is a bookkeeping one worth carrying: the third row is `MeasureTheory.…`, so it leaves
that namespace's demand and not `AutomorphicForm.`'s — the AF count falls by **2** (78, 209), not 3,
while the *lines* still fall by the whole 287 (the third row's 139 lines are `MeasureTheory.`'s).
The `MeasureTheory` demand went 15 / 2,120 → **14 / 1,981**.

**One statement deviation, and it is a genuine one.** The pin's `eLpNorm_two_eq` states an
*unconditional* identity `eLpNorm φ 2 ν = (∫⁻ ‖φ‖²)^(1/2)`. At mathlib v4.34 `eLpNorm` is `∞` off
a.e.-strong measurability, so the pin's statement is **false** here; the port's copy is `private` and
takes `hφ : AEStronglyMeasurable φ ν`, with the pin's proof body otherwise unchanged. Because it is
private, the checker never diffs it (`0 own`), and nothing public depends on the altered signature.
The rest of the drift is proof-level and recorded with pin lines: `dif_pos` → `Function.invFun`
(−3 lines), `haveI : CompactSpace K` → `have`, `dist_coe_le_dist` namespaced, `eLpNorm_le_of_ae_bound`
gaining its v4.34 measurability argument (which splits `hgm` in two, +3 lines), `eLpNorm_add_le`'s
reordered signature. Two new imports (`Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli`,
`Adelic/TestFnTop`) and two `open scoped`s (`Pointwise`, `BoundedContinuousFunction`).

**How much of the 209 row is SET-AF26.** Pin 116–118 is the whole reuse: one `obtain` of SET-AF26's
mass bound, applied once (pin :193) inside `hk5` — 12 lines of `hk5` precisely *because* the Siegel
covering is not redone. Around it sit this column's two adapters (the constant packaging at pin
120–127, and the lintegral→`eLpNorm` bridge `eLpNorm_two_eq` at pin 191–193, which converts
`∫⁻ ≤ ofReal N · ∫⁻` into the `eLpNorm φ 2 (R) ≤ b · eLpNorm φ 2 (Φ₀)` that Hölder needs). So ≈26 of
128 proof lines (20 %) are SET-AF26 plus adapter, and they buy the `a·b/(a·b+1) < 1` slack the final
arithmetic closes on; the other ~102 lines are the pin's own route.

## 7. What this set does not do, and the two blocked rows this pass found

- **The 285 gateway and the compact-operator block** (`isCompactOperator_lift_rightConv_comp_cuspSubcarrier`
  285, then `exists_isCompactOperator_isSymmetric_lift_rightConv` 114 and
  `exists_isCuspLift_rightConv_isCompactOperator` 43): still 3 premises short (`1,165` — itself 4
  premises short — `1,781` and `119`). The next set on this chain is `118/119 + 1,781`, not the gateway.
- **The Weyl intertwining pair, and why it is *not* AF27.** This pass scoped it
  (`weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` 1,349 +
  `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`
  1,291: 2,640 silo but only **1,072 net**, 1,499 declaration lines already in the port — the most
  composition-heavy pair left) and **could not scaffold it**, for two port-side reasons that are
  manager decisions, not worker ones:
  1. the 1,291 statement writes `NumberField.AdelicBox.integralFiniteAdeles`, and the port homes that
     definition in `NumberField.AdelicLevel` (`NumberTheory/AdelicLevel/IdealBall.lean:159`); the
     qualified path the pin's text uses does not exist, so the statement cannot be transcribed
     verbatim (FR-0151);
  2. the 1,349 statement's `(hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))` relies on an **auto-bound** `x`, which
     `set_option autoImplicit false` (project-wide) forbids; the pin's wrapper compiles only because its
     own `set_option` is not in force for the generated statement. Writing the binder explicitly changes
     the statement text (FR-0151).

  Both are one-line port-side fixes (an `abbrev` alias in `NumberField/AdelicBox.lean`; an `own:` row
  with a recorded reason for the binder annotation) — but each is a hub edit with a cascade, so they
  belong to a manager pass that scopes the pair, not to a worker. The pair stays the largest open
  subject on the shelf and is the natural next set once those two decisions are taken.
- **The `isCuspConstituent` cluster** remains as SET-AF25 §8 lists it (the 458 row's 107-node /
  29,103-silo closure).
