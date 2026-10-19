# TOPIC — the local twisted integral: the `EisensteinGeneral` ready shelf

**Status: Set A landed 2026-10-18; Set B pending.** The orders are
[WORKORDER-E1-local-twisted-ram.md](WORKORDER-E1-local-twisted-ram.md) (Set A, the ramified
side, three headlines) and WORKORDER-E2 (Set B, the unramified pair, two headlines — written
after Set A lands, importing its engine).

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is `v4.34.0`.

**Method.** The six-step loop of
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3, its §4, and
[porting-playbook.md](../../../porting-playbook.md) §2–§5.

**Companions.** [../../PORTING-AutomorphicForm.md](../../PORTING-AutomorphicForm.md) — the
`AdelicLevel` definition layer these statements sit over. The Tate-local analytic core these
integrals are computed against is
[../tateGlobal/TOPIC-tateglobal-analytic-core.md](../tateGlobal/TOPIC-tateglobal-analytic-core.md)
and `LanglandsTunnell/TateLocalZeta.lean`. The `WeylSmooth`/`WeylShell` modules whose private
prelude this set promotes are the `AutomorphicForm` local-intertwining layer's.

## 1. The cluster

Five ready rows of the `EisensteinGeneral` namespace (21 rows / 11,457 silo lines on the shelf),
one story: **the local integral of a twisted smooth function at one place, and its two
degenerations** — the ramified place, where the integral reduces to the integral over the unit
ball plus a finite sum over the shells `|x| = q^{-k}`; and the unramified place, where the same
integral has a closed form and vanishes once the additive character's level is below `|ξ|`.

| node | pin proof | raw lines | what it says |
|---|---|---:|---|
| `EisensteinGeneral.LocalRam.integral_twisted_smooth_eq` | `S_…_integral_twisted_smooth_eq` | 864 | the integral of `untwisted χ s A B · ψ(-ξ·)` equals its `𝒪`-part plus `∑_{k=1}^{max(m-1, n+c-e)} (q^{-(2s+1)})^k ∫_{|x|=q^{-k}} χ⁻¹(x) B(x⁻¹) ψ(-ξx)` |
| `EisensteinGeneral.LocalRam.integrable_twisted_smooth` | `S_…_integrable_twisted_smooth` | 567 | the same integrand is `Integrable` |
| `EisensteinGeneral.LocalRam.integral_twisted_smooth_eq_zero_of_exp_lt` | `S_…_zero_of_exp_lt` | 260 | it vanishes when `exp (n + max m c) < |ξ|` |
| `EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq` | `S_…_integral_norm_eq` | 297 | unramified case: integrable, and the integral of the norm is `μ(𝒪) · (1 - ‖χϖ‖ q^{-(2s+1)}) · (1 - ‖χϖ‖ q^{-2s})⁻¹` |
| `EisensteinGeneral.LocalUnr.integral_twisted_eq_zero_of_exp_lt` | `S_…_zero_of_exp_lt` | 146 | unramified case: it vanishes when `exp n < |ξ|` |

**The mathematics.** `untwisted χ s A B` is the twisted smooth function of the local Rankin–Selberg
/ Godement–Eisenstein computation at `v`: `A` on the unit ball `𝒪`, and on its complement
`charExt χ⁻¹ y · |y|^{-(2s+1)} · B(y⁻¹)`. Its archimedean twin is the `WeylSmooth` subject; here
the place is non-archimedean, the measure is a Haar measure on `v.adicCompletion F`, and
`ψ(-ξ·)` is the additive character of level `n`. The integral splits at `𝒪`; on the shells it
is elementary because `untwisted` is constant there (the `untwisted_add_eq_*` lemmas), the
`|x|`-factor is a geometric progression in `q^{-(2s+1)}`, and the sum is cut off at
`max (m-1) (n + c - e)` by the two level conditions (`hB`'s `ϖᵐ`-invariance, `hψn`'s level, and
the conductor `c` of `χ` via `higherUnitsAt`). The unramified case is the same with
`A = B = 1`: the shells contribute `χ⁻¹(u)` averaged over the unit group, which vanishes when
`χ` is unramified and the character's level is below `|ξ|`, and otherwise sums to the geometric
series above.

## 2. The measurement

```bash
cd tools/deps
python3 port_advise.py --target EisensteinGeneral.LocalRam.integral_twisted_smooth_eq \
  --target EisensteinGeneral.LocalRam.integrable_twisted_smooth \
  --target EisensteinGeneral.LocalRam.integral_twisted_smooth_eq_zero_of_exp_lt \
  --target EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq \
  --target EisensteinGeneral.LocalUnr.integral_twisted_eq_zero_of_exp_lt \
  --json build/eg_local_advise.json
python3 port_plan.py --json build/eg_local_advise.json
```

| quantity | value |
|---|---:|
| raw `S_` lines (five files) | 2,134 |
| declaration lines / groups | 2,017 / 59 |
| duplicate copies inside the slice | 673 |
| once-cost after dedup | 1,344 |
| already in the port | 42 |
| **net new math lines** | **1,302** |

**The dedup is the point.** The two big `LocalRam` files share a **byte-identical 486-line
prelude** (file A lines 24–486 ≡ file B lines 26–488; the only difference in that range is the
`section` header at its end): `setOf_valued_sub_*`, `valued_uniformizer_*`, `continuous_of_depth`,
`charExt_inv_eq_of_sub_le`, `continuousOn_charExt_inv`, `continuous_addChar_neg_mul`,
`norm_addChar_of_level`, `untwisted`, `modulus_eq_of_valued_eq`, `isOpen_integers`,
`isCompact_integers`, `continuousOn_of_valued_eq`, `continuousOn_modulus_cpow`,
`compl_integers_subset`, `aestronglyMeasurable_untwisted`, `absChar` and its lemmas, `absNorm_pos`,
`hs_absChar`, `norm_untwisted_le`, `integrableOn_norm_add_one`, `charExt_absChar_inv_eq`,
`integrable_dominator` (95 lines). The third Ram file re-proves three of them
(`charExt_inv_eq_of_sub_le`, `untwisted`, `modulus_eq_of_valued_eq`) verbatim. So 972 lines are
written once, and the cluster's marginal cost is roughly half its raw size.

The cluster's own prices, as cut:

| set | files | raw | net new |
|---|---|---:|---:|
| **A** — the Ram trio | 3 | 1,691 | ≈1,000 (E1 486-line engine + E2 shell sets + three headlines) |
| **B** — the Unr pair | 2 | 443 | **374** standalone; ≈330 marginal after A homes `norm_addChar_of_level` |

## 3. The definition gate and the promotions (the manager's work, landed)

Nothing can be *stated* before the pin's `Def_LanglandsTunnell_TateLocalConstantsAt` exists: all
five statements quantify over `higherUnitsAt F v c`. That module is 155 lines / 21 declarations
(`higherUnitsAt`, `HasConductorExponentAt`, `conductorExponentAt`, `localLFactorAt`,
`localEpsilonAt` and their lemmas) and it has **no `Theorems/` wrapper**, so it is its own
statement authority and was homed **whole** at
`FLTForHuman/LanglandsTunnell/TateLocalConstantsAt.lean` (playbook §2.3; the same shape as the
centre-cut and arch-Casimir definition gates) and **listed**, so the checker diffs all 21.

Three private helpers that the pin re-copies into its `S_` files were promoted out of `private`
in their existing port homes rather than re-proved (§4(b)):

| declaration | host | why |
|---|---|---|
| `setOf_valued_sub_le_mem_nhds` | `TateGlobal/WeylSmooth.lean` | 14 lines of valuation-neighbourhood glue, re-copied by two pin files |
| `setOf_valued_sub_lt_mem_nhds` | `TateGlobal/WeylSmooth.lean` | 15 lines, same |
| `ofReal_pow_cpow` | `TateGlobal/WeylShell.lean` | 8-line `ℂ^s` identity, re-copied by two pin files (the third Ram file and `LocalUnr.integral_twisted_eq`, not in this set) |

All three statements are the pin's — the checker now diffs them (they are in listed modules),
which is the evidence, not port_advise's name match. Wave: `WeylSmooth` + `WeylShell` +
`WeylUnramified`, 3,795 jobs, ≈18 s. `isCompact_integers` needed no promotion: it is already
public tier 3 in `TateGlobal/LocalZetaUnramified.lean`.

**One collision the gate exposed, and the dedup it forced.** `TateGlobal/WeylSmooth.lean`
already carried a copy of `LanglandsTunnell.TateLocal.higherUnitsAt` (from an earlier landing
whose docstring said "its natural home is a `LanglandsTunnell/TateLocalConstantsAt.lean` module; a
later refactor round should move it there"), so homing the pin's definition module gave the tree
**two** declarations of that name and no module could import both. The refactor round is this one:
the copy in `WeylSmooth.lean` is deleted and `WeylSmooth.lean` imports the definition module
instead (one host edit; wave `WeylSmooth`/`WeylShell`/`WeylUnramified`, 3,795 jobs, ≈20 s; the
only importer of `WeylSmooth` is the new engine). Statements unaffected — both copies were the
pin's, and the checker still sees exactly one.

Gate effect: checker **10,344 → 10,367 identical** — +21 for the definition module, +3 for the
promotions, −1 because `higherUnitsAt` had been counted twice (once per host) before the dedup —
0 mismatched / 0 missing; 702 of the identical are now promoted from pin-private (was 700).

## 4. The port structure

**Set A — the Ram trio** ([WORKORDER-E1-local-twisted-ram.md](WORKORDER-E1-local-twisted-ram.md)):

| module | contents | tier |
|---|---|---|
| `EisensteinGeneral/LocalTwisted.lean` | the 486-line shared prelude, 25 declarations, namespace `EisensteinGeneral.TwistedSmoothLocal` | 3 |
| `EisensteinGeneral/LocalRamShells.lean` | `integrable_twisted_aux`, the `isOpen_setOf_valued_*` / `measurableSet_setOf_*` shell sets, `toAdd_unzero_exp`, `coe_modulus_of_valued_eq`, `untwisted_add_eq_of_sphere`, and file C's `untwisted_add_eq` | 3 |
| `EisensteinGeneral/LocalRam.lean` | the three headlines at the wrappers' dotted names | **1** |

**Set B — the Unr pair** (WORKORDER-E2, to be written): one listed module holding the two
headlines and their own machinery (`valued_uniformizer_zpow`, `isOpen_ball`,
`measureReal_integers_pos`, `continuous_addChar_of_level`, `untwisted` (the `A = B = 1`
specialization), `integrable_untwisted`, `normChar`, `ofReal_norm_untwisted_mul`), importing
Set A's engine for `norm_addChar_of_level` and the definition module for `higherUnitsAt`.

**Namespace policy.** The pin's shared preludes live in `P2MW.S_…TwistedSmoothLocal` /
`…TwistedUnramifiedLocal`; the port keeps the meaningful half (`EisensteinGeneral.TwistedSmoothLocal`)
and drops the p2m prefix, as every engine does. The headlines keep the wrappers' dotted names
(`EisensteinGeneral.LocalRam.*`, `EisensteinGeneral.LocalUnr.*`) because those are the checker's
wire.

## 5. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --rank-by silo --ready --top 0 | grep EisensteinGeneral
python3 port_advise.py --target <the five nodes> --json build/eg_local_advise.json
python3 port_plan.py --json build/eg_local_advise.json

# the dedup, verified directly: the two preludes differ only at their ends
diff <(sed -n '24,486p' ~/proj/fermats-last-theorem/P2M/Sol/S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean) \
     <(sed -n '26,488p' ~/proj/fermats-last-theorem/P2M/Sol/S_EisensteinGeneral_LocalRam_integrable_twisted_smooth.lean)

# the definition gate's wave (already paid)
python3 build_ladder.py --edit FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylShell.lean
python3 build_ladder.py --edit FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylSmooth.lean
```

## 6. Landing record

### Set A

| | |
|---|---|
| definition gate | `LanglandsTunnell/TateLocalConstantsAt.lean` — 21 declarations, listed (**+21**) |
| promotions | `WeylSmooth.setOf_valued_sub_{le,lt}_mem_nhds`, `WeylShell.ofReal_pow_cpow` (**+3**) |
| dedup | `higherUnitsAt` moved out of `WeylSmooth.lean` into the gate (**−1**, a double count) |
| engines | `EisensteinGeneral/LocalTwisted.lean` (527 lines, 25 decls), `…/LocalRamShells.lean` (265, 9) — tier 3 |
| façade | `EisensteinGeneral/LocalRam.lean` (354 lines, 3 headlines) — listed (**+3**) |
| checker | **10,370 identical** (was 10,344), 0 mismatched / 0 missing, 10,706 checked |
| axioms | all three headlines `[propext, Classical.choice, Quot.sound]` |
| build | gate 4.7 s; the Weyl wave 3,795 jobs; Set A 3,803 jobs; tier-0 0 warnings everywhere |
| register | 134 → 136 modules, 4100 → 4134 public, 3796 → 3830 with a pin counterpart |
| existing modules edited | `WeylSmooth.lean` (promotions + dedup), `WeylShell.lean` (promotion) — the manager's own hub work |

Five proof adaptations, all proof-level (`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`,
`zero_le'` → `zero_le`, `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`,
`modulus_adicCompletion_eq_nnnorm`'s binder arity, and one `haveI` → term-mode
`Ideal.finiteQuotientOfFreeOfNeBot`); every statement is the pin's. The full record is
[logs/eisenstein-local-twisted-ram.md](../../../logs/eisenstein-local-twisted-ram.md) and the
results are [WORKORDER-E1-local-twisted-ram.md](WORKORDER-E1-local-twisted-ram.md) §8.

### Set B

| | |
|---|---|
| module | `EisensteinGeneral/LocalUnr.lean` — 408 lines, **18** public declarations, all listed |
| contents | 16 machinery (`TwistedUnramifiedLocal`) + 2 headlines (`EisensteinGeneral.LocalUnr`) |
| checker | **10,388 identical** (was 10,370), 0 mismatched / 0 missing, 10,724 checked — delta **+18** |
| promoted-from-pin-private | 702 → 718: the machinery is `private` in both pin files |
| axioms | both headlines `[propext, Classical.choice, Quot.sound]` |
| build | tier-0 exit 0 / 0 warnings; tier-1 green, 3,803 jobs |
| existing modules edited | none |

**The shape differs from Set A on purpose.** Set B's machinery has no other consumer, so it is
written into the one *listed* module (with its two `S_` files in `SOURCES`) instead of a tier-3
engine plus façade: listing costs two `SOURCES` entries and puts 16 declarations under the
checker that a tier-3 engine would have left unchecked with no future importer to justify it.
Record: [logs/eisenstein-local-twisted-unr.md](../../../logs/eisenstein-local-twisted-unr.md);
order and results: [WORKORDER-E2-local-twisted-unr.md](WORKORDER-E2-local-twisted-unr.md) §8.

**The cluster is now complete on the ready shelf.** The remaining rows of the family are
`EisensteinGeneral.LocalUnr.integral_twisted_eq` (601 pin lines; needs two unported
`LanglandsTunnell` rows, 249 raw lines) and the `LocalCorrection` pair (173 lines, not ready);
the five landed headlines feed the `AutomorphicForm` Godement–Eisenstein local-factor assembly,
which is not this column's.
