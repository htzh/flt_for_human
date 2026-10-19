# WORKORDER-E1 — the local twisted integral at a ramified place (tier-3 engine, one headline ×3)

**Status: issued 2026-10-18.** Read
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3 (the workflow), §4
(definitions whole node; `private` is a build tool; a hub edit is a wave) and
[porting-playbook.md](../../../porting-playbook.md) §3–§5 before starting, then
[TOPIC-local-twisted-integral.md](TOPIC-local-twisted-integral.md) (the cluster's measurement).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

**The set: three ready shelf rows of the `EisensteinGeneral` cluster, one story — the local
integral of a twisted smooth function at a ramified place.** Two pin `S_` files share a
byte-identical 486-line prelude (lines 24–486), a third re-proves three of its declarations;
the three headlines are one façade. Net new ≈ **1,000 lines**, three headlines.

**The definition gate and the promotions are already done — do not redo them.** The manager
landed, before this order:

* `FLTForHuman/LanglandsTunnell/TateLocalConstantsAt.lean` — the pin's
  `Def_LanglandsTunnell_TateLocalConstantsAt` whole (21 declarations: `higherUnitsAt`,
  `HasConductorExponentAt`, `conductorExponentAt`, `localLFactorAt`, `localEpsilonAt` …), listed
  and checker-diffed. **Import it** for `higherUnitsAt`; do not re-declare anything from it.
* `NumberField.TateGlobal.WeylSmooth.setOf_valued_sub_le_mem_nhds` and
  `…setOf_valued_sub_lt_mem_nhds` — **now public** (were port-`private`).
* `NumberField.TateGlobal.WeylShell.ofReal_pow_cpow` — **now public** (was port-`private`).
* `NumberField.TateGlobal.LocalZetaUnramified.isCompact_integers` — already public tier 3.

Those four plus the definition module are the substitutions: **import them, never re-prove
them.** If any of them is missing or has the wrong statement, **stop and report** (§6).

## 1. Scope

Three new files, nothing else:

| # | module | contents | tier |
|---|---|---|---|
| E1 | `FLTForHuman/EisensteinGeneral/LocalTwisted.lean` | the 28-declaration shared prelude (pin lines 24–486) | 3 |
| E2 | `FLTForHuman/EisensteinGeneral/LocalRamShells.lean` | the shell/set machinery the three files still need (pin lines 490–625 of file A, 67–165 of file C) | 3 |
| E3 | `FLTForHuman/EisensteinGeneral/LocalRam.lean` | the **three headlines**, statements verbatim from the three wrappers | **listed** |

E1 and E2 are engines: every declaration **public**, at its pin name, namespace
`EisensteinGeneral.LocalRam` (the pin's), each with a
`-- pin: <name> (<S_ file>:<line>)` marker. E3 holds only the three headlines.

**Explicitly not this order.**

* **The `LocalUnr` pair** — `EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq`
  and `…integral_twisted_eq_zero_of_exp_lt`. They are the *unramified* side, they share only
  `norm_addChar_of_level` (in E1) with this set, and they are a separate order (Set B). Do not
  write them; E1 already homes the two declarations they share, so Set B can import it.
* `EisensteinGeneral.LocalUnr.integral_twisted_eq` — not ready (needs 2 unported
  `LanglandsTunnell` rows).
* Any other `EisensteinGeneral` row; the `LocalCorrection` pair; the `AutomorphicForm` consumers.
* **Any edit to an existing module.** No promotion, no hub edit, no wave — see §6.

## 2. Pin sources

Statement authority (state each headline **verbatim**, the checker diffs them):

* `Theorems/Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean`
* `Theorems/Thm_EisensteinGeneral_LocalRam_integrable_twisted_smooth.lean`
* `Theorems/Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq_zero_of_exp_lt.lean`

Proofs (read-only, on disk at `~/proj/fermats-last-theorem/P2M/Sol/`):

* `S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean` (864 lines) — the shared
  prelude at 24–486, the engine remainder at 490–625, the headline `integral_twisted_smooth_eq`
  at 626 (211 lines) and `solution` at 837.
* `S_EisensteinGeneral_LocalRam_integrable_twisted_smooth.lean` (567 lines) — the shared prelude
  at 26–488 (byte-identical to the other file's, modulo a 2-line offset), then
  `integrable_twisted_aux` at 492 and the headline at 520 (26 lines) with `solution` at 546.
* `S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq_zero_of_exp_lt.lean` (260 lines) —
  `untwisted_add_eq` at 67 (99 lines) and the headline at 166 (69 lines), `solution` at 235.

The wrappers' `attribute [-instance]` / `attribute [-simp]` preludes are **not** reproduced; the
port's definition layer already states the instances (the same choice every landed `TateGlobal`
wrapper made).

## 3. The three modules, declaration by declaration

### E1 — `LocalTwisted.lean`, the shared prelude (pin file A lines 24–486 ≡ file B lines 26–488)

This block is **byte-identical in the two Ram files** — write it once (that is the whole point
of the dedup: 972 lines → 486). Declarations, in order (pin line of file A):

| pin | declaration |
|---:|---|
| 24 | `setOf_valued_sub_le_mem_nhds` — **substitution**, import from `TateGlobal/WeylSmooth.lean` |
| 38 | `setOf_valued_sub_lt_mem_nhds` — **substitution**, same home |
| 53 | `valued_uniformizer_exp` |
| 58 | `valued_uniformizer_pow` |
| 65 | `continuous_of_depth` |
| 83 | `charExt_inv_eq_of_sub_le` |
| 112 | `continuousOn_charExt_inv` |
| 135 | `continuous_addChar_neg_mul` |
| 164 | `norm_addChar_of_level` (this one is also shared with the `LocalUnr` pair — home it here) |
| 204 | `untwisted` (`def`) |
| 210 | `modulus_eq_of_valued_eq` |
| 217 | `isOpen_integers` |
| 227 | `isCompact_integers` — **substitution**, import from `TateGlobal/LocalZetaUnramified.lean` |
| 231 | `continuousOn_of_valued_eq` |
| 242 | `continuousOn_modulus_cpow` |
| 246 | `compl_integers_subset` |
| 259 | `aestronglyMeasurable_untwisted` |
| 289 | `absChar` (`def`) |
| 299 | `absChar_apply` |
| 303 | `absChar_higherUnits` |
| 311 | `norm_charExt_inv_absChar` |
| 320 | `depth_norm_add_one` |
| 327 | `absNorm_pos` |
| 331 | `hs_absChar` |
| 343 | `norm_untwisted_le` |
| 371 | `integrableOn_norm_add_one` |
| 380 | `charExt_absChar_inv_eq` |
| 395 | `integrable_dominator` (95 lines) |

So E1 carries **25** declarations of its own (28 entries less the three substitutions). Its
header is the pin's, with only the p2m prefix dropped:

```lean
open MeasureTheory IsDedekindDomain NumberField

namespace EisensteinGeneral

namespace TwistedSmoothLocal

section Prep

open IsDedekindDomain.HeightOneSpectrum Filter Topology
open LanglandsTunnell.TateLocal NumberField.AdelicLevel

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
```

— note `F` and `v` are **implicit** here (the pin's `variable {F} … {v}`), unlike the headlines.
The pin's `private` becomes public (playbook §4(b): these are the engine the three headlines and
the `LocalUnr` pair import).

### E2 — `LocalRamShells.lean`, the shell/set machinery

From file A (490, 510–625) and file C (67):

| pin | declaration | note |
|---:|---|---|
| A:490 | `integrable_twisted_aux` | used only by the `integrable_twisted_smooth` headline |
| A:510 | `isOpen_setOf_valued_le` | |
| A:520 | `isOpen_setOf_valued_lt` | |
| A:534 | `measurableSet_setOf_valued_eq` | |
| A:549 | `measurableSet_setOf_exp_lt` | |
| A:564 | `toAdd_unzero_exp` | |
| A:568 | `coe_modulus_of_valued_eq` | uses `modulus_adicCompletion_eq_nnnorm` (port: `TateGlobal/NormIntegrable.lean:258`) |
| A:575 | `ofReal_pow_cpow` | **substitution**, import from `TateGlobal/WeylShell.lean` |
| A:583 | `untwisted_add_eq_of_sphere` (43 lines) | |
| C:67 | `untwisted_add_eq` (99 lines) | the third file's own version — port it too, at its name |

### E3 — `LocalRam.lean`, the three headlines

Statements verbatim from the three wrappers (§2); proofs are the pin's `solution` bodies:

The pin declares each of the three as a `private theorem` inside `namespace TwistedSmoothLocal`
(file A line 626, file B line 520, file C line 166), i.e. `…TwistedSmoothLocal.integral_twisted_smooth_eq`
and siblings; the port states them at the **wrappers'** dotted names
`EisensteinGeneral.LocalRam.*` (that is the checker's wire), with
`open EisensteinGeneral.TwistedSmoothLocal` in front so the pin's proof bodies transcribe
unchanged. The pin's `private` headline copies are therefore not ported a second time.

* `EisensteinGeneral.LocalRam.integrable_twisted_smooth` (26 lines, file B `solution`);
* `EisensteinGeneral.LocalRam.integral_twisted_smooth_eq` (211 lines, file A `solution`);
* `EisensteinGeneral.LocalRam.integral_twisted_smooth_eq_zero_of_exp_lt` (69 lines, file C
  `solution`).

All three are proved by applying the engine lemmas of E1/E2; the pin's `solution` proofs are the
route. Namespace `EisensteinGeneral.LocalRam` — the headlines' dotted names must be exactly the
wrappers' (they are the checker's wire).

## 4. What is already in the port, and the names to hand-check

| pin name used | port home |
|---|---|
| `higherUnitsAt` | `LanglandsTunnell/TateLocalConstantsAt.lean` (**new**, landed by the manager) |
| `charExt`, `modulus`, `localZeta`, `localGammaAt` | `LanglandsTunnell/TateLocalZeta.lean` |
| `uniformizerUnit` | `NumberField/AdelicLevel/HeckeGen.lean:198` |
| `modulus_adicCompletion_eq_nnnorm` | `TateGlobal/NormIntegrable.lean:258` |
| `setOf_valued_sub_le_mem_nhds`, `setOf_valued_sub_lt_mem_nhds` | `TateGlobal/WeylSmooth.lean` (**promoted**) |
| `ofReal_pow_cpow` | `TateGlobal/WeylShell.lean` (**promoted**) |
| `isCompact_integers` | `TateGlobal/LocalZetaUnramified.lean:83` (tier 3) |
| `Valued.isOpen_closedBall`, `Valued.isOpen_ball`, `Valuation.map_add_of_distinct_val`, `WithZero.exp_*`, `WithZeroMulInt.toNNReal_neg_apply`, `NumberField.FinitePlace.norm_def` | mathlib |

Read each of the promoted declarations' **statements** in their port homes before use; the two
`setOf_valued_sub_*` take `(x z : v.adicCompletion F) (hz : Valued.v z ≠ 0)` with `v` a section
variable in namespace `NumberField.TateGlobal.WeylSmooth`, and `ofReal_pow_cpow` takes
`{a : ℝ} (ha : 0 ≤ a) (s : ℂ) (k : ℕ)` in `NumberField.TateGlobal.WeylShell`. If a statement is
not the pin's, **stop and report** — do not adapt a statement.

## 5. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect. Diagnose
> it (`set_option diagnostics true`, `trace.Meta.synthInstance true` on that one declaration, in
> a scratch copy under `tmp/`), fix the inference, re-run. Never raise `maxHeartbeats`, never add
> a module `set_option maxHeartbeats`. When a file is done,
> `flock .lake/flt_build.lock timeout 300 lake build <module>`. Every `lake build` serialized and
> bounded. **Never a bare whole-tree `lake build`.**

**Hub prohibition.** Do not edit `LanglandsTunnell/TateLocal*.lean`, `TateGlobal/Weyl*.lean`,
`TateGlobal/LocalZetaUnramified.lean`, `TateGlobal/NormIntegrable.lean`,
`NumberField/AdelicLevel/*`, or any other existing module. If you believe a promotion is
genuinely required, **stop and report** with the declaration, the host and the price from
`python3 tools/deps/build_ladder.py --edit <host>`. The four names of §4 are already promoted;
nothing else should be needed.

**Drift surface.** The pin sets `set_option maxHeartbeats 3200000` and a long `attribute
[-instance]` prelude in its `S_` files; neither is transcribed. `if_pos`/`if_neg` are
`ite_eq_left`/`ite_eq_right` in `v4.34.0`; `dif_pos`/`dif_neg` likewise. `absChar` and
`untwisted` are `def`s with `classical`/`by` bodies — keep their pin shape. The
`Finset.Icc`-indexed sum in the big headline's statement must be copied character for character
from the wrapper (it is the diffed text).

## 6. Verification

| check | expected |
|---|---|
| tier-0 edit loop, all three modules | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.EisensteinGeneral.LocalRam` | green |
| checker before | 10367 identical / 0 mismatched / 0 missing / 42 own / 294 registered (10703) |
| checker after (the manager wires it) | **10370** identical — delta **+3**, exactly the three headlines |
| `#print axioms` on each headline | `[propext, Classical.choice, Quot.sound]` |
| `git status` | only the three new modules |

## 7. Report shape

1. The three module paths, final line counts, and the declaration names per module.
2. Each module's import block, with one clause per import.
3. Every proof adaptation (pin line → port spelling), with pin line numbers; say what failed
   first when a proof did not transcribe.
4. For each of the four §4 substitutions: the exact port name you used and the statement you
   read (so the manager can confirm no statement drifted).
5. Tier-0 results per module and the tier-1 result, with wall times.
6. The pin line of every `-- pin:` marker, for the register.
7. Anything left undone, any deviation from this order, and any place where you stopped rather
   than edit an existing module.

## 8. Results as landed (2026-10-18)

| | |
|---|---|
| engine 1 | `EisensteinGeneral/LocalTwisted.lean` — 527 lines, **25** public declarations, tier 3 |
| engine 2 | `EisensteinGeneral/LocalRamShells.lean` — 265 lines, **9** public declarations, tier 3 |
| façade | `EisensteinGeneral/LocalRam.lean` — 354 lines, **3** headlines, listed |
| checker | 10,367 → **10,370 identical**, 0 mismatched / 0 missing, 10,706 checked (delta +3) |
| axioms | all three `[propext, Classical.choice, Quot.sound]` |
| tier-0 / tier-1 | 0 warnings; `lake build FLTForHuman.EisensteinGeneral.LocalRam` green, 3,803 jobs |
| register | 136 modules / 4134 public / 3830 with a pin counterpart (was 134 / 4100 / 3796) |
| existing modules edited | none by this order |

Deviations from the order, all recorded:

1. **The import collision (§1's "the manager landed the gate").** `TateGlobal/WeylSmooth.lean`
   already declared `LanglandsTunnell.TateLocal.higherUnitsAt`, so `LocalTwisted.lean` could not
   import both `TateLocalConstantsAt` and `WeylSmooth`. The manager fixed it at the host — the
   duplicate block is deleted from `WeylSmooth.lean`, which now imports the gate — and the wave
   (`WeylSmooth`/`WeylShell`/`WeylUnramified`, 3,795 jobs) is green. The subagent's first
   resolution (take `higherUnitsAt` from `WeylSmooth`) was correct under the collision and was
   re-pointed to the gate afterwards; both paths now compile, and there is exactly one
   `higherUnitsAt` in the tree.
2. **`ofReal_pow_cpow` was used from `TateGlobal/WeylShell.lean`** (the promotion) rather than
   re-proved — as ordered.
3. Five proof adaptations, none touching a statement: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`,
   `zero_le'` → `zero_le`, `modulus_adicCompletion_eq_nnnorm`'s binder arity (`F`, `v`
   implicit), `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` (in the gate), and one `haveI` →
   term-mode `Ideal.finiteQuotientOfFreeOfNeBot` in `absNorm_pos` (the lint, not a proof change).

The full record is [logs/eisenstein-local-twisted-ram.md](../../../logs/eisenstein-local-twisted-ram.md).
