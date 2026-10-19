# WORKORDER-E2 — the local twisted integral at an unramified place (one listed module, two headlines)

**Status: issued 2026-10-18.** Read
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3–§4,
[porting-playbook.md](../../../porting-playbook.md) §3–§5, and
[TOPIC-local-twisted-integral.md](TOPIC-local-twisted-integral.md) (§1–§4 for the cluster,
§6 for Set A's landing record).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

**The set: Set B of the `EisensteinGeneral` local-integral cluster — the unramified side, two
headlines, 443 raw pin lines / ≈330 net new after Set A's engine.** Unlike Set A this set's
machinery has **no other consumer**, so it is all written into the one module that the checker
diffs, rather than split into an engine and a façade.

## 1. Scope

One new file:

`FLTForHuman/EisensteinGeneral/LocalUnr.lean` — **listed**, holding the machinery (namespace
`EisensteinGeneral.TwistedUnramifiedLocal`, public at the pin names) **and** the two headlines
(namespace `EisensteinGeneral.LocalUnr`, statements verbatim from the wrappers).

Because the whole module is listed and its two pin `S_` files are added to `SOURCES` (the
manager does that wiring), **every** declaration in the module is diffed — that is the point of
the shape here: the machinery is new, unique to this subject, and would otherwise sit unchecked
in a tier-3 engine. Expected checker delta: **+18** (16 machinery + 2 headlines), and the manager
reconciles it against the register.

**Explicitly not this order.** The `LocalRam` trio (Set A, landed — import its engine); the
`LocalUnr.integral_twisted_eq` node (not ready: it needs two unported `LanglandsTunnell` rows);
any other `EisensteinGeneral` row; **any edit to an existing module**.

## 2. Pin sources

Statement authority (state both headlines **verbatim**):

* `Theorems/Thm_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean`
* `Theorems/Thm_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean`

Proofs (read-only, on disk at `~/proj/fermats-last-theorem/P2M/Sol/`):

* `S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean` (297 lines) — the
  machinery at 21–210, the headline's `solution` at 228.
* `S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean` (146 lines) — the
  machinery at 20–95, `solution` at 96.

Both files open `namespace TwistedUnramifiedLocal` with
`variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}` and
`open LanglandsTunnell.TateLocal NumberField.AdelicLevel Filter Topology`; the pin's
`set_option Elab.async false`, `attribute [-instance]` prelude and `p2m_*` scaffolding are not
transcribed.

## 3. The declarations

Machinery — port once each, publicly, at the pin name (the two files share the last three rows'
statements only through the first file's copy):

| pin | declaration | file |
|---:|---|---|
| U1:23 | `valued_uniformizer_zpow` | U1 |
| U1:31 | `isOpen_ball` | U1 |
| U1:44 | `measureReal_integers_pos` | U1 |
| U1:52 | `continuous_addChar_of_level` | U1 |
| U1:108 | `untwisted` (`def`, the `A = B = 1` specialization — **not** the `LocalRam` one) | U1 |
| U1:114 | `untwisted_of_le` | U1 (+ U2) |
| U1:120 | `untwisted_of_lt` | U1 (+ U2) |
| U1:127 | `norm_mul_natCast_cpow` | U1 |
| U1:133 | `re_neg_two_mul_add_one` | U1 |
| U1:136 | `integrable_untwisted` (52 lines) | U1 |
| U1:188 | `normChar` (`def`) | U1 |
| U1:198 | `normChar_apply` | U1 |
| U1:201 | `ofReal_norm_untwisted_mul` (27 lines) | U1 |
| U2:30 | `charExt_inv_eq_of_valued_eq` (15 lines) | U2 |
| U2:64 | `untwisted_add_of_lt` (16 lines) | U2 |
| U2:80 | `untwisted_add_of_le_one` (16 lines) | U2 |

**Substitutions — import, never re-prove:**

| pin name | port home |
|---|---|
| `isCompact_integers` (U1:39) | `NumberField.TateGlobal.LocalZetaUnramified.isCompact_integers` |
| `norm_addChar_of_level` (U1:68) | `EisensteinGeneral.TwistedSmoothLocal.norm_addChar_of_level` (Set A's engine, `EisensteinGeneral/LocalTwisted.lean`) |
| `modulus_eq_of_valued_eq` (U2:24) | `EisensteinGeneral.TwistedSmoothLocal.modulus_eq_of_valued_eq` (same engine) |

Headlines (both `Integrable …` conjunctions or vanishing statements — copy them character for
character from the wrappers):

* `EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq` — the integrand is `L¹`
  **and** the integral of its norm is `μ(𝒪) · (1 - ‖χϖ‖ q^{-(2s+1)}) · (1 - ‖χϖ‖ q^{-2s})⁻¹`;
* `EisensteinGeneral.LocalUnr.integral_twisted_eq_zero_of_exp_lt` — it vanishes when
  `exp n < |ξ|`.

The pin's headline copies are `private theorem solution` in the `TwistedUnramifiedLocal`
namespace with `open TwistedUnramifiedLocal … in`; the port states them at the wrappers' dotted
names, with `open EisensteinGeneral.TwistedUnramifiedLocal` in front so the proofs transcribe.

## 4. Imports

* `FLTForHuman.EisensteinGeneral.LocalTwisted` — Set A's engine (`norm_addChar_of_level`,
  `modulus_eq_of_valued_eq`);
* `FLTForHuman.NumberTheory.NumberField.TateGlobal.LocalZetaUnramified` — `isCompact_integers`;
* `FLTForHuman.LanglandsTunnell.TateLocalConstantsAt` — `higherUnitsAt` (needed only if a
  statement or proof names it);
* `FLTForHuman.LanglandsTunnell.TateLocalZeta` — `charExt`, `modulus`, `modulus_adicCompletion_eq_nnnorm`
  comes from `TateGlobal/NormIntegrable.lean` if the proofs use it;
* mathlib for `AddChar`, `Measure.real`, `Complex.norm_cpow_eq_rpow_re_of_pos`,
  `Complex.ofReal_cpow`, `Complex.mul_cpow_ofReal_nonneg`, `Nat.cast_pos`,
  `NumberField.HeightOneSpectrum.one_lt_absNorm`.

Verify each name in its port home before use; if a statement is not the pin's, **stop and
report** (do not adapt a statement).

## 5. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect. Diagnose
> it (`set_option diagnostics true`, `trace.Meta.synthInstance true` on that one declaration, in
> a scratch copy under `tmp/`), fix the inference, re-run. Never raise `maxHeartbeats`, never add
> a module `set_option maxHeartbeats`. When the file is done,
> `flock .lake/flt_build.lock timeout 300 lake build <module>`. **Never a bare whole-tree
> `lake build`.**

**Hub prohibition.** Do not edit `EisensteinGeneral/*.lean` (Set A's three modules are frozen),
`LanglandsTunnell/*`, `TateGlobal/*`, `NumberField/AdelicLevel/*`, or any other existing module.
If a promotion seems needed, **stop and report** with the declaration, host and
`build_ladder.py --edit` price.

## 6. Verification

| check | expected |
|---|---|
| tier-0 edit loop | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats`/`set_option Elab.async` |
| tier-1 `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.EisensteinGeneral.LocalUnr` | green |
| checker before (the manager's) | 10370 identical / 0 mismatched / 0 missing / 42 own / 294 registered (10706) |
| checker after (the manager wires) | **10388** identical — delta **+18**, exactly this module's public surface |
| `#print axioms` on both headlines | `[propext, Classical.choice, Quot.sound]` |
| `git status` | only the new module |

## 7. Report shape

1. The module path, line count, and every declaration it holds.
2. The import block with one clause per import.
3. Every proof adaptation (pin line → port spelling) with pin line numbers; what failed first.
4. The three substitutions: the exact port name used and the statement you read.
5. Tier-0 and tier-1 results with wall times.
6. Anything left undone, any deviation, and any place where you stopped rather than edit an
   existing module.

## 8. Results as landed (2026-10-18)

| | |
|---|---|
| module | `EisensteinGeneral/LocalUnr.lean` — 408 lines, **18** public declarations, listed |
| contents | 16 machinery (`EisensteinGeneral.TwistedUnramifiedLocal`) + 2 headlines (`EisensteinGeneral.LocalUnr`) |
| checker | 10,370 → **10,388 identical**, 0 mismatched / 0 missing, 10,724 checked (delta **+18**, as §6 predicted) |
| promoted-from-pin-private | 702 → 718 — the 16 machinery rows, `private` in both pin files, matched through the dotted-name fallback |
| axioms | both headlines `[propext, Classical.choice, Quot.sound]` |
| tier-0 / tier-1 | exit 0 / 0 warnings; `lake build FLTForHuman.EisensteinGeneral.LocalUnr` green, 3,803 jobs |
| register | unchanged (136 modules / 4134 public): the module is listed, so its 18 declarations are tier 1 |
| existing modules edited | none |

Deviations from the order, all recorded:

1. **One import added**: `TateGlobal/WeylUnramified.lean` for
   `integral_unramifiedWeylIntegrand_adicCompletion`, which `integrable_untwisted` and the first
   headline consume — the order's §4 list missed it (it named the *ramified* twin instead).
2. **Two §4 imports dropped as unused**: `TateLocalConstantsAt` (no declaration of this set names
   `higherUnitsAt` — the unramified hypotheses are the pointwise `χ u = 1` form) and
   `NormIntegrable` (`modulus_adicCompletion_eq_nnnorm` is inside the substituted
   `modulus_eq_of_valued_eq`). Both stay transitively available through `LocalTwisted`.
3. **Two proof-shape adaptations of the port, not the pin**: the headlines are declared at root
   after `end EisensteinGeneral` (the `LocalRam.lean` shape), and the engine's `untwisted` is
   **not** opened at root — the two `untwisted` definitions (3-arg unramified, 5-arg ramified)
   would tie in `Ambiguous term`, so the two engine names are qualified instead.
4. No mathlib `v4.34.0` drift fixes were needed at all in this module: `Valuation.map_add_eq_of_lt_right`,
   `Valuation.map_add_le_max'`, `Complex.norm_cpow_eq_rpow_re_of_pos`, `Complex.ofReal_cpow`,
   `AddChar.map_add_eq_mul`, `integral_add_left_eq_self` and the `WithZero.exp_*` family all
   resolve as in the pin.
