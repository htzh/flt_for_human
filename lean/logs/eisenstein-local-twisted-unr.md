# The local twisted integral at an unramified place — one listed module, two headlines

**Status: landed 2026-10-18.** One new module, green with 0 errors and 0 warnings:
`FLTForHuman/EisensteinGeneral/LocalUnr.lean` — 408 lines, **18 public declarations**: the
sixteen machinery lemmas (namespace `EisensteinGeneral.TwistedUnramifiedLocal`, at the pin names)
and the two headlines (namespace `EisensteinGeneral.LocalUnr`, statements verbatim from the
wrappers). Listed: **all 18 are checked**.

Checker **10,370 → 10,388 identical**, 0 mismatched / 0 missing, 10,724 port declarations
checked; 718 of the identical are now "promoted from pin-private declarations" (was 702) — the
16 machinery rows, which are `private` in the pin. `#print axioms` on both headlines is
`[propext, Classical.choice, Quot.sound]`. No existing module was edited.

| | |
|---|---|
| headline 1 | `EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq` |
| headline 2 | `EisensteinGeneral.LocalUnr.integral_twisted_eq_zero_of_exp_lt` |
| pin proofs | `S_…_LocalUnr_integrable_twisted_and_integral_norm_eq.lean` (297 lines) and `S_…_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean` (146) |
| net new | 374 standalone (443 raw), ≈330 marginal on Set A's engine |
| structure | one **listed** module: machinery + headlines (no tier-3 engine) |
| build | tier-0 exit 0 / 0 warnings; tier-1 green, 3,803 jobs |

## 1. What the two headlines say

The unramified side of the same local computation
([logs/eisenstein-local-twisted-ram.md](eisenstein-local-twisted-ram.md) §1), with the twisted
smooth function specialized to `A = B = 1`:

* `integrable_twisted_and_integral_norm_eq` — for an unramified `χ` (trivial on the units), a
  continuous additive character `ψ` of level `n`, and `‖χϖ‖·q^{-2s} < 1`, the integrand
  `1_𝒪 + 1_{𝒪ᶜ}·χ⁻¹·|·|^{-(2s+1)}` twisted by `ψ(-(ξ·))` is integrable, and
  ```
  ∫ ‖untwisted χ s x · ψ(-(ξ x))‖ ∂μ
    = μ(𝒪) · (1 - ‖χϖ‖ q^{-(2s+1)}) · (1 - ‖χϖ‖ q^{-2s})⁻¹
  ```
* `integral_twisted_eq_zero_of_exp_lt` — the same integral is `0` when `exp n < |ξ|`.

The mechanism is the same shell decomposition as the ramified case — the unit ball contributes
`μ(𝒪)`, each shell `{|x| = exp k}` contributes `χ⁻¹(u)` times a geometric factor, and the
`χ⁻¹`-average over the unit group vanishes unless the additive character's level reaches the
shell, which is what `untwisted_add_of_lt` / `untwisted_add_of_le_one` pin down.

## 2. Why one listed module and not engine + façade

Set A's shape (tier-3 engine + thin listed façade) exists because its engine is imported by
three headlines *and* by the `LocalUnr` pair. Set B's machinery — `untwisted` (the `A = B = 1`
specialization), `untwisted_of_le/lt`, `integrable_untwisted`, `normChar`,
`ofReal_norm_untwisted_mul`, `valued_uniformizer_zpow`, the additive-character continuity lemmas,
`charExt_inv_eq_of_valued_eq`, `untwisted_add_of_lt`, `untwisted_add_of_le_one` — has **no other
consumer**. Hiding it in a tier-3 engine would leave 16 declarations unchecked with no future
importer to justify the economy; listing the module and its two `S_` files in `SOURCES` puts all
18 under the checker for the price of two `SOURCES` entries. That is the trade the playbook's
§4.1 leaves open, and here it goes the other way from Set A.

This is also the first set in the column where the checker's **promoted-from-pin-private**
mechanism carries most of the delta: the machinery is `private` in both pin files, so 16 of the
18 new rows are matched through the dotted-name fallback rather than by an exact pin name.

## 3. The dedup

The two pin files share `untwisted`, `untwisted_of_le`, `untwisted_of_lt` (19 duplicate lines),
and both re-prove `modulus_eq_of_valued_eq` and `isCompact_integers`, which the port already
homes elsewhere. Written once here; substituted:

| pin name | port home |
|---|---|
| `norm_addChar_of_level` | `EisensteinGeneral.TwistedSmoothLocal.norm_addChar_of_level` (Set A's engine) |
| `modulus_eq_of_valued_eq` | `EisensteinGeneral.TwistedSmoothLocal.modulus_eq_of_valued_eq` (Set A's engine) |
| `isCompact_integers` | `NumberField.TateGlobal.LocalZetaUnramified.isCompact_integers` |

## 4. Proof adaptations (pin → v4.34.0), statements verbatim

The same family as Set A's, plus one of its own:

1. `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; `zero_le'` → `zero_le`.
2. `modulus_adicCompletion_eq_nnnorm`'s binder arity (`F`, `v` implicit in the port).
3. One `haveI : Finite …` replaced by term mode (the `linter.style.haveILetI` lint; no
   `set_option` was needed).
4. The pin's `set_option Elab.async false` is not transcribed.

## 5. Verification

| check | result |
|---|---|
| tier-0 `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` | exit 0, **0 warnings** |
| tier-1 `flock … lake build FLTForHuman.EisensteinGeneral.LocalUnr` | green, 3,803 jobs |
| checker before | 10,370 / 0 / 0 / 42 own / 294 registered (10,706) |
| checker after | **10,388** / 0 / 0 / 42 own / 294 registered (10,724) — delta **+18** = 16 machinery + 2 headlines |
| `#print axioms` | both headlines `[propext, Classical.choice, Quot.sound]` |
| register | unchanged at 136 modules / 4134 public (the module is listed, so its 18 declarations are tier 1, not tier 3) |
| `git status` | the new module, `spec/check_flt_statements.py`, the notes |

## 6. Residuals

* `EisensteinGeneral.LocalUnr.integral_twisted_eq` (601 pin lines) — the *general* unramified
  formula, of which `integral_twisted_eq_zero_of_exp_lt` is the vanishing special case — needs
  two unported `LanglandsTunnell` rows (`LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp`
  and one more; 249 raw lines). It is the natural next cut of this family.
* The `LocalCorrection` pair (`exists_forall_norm_corrOn_le_of_le_re`, 107 lines;
  `norm_corrOff_le_of_le_re`, 66) is on the shelf but not ready.
* The `AutomorphicForm` consumers of the five local headlines (the Godement–Eisenstein local
  factor assembly) are a later column's.

## 7. Reproduce

```bash
cd lean
timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/EisensteinGeneral/LocalUnr.lean
flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.EisensteinGeneral.LocalUnr
timeout 600 python3 spec/check_flt_statements.py | tail -1   # 10388 identical
```
