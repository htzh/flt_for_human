# The local twisted integral at a ramified place — definition gate, promotions, two engines, three headlines

**Status: Set A landed 2026-10-18.** Four steps, all green:

1. **The definition gate** — `FLTForHuman/LanglandsTunnell/TateLocalConstantsAt.lean`, the pin's
   `Def_LanglandsTunnell_TateLocalConstantsAt` whole (155 pin lines, 21 declarations:
   `higherUnitsAt`, `HasConductorExponentAt`, `conductorExponentAt`, `localLFactorAt`,
   `localEpsilonAt` and their lemmas), listed and checker-diffed (**+21**).
2. **Three promotions** — `setOf_valued_sub_le_mem_nhds` and `setOf_valued_sub_lt_mem_nhds` in
   `TateGlobal/WeylSmooth.lean`, `ofReal_pow_cpow` in `TateGlobal/WeylShell.lean` (**+3**).
3. **A dedup the gate forced** — `WeylSmooth.lean` carried a second copy of
   `LanglandsTunnell.TateLocal.higherUnitsAt`; it is now imported from the gate (**−1**, the
   double count).
4. **Set A** — two tier-3 engines and one listed façade: `EisensteinGeneral/LocalTwisted.lean`
   (527 lines, 25 declarations — the 486-line prelude the pin writes twice), 
   `EisensteinGeneral/LocalRamShells.lean` (265 lines, 9 declarations), and
   `EisensteinGeneral/LocalRam.lean` (354 lines, **three headlines**, **+3**).

Checker **10,344 → 10,370 identical** (+21 +3 −1 +3), 0 mismatched / 0 missing, 10,706 port
declarations checked. `#print axioms` on all three headlines is
`[propext, Classical.choice, Quot.sound]`. No module of another subject was edited; the only
existing-module edits are the four of steps 2–3, which are the manager's own hub work.

| | |
|---|---|
| cluster | five ready rows of `EisensteinGeneral` (2,134 raw `S_` lines, 1,302 net new) |
| this set | the three `LocalRam` rows (1,691 raw lines) |
| structure | 1 listed definition module + 3 promotions + 2 tier-3 engines + 1 listed façade |
| engine declarations | 25 + 9 = 34, all registered with a pin line |
| build | gate 4.7 s; wave (WeylSmooth/WeylShell/WeylUnramified) 3,795 jobs ≈20 s; Set A 3,803 jobs |
| register | 134 → 136 modules, 4100 → 4134 public declarations, 3796 → 3830 with a pin counterpart |

## 1. What the three headlines say

At a finite place `v` of a number field `F`, let `χ` be a continuous multiplicative character
of the completion with conductor `≤ c` (`χ = 1` on `higherUnitsAt F v c`), `ϖ` a uniformizer,
`ψ` an additive character of level `n`, and let `A` be an `L¹` function on the unit ball and `B`
a function constant on `ϖᵐ`-balls. Then `untwisted χ s A B · ψ(-(ξ·))` — the function that is
`A` on `𝒪` and `charExt χ⁻¹ y · |y|^{-(2s+1)} · B(y⁻¹)` off it — is integrable
(`integrable_twisted_smooth`), and

```
∫ untwisted χ s A B x · ψ(-(ξ x)) ∂μ
  = ∫_{𝒪} A x · ψ(-(ξ x)) ∂μ
    + ∑ k ∈ Icc 1 (max (m - 1) (n + c - e)),
        (q^{-(2s+1)})^k · ∫_{|x| = exp k} χ⁻¹(x) · B(x⁻¹) · ψ(-(ξ x)) ∂μ
```

(`integral_twisted_smooth_eq`, with `|ξ| = exp e`), and it is `0` when `ξ` is deeper than
`exp (n + max m c)` (`integral_twisted_smooth_eq_zero_of_exp_lt`). The shells
`{|x| = exp k}` are where `untwisted` is constant (`untwisted_add_eq_of_sphere`), the geometric
factor is `q^{-(2s+1)}` per shell, and the cut-off `max (m-1) (n + c - e)` is what the three
level conditions — `B`'s `ϖᵐ`-invariance, `ψ`'s level `n`, `χ`'s conductor `c` — allow.

## 2. The definition gate

Nothing can be *stated* before `higherUnitsAt` exists: all three statements quantify over it,
and the pin's `Def_LanglandsTunnell_TateLocalConstantsAt` (155 lines) is one of the pin
`Definitions/` modules the port had never homed. It has no `Theorems/` wrapper, so it is its own
statement authority and was homed **whole** and **listed** — the same shape as the centre-cut
and arch-Casimir definition gates (playbook §2.3: home the whole node, not the block a consumer
reaches).

Its two pin imports are the port's `LanglandsTunnell/TateLocalZeta.lean` (`modulus`, `charExt`,
`localZeta`, `localGammaAt`) and `NumberField/AdelicLevel/HeckeGen.lean` (`uniformizerUnit`, the
pin's `Def_NumberField_AdelicLevel`). Two proof drift: `if_pos`/`if_neg` →
`ite_eq_left`/`ite_eq_right`.

## 3. The promotions, and the collision they exposed

The pin re-copies three private helpers into its `S_` files. All three already lived in the port
as `private` declarations in **listed** modules, so promoting them (playbook §4(b): the new
consumers import them) both removes the duplication and puts them under the checker:

| declaration | host | lines |
|---|---|---:|
| `setOf_valued_sub_le_mem_nhds` | `TateGlobal/WeylSmooth.lean` | 14 |
| `setOf_valued_sub_lt_mem_nhds` | `TateGlobal/WeylSmooth.lean` | 15 |
| `ofReal_pow_cpow` | `TateGlobal/WeylShell.lean` | 8 |

`ofReal_pow_cpow` is worth a remark: the port has a *different* lemma of the same name in
`NumberField/CompletedDedekindZeta/Mellin.lean` (`((a : ℂ) ^ n) ^ z = (a : ℂ) ^ (n * z)`), and
`WeylShell`'s copy is the pin's `(((a ^ k : ℝ)) : ℂ) ^ s = (((a : ℝ) : ℂ) ^ s) ^ k`. The
promotion is of the pin's statement; the homonym is recorded in the docstring so a later
`port_advise` run does not read them as duplicates.

**The collision.** `WeylSmooth.lean` already declared `LanglandsTunnell.TateLocal.higherUnitsAt`
— from the `AutomorphicForm` local-intertwining landing, whose docstring said the declaration's
natural home is exactly the module this set homes, "a later refactor round should move it
there". Homing the pin's definition module therefore produced two declarations of one name, and
no module could import both (Lean: *environment already contains
`'LanglandsTunnell.TateLocal.higherUnitsAt'`*). The work order's subagent hit it on the first
import; the fix is the refactor round: the copy in `WeylSmooth.lean` is deleted, `WeylSmooth.lean`
imports the gate instead, and the wave (`WeylSmooth`/`WeylShell`/`WeylUnramified`, 3,795 jobs,
≈20 s) is green. Both copies were the pin's statement, so nothing changed semantically — the
checker count moved by −1 because the declaration had been counted once per host.

**Lesson for the column.** A definition gate can collide with a declaration an earlier landing
already homed "temporarily"; check for the name before wiring (`grep -rn "def <name>\b"`), and
treat the earlier docstring's "later refactor round" as part of the gate's price.

## 4. Set A: the dedup

The two big pin files (`S_…_integral_twisted_smooth_eq.lean` 864 lines and
`S_…_integrable_twisted_smooth.lean` 567) share a **byte-identical 486-line prelude**
(lines 24–486 ≡ 26–488; the only difference in that range is the `section` header at its end),
and the third file (`…_zero_of_exp_lt.lean`, 260) re-proves three of its declarations verbatim.
Written once:

| module | contents | declarations |
|---|---|---:|
| `EisensteinGeneral/LocalTwisted.lean` (527) | the shared prelude: `setOf_valued_sub_*` (imported), `valued_uniformizer_*`, `continuous_of_depth`, `charExt_inv_eq_of_sub_le`, `continuousOn_charExt_inv`, `continuous_addChar_neg_mul`, `norm_addChar_of_level`, `untwisted`, `modulus_eq_of_valued_eq`, `isOpen_integers`, `isCompact_integers` (imported), `continuousOn_of_valued_eq`, `continuousOn_modulus_cpow`, `compl_integers_subset`, `aestronglyMeasurable_untwisted`, `absChar`, its lemmas, `absNorm_pos`, `hs_absChar`, `norm_untwisted_le`, `integrableOn_norm_add_one`, `charExt_absChar_inv_eq`, `integrable_dominator` | 25 |
| `EisensteinGeneral/LocalRamShells.lean` (265) | `integrable_twisted_aux`, the `isOpen_setOf_valued_{le,lt}` / `measurableSet_setOf_{valued_eq,exp_lt}` shell sets, `toAdd_unzero_exp`, `coe_modulus_of_valued_eq`, `untwisted_add_eq_of_sphere`, and file C's `untwisted_add_eq` | 9 |
| `EisensteinGeneral/LocalRam.lean` (354) | the three headlines at the wrappers' dotted names | 3 (**listed**) |

So the 1,691 raw lines of the trio are ≈1,000 net new, of which 486 are the prelude that would
otherwise have been written twice, and the façade is 306 lines of headline proofs.

## 5. Proof adaptations (pin → v4.34.0), statements verbatim

1. `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `zero_le'` → `zero_le` (both in mathlib
   `v4.34.0`).
2. The pin's `AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion` is
   the port's `NumberField.TateGlobal.WeylSmooth.integral_smoothWeylIntegrand_adicCompletion`.
3. `modulus_adicCompletion_eq_nnnorm F v x` → `modulus_adicCompletion_eq_nnnorm x` (the port's
   copy takes `F`, `v` implicit).
4. `absNorm_pos`'s `haveI : Finite …` became the term-mode `Ideal.finiteQuotientOfFreeOfNeBot`
   (the `haveI` tripped `linter.style.haveILetI`; no `set_option` was needed).
5. `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` in the definition gate.

## 6. Verification

| check | result |
|---|---|
| tier-0 all four modules | exit 0, **0 warnings** |
| tier-1 `… lake build FLTForHuman.EisensteinGeneral.LocalRam` | green, 3,803 jobs |
| tier-1 gate + wave | green, 3,795 jobs |
| checker | **10,370 identical** (was 10,344), 0 mismatched / 0 missing, 10,706 checked: +21 gate, +3 promotions, −1 dedup double-count, +3 headlines |
| `#print axioms` | all three headlines `[propext, Classical.choice, Quot.sound]` |
| forbidden tokens | none (`sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`maxHeartbeats`; the pin's `set_option Elab.async false` is not transcribed) |
| register | `unwired_register.py --check` current; 136 modules / 4134 public / 3830 with a pin counterpart |
| `git status` | the gate, Set A's three modules, `WeylSmooth.lean`, `WeylShell.lean`, the two spec files, the topic and the orders |

## 7. What remains — Set B

The **unramified pair** (`EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq`,
`…integral_twisted_eq_zero_of_exp_lt`) is priced at 443 raw / 374 standalone net new (≈330
marginal: Set A's engine already homes `norm_addChar_of_level`, and `modulus_eq_of_valued_eq`).
Its order is [WORKORDER-E2-local-twisted-unr.md](WORKORDER-E2-local-twisted-unr.md): **one listed
module** — the machinery has no other consumer, so listing it puts 18 declarations under the
checker instead of hiding them in a tier-3 engine. Then
`EisensteinGeneral.LocalUnr.integral_twisted_eq` (601 lines) once its two `LanglandsTunnell`
premises land, and the `LocalCorrection` pair (173 lines, not ready).

## 8. Reproduce

```bash
cd lean
timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/LanglandsTunnell/TateLocalConstantsAt.lean
flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.EisensteinGeneral.LocalRam
timeout 600 python3 spec/check_flt_statements.py | tail -1   # 10370 identical
python3 tools/deps/unwired_register.py --check               # current
```
