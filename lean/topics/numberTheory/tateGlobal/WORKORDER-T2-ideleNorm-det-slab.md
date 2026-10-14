# WORKORDER-T2 — the `GL₂` idele-norm slab headlines (tier 1)

**Status: landed 2026-10-13** — manager's own work (the set is below the subagent threshold,
playbook §0.2). Results in §8.

The two successors of the just-landed `continuous_ideleNorm_det` wire. Read
[TOPIC-continuous-ideleNorm.md](TOPIC-continuous-ideleNorm.md) §10 (the landing) and
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3 (the workflow) first.
**51 net new lines for two headlines with 9 and 86 project-wide dependents** — the
cheapest high-leverage cut on the ready shelf.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

## 1. Scope

Write **one tier-1 module**, `FLTForHuman/NumberTheory/NumberField/TateGlobalIdeleNormDet.lean`,
holding the two headlines, and wire it (`SOURCES` + `PORT_FILES`). This is manager's work:
the set is below the subagent threshold (playbook §0.2).

**Explicitly not this order.** Any other `NumberField.TateGlobal` row; the modulus family
([../adelicModulus/TOPIC-adelic-modulus.md](../adelicModulus/TOPIC-adelic-modulus.md)); the
two `NumberField.AdeleRing.secondCountableTopology`-gated topology rows (a different subject,
and their readiness is a last-name artifact — see the modulus topic §6.5); any edit to an
existing module.

## 2. The two headlines

| pin `S_` file | net new | headline |
|---|---:|---|
| `P2M/Sol/S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem.lean` | 44 | `NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem` |
| `P2M/Sol/S_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc.lean` | 7 | `NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc` |

Statement authority is the pin wrapper
`Theorems/Thm_NumberField_TateGlobal_{ideleNorm_det_eq_one_of_isCompact_of_mem,measurableSet_setOf_ideleNorm_det_mem_Icc}.lean`.
State each **verbatim from its wrapper** (the checker diffs it):

```lean
theorem NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (u : AdelicGL2 (𝓞 F) F) (hu : u ∈ U) :
    ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1

theorem NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc
    (F : Type) [Field F] [NumberField F] (d₁ d₂ : ℝ) :
    @MeasurableSet (AdelicGL2 (𝓞 F) F) (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F)
      {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}
```

## 3. What the module imports

* `FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm` — the landed
  `NumberField.TateGlobal.continuous_ideleNorm_det`, the only premise of both headlines;
* `FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs` — `ideleNorm`,
  `ideleNorm_pos`, `ideleNorm_mul`;
* `FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear` — `NumberField.AdelicHaar.glBorel`,
  `borelSpace_glBorel`;
* `FLTForHuman.AutomorphicForm.Adelic.Basic` — `AdelicGL2`;
* mathlib for `Matrix.GeneralLinearGroup.det`, `isClosed_Icc`,
  `pow_unbounded_of_one_lt`, `IsBounded.bddAbove`.

No new helper is needed: the pin's two `solution` proofs are 44 and 7 lines and are the
whole content.

## 4. The mathematics

**Slab.** `ideleNorm ∘ det` is continuous, and $`\{x \in \mathbb{R} : x \in [d_1,d_2]\}` is
closed, so its preimage is closed, hence Borel for `glBorel`. (The pin's proof first
installs `glBorel`/`borelSpace_glBorel` as local instances, then
`(isClosed_Icc.preimage (continuous_ideleNorm_det F)).measurableSet`.)

**Compact subgroups have determinant norm 1.** On a compact subgroup `U`,
$`g \mapsto |\det g|`$ is continuous with compact image, hence bounded by some `M`. For
$`u \in U`$, `u ^ n ∈ U` gives $`x^n \le M`$ for all `n`, and `u⁻¹ ^ n ∈ U` gives
$`x^{-n} \le M`; both together force `x = 1`. `ideleNorm_mul` and `ideleNorm_pos` supply
the multiplicativity and positivity.

## 5. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with
> `flock` and bounded with `timeout`. Per wave, build only the wave's affected targets —
> **never a bare whole-tree `lake build`**. A whole-tree build happens once, at the
> session's end, and only with the user's permission.

**Drift surface.** `Matrix.GeneralLinearGroup.det` and `continuous_det` (already used by the
landed façade); `NumberField.AdelicHaar.glBorel`/`borelSpace_glBorel` instance names;
`IsBounded.bddAbove` (the pin uses `(hU.image hcont).isBounded.bddAbove`). Adapt proofs,
never statements.

## 6. Verification

| check | expected |
|---|---|
| tier-0 loop | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| checker before | 9542 identical / 0 mismatched / 0 missing / 38 own (9580) |
| checker after | **9544** identical — delta **+2**, exactly the two headlines |
| one-token mutation on one headline | exactly 1 more `mismatched`, reverted |
| `#print axioms` on both headlines | `[propext, Classical.choice, Quot.sound]` |
| tier-1 `flock … lake build FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet` | green |
| wiring | the two wrappers then their two `S_` files appended last to `SOURCES`; the module appended last to `PORT_FILES` |
| `python3 tools/deps/unwired_register.py --check` | unchanged (tier-1 module) |
| `git status` | only the new module and the two edited spec files |

## 7. Report shape

1. Module path and final line count.
2. Checker before/after with the delta reconciled against the +2 surface; mutation result.
3. `#print axioms` for both headlines; the forbidden-token sweep.
4. Tier-0 / tier-1 results with jobs and times.
5. Any drift adaptation made to a proof.

## 8. Results as landed (2026-10-13)

| | |
|---|---|
| module | `FLTForHuman/NumberTheory/NumberField/TateGlobalIdeleNormDet.lean` — **87 lines, 2 public headlines, 0 `private`** |
| tier 0 | exit 0, **0 warnings** (one narrow `set_option linter.style.haveILetI false in` on the slab headline: its two local instances are load-bearing) |
| tier 1 | `flock … lake build FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet` green |
| checker | **9569 → 9571 identical (+2)**, 0 mismatched / 0 missing / 38 own |
| mutation | `Set.Icc d₁ d₂` → `Set.Ioc d₁ d₂` on the slab headline → exactly **1 mismatched** (9,570), reverted |
| axioms | both headlines `[propext, Classical.choice, Quot.sound]` |
| wiring | the two `Theorems/` wrappers then their two `S_` files appended last to `SOURCES`; the module appended last to `PORT_FILES` |
| existing modules edited | **none** — no promotion, no hub wave |

**The landed headlines.**

* `NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc` — the determinant-norm
  slab `{g | |det g| ∈ [d₁, d₂]}` is Borel for `NumberField.AdelicHaar.glBorel`, because
  `ideleNorm ∘ det` is continuous (the landed `continuous_ideleNorm_det`) and `Icc` is closed.
* `NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem` — every element of a
  compact subgroup of `GL₂(𝔸_F)` has determinant of idelic norm `1`: the compact image of
  $`g \mapsto |\det g|` is bounded by some `M`, and `u ^ n`, `u⁻¹ ^ n ∈ U` give
  `x ^ n ≤ M` and `x⁻¹ ^ n ≤ M` for all `n`, forcing `x = 1`.

Both statements are the pin wrappers' verbatim; the only proof adaptation beyond the
transcription is the house `haveI` linter setting above. The build's one warning — a
pre-existing `this tactic is never executed` at
`AlgebraicCurve/Defs/PlaceCompletion.lean:473` — comes from a dependency, not this module.

**Process note.** This order was executed by the manager directly rather than dispatched: at
51 net lines it is below the playbook §0.2 subagent threshold, and its two `S_` files carry no
private helper and no shared prelude, so there was nothing to delegate. It is the first set of
the round, and its +2 is the `9569 → 9571` step of the round's checker ledger (final: 9582
after the definition gate and the A1/A2 sets).
