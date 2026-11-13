# SET-AF60 — the `Kf`-smooth predicate: the away reduction and the compact-open factorization

**Status: LANDED (2026-11-13).** Read off the D–S shelf after SET-AF59. The sixtieth
set of the column, and the last `AutomorphicForm` story the AF waves left as a *pair*: the two rows of
the `IsKfSmooth` subject, both ready, one premise each, no shared premise but the same predicate.

**2 rows / 317 silo / ≈300 net** in **one new module**, one order.

| # | row (`AutomorphicForm.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1/3 | new `Adelic/KfSmoothReduction` |
| **B** | `IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq` | 108 | 1/1 | same module |

## 0. The read

| figure | value |
|---|---:|
| `needed [F terminal]` | **668 / 286,982** |
| frontier F | 1,749 / 840,570 |
| ready rows, all namespaces | **27 / 5,377** |
| leaves, all namespaces | **183 / 46,068** |
| `AutomorphicForm` demand | 237 / 110,452 |

`--selfcheck` unchanged (MD-005's ten + MD-006's one, neither cited here).

## 1. What the set says

- **A** — a `Kf`-smooth `f` is unchanged when its argument is multiplied by an element of a small
  enough neighbourhood of `1` inside `maximalCompactAway` — the neighbourhood comes from
  `exists_maximalCompactAway_subset_of_mem_nhds_one`, and the row is what lets the archimedean part be
  moved without touching the value.
- **B** — a `Kf`-smooth function factors through the finite variable on a compact-open set of the shape
  `K_f * K_∞ ∩ U N`: `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` supplies the compactness.

### 1.1 What the set does not cut

- The **content/height row** (333), the **level-one obstruction** (229), `rationalCentreUnipotent` (179),
  the character-matching row (113) and the Siegel-centre covering (30): five independent `AutomorphicForm`
  subjects, each its own story.
- The **Tate-local modulus pair** — `TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion`
  (305, lev 1/7) and `TateLocal.measureReal_setOf_valued_le_exp` (100, lev 1/13), which **share** the
  premise `TateLocal.modulus_adicCompletion_eq_nnnorm` (`NumberTheory/NumberField/TateGlobal/NormIntegrable.lean`)
  and are the obvious next story. **Both are held back, for reasons of their own.** The 100-line row's
  pin opens with `set_option maxHeartbeats 4000000` and `set_option synthInstance.maxHeartbeats 400000`
  (the port forbids a per-file cap: an override is a defect marker, not a budget). And the 305-line row
  — scaffolded in a first attempt at SET-AF61 and withdrawn, see
  [../../logs/frictions.md](../../logs/frictions.md) FR-0198 — has a prelude row (`integral_comp_inv`)
  whose section binders carry **two overlapping instance parameters** (`[μ.IsAddHaarMeasure] [μ.Regular]`,
  the second implying the first's `IsFiniteMeasureOnCompacts`); Lean 4.34's `linter.overlappingInstances`
  fires, and the port's triple — statement frozen by the checker, no silencer, zero warnings — has no
  legal exit. That row needs a reviewer's decision (an accepted-warning class or a checker-side marker),
  not a wave.
- The rest of the shelf, as SET-AF58 §1.1 lists it.

## 2. The price

| figure | SET-AF60 |
|---|---:|
| raw `S_` lines | 317 |
| declarations | 19 (A: 12 public prelude rows; B: 5 public prelude rows; + 2 headlines) |
| `twin_scan` | `new` for both |

## 3. The home, and the manager's landed layer

`AutomorphicForm/Adelic/KfSmoothReduction.lean` — 169 lines, 16 `sorry`s, **17 ok / 0 mismatch /
0 missing**, builds silent (3,848 jobs). The pin's token label `RS22` is rectified to the word namespace
`KfSmoothReduction`; B's prelude keeps the pin's real `AutomorphicForm` namespace. Both preludes are
public in the pin and stay public here, so seventeen declarations are checker-visible (fifteen prelude
rows and the two headlines).

**One scaffold finding**: A's statement needs `UnramifiedWhittaker.placeEmbed`, which the generated
import block did not reach; the module now imports `RepTheory/LocalLanglands/UnramifiedWhittaker.lean`
(FR-0181's remedy — the specific import, recorded here).

## 4. The order and the gates

One dispatch: `tmp/af60/WORKORDER-AF60A-kf-smooth.md`. The gates are the recipe's §6, written into the
order: no tree build; the edit loop at `-DmaxHeartbeats=200000`; `lake build <module>` under
`flock`/`timeout`; `check_port` unchanged (**17 ok**); `#print axioms` on both headlines; zero warnings;
no `sorry`; no `set_option` beyond `autoImplicit false`; no silencer; `dedup`/`move_dead` clean; one
consumer zone with an executed composition per headline.

## 5. The shelf effect, measured (statements in)

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 668 / 286,982 | **666 / 286,665** | 666 / 286,665 ✓ |
| frontier F | 1,749 / 840,570 | **1,751 / 840,887** | +317 ✓ |
| ready rows | 27 / 5,377 | **25 / 5,060** | — |

## 6. The landing record (2026-11-13)

One row pair, one module, **195 written proof lines** (169 → 348), 16 `sorry`s → **0**, no imports and no
`set_option` added, statements untouched.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `Adelic/KfSmoothReduction.lean` | 169 → **348** | 19 | 16 → **0** | 3,848 jobs, silent | **17 ok / 0 / 0** | **2/2 clean** |

`move_dead --dry-run`: 0 declarations, 0 lines. Consumer zone
`spec/AutomorphicFormSetAF60AConsumer.lean` (147 lines, **seven** executed compositions: A at a chosen
`k ∈ maximalCompactAway`, at `k⁻¹`, at a product, and at a constant `φ`; B's compact-open invariance, the
"finite variable is invisible on `U`" reading at two points of one coset, and a constant `φ`): **0 errors**,
silent. The whole module is also silent at 10,000 heartbeats.

**`dedup --within` reports one cluster, and it stays.** Fourteen lines, `shape` tier: the prelude's
`apply_mul_eq_of_mem_maximalCompactAway` and its wrapper headline
`apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway`. That is the pin's own
wrapper-over-engine pair (pin `S_…:171` and `Thm_…:11`), both statements frozen and both checker-visible,
the wrapper's body a one-line `exact` — the recipe's "wrapper-over-engine `shape` clusters are the pin's own
pattern and stay, with the reason recorded". Recorded here as the reason. Not removable.

Two proof-level deviations: at v4.34 the pin's `convert … using 1` closes the compactness goal outright
while `rw [this]` cannot match the pp-identical image term, so the set equality is spent as
`Eq.mpr (congrArg IsCompact this) …`; and the pin's file-wide `p2m_open "… FLT.SmoothVectors"` has no
counterpart in the frozen `open` block, so two proof terms are qualified `FLT.SmoothVectors.…`. The
worker also corrected one *manager* error in the brief: the second premise lives at
`AutomorphicForm/Adelic/LevelCompactness.lean:150`, reached through `MaximalCompactFactors`, not in
`NumberTheory/AdelicLevel/Level.lean` — the module header is fixed accordingly.

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf16.json
python3 ../tmp/af60/gen.py
cd .. && python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/KfSmoothReduction.lean
```
