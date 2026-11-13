# SET-AF61 — the level-one obstruction for a Hecke coset eigenfunction

**Status: LANDED (2026-11-13).** Read off the D–S shelf after SET-AF60. The
sixty-first set of the column, dispatched **in parallel** with SET-AF60 (disjoint files).

**1 row / 229 silo / ≈220 net** in **one new module**. It is the first attempt of the day that had to be
re-cut: the Tate-local modulus row was scaffolded first and **withdrawn** (§1.1, FR-0198), so this set
carries the next clean row instead.

| # | row (`AutomorphicForm.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1/1 | new `Cusp/LevelBotObstruction` |

## 0. The read

| figure | value |
|---|---:|
| `needed [F terminal]` | **666 / 286,665** |
| frontier F | 1,751 / 840,887 |
| ready rows, all namespaces | **25 / 5,060** |
| `AutomorphicForm` demand | 235 / 110,135 |

`--selfcheck` unchanged (MD-005's ten + MD-006's one, neither cited here).

## 1. What the set says

A function that is a Hecke coset eigenfunction at **trivial level** — eigen under every `heckeGen` and
living in `levelOne _ K ⊥ ⊓ finiteAdelicGL2Subgroup K` — is zero. The proof reduces the level-one group
to the mirabolic `mirabolicFin` (`levelOne ⊥ ⊓ top ⊆ mirabolicFin`, `mem_mirabolicFin_iff`), computes the
double-coset structure (`doubleCoset_mono`, `doubleCoset_subset_of_le`, `heckeGen_mem_mirabolicFin`), and
contradicts the Hecke coset system of a local representation
(`HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen`). Thirteen public prelude rows and the
headline.

### 1.1 The withdrawal that preceded it — the Tate-local modulus row (FR-0198)

`LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` (305,
lev 1/7) was the day's obvious next story: it shares its premise with the 100-line measure row, and it has
no cap override. It was scaffolded (`LanglandsTunnell/TateLocalHaarInvariance.lean`, 91 lines, elaborating
and checker-clean) and then **withdrawn**, because its prelude row `integral_comp_inv` inherits two
overlapping instance parameters from the section (`[μ.IsAddHaarMeasure] [μ.Regular]`, the second implying
the first's `IsFiniteMeasureOnCompacts`) and Lean 4.34's `linter.overlappingInstances` fires. The port's
triple — statement frozen by the checker, never silence a linter, zero warnings — has no legal exit for a
statement the *pin* spells redundantly: removing the binder is a statement change (MISMATCH), `omit` is
the same thing, and a `set_option` is the forbidden silencer. That row is a **reviewer's** decision (an
accepted-warning class, a checker marker, or a `own:` row with the type repaired), and it is registered in
[../../logs/frictions.md](../../logs/frictions.md) FR-0198 rather than quietly forced.

### 1.2 What the set does not cut

The four remaining `AutomorphicForm` ready rows (content/height 333, `rationalCentreUnipotent` 179, the
character-matching row 113, the Siegel-centre covering 30), the two Tate-local rows above, and the rest of
the shelf as SET-AF58 §1.1 lists it.

## 2. The price

| figure | SET-AF61 |
|---|---:|
| raw `S_` lines | 229 |
| declarations | 14 (13 public prelude rows + the headline) |
| `twin_scan` | `new` |

## 3. The home and the manager's landed layer

`AutomorphicForm/Adelic/Cusp/LevelBotObstruction.lean` — 135 lines, 12 `sorry`s, **14 ok / 0 mismatch /
0 missing**, builds silent (3,871 jobs). The pin's two-line machine-token label (`Ws20` / `LevelBot`) is
rectified to the single word namespace `LevelBotObstruction`; the thirteen prelude rows are public in the
pin and stay public here, so the module's whole surface is checker-visible.

**Two scaffold findings, both the same shape**: the generated import block did not reach
`AdelicDock.finEmbed`/`AdelicGL2`'s vocabulary or `localRepInf`, and — the reason the errors looked
unrelated — **a failed `open` command silently kills the rest of the line's opens**, so
`open … AutomorphicForm.CuspidalConstituent` failing made `AdelicGL2`/`FiniteAdeleRing` read as unknown
identifiers twenty lines later. The module now imports `NumberTheory/AdelicDock/LocalEmbedding.lean`,
`RepTheory/LocalLanglands/HeckeCosetLocal.lean` and `Cusp/Constituent.lean`, and opens
`NumberField.SiegelVolume`, `HeckeIntegralSeam`, `LocalGL2`, `AdelicDock` — the pin's own list.

## 4. The order and the gates

One dispatch: `tmp/af61/WORKORDER-AF61A-level-bot.md`. The gates are the recipe's §6, written into the
order: no tree build; the edit loop at `-DmaxHeartbeats=200000`; `lake build <module>` under
`flock`/`timeout`; `check_port` unchanged (**14 ok**); `#print axioms` on the headline; zero warnings; no
`sorry`; no `set_option` beyond `autoImplicit false`; no silencer; `dedup`/`move_dead` clean; one consumer
zone.

## 5. The shelf effect, measured (statements in)

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 666 / 286,665 | **665 / 286,436** | 665 / 286,436 ✓ |
| frontier F | 1,751 / 840,887 | **1,752 / 841,116** | +229 ✓ |
| ready rows | 25 / 5,060 | **25 / 4,887** | — |

**One row readied by the scaffold**: `AutomorphicForm.isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf`
— the isotypic-carrier vanishing that the level-one obstruction's `mirabolicFin` reduction feeds.

## 6. The landing record (2026-11-13)

One row, one module, **135 written proof lines** (135 → 270), 12 `sorry`s → **0**, no imports and no
`set_option` added, statements untouched (all thirteen prelude rows and the headline verified against the
pin by the checker).

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `Cusp/LevelBotObstruction.lean` | 135 → **270** | 14 | 12 → **0** | 3,871 jobs, 4.4 s, silent | **14 ok / 0 / 0** | clean |

`dedup --within` (all tiers): 0 clusters, 0 removable. `move_dead --dry-run`: 0 declarations, 0 lines.
Silent at 10,000 heartbeats (first failures at 6,000), so nothing is near the 200,000 gate. Consumer zone
`spec/AutomorphicFormSetAF61AConsumer.lean` (4 executed compositions — the row spent as `φ = 0`, then
pointwise, then turned on the **zero function** to conclude that *no* Hecke coset system exists at trivial
level for any `reps`, and then as the negated existential): **0 errors**, silent. Zone C is the sharpest
reading of the row: the obstruction is provably not in the eigen-equation.

Three proof-shape deviations, all recorded by the worker: the pin's four-slot `obtain` against the
(identical) two-plus-two-field `IsLevelOneMatrix`/`IsLevelZeroMatrix`; the pin's `open Ws20.LevelBot in`
having no port counterpart, so the prelude names are qualified in the body; and the headline's tail, where
the pin's `haveI : Finite (𝓞 F ⧸ v.asIdeal)` + `Nat.card_eq_fintype_card`/`Fintype.card_fin` route is
unavailable (a `Prop`-class `haveI` trips the style linter, and the port registers no `Finite → Fintype`
instance — verified by `synthInstanceFailed`) and is replaced by
`hfin` + `@Nat.card_le_card_of_injective _ _ hfin f hfinj` + `Nat.card_fin` + `omega`, with no silencer
and no statement change. That last one is recorded as FR-0199: the second pin tail this session whose
route leaned on an instance the port does not register.

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf17.json
python3 ../tmp/af61/gen.py
cd .. && python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/Cusp/LevelBotObstruction.lean
```
