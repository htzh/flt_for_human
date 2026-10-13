# The Tate-curve twins and the lurking triplet — `BridgeX`, its mathematics and its port

The `ModularCurve` frontier's step-6 re-read after WORKORDER-F1 put three `tateCurve` rows on the
ready shelf. They are not three subjects: they are two classes of near-identical pin `S_` files —
a **twin pair** and a **triplet** — and the five files share one development. This note is the
group's home: §1 the mathematics, §2 the measurement and the two equivalence classes, §3 the
definition layer (landed), §4 the port structure, §5 the five headlines, §6 risks and negatives.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

Companions: the column note [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §1–§2, the
definition layer's sibling [TOPIC-tate-slots-weight-four.md](TOPIC-tate-slots-weight-four.md) (the
F1 group), and the work order [WORKORDER-F2-tate-curve-twins.md](WORKORDER-F2-tate-curve-twins.md).

## 1. The mathematics

The five files evaluate the **Tate curve `TateCurve.curve (q ^ p)`** and its **point coordinates
`pointX`/`pointY`** at the `p`-th power of the Tate parameter, and identify them with the
`ModularCurve` objects:

* `TateCurve.curve (q ^ p) = tateBase F p` — the Tate curve at `q ^ p` is the base-changed Tate
  curve `tateBase`.
* `TateCurve.pointX (q ^ p) (C c) = (tateToricPoint F p c).1` and the `pointY` counterpart — the
  **toric** point: the `ℓ`-torsion point over the Tate parameter, from
  `Def_ModularCurve_KatzLevelPCusps`.
* `TateCurve.pointX (q ^ p) (C c * q ^ j) = (nonToricPoint F p c j).1` and the `pointY`
  counterpart — the **non-toric** point in the `Γ₀(p)` slot `j`, from `Def_ModularCurve_TateSlots`.

The proofs live in one namespace, `ModularCurve.BridgeX`: `expand` rewrites `q`-series along
`q ↦ q ^ p`; `xfun`/`yfun` are the rational functions `w / (1 - w) ^ 2` and `w ^ 2 / (1 - w) ^ 3`;
`xTerm`/`yTerm` and their summability give `pointX`/`pointY` as absolutely convergent series;
`xSeries_identity`/`ySeries_identity` and `sum_sum_divisors_*` are the divisor reorganisations; and
the two families split at the last step, `pointX_toric`/`pointY_toric` against
`pointX_slot`/`pointY_slot`.

## 2. The measurement and the two equivalence classes

Five pin `S_` files, and two classes under a normalized `diff` (namespace stem folded):

| class | files | lines | normalized diff |
|---|---|---:|---|
| **twin pair** | `S_…_pointX_C_mul_X_pow_eq_nonToricPoint_fst`, `…_pointY_…_snd` | 1,343 each | **2 lines** — the final `solution` conjunct and its `BridgeX` lemma |
| **triplet** | `S_…_curve_X_pow_eq_tateBase`, `S_…_pointX_C_eq_tateToricPoint_fst`, `S_…_pointY_C_eq_tateToricPoint_snd` | 754 / 756 / 756 | **8 / 8 / 2 lines** — the same, for the curve and toric-point headlines |

```bash
cd tools/deps
python3 port_advise.py --nodes ModularCurve.tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst \
  --nodes ModularCurve.tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd \
  --nodes ModularCurve.tateCurve_curve_X_pow_eq_tateBase \
  --nodes ModularCurve.tateCurve_pointX_C_eq_tateToricPoint_fst \
  --nodes ModularCurve.tateCurve_pointY_C_eq_tateToricPoint_snd --json build/tateCurve_all.json
python3 port_plan.py --json build/tateCurve_all.json
```

`port_plan` on all five reports **4,952 raw / 4,838 declaration lines / 3,500 duplicate / 75
declaration groups / 1,338 once-cost / 0 already in the port**, in two shared blocks:

| block | names | lines | files |
|---|---:|---:|---|
| the common `BridgeX` development | 47 | 738 | **all five** |
| the non-toric slot extension | 23 | 573 | the pair only |

(`port_plan`'s in-target factor set shows 46 for the first row: the one it omits is
`expand_coeff_mul`, which is in no headline's dependency closure but **is** in all five files, so
the true shared surface is 47 + 23 = 70.)

So the five files are **one 1,338-line development written up to five times**, and the triplet is
the common block alone: its three kernels (`curve_X_pow_eq_tateBase`, `pointX_toric`,
`pointY_toric`) sit in the 47-name common block, while the pair's two kernels (`pointX_slot`,
`pointY_slot`) are in the 23-name extension. `port_advise` reports **0 substitutions**, 69 shared
names and ≈3,495 removable lines.

## 3. The definition layer (landed)

The five `S_` files import `Def_LaurentSeries_XAdic`, `Def_TateCurve_PointSeries`,
`Def_ModularCurve_TateSlots` (already ported, F1), `Def_ModularCurve_KatzLevelPCusps` and, through
those, `Def_TateCurve_QSeries`, `Def_ModularForm_KatzLevelOne` and `Def_ModularCurve_KatzLevelP`.
All six of the unported ones are now homed **whole** (playbook §2.3), transcribed verbatim:

| pin | port | decls |
|---|---|---:|
| `Def_LaurentSeries_XAdic` | `Algebra/LaurentSeriesXAdic.lean` | 7 |
| `Def_TateCurve_QSeries` | `TateCurve/QSeries.lean` | 32 |
| `Def_TateCurve_PointSeries` | `TateCurve/PointSeries.lean` | 23 |
| `Def_ModularForm_KatzLevelOne` | `ModularForms/KatzLevelOne.lean` | 28 |
| `Def_ModularCurve_KatzLevelP` | `ModularCurve/Defs/KatzLevelP.lean` | 90 |
| `Def_ModularCurve_KatzLevelPCusps` | `ModularCurve/Defs/KatzLevelPCusps.lean` | 37 |

Each is 0-warning at the low cap and text-identical to its `Definitions/` source (declaration
statements, verified with the checker's own parser). The six are appended last to `SOURCES` /
`PORT_FILES`; the checker moves **9318 → 9535 identical** (648 → 656 promoted), 0 mismatched /
0 missing — **+217**, exactly the six modules' declaration count. `qTwist` comes from the already
ported `Defs/Twist.lean` (the pin's `Def_ModularCurve_PhiGen`).

## 4. The port structure

Two tiers, by the port's usual economy.

**Tier 3 — the shared development**, two new modules keeping the pin's `ModularCurve.BridgeX`
namespace:

| module | content | lines |
|---|---|---:|
| `FLTForHuman/ModularCurve/TateCurve/Bridge.lean` | the common `BridgeX` block: `expand` and its coefficient lemmas, `xfun`/`yfun`, `xTerm`/`yTerm` and summability, `xSeries_identity`/`ySeries_identity`, `curve_X_pow_eq_tateBase`, `pointX_toric`, `pointY_toric` | 839 |
| `FLTForHuman/ModularCurve/TateCurve/NonToricSlot.lean` | the non-toric extension: `C_mul_X_pow`, `X_pow_pow_mul_single`, `expand_X'`, `hasSum_expand_gen`, `sum_sum_divisors_{pos,neg,diag}`, `s₁_X_pow'`, `pointX_slot`, `pointY_slot` | 674 |

Both built green at the low cap with **no heartbeat blow-up** (Bridge 3,177 jobs / module 5.6 s;
Slot 3,179 jobs / 5.1 s), the pin's six heartbeat-bump markers dropped; the only proof adaptations
were the v4.34 deprecation renames and three unused-binder references. The five kernels are public
under `ModularCurve.TateCurve.*`. The façade `TateCurve/QPow.lean` states the five wrappers
verbatim; the checker moves **9535 → 9540** (delta +5), 0 mismatched / 0 missing.

`Slot.lean` imports `Bridge.lean`; both import the six definition modules of §3. The pin's
`private` helpers stay `private`; the five kernels are promoted to public
`ModularCurve.TateCurve.<kernel>` (the pin's `private` name is not available publicly, and for the
common three it *is* the headline name, so it cannot be reused).

**Tier 1 — the headline façade** (the manager's):
`FLTForHuman/ModularCurve/TateCurve/QPow.lean`, the five public `ModularCurve.<name>`
statements verbatim from their `Theorems/Thm_ModularCurve_*` wrappers, each a one-line application
of its kernel — the pin's own `solution := BridgeX.*` shape, one namespace deeper.

## 5. The five headlines

| headline `ModularCurve.<name>` | kernel `ModularCurve.TateCurve.<name>` | module |
|---|---|---|
| `tateCurve_curve_X_pow_eq_tateBase` | `curve_X_pow_eq_tateBase` | Bridge |
| `tateCurve_pointX_C_eq_tateToricPoint_fst` | `pointX_toric` | Bridge |
| `tateCurve_pointY_C_eq_tateToricPoint_snd` | `pointY_toric` | Bridge |
| `tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst` | `pointX_slot` | Slot |
| `tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd` | `pointY_slot` | Slot |

The checker delta is exactly +5.

## 6. Risks and recorded negatives

* **No hub edit.** Two new tier-3 modules plus one tier-1 façade; no existing Lean module is
  touched. The def layer (§3) is already in.
* **Build-time blow-up is the named risk.** The pin's `hasSum_expand` (93 lines) and
  `sum_sum_divisors_pos`/`_neg` (94 lines each) are the long `Finset`/`tsum` reorganisations, and
  `pointX_*`/`pointY_*` are their series consequences. The low `maxHeartbeats=200000` cap is the
  instrument; a declaration that will not fit is fixed by instance inference, never by raising the
  cap.
* **Statements are the wrappers'.** The `Theorems/Thm_ModularCurve_*` wrapper is the checker's
  statement authority; the façade uses the wrapper binders.
* **Recorded negative: the five `S_` files are not ported.** Their only non-shared content is the
  `solution` headline, which is the façade; `SOURCES` lists them only to supply the pin's public
  prelude rows and the kernel statements.
* **The triplet was found by scanning the neighbourhood, not the shelf.** `frontier.py` showed
  three `tateCurve` rows; the equivalence-class check (normalized `diff` over the five
  `BridgeX.`-carrying files) found the 5-file class structure. A node list is not a subject list.
