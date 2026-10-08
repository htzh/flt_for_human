# SET-H-A — the `X_H(M)` vocabulary: function field, Hecke degeneracy maps, diamond predicate and the input bundle

Work order: SET-H-A of
[TOPIC-xH-hecke-diamond-inputs.md](../topics/hecke/TOPIC-xH-hecke-diamond-inputs.md) §5.
Pin: `aa2d8b3` (mathlib `v4.34.0`). Definitions-first; no headline proofs.

**Result.** 3 new modules (385 raw / 155 content lines, 35 declarations), 1 checker
wiring (2 `SOURCES` + 3 `PORT_FILES` entries, plus 3 `S_` files that verify the
promotions), **15 promotions** in the X₁ prelude with 1 rename, 1 consumer file.
Checker `6315 → 6365 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing,
36 own (6401 checked)`. Consumer `spec/XHConsumer.lean` error+warning count `0`;
delete-fail `3`. Whole-tree `lake build` green (9,332 jobs).

## 1. Reconnaissance applied, and the one divergence from the plan

The plan's three definition modules are thin over the ported vocabulary, and the
build confirmed it. Two blocks of `Def_ModularCurve_XH.lean` needed no work:

* the `Groups` block (`translation_mem_GammaH`, `Gamma1_le_GammaH`, `GammaH_bot`,
  `GammaH_mono`, pin 20–68) is the `CohCarrier` copy already public in
  `ModularForms/Defs/GammaH.lean:111–151,99`; duplicating it in `XH/` would have
  been a second home for the same mathematics;
* the pin's `PrivateSupply` in `XHHeckeOperator.lean` (`coeffMap_qExpandH`,
  `coeffEmb_qExpandH`, `laurentBaseChange_monoH`, `qExpand_mem_laurentBaseChangeH`,
  pin 14–57) is byte-for-byte `Defs/Laurent.lean`'s public
  `coeffMap_qExpand`/`coeffEmb_qExpand`/`laurentBaseChange_mono`/
  `qExpand_mem_laurentBaseChange`; the `…H` copies were dropped, as the plan §3
  item 5 directed.

The off-cone blocks were left out as scoped: `JH`/`torsionGaloisRep`/`tateGaloisRep`/
`JHC` (pin `XH.lean:119–175`), `heckeDivHBar`/`heckePic0HBar`/the transposes and
`heckeOperatorHAlong` (pin `XHHeckeOperator.lean:138–231`), `diamondHBar`/`genOpH`/
`tateGenOpH` (pin `XHOperators.lean:57–107`). None is referenced by the four `S_`
files, and no port declaration names them, so the checker cannot report them
`missing`.

## 2. Per-module line counts

| module | raw | content | decls | pin source (raw / content) |
|---|---:|---:|---:|---|
| `FLTForHuman/ModularCurve/XH/FunctionField.lean` | 106 | 35 | 12 | `Definitions/Def_ModularCurve_XH.lean:72–126` (179 / 111) |
| `FLTForHuman/ModularCurve/XH/HeckeOperator.lean` | 172 | 75 | 16 | `Definitions/Def_ModularCurve_XHHeckeOperator.lean` (249 / 154) |
| `FLTForHuman/ModularCurve/XH/Operators.lean` | 107 | 45 | 7 | `Definitions/Def_ModularCurve_XHOperators.lean` (133 / 77) |
| **new total** | **385** | **155** | **35** | 561 / 342 |

(content = raw minus `import`/`attribute`/`namespace`/`end`/`open`/`section`/
`variable`/`#`/comment/blank lines.) The plan estimated ≈340 definition content
lines "minus reuse"; the 155 delivered is the reuse: 4 of the pin's 25 `XH.lean`
declarations, its whole `HeckePic0HBar`/`Total`-capstone half, and its whole
`GenOp` block are either already ported or off-cone.

Edits (numstat):

| file | +/− | content |
|---|---|---|
| `X1/QExpandStretch.lean` | +5/−5 | `private` dropped on 5 declarations (§3) |
| `X1/DiamondAut.lean` | +8/−8 | `private` dropped on 8 declarations |
| `X1/FunctionField.lean` | +4/−4 | `private` dropped on 2, renamed to the pin's primed names |
| `spec/check_flt_statements.py` | +43/−0 | 2 `SOURCES` + 3 `PORT_FILES` + 3 promotion-verifying `S_` files |
| `spec/XHConsumer.lean` | +189/−0 | the new consumer (Zones XH-A/B/C) |

## 3. The promotions — 15 landed, 7 rejected on measurement

The plan (§2, §5) asked for the port-private X₁ diamond prelude to be promoted in
place. `port_advise --targets build/hH_targets.txt` names 32 substitution rows; per
unique declaration they are the 15 below. Each was promoted one at a time and the
checker re-run; the count moved by exactly +1 each time, `0 mismatched / 0 missing`
throughout.

| port home | promoted | pin-public original |
|---|---|---|
| `X1/QExpandStretch.lean` | `heckeDiagMatrix_mul_eq`, `isCusp_heckeDiagMatrix_smul`, `expandPS`, `coeff_expandPS`, `intSeriesC_expandPS` | both diamond `S_` files |
| `X1/DiamondAut.lean` | `IsRatio`, `ratioField`, `toC_injective`, `toC_algebraMap`, `qC_zero`, `qC_one`, `slash_inv_slash`, `slash_slash_inv` | both diamond `S_` files |
| `X1/FunctionField.lean` | `intSeriesC_add'`, `intSeriesC_neg'` | `S_…heckeDiamondInputsHAll.lean:132,136` |

The last two are a **rename**, not a bare `private`-drop: the pin writes
`intSeriesC_add'`/`intSeriesC_neg'` (with a prime) and the port's private copies
were `intSeriesC_add`/`intSeriesC_neg`. Renaming in place (two internal call sites
updated) is the dedup; leaving them unprimed, as the plan's §2 table could be read
to mean, reports `MISSING IN FLT` and drops the checker to `2 missing`.

**Rejected on measurement** (recorded negative, do not retry): the topic's §2 list
also names `qC_mul`, `qC_add` and is truncated with "…". The pin's `S_` files state
the whole `qC_*` group over a general `Γ` (`ModularForm GL↑(Γ) a`), while the port's
private copies are specialised to `Γ₁(M)`:

```
pin  S_…diamondAutHBar.lean:41   qC_mul {a b : ℤ} (f : ModularForm GL↑(Γ) a) …
port X1/DiamondAut.lean:200      qC_mul {a b : ℤ} (f : ModularForm Γ₁(M) a) …
```

Their statements are **not** identical, so promoting them is a `MISMATCH`, not a
promotion. Only `qC`, and the six whose statements do not mention a `ModularForm Γ`
(`qC_one`, `qC_zero`, `slash_inv_slash`, `slash_slash_inv`, `toC_injective`,
`toC_algebraMap`), are promotable. SET-H-B's shared engine must therefore
**generalise** the `qC`/`ratioField`/`pull` block to `Γ_H(M) ∩ Γ₀(t)` (as the plan
§3 item 1 already wanted), not merely promote it; the `Γ₁(M)` specialisations stay
private in `X1/DiamondAut.lean`.

Two consequences of the promotions, both reconciled:

* the three `S_` files are now in `SOURCES`. Without them a promoted helper's pin
  original is nowhere in the lookup pool and the checker reports `missing`; adding
  them is monotone (measured: with them present and *no* promotions the pass is
  unchanged at `6350 / 0 / 0`). SET-H-B/C append their own `Theorems/` wrappers and
  the `S_ModularCurve_heckeInputsHAlong.lean` copy beside them;
* the promoted `IsRatio` adds one **advisory** `--prop-bodies` row: the port's
  `X1DiamondPullback.IsRatio` (`∃ k f g, qC ⇑g ≠ 0 ∧ x = qC ⇑f / qC ⇑g`) is the pin's
  `S_…diamondAutBar.lean:168` body verbatim, but the pass keys by last name and
  picks the unrelated `S_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div.lean:94`
  `IsRatio` (`∃ k g h, h ≠ 0 ∧ x * qL h = qL g`), which shares only the `: Prop`
  type. `--prop-bodies` is advisory and does not affect the exit status; the main
  pass is `0 / 0`.

## 4. Checker

```
baseline (before SET-H-A):  6315 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6351 checked)
+ the three modules:         6350 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6386 checked)   (+35)
+ the 15 promotions:         6365 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6401 checked)   (+15)
```

The +35 reconciles exactly as `XH/FunctionField.lean` 12 + `XH/HeckeOperator.lean`
16 + `XH/Operators.lean` 7. `promoted` stays `312`: none of the two new `SOURCES`
definition files and none of the three promotion-verifying `S_` files contributes a
declaration that an earlier source had not already claimed under its last name, and
all 15 promotions resolve through the public last-name lookup (their pin copies are
public), not the pin-private fallback.

One-token mutation check: `xHFunctionFieldC_le_x1`'s `≤ → <` gave
`6349 identical / 1 mismatched / 0 missing`; reverted → `6365 / 0 / 0`.

`--prop-bodies`: `275 Prop-valued def bodies identical, 7 differ` (was
`269 identical, 6 differ`); the +6 identical are the six new `Prop`-valued
definitions (`HeckeBetaHDefined`, `HeckeAlphaHBarIntegral`, `HeckeBetaHBarIntegral`,
`HeckeInputsHAlong`, `IsDiamondAutHBar`, `HeckeDiamondInputsHAll`), the +1 difference
is the `IsRatio` collision of §3. In particular the body of `HeckeInputsHAlong` was
diffed against the pin and is identical — the plan's §6 risk 3 (the
`HeckeInputsHAlong` vs `HeckeInputsAlong` confusion) did not materialise, because
the pin's `∃`-body was transcribed verbatim.

## 5. Consumer

`spec/XHConsumer.lean`, three zones, all examples naming their declaration:

* **`[xh-ff]`** — `xHFunctionFieldC`/`xHFunctionField`/`xHTopFunctionFieldC` and
  `xHFunctionFieldBar` at `(K, M, H) = (ℚ, 2, ⊥)`, the `rfl` bridge
  `xHFunctionFieldC_rat`, the α-inclusion `xHFunctionFieldC_le_top`, the level-one
  collapse `xHTopFunctionFieldC_one`, the four `Γ_H` endpoints
  (`xHFunctionFieldC_top`/`_bot`, `x0_le_xHFunctionFieldC`, `xHFunctionFieldC_le_x1`)
  and the antitone direction at `⊥ ≤ ⊤`;
* **`[xh-hecke]`** — `heckeAlphaHBar`/`heckeBetaHBar` with the pinned `xHTopFunctionFieldC`
  codomain, `coe_heckeAlphaHBar`/`coe_heckeBetaHBar`, `heckeAlphaHBar_eq_inclusion`,
  the `HeckeInputsHAlong.betaHDefined` accessor and the seven-binder constructor;
* **`[xh-diamond]`** — `IsDiamondAutHBar`, `diamondAutHBar`,
  `isDiamondAutHBar_diamondAutHBar`, `diamondAutHBar_of_not`, and
  `HeckeDiamondInputsHAll` destructured into a real `HeckeInputsHAlong` at `ℓ = 3`
  and a real diamond automorphism at every `d`.

`timeout 300 lake env lean spec/XHConsumer.lean 2>&1 | grep -c 'error\|warning'`
→ **0**. Delete-fail (rename one `coe_heckeAlphaHBar` call, one
`xHFunctionFieldC_le_top` call and one `isDiamondAutHBar_diamondAutHBar` call) →
**3** errors, one per zone. No `#check`, no `sorry`, no unported hypothesis: the
bundle halves are consumed under a hypothesis, which SET-H-C supplies.

The pre-existing consumer `spec/ModularCurveHeckeConsumer.lean` (Zones A…X1-CAP,
which import `X1/DiamondAut.lean` and `X1/QExpandStretch.lean`) still reports
`0` errors and warnings after the promotions.

## 6. Build discipline and times

| command | result | wall | user | sys |
|---|---|---:|---:|---:|
| `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` | edit loop | — | — | — |
| `flock … timeout 600 lake build FLTForHuman.ModularCurve.XH.FunctionField` | ✔ 4125 jobs | 6.2s | 5.0s | 5.5s |
| `flock … timeout 600 lake build FLTForHuman.ModularCurve.XH.HeckeOperator` | ✔ 4131 jobs | — | — | — |
| `flock … timeout 600 lake build FLTForHuman.ModularCurve.XH.Operators` | ✔ 4132 jobs | — | — | — |
| `flock … timeout 900 lake build` (set boundary, whole tree) | ✔ 9332 jobs | 38.2s | 94.5s | 14.9s |
| `timeout 300 lake env lean spec/XHConsumer.lean` | 0 errors | 6.3s | 6.0s | 2.0s |
| `timeout 600 lake env lean spec/ModularCurveHeckeConsumer.lean` | 0 errors | 22.5s | 24.0s | 2.2s |

No bound was hit; `maxHeartbeats` was never raised. `#print axioms` on the three
module surfaces (`xHFunctionFieldC_le_top`, `xHTopFunctionFieldC_one`,
`xHFunctionFieldC_bot`, `heckeBetaHBar_eq`, `coe_heckeBetaHBar`,
`isDiamondAutHBar_diamondAutHBar`, `HeckeInputsHAlong.betaHDefined`,
`HeckeDiamondInputsHAll.heckeInputsHAlong`, `HeckeDiamondInputsHAll.isDiamondAutHBar`)
is `[propext, Classical.choice, Quot.sound]`; `grep -rn sorry` over `XH/` is empty.

## 7. What SET-H-A leaves for SET-H-B/C

* the two headline statements are unported: `exists_algEquiv_intertwinesAlong_diamondAutBar`
  (X₁) and `…_diamondAutHBar` (H). Their engine is the `qC`/`slashForm`/`exists_psi*`/
  `exists_gammas`/`cocycle` block, and — see §3 — it must be **generalised** over
  `Γ`, not promoted from the `Γ₁(M)` copies;
* `HeckeInputsHAlong` is defined and checker-verified, but has no producer yet: the
  seven inputs of `S_ModularCurve_heckeInputsHAlong.lean` are SET-H-C's;
* `HeckeDiamondInputsHAll` is defined; its capstone proof is the manager's, per
  plan §5. Its two accessors and the definition-module lemma
  `isDiamondAutHBar_diamondAutHBar` are already public, so the plan's §3 item 6
  (three proofs of the same diamond existence) can now be reconciled by having the
  bundle cite the definition-module lemma rather than reprove it in place;
* coverage: re-running `frontier.py --target ModularCurve.heckeDiamondInputsHAll
  --no-rank --list` still prints `needed [literal] 1 nodes / 918 lines`, i.e. the
  node itself, exactly as the plan recorded. The tool *does* scan
  `lean/FLTForHuman` (`frontier.py:492`), so the new modules are seen as ported
  declarations; what it does not do is count a definition module as *demand* for a
  `def`-valued target. The plan's §6 risk 1 is therefore a tool-level gap, not a
  port-side one, and it remains open.
