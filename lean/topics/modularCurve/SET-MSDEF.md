# SET MS-DEF — the MS-7 gate and the `qExpansion_E6_eq_map_mk` promotion

**Status: landed (2026-10-28), the manager lane of ready shelf 1.** Ready shelf 1
([TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md)) §0.2, §1.1, §5 item 6; brief
[WORKORDER-MSDEF-gate-and-promotion.md](WORKORDER-MSDEF-gate-and-promotion.md). Two items, two
modules, no row: this lane unblocks **MS-7** and moves no shelf figure.

| item | file | size | checker | axioms |
|---|---|---|---:|---|
| the gate | **new** `ModularCurve/Defs/XHDiamondModL.lean` | 80 lines, 2 declarations + the pin's `variable` block, 1 `spec-pin:` | **2 ok / 0 / 0 / 0** | clean |
| the promotion | `ModularCurve/X1/IntegralityJqNModC.lean` (edit) | the declaration moved out of `EisensteinCube`, 2 `spec-pin:` lines, one header bullet | **3 ok → 4 ok / 0 / 0 / 0** | clean |

## 0. What landed

**The gate.** `Def_ModularCurve_XHDiamondModL` transcribed whole: `IsDiamondPullbackModL` (the `Prop`
over `ρ : Γ₀(M) →* (qExpFunctionFieldC K (Γ_H M H) ≃ₐ[K] …)`, the pin's body verbatim, including the
`SL(2, ℤ)` slash and the `intSeriesC` ratios) and its projection lemma
`IsDiamondPullbackModL.coe_apply_eq`, with the pin's `variable` block. Nothing else: no helper, no
`set_option`, no `attribute` prelude. Imports are the vocabulary's two homes
(`ModularCurve/X1/Defs.lean`, `ModularForms/Defs/GammaH.lean`); the X₁ precedent module
`X1/DiamondAut.lean` is **not** imported (it is a 745-line proof module; the gate needs the
vocabulary only).

**The promotion.** `qExpansion_E6_eq_map_mk` was `private`, inside `namespace EisensteinCube`, of
`X1/IntegralityJqNModC.lean`. It is now public at the pin's name
`ModularCurve.qExpansion_E6_eq_map_mk`, outside that namespace, with `namespace EisensteinCube`
re-opened after it so the module's own `eisenstein4_cube_sub_mk_sq_aux` resolves by namespace
lookup unchanged. Statement byte-identical to the pin (`Thm_ModularCurve_qExpansion_E6_eq_map_mk.lean:7-9`).
Two `spec-pin:` lines: the wrapper and the `S_` copy. The `S_` copy's three Bernoulli helpers are
**not** transcribed (the port decides `bernoulli 6 = 1/42` by `decide +kernel`), and the header says
so — the `S_` line is statement-only wiring, which `check_port --force` accepts.

## 1. The verification of the pair

| check | result |
|---|---|
| `check_port --force` on the gate | 2 ok / 0 / 0 / 0 |
| `check_port --force` on the promotion module | **4 ok** (baseline 3) / 0 / 0 / 0 |
| `#print axioms` on all three declarations | `[propext, Classical.choice, Quot.sound]` |
| builds | gate 3,419 jobs; promotion module 3,980 jobs — both `exit=0` |
| edit loop (200k cap) | silent, zero warnings, both |
| **`twin_scan --node ModularCurve.qExpansion_E6_eq_map_mk`** | **`twin-private` → `twin-public`** |
| **the read** | **unchanged**: `needed` 960 / 388,827, MC ready 20 / 8,178, frontier 1,455 / 738,539 |

The last two lines are the point of the lane, and they are the same distinction the definition wave
drew: **a promotion is statability, not demand.** The node was already counted ported — `frontier.py`'s
name tier scans private declarations by design — so promoting it changes no figure. What changes is
that the two rows citing it (373-XH and 168) can now be written. The `--unport` experiment is the
*diagnostic* for the gap, not the landing: it moves `needed` to 961 / 388,861 because it forces the
node unported.

## 2. What this lane found (FR-0071)

The mechanism is a general one and it had a second, larger instance in the same tree:
`AlgebraicCurve.Divisor.pushforwardNormFormula_of_finiteDimensional` is held `private` in
`AlgebraicCurve/PrincipalDivisors/Transcendence.lean:359` behind its own `spec-pin:` (line 43), so the
instrument reads a 650-line `AlgebraicCurve` row as ported. That one is **not** this lane's (it is
the `AlgebraicCurve` column's promotion-or-unwire decision), and it is recorded as FR-0071 with both
instances rather than fixed here.

## 3. What this lane does not do

- No row, no shelf movement, no migration, no `PORT_FILES` edit, no marker row.
- No promotion beyond the one above: `qExpansion_E4_cube_sub_E6_sq` and the other `EisensteinCube`
  helpers stay `private` (no external consumer), and the `X₁`-side `frickeGL` question is MS-1's
  dedup rule, not a promotion.
