# The q-expansion definition layer gets its homes — refactor record (2026-10-21)

Three structural defects, all one story: the pin's `Definitions/Def_ModularCurve_X1.lean` was never
homed whole, and the pieces went where their first consumer lived.

1. **`ModularCurve.IsIntegralQExp`** — a three-line predicate over mathlib's
   `UpperHalfPlane.qExpansion` — sat at the head of
   `ModularForms/WeightOne/Gamma0Integral.lean`, a 2,245-line analytic weight-one module. That file's
   own header recorded why: *"transcribed verbatim because the third headline's statement names it"*.
2. **The pin's `Restrict` and `FunctionField` blocks** (lines 18–126: `restrictForm` and the whole
   `intSeriesC`/`intFormRatiosC`/`qExpFunctionFieldC` vocabulary) were homed inside the **node**
   module `ModularCurve/JqIntegralRatios.lean` (the `jqModC = E₄³/Δ` exhibit). So
   `ModularCurve/X1/Defs.lean` — the pin module's actual home, already holding 14 of its 35
   declarations — imported a node module to reach its own definition layer.
3. Consequently every consumer of `qExpFunctionFieldC` inherited the weight-one blob through that
   edge. Measured on `tools/deps/build/port_graph.json`: **63 modules reach
   `ModularForms.WeightOne.Gamma0Integral`; 40 still would with the `JqIntegralRatios` route removed
   — 23 lightened**, the whole lower q-expansion layer (`Degree/*`, `Frobenius/*`, `LevelN/*`,
   `X0/FunctionFieldFull`, `X1/{Defs,Diamond,HeckeModule,HeckeOperator,IntegralityJqNModC}`,
   `XH/{FunctionField,HeckeOperator}`, `HeckeCommuteBar`, `OmegaRowT2`, …).

The refactor follows [topics/TOPIC-dedup-refactoring.md](../topics/TOPIC-dedup-refactoring.md) §5:
the ground goes home first, at the pin's statements, and the four touched modules are then handed
over from the frozen registry to their own `spec-pin:` wires.

## 1. The edits — four modules, seven files

| module | change | why |
|---|---|---|
| `ModularCurve/X1/Integral.lean` | gains the pin's `def IsIntegralQExp`; its import of `WeightOne/Gamma0Integral` becomes mathlib (`ModularForms.QExpansion`, `PowerSeries.Basic`, `Int.Cast.Lemmas`); `spec-pin: Definitions/Def_ModularCurve_X1.lean` | it already declared itself the pin's `Integral` block (lines 37–63) and imported a 2,245-line blob for the one `def` it did not state |
| `ModularForms/WeightOne/Gamma0Integral.lean` | loses the `def`, its docstring and the `namespace ModularCurve` wrapper; imports `X1/Integral`; loses the then-dead `private T_mem_Gamma1`; its `private one_mem_strictPeriods` body becomes `by simp`; six `spec-pin:` lines | the predicate is not weight-one mathematics, and the module imports it |
| `ModularCurve/X1/Defs.lean` | gains the pin's `Restrict` + `FunctionField` blocks (12 declarations); drops the `JqIntegralRatios` import, imports `X1/Integral`; `spec-pin: Definitions/Def_ModularCurve_X1.lean` | the pin module's home now holds 26 of its 35 declarations and imports nothing above the definition layer |
| `ModularCurve/JqIntegralRatios.lean` | loses those 12 declarations; drops `Gamma0Integral` for `X1/Defs` + `JqAnalyticModel`; drops its `Def_ModularCurve_X1` wire line | it is the `jqModC` node; its header said so while carrying the definition layer |
| `ModularCurve/X1/FunctionField.lean` | two explicit mathlib imports (`LevelOne.GradedRing`, `LevelOne.DimensionFormula`); `spec-pin:` header + three `pin:` rows | it named `discriminant_eq_E₄_cube_sub_E₆_sq` and `ModularForm.qExpansion_eq_qExpansion_discriminant_mul`, both **mathlib**, through the weight-one leg it had been inheriting |
| `spec/old_check_stmts.py` | four `PORT_FILES` entries retired (`X1/Defs`, `X1/Integral`, `X1/FunctionField`, `Gamma0Integral`) | the handoff rule: an edited legacy module moves to its own wire |
| `spec/decl_markers.tsv` | three `pin:` rows for `X1/FunctionField` | its `IsIntegralQExp` prelude is the pin's, but stated in two sibling `S_` files its header does not list |

The seven direct importers of `X1/Defs` that lost the transitive node edge were checked by `rg` for
every name that stays in `JqIntegralRatios` (`jqModC`, `e4cube`, `delta`, `map_ofPowerSeries`,
`coeffEmb_intSeriesC`, `intSeriesC_eq_zero_iff`, `coeffEmb_image_intFormRatiosC`): **none uses any**.
`X1/FunctionField` was the only module that broke, and only on the two mathlib facts above.

`Def_ModularCurve_X1` before → after: X1/Defs 14 + JqIntegralRatios 12 + Gamma0Integral 1 +
X1/Integral 5 = 32 wired, 3 deferred (`JOne.torsionGaloisRep{,_apply}`,
`coe_torsionGaloisRep_apply` — the unported `Pic0` torsion action). After: **X1/Defs 26 +
X1/Integral 6 = 32 wired**, same 3 deferred.

## 2. Measured

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/Integral.lean \
    FLTForHuman/ModularCurve/X1/Defs.lean FLTForHuman/ModularCurve/JqIntegralRatios.lean \
    FLTForHuman/ModularForms/WeightOne/Gamma0Integral.lean FLTForHuman/ModularCurve/X1/FunctionField.lean
#   X1/Integral.lean        6 ok, 0 mismatch, 0 missing, 0 own, 0 kw
#   X1/Defs.lean           26 ok   (the whole public surface is one pin file: Definitions/Def_ModularCurve_X1.lean)
#   JqIntegralRatios.lean  15 ok
#   Gamma0Integral.lean    19 ok   (7 pin files)
#   X1/FunctionField.lean  78 ok   (Thm + S_ pair, + 3 pin: rows)
python3 spec/check_port.py --all
# 4023 ok, 0 mismatch, 0 missing, 11 own, 0 kw — 159 module(s), 573 exempt (PORT_FILES); corpus aa2d8b3
python3 spec/old_check_stmts.py
# 8684 statements identical (656 promoted, 17 renamed), 0 mismatched, 0 missing,
# 37 own-proof exemptions, 294 registered-unwired exempted (9015 checked)
python3 spec/unwired_register.py --check
# unwired_register: register is current
```

* The four handoffs move the exempt count **577 → 573** and the wired surface **+129 declarations**
  (26 + 6 + 19 + 78); `11 own` is unchanged — no new tier-2 statement was introduced.
* The frozen registry's total falls (10,473 → 8,684) because the modules it no longer parses are
  diffed by `check_port.py` instead; its invariant, **0 mismatched / 0 missing**, holds.
* Each edited module elaborates clean at the 200k edit-loop cap. `X1/Integral` needs 3,087 jobs,
  `X1/Defs` 3,414, `JqIntegralRatios` 3,967, `Gamma0Integral` 4,122 — all `lake build` green,
  **0 warnings** from the four.
* The dependent wave (the 23 lightened modules and their closures, 4,648 jobs) builds **green**. Its
  only warnings are three pre-existing deprecations in
  `WeierstrassCurve/Isogeny/TwoCurveDescent.lean`, which is a stale *dependency* of
  `ModularCurve.ModularPolynomialEvalJ`, not a dependent of the change
  ([logs/build-time-issues.md](build-time-issues.md) §7).
* `git status`: the seven files above, nothing else.

## 3. `one_mem_strictPeriods` — the class verdict

It is **spelling, not mathematics**. mathlib states the fact three ways:

* `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem` (`Mathlib/NumberTheory/ModularForms/Cusps.lean:297`),
  for any `Γ ≤ SL(2, ℤ)` with `T ∈ Γ`;
* `@[simp] CongruenceSubgroup.strictPeriods_Gamma0` (`:435`) and `strictPeriods_Gamma1` (`:440`);
* `one_mem_strictPeriods_SL` (`Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean:70`).

Probe (`lean/tmp/probe_strictper2.lean`, importing the compiled `X1/FunctionField`, clean): the
general form closes with `by simp [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]`, and the
`Γ₀`/`Γ₁` instances with **`by simp` alone** — no port lemma named.

So the family wants **no home and no promotion**. Done here: `Gamma0Integral`'s private copy became
`by simp`, and its `T_mem_Gamma1` helper, used only by that proof, was deleted. What remains is 37
copies / **95 proof lines**, of which 34 are already 1–2-line `simp`/`rw` spellings; the one real
re-derivation is `ModularCurve/X1/FunctionField.lean:361` (13 lines of `fin_cases` matrix entries).
The four **conjugation transports** (`RelIndex/LevelRaise.lean:142,158,211`, `XH/Relrank.lean:468`)
are genuine mathematics and stay where they are — the `RelIndex` ground.

The rule, for the column: a single call site writes `by simp` and no lemma; a `private` one-liner
used twice or more in one file may stay, with `by simp` as its body; a copy never earns a promotion,
and a consumer that needs the fact writes `by simp` rather than importing a module for it. What a
named copy buys is small but real, and it is not what it looks like: **not** monomorphization (Lean
has none, and the lemma is already monomorphic in the group) and **not** rewritability (every site
in the tree passes it as the membership *hypothesis* of `qExpansion_{add,mul_coe,smul}`,
`periodic_comp_ofComplex`, `isCusp_of_mem_strictPeriods` or `qExpansion_coeff_unique`; none rewrites
with it) — rather one elaboration in the olean instead of one simplifier run per site, one point of
repair if the `simp` set moves, and a readable call site that is also the pin's own proof text.

## 4. Deliberately not done

* No sweep of the 37 `one_mem_strictPeriods` copies: 95 lines across ~20 modules, 34 of them
  one-liners, each costing a module re-elaboration. The rule above stops the growth; the copies go
  opportunistically (§3).
* No `ModularForms/RestrictForm.lean`: `restrictForm` is a six-line `ModularForm` constructor, and a
  module for one declaration is what [porting-playbook.md](../porting-playbook.md) §4 forbids. It is
  now public in the definition layer (`X1/Defs.lean:53`), which is a defensible home; the two
  `private` copies elsewhere are recorded in [CARRY-FORWARD.md](../CARRY-FORWARD.md).
* No bisection of `TwoCurveDescent` (over the two-minute bound; a stale dependency, not part of this
  change).
* `JOne.torsionGaloisRep` stays deferred on the unported `Pic0` torsion action — a definition gate,
  not a placement question.

## 5. Reproduce

```bash
cd tools/deps
python3 port_graph.py >/dev/null && \
  jq -r '.modules[] | select(.name=="FLTForHuman.ModularCurve.X1.Defs") | .imports' build/port_graph.json
# the definition layer now imports X1/Integral + Defs/Laurent + AlgebraicCurve/Defs/Divisor
# + CongruenceSubgroupOrder + two mathlib files — and no node module
cd ../../lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/Defs.lean
python3 spec/check_port.py --all
```
