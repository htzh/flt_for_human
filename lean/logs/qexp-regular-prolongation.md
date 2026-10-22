# The Gauss regular prolongation of the q-expansion valuation — landing record

`ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC` and its two
`_residue_div` / `_residue_mul_eq` siblings, three ready nodes of the D-S shelf cut as **one set** —
the pin writes the same development three times (853 + 875 + 875 = 2,603 raw `S_` lines; the shared
block is byte-identical through line 815, the tails differ by 7–8 lines each). One new module,
739 lines, **3 public headlines, 50 private engine declarations**. Order:
[topics/modularCurve/WORKORDER-RP1-qexp-regular-prolongation.md](../topics/modularCurve/WORKORDER-RP1-qexp-regular-prolongation.md).

The mathematics: the Deuring/Gauss regular prolongation of the valuation of
`laurentBaseChange L (qExpFunctionFieldC ℚ Γ)` at `q = 0`, with residue target
`qExpFunctionFieldC (IsResidueField A) Γ` — integers = the Gauss ring (`f` is integral iff
`f = x/y` with `x, y` Laurent series over `A`, `y` reducing nonzero, and `f · y = x`), residue =
coefficientwise reduction. The two siblings add the residue-multiplicativity conjunct, stated in two
different binder shapes (`f : R.integers` versus `f : FF` + `hf`), so both are written.

## 1. Structure and reuse

`FLTForHuman/ModularCurve/X1/QExpRegularProlongation.lean`, engine `private` in
`namespace ModularCurve.QExpDeuring`, the three headlines after `end QExpDeuring` with
`open QExpDeuring in` (the `FunctionFieldResidue.lean:996–998` shape). Imports are exactly four —
`X1.FunctionFieldResidue`, `X1.Defs`, `AlgebraicCurve.RegularProlongation`,
`RingTheory.PowerSeries.Saturation` — and the module's whole import closure (**177 modules**) contains
**no `ModularForms.WeightOne` module** (`port_graph.py`), which is what the re-homing of
[logs/qexp-definition-layer-homes.md](qexp-definition-layer-homes.md) bought: the first consumer of
that definition layer would otherwise have imported a 2,245-line analytic weight-one blob for it.

| the pin's block | disposition |
|---|---|
| `Coeff` (ι, ϖ, `IsInt` + its six lemmas, `intSeriesA`, …) | **imported** (`QExpDeuring`) — ~106 pin lines, none re-proved |
| `Gauss` (`gaussRing`, `exists_witness`, `wit`, `resL`, `resHom`, `resHom_eq`, `algebraMap_mem_gaussRing_iff`, `resHom_eq_zero_iff`, `coe_algebraMap`, the 3-conjunct `exists_frac_form`) | **imported and used** — the port states them for an arbitrary `Γ`, strictly stronger than the pin's `hT`-parameterised copies (~170 pin lines) |
| `resRange`, `qExpFunctionFieldC_le_resRange`, the pin's `resF_surjective` proof (pin 711–768) | **not ported**: `QExpDeuring.exists_resHom_eq` is the same `Subfield.closure_le` argument; `resF_surjective` is 3 lines |
| `Forms` + `FracForm` (`Lam`, `LamSub`, `homSpan`, `IsFrac`, `ofPS`, `div_mem_qExpFunctionFieldC_of_mem_span`, `exists_primitive_of_mem_homSpan`) | **new, ~300 of the 739 lines** — see §2 |
| `Assembly` (`gaussProlongation`, `main`, the two tails) | new, ~120 lines |
| `PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated` | **called**, not re-proved (ported by WORKORDER-PH3B) |

Net: 2,603 pin lines → 739 port lines, **+3** statements; the engine is `private`, so the checker
sees the three headlines only.

## 2. The crux, and why the `Lam` layer is not dedup-able

Grepping the pin's call sites: the fourth conjunct of `exists_frac_form`
(`ϖ u₀ / ϖ w₀ ∈ qExpFunctionFieldC kk Γ`) is consumed by **exactly one** declaration, `resHom_mem`
(pin:650) — and `resHom_mem` is the only pin declaration in the file with no ported counterpart
(`resF` is a ring hom *into* the residue function field, so it needs it). Everything the pin builds
to reach it — the graded `Lam`/`homSpan`/`IsFrac` layer and `FracForm` — is one statement's worth of
machinery, and it is what makes the module new rather than a transcription of the port's own route.

The port's route (`QExpDeuring.exists_frac_form` via `gensZ` + `exists_primitive_form`) gives the
decomposition and both `ϖ`-nonvanishing conjuncts but **not** the residue-membership: its primitive
form is conditioned only on coefficients lying in a finitely generated `ℤ`-submodule, so nothing
constrains `ϖ x₀` to lie in the span of the `Lam` image. The dispatch's optional "route A" probe was
therefore not run — the statement is not derivable from that lemma's hypotheses — and the graded
layer was transcribed (route B) with the ported `Saturation` premise called at
`exists_primitive_of_mem_homSpan`. Recorded so that a later reader does not re-open the question as
a dedup.

## 3. Two build-time findings

**(a) A `≤`-shaped lemma applied to a membership inside a *large* statement can blow the 200k
diagnostic** — with nothing wrong with either the lemma or the statement. Transcribing the pin's
`exists_frac_form`, the line

```lean
have hfF : (f : LaurentSeries L) ∈ qExpFunctionFieldC L Γ := laurentBaseChange_le Γ f.2
```

timed out deterministically at `isDefEq`: applying a `FF ≤ qExpFunctionFieldC L Γ` proof to an
element unfolds `SetLike.le`, and inside that four-conjunct statement the unification is expensive.
Stubbing the proof showed the *statement* elaborates in a second, so the cost is the application.
The cure is local and cheap: an element-shaped statement (`mem_qExp_of_mem_FF`, proved by
`SetLike.le_def.mp`), applied at the site — the declaration then closes in about a second. It is the
same class as the `ZLattice` `LocSum` cure (`logs/build-time-issues.md` §2): name the shape once,
and the elaborator stops unfolding it. No heartbeat was raised, no statement weakened.

**(b) `gaussProlongation` must be an `abbrev`, not a `def`** (the pin has `def`). The two siblings'
assembly steps `change`/`rw` across `(gaussProlongation hT A).integers = gaussRing A Γ` do not
typecheck at `implicit` transparency when the value is a plain `def` ("not type-correct under the
`implicit` transparency level"): the projections must reduce. If it is ever made public, keep it
`abbrev`-reducible.

## 4. Measured

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/QExpRegularProlongation.lean
# QExpRegularProlongation.lean  [ok]  3 ok, 0 mismatch, 0 missing, 0 own, 0 kw
#   each headline -> Theorems/Thm_…:11
python3 spec/check_port.py --changed
# 4026 ok, 0 mismatch, 0 missing, 11 own, 0 kw — 160 module(s)
python3 spec/unwired_register.py --check       # register is current
```

* edit loop at `-DmaxHeartbeats=200000`: exit 0, **empty output** — the pin's
  `synthInstance.maxHeartbeats 400000` (wrappers) and `1600000` (`S_` file) are not inherited and are
  not needed.
* `lake build FLTForHuman.ModularCurve.X1.QExpRegularProlongation`: **4,179 jobs, 24 s, 0 warnings**.
* `#print axioms` on all three headlines: `[propext, Classical.choice, Quot.sound]`.
* `git status`: one new file (plus the re-homing round's files).

Frontier, re-read after the landing: all three nodes read `needed 0 / 0 lines`, *"target is ported"*.
The family had been priced as **one** row (1 node / 853 lines — the two sibling files were never
separate demand rows, which is exactly why the triplet had to be cut together), and that row is gone;
the ready shelf reads **110** candidates. The order's predicted successor is ready:
`ModularCurve.FullLevel.exists_regularProlongation_fieldBar_integers_eq` drops **2 nodes / 888 lines →
1 / 35**, and is the next cut of this family.

## 5. Deviations from the pin (statements: none)

No statement moved — the checker matches all three headlines to the wrappers' hashes. Proof/structure
drift:

1. `laurentBaseChange_le` (pin `S_:301–320`) re-derived `private` (17 lines): the pin's
   `exists_frac_form` needs `FF ≤ qExpFunctionFieldC L Γ`, and the frozen engine carries only the
   *`gensZ`* strengthening — see the promotion candidate in [CARRY-FORWARD.md](../CARRY-FORWARD.md).
2. `exists_frac_form` → `exists_frac_form_mem` (name only; the engine owns the 3-conjunct name), all
   four conjuncts kept.
3. `hT` threaded only where the pin has it (the engine's Gauss block is `hT`-free).
4. `one_mem_strictPeriods` is a 4-use `private` one-liner (`by simp` body), per the rule of
   [logs/qexp-definition-layer-homes.md](qexp-definition-layer-homes.md) §3.
5. Mathlib drift: `FunLike.coe_{add,zero,neg,smul}` for the deprecated `ModularForm.*` aliases.
6. `coe_LamSub` (pin:188) dropped — no consumer.

## 6. What this leaves

* The successor above (35 own lines) — ready, next.
* `laurentBaseChange_le`'s promotion beside `laurentBaseChange_le_adjoin_gensZ` in
  `X1/FunctionFieldResidue.lean`, and the seven Gauss-block helpers the engine dropped
  (`coe_LamSub`, `resHom_apply`, `ι_mem_gaussRing`, `resHom_ι`, `ker_resHom`, `coe_smul'`,
  `exists_smul_mem_gaussRing`) — now `private` here, the natural content of a later promotion pass.
  Recorded in [CARRY-FORWARD.md](../CARRY-FORWARD.md), not opened.

## 7. Reproduce

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/QExpRegularProlongation.lean
cd ../tools/deps
python3 frontier.py --ds --target ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq --top 2   # needed 0
python3 frontier.py --ds --target ModularCurve.FullLevel.exists_regularProlongation_fieldBar_integers_eq --top 3                        # needed 1 / 35
```
