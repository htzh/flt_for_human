# TOPIC — the `ANb` dictionary and the analytic-order bound

**Status (2026-10-25): landed.** The node
`ModularCurve.analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow` (silo 409) is green, and
the dictionary its pin file shares with `omegaRow_T2` is now its own module. Measured on
the landing: `check_port` **41 ok / 0 mismatch / 0 missing / 0 own** on the dictionary,
**11 ok / 0 own** on the omega row, **2 ok / 0 own** on the new node; tier-1 builds green
with no warning; `dedup.py` over the three modules reports **0 clusters**; the consumer
`spec/DsHeadConsumer.lean` untouched; and the frontier `1,201 → 1,200` needed nodes with
`458,572 → 458,163` raw `S_` lines (exactly minus the node's 409).

## 0. The pre-check: what the node actually contained

`port_advise` priced the node at 43 declarations and found **28 statement-identical** to
public port declarations (≈163 lines); `twin_scan` reported `prelude 36/40`. The two pin
files it lives between — `S_omegaRow_T2.lean` (447 ln) and
`S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow.lean` (409 ln) — share
**39 of their 40/41 declarations**: the `ANb` dictionary. Only two declarations are unique
to the new node.

The pre-check on a shared *engine* came back negative: the two headlines differ in kind.
`omegaRow_T2` is a `q`-expansion identity (`coeffMap … * Δ = -(E₄²E₆)`, two lines from
`thetaJ_mul_D`), while this node is the analytic-order argument. Nothing to generalise
there — but the shared dictionary had no home of its own, which is what the split fixes.

One genuine find: the two pin files state `order_le_of_identity` **differently**. The
`omegaRow_T2` copy specialises the first factor to `d ^ m`; this file's copy keeps a free
`d₁`. The port had transcribed the specialised one, which **nothing used**. It is replaced
by the general form (`d₁`, `d` separate), which is the statement the new proof needs and
which the checker verifies against this node's `S_` copy (`ANb.lean`, 41 ok).

## 1. Where it goes, and why not in `OmegaRowT2.lean`

`OmegaRowT2.lean` was carrying three roles: the `θ`/`coeffMap` node
(`thetaL_coeffMap_eq_coeffMap_single_mul_derivative`, its own pin file), the 267-line `ANb`
dictionary, and the `omegaRow_T2` headline. Adding a fourth (an unrelated analytic-order
statement) would have made the name say nothing. The dictionary is the part two unrelated
headlines share, so it is the part that gets the module:

| module | lines | subject | checker |
|---|---:|---|---|
| `ModularCurve/Analytic/ANb.lean` | 324 | `𝒩` (`niceSubalgebra`), `ψ` + injectivity, `toC` + analyticity, `𝔞`/`𝔟`/`𝔡`, the coefficient facts, `J_mul_D`/`J_sub_mul_D`, `order_le_of_identity`, `one_mem_strictPeriods_{gamma0,of_T_mem}` | 41 ok |
| `ModularCurve/OmegaRowT2.lean` | 277 | the `θ`/`coeffMap` node and the `omegaRow_T2` identity, importing the dictionary | 11 ok |
| `ModularCurve/Analytic/IntegralOrderBound.lean` | 176 | `ANb.core` and the headline, importing the dictionary | 2 ok |

Nothing in the port imported `OmegaRowT2`, so the extraction needed no import update. The
two pin headlines are now two modules with one dictionary between them — which is the
shape the pin itself has, twice.

## 2. What the new mathematics is

`ANb.core` (92 lines) with the module's own vocabulary: for `𝔤 𝔥 : 𝒩` and `X` with
`X · ψ 𝔥 = ψ 𝔤`, and `X ^ 6 · j̄ ^ (4w) · (j̄ - 1728) ^ (3w)` integral over `ℂ[j̄]`, the
analytic order of `toC (𝔥 * 𝔡 ^ w)` is at most that of `toC (𝔤 * (𝔞 ^ 2 * 𝔟) ^ w)`. The
proof reads the integral relation `∑ i, pᵢ · Y ^ i = 0` as a single identity
`P ^ (6n) · Δ ^ m + ∑ i, Cᵢ · (P ^ (6i) · (Q ^ 6 · Δ ^ w) ^ (n-i)) = 0`, where each `Cᵢ`
absorbs the coefficient `pᵢ` through `j̄ · Δ = E₄³` — which is why the coefficients come
out divisible by `Δ ^ m` — and hands it to `order_le_of_identity`. The headline is then
`coeffEmb_jq` plus that engine (4 lines).

`one_mem_strictPeriods_of_T_mem` (2 lines: `strictPeriods_eq_zmultiples_one_of_T_mem`,
mathlib's `Cusps.lean:297`, and `mem_zmultiples`) is a *vocabulary* fact, not this node's
mathematics, so it lives in `ANb.lean` beside `one_mem_strictPeriods_gamma0` rather than
in the headline's module.

## 3. Verification

```
cd lean
lake build FLTForHuman.ModularCurve.Analytic.ANb \
            FLTForHuman.ModularCurve.OmegaRowT2 \
            FLTForHuman.ModularCurve.Analytic.IntegralOrderBound      # 3,990 jobs, no warning
python3 spec/check_port.py --force FLTForHuman/ModularCurve/Analytic/ANb.lean
#   41 ok, 0 mismatch, 0 missing, 0 own
python3 spec/check_port.py --force FLTForHuman/ModularCurve/OmegaRowT2.lean
#   11 ok, …
python3 spec/check_port.py --force FLTForHuman/ModularCurve/Analytic/IntegralOrderBound.lean
#   2 ok, …
cd tools/deps && python3 dedup.py --module '*ANb*' --module '*OmegaRowT2*' --module '*IntegralOrderBound*'
#   0 duplicate clusters
```

`#print axioms ModularCurve.analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow` is
`[propext, Classical.choice, Quot.sound]`. Two drifts were fixed on the way: the general
`order_le_of_identity` (above), and `ENat.coe_le_coe` → `ENat.natCast_le_natCast` in its
proof (mathlib deprecation). The `thetaL_coeffMap_impl` private helper was folded into its
public wrapper — the two had the same statement, and the wrapper is the pinned one.
