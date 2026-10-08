# The qexp head's promotion ledger — decided by mathematical content

**Status: landed and verified 2026-10-08.** Pin `aa2d8b3`, mathlib `v4.34.0`.
The five qexp targets leave **79 pin declarations the port holds only as
`private`** (741 raw lines). Every one is now **decided**, not deferred:

* **82 declarations promoted** (75 in the `JOneES` block, 7 content-bearing rows
  in the hubs);
* **21 kept `private`** — glue, adapters and generic lemmas whose local
  re-derivation is cheaper than widening a hub's public surface.

Checker **6520 → 6602 identical (312 promoted, 83 renamed), 0 mismatched, 0
missing, 36 own (6638 checked)**. Tier 0, tier 1, and the dependent wave are all
green — the wave is the union of the edited modules' dependents and covers
**9,206 jobs**, finished under `flock` with a 900 s bound after an initial 300 s
bound proved too small (real compute, not a blow-up). No bare `lake build` was
issued.

## 1. The decision rule

Build cost does not decide anything. The test is mathematical content:

* **Promote** when the declaration carries mathematics another theory could
  state or reuse — an existence, a rationality/integrality statement, a Galois
  or transport identity. These are the pin's own public API, and the head will
  need them by name, so we pay the cascade once.
* **Keep `private`** when the declaration only adapts another theory (a slash
  formula specialised from `slash_action_eqn''`, a coercion identity, an `rfl`
  unfolding), or is a generic analysis/group lemma (`f^n` bounded, periodic
  difference, `T^n ∈ Γ₁`), or a one-line definition. A consumer re-derives these
  in a few lines and stays decoupled from the hub.

The 79 rows split `51 + 28`; the 28 are decided one by one in §3.

## 2. The `JOneES` block — 75 promoted

`ModularCurve/X1/FunctionField.lean` transcribed the pin's JOneES `S_` file as
four `private` inner blocks (`JOneESAlg`, `JOneESLevelOne`, `JOneESNorm`,
`JOneESRat`) with only the headline public; the pin declares them all publicly.
The 51 rows the targets consume are the engine of the finrank target, and the
rest of the block is their surrounding API — the `Cos`-indexed norm
`charPolyAt`, the `Nice` analyticity predicate and its algebra, the monomial
span, the `intFormRatiosC` closure, the `E₄³/Δ` integral ratios. All of it is
mathematics the target modules state against, so the whole block is promoted
(75 declarations, all in one module).

Two deliberate exceptions:

* **`coeff_one_eisenstein4` stays `private`** — its pin counterpart
  `coeff_one_P4` is stated over the pin's `P4`, which the port substituted by
  `eisenstein4`; a promotion under the pin name would `MISMATCH`. It is not in
  the 51 and appears only in proof bodies.
* **The anonymous `Fintype (Cos Γ)` instance stays `private`** — `DECL_RE`
  requires a name after `instance`, so it is invisible to the checker on both
  sides; a consumer declares its own `scoped instance`, as the pin's
  `...le_index.lean:235` does.

One rename to the pin name at the same statement: `intSeriesC_P4_cube_ne_zero` →
**`intSeriesC_E4_cube_ne_zero`**.

## 3. The 28 hub rows — 7 promoted, 21 kept private

| host / row | lines | decision | reason |
|---|---:|---|---|
| **`Gamma0Rationality.lean`** | | | |
| `tσ_lift` | 27 | **promote** | the σ-transport existence: a `Tσ`-related pair lifts to `RatAt` data at every `M ≥ m` with matching `phiOf`-images — the Galois transport engine |
| `exists_discSeries` | 10 | **promote** | a `K`-valued series with rational coefficients whose `algebraMap`-image is `qExpansion N Δ` — the discriminant rationality input |
| `aeval_relPoly` | 9 | **promote** | the relation-polynomial evaluation identity `aeval … (X·Q − P) = G·evφ Q − evφ P` — the diamond-rationality interpolation |
| `map_phiOf_eq_of_rat` | 9 | **promote** | Galois acts as the ℂ-embedding on a rational-coefficient series — the rationality descent |
| `evφ_algebraMap` | 3 | keep | `rfl` adapter (`evφ` at `algebraMap` *is* `ev`) |
| **`Gamma1Basis.lean`** | | | |
| `qExpansion_disc_rat_one` | 12 | **promote** | rationality of Δ's width-1 q-expansion — a rationality statement in its own right |
| `qExpansion_widthN_rat_of_levelOne` | 9 | **promote** | width-1 rationality transfers to width `N` for level-one forms — the cusp-width transfer |
| `disc_smul`, `E₄_smul` | 7, 6 | keep | slash formulas specialised from `SlashInvariantForm.slash_action_eqn''` — adapters |
| `coe_discForm` | 6 | keep | coercion identity, proved by `ring` |
| `gen_ds_eq`, `gen_id_eq` | 7, 2 | keep | `rfl` unfoldings of `gen` |
| `bdd_pow`, `exists_ne_zero`, `periodic_sub`, `periodic_disc` | 5, 5, 5, 3 | keep | generic analysis glue |
| `idxMap` | 5 | keep | a def for the index map |
| `disc_ne_zero`, `mem_SL` | 2, 2 | keep | one-line mathlib wrappers |
| **`Gamma0Integral.lean`** | | | |
| `constantCoeff_P4`, `constantCoeff_P6` | 3, 3 | keep | `constantCoeff (P4) = 1` arithmetic |
| **`Defs/GammaRational.lean`** | | | |
| `T_pow_mem_Gamma1` | 4 | keep | group bookkeeping `T^t ∈ Γ₁` (port name `T_zpow_mem_Gamma1_aux`) |
| **`JqIntegralRatios.lean`** | | | |
| `isIntegralQExp_E4` | 10 | **promote** | `E₄` has integral q-expansion — an integrality statement, part of the `IsIntegralQExp` API |
| `A12`, `D12`, `AΓ`, `BΓ` | 5, 4, 2, 2 | keep | one-line `restrictForm` defs; the parser's *type-only* matches to the port's single private `e4cube`/`delta`, and the pin has four distinct names — the new module writes the pin's own defs |
| **`DeligneSerre/Lifting.lean`** | | | |
| `zetaU` | 2 | keep | packaging (`Units.mk0`) — and the port's `zetaUnit` is the generalised form over an arbitrary primitive root, not the pin's `zetaU ℓ` |

The seven promotions all matched a pin public copy in the five target `S_` files
(three of which were already in `SOURCES`), so **no new `SOURCES` wiring was
needed for them**; the checker count moved by exactly `+7`, `0/0`.

## 4. Verification

| gate | result |
|---|---|
| checker | **6602 identical (312, 83), 0 mismatched, 0 missing** — baseline 6520, +75 for JOneES, +7 for the hubs |
| one-token mutation (`intSeriesC_E4_cube_ne_zero`) | `6601 / 1 mismatched`, reverted |
| tier 0 `lake env lean` | `JqIntegralRatios` 25 s, `Gamma0Rationality` 26 s, `Gamma1Basis` 32 s — green |
| tier 1 `lake build` | `JqIntegralRatios` 4 s, `Gamma0Rationality` 28 s, `Gamma1Basis` 43 s (with `Gamma0Integral` 16 s) |
| wave | `ModularPolynomialE4Cube` 280 s, `Frobenius.QExpModL` 165 s, `XH.DiamondLift` 86 s, … — the full cascade is **9,206 jobs**, green |

The promoted declarations keep the pin's spelling, so the new modules transcribe
the pin bodies and drop into the public API. The 21 kept-private rows are
re-derived in the consumer module; the two that are more than bookkeeping are
`tσ_lift`-adjacent work the consumer does not need (see §3) and the `A12`/`D12`
family, where the pin's own definitions are written fresh.

## 5. Regenerate

```bash
cd tools/deps
python3 build_ladder.py --edit FLTForHuman/ModularCurve/JqIntegralRatios.lean
python3 build_ladder.py --edit FLTForHuman/ModularForms/WeightOne/Gamma0Rationality.lean
python3 build_ladder.py --edit FLTForHuman/ModularForms/WeightOne/Gamma1Basis.lean
cd ../lean
timeout 300 python3 spec/check_flt_statements.py        # 6602 / 0 mismatched / 0 missing
flock .lake/flt_build.lock timeout 900 lake build       # 9,206 jobs, green
```
