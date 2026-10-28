# WORKORDER RB1 — a place from a ramified Hahn-series embedding

Scope: **one new definition module**, **one insertion** into
`FLTForHuman/AlgebraicCurve/Place/ValueDictionary.lean`, and **one port-native public theorem** (the
`ℚ`-valued order-map realisation), for which the manager writes the `own:` row before dispatch. Nothing
else may be edited. (Part of SET 5, [SET-5.md](SET-5.md) §1 and §4.4 — **route (b)**, the engine
generalised, paid now.)

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | decls | home |
|---|---|---:|---:|---|
| `AlgebraicCurve.Place.exists_ord_mul_eq_order_of_hasRamBound` | `S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound` | 340 | 23 | insert into `Place/ValueDictionary.lean` |

plus the pin definition module the statement needs:

| pin module | decls | home |
|---|---:|---|
| `Definitions/Def_HahnSeries_RamificationBound.lean` | 7 | **new** `FLTForHuman/AlgebraicCurve/Defs/HahnSeriesRamificationBound.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`:
<https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound.lean>,
<https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_HahnSeries_RamificationBound.lean>.
**Statement from the node's `Theorems/` wrapper**, proof written fresh (see below).

**The mathematics.** A `K`-algebra map `φ : F →ₐ[K] HahnSeries ℚ L` whose values are ramified of
bounded denominator (`HasRamBound d`: every support point lies in `(1/d)ℤ`), and which is not
order-trivial, arises from a place: there are `w : Place K F` and a positive rational `g` with
`(w.ord x : ℚ) * g = (φ x).order` for every `x`.

## The route (do not transcribe the pin's construction)

The pin proves this from scratch (23 public declarations: `map_ne_zero`, `order_map_mul`, …,
`valuationSubring`, `exists_generator`, `irreducible_gen`, `hasUnitMulPowIrreducibleFactorization`,
`place`, `ord_mul_order_gen`, `solution`). **Do not port that construction.** The port already has
the realisation core `Place.exists_of_orderMap` (`Place/ValueDictionary.lean:1013`): a
`WithTop ℤ`-valued order map (multiplicative, nonarchimedean, trivial on constants, non-trivial)
is `e` times the order of a place, for some `e : ℕ`, `0 < e`. The pin's ramified case reduces to it:

1. **Write the definition module** (`Defs/HahnSeriesRamificationBound.lean`): `HahnSeries.ramScale`,
   `ramScale_apply`, `ramScale_injective`, `ramScale_le_iff`, `puiseuxRamEmb`,
   `HasRamBound`, `puiseuxRamSubfield`, transcribed verbatim at the pin's names and namespace
   (`namespace HahnSeries`), with its `spec-pin:` wire. It is `import Mathlib`-only in the pin.
2. **The denominator lemma.** The pin's `exists_int_order_mul` (line 129): from `hφ`, `∀ x`,
   `∃ k : ℤ, (φ x).order * d = k`. Port it as written.
3. **The scaling adapter** (private to the insertion): with `μ x := if φ x = 0 then ⊤ else
   ↑(d * (φ x).order)` (the integer from step 2), prove `exists_of_orderMap`'s five hypotheses:
   `h_top` from `φ` injective on a field, `h_mul` / `h_add` / `h_const` by transferring mathlib's
   `HahnSeries.order_mul`, `HahnSeries.min_order_le_order_add`, `HahnSeries.order_C` through
   `Int.cast_injective` into `WithTop ℤ`, `h_nontriv` from the pin's `hnt` and `d > 0`.
   `HahnSeries.order_pow`, `order_single`, `order_neg`, `order_one` are also in v4.34, so the pin's
   six `order_map_*` helpers are one-liners at most — do not write six proofs for them.
4. **Apply the engine** and conclude: `e * P.ord x = d * (φ x).order` gives the node's `g = e/d`.
   At `x = 0` both sides are `0` (`Place.ord_zero`, and `HahnSeries.order` has the junk value `0` at
   the zero series), so the `∀ x` form is fine; watch these two junk values, they are where the
   adapter's case analysis lives.
5. **The `ℚ`-valued engine, public** (the manager's `own:` row, written before dispatch):
   `Place.exists_of_orderMap_rat` — the same five hypotheses for `μ : F → WithTop ℚ`, a common
   denominator `d` (`∀ x, ∃ k : ℤ, μ x = k / d`), conclusion `∃ P g, 0 < g ∧ (∀ x, x ∈
   P.toValuationSubring ↔ 0 ≤ μ x) ∧ ∀ x, x ≠ 0 → μ x = g * (P.ord x : ℚ)`. Its proof is the same
   scaling reduction, so it is a wrapper over the `ℤ` engine, not a second engine. State it in
   `Place/ValueDictionary.lean` beside `exists_of_orderMap`, which keeps its statement and wire
   untouched; **import, do not restate, `exists_of_orderMap`.**
   Step 3–4 should be written *as* the derivation from this `ℚ` statement if that is shorter; the
   headline then needs only the `HasRamBound` bookkeeping. Either order of writing is fine; the two
   statements must not duplicate the engine's proof.

**What is not written:** the pin's `valuationSubring`, `mem_valuationSubring_iff`, `coe_ne_zero`,
`ne_zero_of_coe_ne_zero`, `isUnit_iff_order_eq_zero`, `posOrders`, `posOrders_nonempty`,
`exists_generator`, `gen_ne_zero`, `gen_mem`, `exists_nat_of_mem`, `irreducible_gen`,
`hasUnitMulPowIrreducibleFactorization`, `place`, `ord_mul_order_gen`. They re-prove what the engine
proves. `port_advise` reports the node's `valuationSubring` as a `qIntegersBar` match — a false
positive of its `def … : Subring` tier; ignore it. If the derivation turns out **not** to reach the
pin's exact statement, stop and report with the obstruction rather than falling back to the
transcription — the route is the reviewer's decision, not a preference.

## Why this home (do not re-home it)

`Place/ValueDictionary.lean` (1,178 lines, 4 `spec-pin:` lines, 1 importer) is the module of
`exists_of_orderMap`, i.e. of the order-map→place realisation, and the ramified case is that
realisation with a denominator. `Place.exists_of_orderMap` is at line 1013 and the module imports
`Defs/Place` (for `Place`, `Place.ord`) — no new import is needed for the headline beyond the two
new modules'.

## Rules

- The new definition module: header `/- … -/` with prose and `spec-pin:` lines for the pin `Def_`
  file; `set_option autoImplicit false`, `noncomputable section`; the pin's `namespace HahnSeries`
  and names verbatim.
- The insertion: append to `Place/ValueDictionary.lean` (after `exists_of_orderMap`) and add the
  node's wrapper **and** `S_` file to its existing `spec-pin:` block; keep every existing
  declaration untouched. The `ℚ`-valued engine's `own:` row must be in `spec/decl_markers.tsv`
  before this order runs (the manager writes it; a `spec-pin:` line is **not** added for it — it has
  no pin source). If it is missing, stop and report.
- Universe and binder spelling from the wrapper, character for character.
- Imports stay specific: **never `import Mathlib`** in a library module. Replace the pin's
  `import Mathlib` (and any broad import a `S_` file carries) with the specific mathlib modules the
  file needs — playbook §4's hygiene rule.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>` from `lean/`; finished modules `flock .lake/flt_build.lock timeout
  110 lake build <module>`. Every command under 2 minutes, its own `timeout`, no loops; logs under
  `lean/tmp/rb1-*.log`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** per module, the added
  declaration `ok`; `#print axioms` on the headline and on the `ℚ` engine →
  `[propext, Classical.choice, Quot.sound]`; 0 warnings; no `sorry`/`admit`/`axiom`; no
  `set_option maxHeartbeats`; no commit.
- If a proof needs a `private` port helper or a declaration below its home, **stop and report** —
  do not promote, do not restate, do not edit a hub.

## Report (one message)

both modules' builds + warnings and checker summary lines; the axioms lines; the line count of the
derivation split as definition module / denominator / adapter / engine / headline; the exact
`ℚ`-engine statement as written (it is the set's one port-native public theorem); any blocker.
