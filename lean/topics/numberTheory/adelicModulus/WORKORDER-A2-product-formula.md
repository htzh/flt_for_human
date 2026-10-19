# WORKORDER-A2 — the product formula: principal ideles preserve Haar (tier 3)

**Status: landed 2026-10-13** — results in §9.

Read [TOPIC-adelic-modulus.md](TOPIC-adelic-modulus.md) first; §1 carries the mathematics
(the corollary half) and §4 the four-node chain. This order is one engine module and
nothing else.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

## 1. Scope

Write **one tier-3 engine module**:

`FLTForHuman/NumberTheory/AdelicHaar/ProductFormula.lean` — the four chained pin `S_`
files below, 177 net new lines, 17 declaration groups.

**Explicitly not this order.** The four `solution` declarations (the façade owns the four
wrapped headlines), the tier-1 façade, `SOURCES`/`PORT_FILES` wiring,
`spec/UNWIRED-PUBLIC.md`, `spec/old_check_stmts.py`, and everything in
WORKORDER-A1. No promotion, no edit to any existing module.

## 2. The chain, in dependency order

Transcribe each file whole, except its `solution`:

| # | pin file | new declarations | net new |
|---|---|---|---:|---:|
| 1 | `P2M/Sol/S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.lean` | `FltWs24.AdelicModulusOne.isAddFundamentalDomain_preimage_mul` (18) | 36 |
| 2 | `P2M/Sol/S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean` | `FltWs24.AdelicModulusOne.principalUnit` (16), `mul_eq_coe_mulLeft` (22), `countable_principalSubgroup` (26), `addHaarScalarFactor_map_mulLeft` (33), `measurePreserving_mul` (65) | 71 |
| 3 | `P2M/Sol/S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.lean` | `FltWs24.regular_adelicAddHaar` (13) | 16 |
| 4 | `P2M/Sol/S_NumberField_AdeleRing_distribHaarChar_algebraMap.lean` | `FltWs24.AdelicModulusOneChar.addHaarScalarFactor_eq_one_of_integral_eq` (16), `distribHaarChar_algebraMap_impl` (37) | 54 |

File 2 imports file 1's wrapper (`Theorems.Thm_…_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox`)
and file 3 imports file 2's wrapper; in the port the module's own declarations replace
those wrappers, so the order is a **section order inside one file**, not an import order.
Keep the pin's `local notation "𝔸"` and `variable (F : Type) [Field F] [NumberField F]`
scoping as they are.

The four `solution`s are the four headlines of the manager's façade:

| pin file | headline (wrapper statement) |
|---|---|
| 1 | `NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox` |
| 2 | `NumberField.AdeleRing.measurePreserving_mul_algebraMap` |
| 3 | `NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar` |
| 4 | `NumberField.AdeleRing.distribHaarChar_algebraMap` |

## 3. What is already in the port and must be imported

* `FLTForHuman/NumberTheory/AdelicBox.lean` — `AdelicBox.adelicBox`, `AdelicBox.measurableSet_adelicBox`,
  `AdelicBox.existsUnique_algebraMap_add_mem_adelicBox`, `AdelicBox.isAddFundamentalDomain_adelicBox`.
* `NumberField.AdelicHaar.adeleBorel`, `borelSpace_adeleBorel`, `adelicAddHaar`,
  `isAddHaarMeasure_adelicAddHaar` — the `NumberTheory/AdelicHaar/` directory.
* `AdeleRing.principalSubgroup`, `algebraMap`/`Units.map` API — mathlib + the port.
* `NumberField.TateGlobal.distribHaarChar`-related bridge lemmas as needed
  (`NumberField/TateGlobal/Defs.lean`).

`port_advise` reports **0 substitutions** on the four files: all 17 declarations are new.

## 4. Transcription rules

* Keep the pin's namespaces (`FltWs24.AdelicModulusOne`, `FltWs24.AdelicModulusOneChar`),
  declaration names and statements **verbatim**. Drop the outer `P2MW.S_…` namespace and
  every `p2m_*` line; keep `set_option autoImplicit false`, `noncomputable section` and the
  pin's `open`/`open scoped` lines.
* No pin declaration in the four files is `private`; everything stays public.
* Every transcribed declaration carries, immediately above it (above any `@[...]`), a
  provenance comment `-- pin: <name> (<S_ basename>:<line>)`.
* Replace the pin's bare `import Mathlib` with the specific imports actually used.
* `attribute [local instance] NumberField.AdelicHaar.adeleBorel` (file 3) is file-local; keep
  it in the section it belongs to.

## 5. Route, mathlib map, and stop conditions

* **Statements are the pin's**; a documented `v4.34.0` drift is the only permitted
  difference. Proofs are adapted freely. **If a proof needs a statement to change, stop and
  report.**
* Expected drift surface: `IsAddFundamentalDomain.mk'` and `MeasureTheory.Measure.IsAddHaarMeasure`
  API, `addHaarScalarFactor` and `MeasureTheory.Measure.Haar.Unique`, `Regular` measure
  instances, `ContinuousAddEquiv.mulLeft`, `Function.Surjective.countable` /
  `Module.finBasis`, and the `PrincipalSubgroup` quotient.
* **No new helpers beyond the pin's.** If a proof needs glue the pin does not have,
  re-derive it `private` in the same module and report it. **No promotion and no edit to any
  existing module.** If you believe a promotion is genuinely required, **stop and report**
  the declaration, host and `tools/deps/build_ladder.py --edit` price — the manager decides.
* **Stop and report** if the chain cannot be kept self-contained against `AdelicBox.lean` +
  the `AdelicHaar/` directory + mathlib, or if the four sections cannot share one file.

## 6. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with
> `flock` and bounded with `timeout`. Per wave, build only the wave's affected targets —
> **never a bare whole-tree `lake build`**. A whole-tree build happens once, at the
> session's end, and only with the user's permission.

Concretely: iterate at the low cap until the module is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.NumberTheory.AdelicHaar.ProductFormula`.
Build only this module and its dependencies.

**Build-time blow-up protocol.** The named risk is
`addHaarScalarFactor_map_mulLeft` (32 lines, the unique-Haar argument); if it exceeds the
low cap, diagnose with `set_option diagnostics true` / `trace.Meta.synthInstance true` in a
scratch copy (never commit it), fix the inference, and re-run. Report the declaration and
the fix.

## 7. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `ProductFormula.lean` | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock … lake build FLTForHuman.NumberTheory.AdelicHaar.ProductFormula` | green; record jobs and wall/user time |
| name parity against `port_advise` on the four files | all 17 new names present once each, none invented, the four `solution`s absent |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

Do **not** run `spec/old_check_stmts.py` and do **not** edit the register. No wiring
for this order: the engine is tier 3.

## 8. Report shape

1. The module path, final line count, and the pin file → section map as built.
2. Declaration counts, public / `private`; confirm all four `solution`s are absent and the
   managers' four headline names are free.
3. Tier-0 and tier-1 results, with wall/user/sys times and jobs.
4. Every build-time blow-up, the declaration, the diagnosis, and the fix.
5. Any statement that could not be transcribed verbatim, and why (stop condition).
6. Any helper re-derived `private`, and any promotion you stopped on.

## 9. Results as landed (2026-10-13)

| | |
|---|---|
| engine | `FLTForHuman/NumberTheory/AdelicHaar/ProductFormula.lean` — **216 lines, 9 public declarations, 0 `private`** |
| tier 0 | exit 0, **0 warnings**, no forbidden token |
| tier 1 | 3,450 jobs, first build wall 7.858 s / user 6.195 s / sys 3.621 s; cached re-run wall 2.296 s |
| façade | `FLTForHuman/NumberTheory/AdelicModulus.lean` — the four headlines below, tier 1 |
| checker | **9571 → 9575 identical (+4)**, 0 mismatched / 0 missing / 38 own (9,613 checked) |
| mutation | one token on `NumberField.AdeleRing.distribHaarChar_algebraMap` (`= 1` → `= 2`) → exactly **1 mismatched** (9,574), reverted |
| axioms | all four headlines `[propext, Classical.choice, Quot.sound]` |
| existing modules edited | **none** — no promotion, no hub wave; the engine stays tier 3 |

The four landed headlines:

* `NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox`
* `NumberField.AdeleRing.measurePreserving_mul_algebraMap`
* `NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar`
* `NumberField.AdeleRing.distribHaarChar_algebraMap`

**The order's "17 declarations" was the pin budget (declaration *groups*), not the port's
share.** The four pin `S_` files hold 9 declarations of their own plus the 4 `solution`s and
the 4 `Theorems/` wrappers; the port transcribes the 9 as the engine and the 4 as the façade
headlines, and the 4 wrappers are `SOURCES`-only. 9 + 4 = 13, and the checker's +4 counts the
wrappers' statements against the façade.

**Proof adaptations (statements verbatim).**

1. `regular_adelicAddHaar`: the pin's `first | exact … | (unfold …) | (delta …)` keeps only
   its first, succeeding alternative in `v4.34.0` (the other two were unreachable tactics).
2. `distribHaarChar_algebraMap_impl`: the pin calls the `Theorems/` wrapper
   `NumberField.AdeleRing.measurePreserving_mul_algebraMap`; inside the one engine module that
   wrapper does not exist, so it calls `AdelicModulusOne.measurePreserving_mul` and
   `…isAddFundamentalDomain_preimage_mul` directly. The façade's headline 3 calls the façade's
   own headline 2, exactly as the pin's `solution` does.
3. The pin's `letI`/`haveI` walls carry the house file-level
   `set_option linter.style.haveILetI false`; the façade's `adelicAddHaar` headline carries the
   narrow per-declaration form (three load-bearing `haveI`s).

**Recorded negative.** The subagent's report that `unwired_register.py --check` was stale
*before* this order was wrong: the staleness was this order's own new tier-3 module (9 rows,
one new module) plus the façade's import edge on it. The register was reverted to `HEAD` and
is regenerated once the whole round's modules are reviewed and frozen.
