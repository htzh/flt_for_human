# SET-AF53 — the adelic Haar measure: the product formula and the coordinate hyperplanes

**Status: LANDED (2026-11-12).** Read off the same eleven-marker corrected shelf
(`needed` **699 / 292,705**, `NumberField` demand 97 / 33,513).

**3 rows / 462 silo / ≈430 net in 54 declarations** — the measure-theoretic facts the factorizable-test-
function and Bruhat–Eisenstein integrals consume, and the column's first `NumberTheory/AdelicHaar` set
since that layer landed.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod` | 215 | 3/5 | the `GL n` Haar measure is a scalar times the product of the archimedean and finite measures |
| **A2** | `NumberField.AdelicHaar.adelicAddHaar_setOf_fst_apply_eq_eq_zero` | 128 | 1/1 | the measure of `{x | x.fst = 0}` is zero |
| **A3** | `NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero` | 119 | 1/1 | the same for `{x | x.snd = 0}` |

**Premises**: all ported (the product formula's and the modulus character's rows, plus
`secondCountableTopology`). **Definition gate**: closed (`Def_NumberField_AdelicHaar`,
`Def_NumberField_AdelicLevel`). **Price**: raw 462 / 54 declarations / ≈430 net, one dispatch.

**Home and manager layer** (landed and measured): `NumberTheory/AdelicHaar/ProductMeasure.lean`,
310 lines, 54 declarations, **23 ok / 0 / 0** (the rest are `private` in the pin), 42 `sorry`s. The pin's
labels `Ws1.L1` → `ProductMeasure.L1`, `NULLW` → `FstHyperplane`, `NULLV` → `SndHyperplane` are rectified;
the nine data definitions (`fwd`, `glue`, `bwd`, `splitMulEquiv`, `aAd`, `aInv`, `pi`, …) are transcribed and
building; the module imports `AdelicHaar/{Adele,GeneralLinear,ProductFormula,AdelicModulus,PlaceMeasure}` and
`AdelicDock/LocalEmbedding` (for `AdelicDock.splice`, which the hyperplane arguments use).

**Order**: `tmp/af53/WORKORDER-AF53A-adelic-haar-product-measure.md`.

## 2. The landing (2026-11-12)

| module | lines | `sorry` → | `check_port` | build | axioms |
|---|---|---|---:|---|---|
| `NumberTheory/AdelicHaar/ProductMeasure.lean` | 310 → **492** | 42 → 0 | **23 ok / 0 / 0** | 3,697 jobs, 5.6 s | 3/3 clean |

Silent at 200,000 heartbeats with zero warnings, no `set_option` beyond `autoImplicit false`, no silencer,
no import added (the one transitive dependency, `NumberField.AdeleRing.secondCountableTopology`, is reached
through the already-imported `AdelicHaar/PlaceMeasure`). `dedup` reports one intra-module cluster of 20
lines — the wrapper headline repeating the frozen statement of `ProductMeasure.L1.main`, i.e. the pin's own
wrapper/engine pair, kept; `move_dead` 0. The consumer zone (53 lines) executes three compositions: the
product formula at `GL2/Q` under the four measurable-space hypotheses, and both hyperplane theorems composed
with `Set.inter_univ`. `#check` at the three wrapper names resolves each at `NumberField.AdelicHaar.*`.

**Deviations worth recording**: the pin's `rw [Prod.ext_iff]`/`[map_sum]` no longer match at v4.34's
*reducible* transparency on `Matrix`/`AdeleRing` (FR-0187's family: spell the term), `simp; rfl` → an
entrywise `change` with `Matrix.one_apply_eq/ne`, the pin's unported product-formula name replaced by the
port's `…_of_snd_eq_one_impl` and `ZhatModulus.distribHaarChar_eq_placeModulus`, and two proofs consume an
auto-included hypothesis rather than `omit`ting it.

**Manager cleanup at the landing**: three of the wrapper blocks had injected duplicate
`set_option autoImplicit false` lines into the module body (the generator's `wrapper_block` filtered
`set_option maxHeartbeats` but not this one); the lines were deleted and the module re-elaborated, and the
generator now drops every pin `set_option` line. This is the fifth generator failure mode, recorded with the
other four in FR-0188.

**Forecast**: `needed` (after AF52) → **693 / 291,557**; frontier **+462**; `NumberField` demand
97 / 33,513 → **94 / 33,051**.

**Not this set**: the adelic-box pair (`setLIntegral_adelicBox_comp_mul_add_eq_of_periodic` 129 +
`integral_cond_adelicBox_comp_mul_algebraMap` 122). They were **cut at scoping**: their statement layer
references `adelicAddHaar`/`AdeleRing.principalSubgroup` and opens `AutomorphicForm`, and the first
scaffold attempt failed on those names with the frozen import set — i.e. the home's import cone needs the
`AutomorphicForm/Adelic/*` layer, which is a pricing question for the next scoping, not a proof problem.
Both rows stay on the shelf and are named in SET-AF50 §5.
