# WORKORDER-E3 — factorization of the finite-adelic integral into an Euler product

**Status: issued 2026-10-18.** Read
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3–§4,
[porting-playbook.md](../../../porting-playbook.md) §3–§5, and
[TOPIC-local-twisted-integral.md](TOPIC-local-twisted-integral.md) §1 for the cluster this
feeds (the local twisted integral; this node is its global factorization).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

**The set: one leaf silo, 864 pin lines, 58 declarations, 839 net new, 0 substitutions.** It is
the analytic heart of the Godement–Eisenstein construction: an integral of a product
`∏ᶠ v, h v (x v)` over the finite adèles factorizes into the Euler product `∏' v, …`, given
that the local factors are integrable, are `1` on the unit ball outside a finite set `S`, and
that the deviations from `1` are summable. **This is a pure transcription** — nothing of it is
already in the port — so the whole job is faithful copying and the drift surface is mathlib
`v4.33.1 → v4.34.0`.

## 1. Scope

Six new files, nothing else. Five tier-3 engines and one listed façade:

| # | module | pin lines | decls |
|---|---|---:|---:|
| 1 | `FLTForHuman/EisensteinGeneral/Factorization/ProductMeasure.lean` | 26–98 | 1 |
| 2 | `FLTForHuman/EisensteinGeneral/Factorization/Stratum.lean` | 99–283 | 32 |
| 3 | `FLTForHuman/EisensteinGeneral/Factorization/Measure.lean` | 287–438 | 10 |
| 4 | `FLTForHuman/EisensteinGeneral/Factorization/Integrability.lean` | 442–600 | 7 (+1 substituted) |
| 5 | `FLTForHuman/EisensteinGeneral/Factorization/Tprod.lean` | 601–749 | 5 |
| 6 | `FLTForHuman/EisensteinGeneral/Factorization.lean` — **listed façade** | 750–864 | 1 |

All six are **listed in the checker** (the manager wires `PORT_FILES` for all six and the pin
`S_` file in `SOURCES`), because every declaration here is new, unique to this subject, and has
no other consumer: listing them puts 56 declarations under the statement checker instead of
leaving them unchecked in tier-3 engines. That is a deliberate departure from the
engine-tier-3/façade-tier-1 shape used by WORKORDER-T5 and E1, justified by the same argument as
WORKORDER-E2: no future importer will ever justify hiding this surface. **Consequence for you:**
every declaration needs its `-- pin: <name> (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:<line>)`
marker, and its statement must be the pin's character for character (proof bodies may adapt).

**Explicitly not this order.** Any other `EisensteinGeneral` row; the `AutomorphicForm`
consumers of this factorization; any edit to an existing module.

## 2. Pin sources

* statement authority: `Theorems/Thm_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean`
  (10 lines — state the headline **verbatim** from it);
* proof: `P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean`
  (read-only at `~/proj/fermats-last-theorem/P2M/Sol/`), `solution` at 842–864.

The pin's file structure is four sections plus two more; keep them as the module boundaries:

| pin section | lines | module |
|---|---|---|
| `section Recognition` (general `G`, `Y`) | 20–93 | 1 |
| `section Places` (`Stratum` … `measurableEmbedding_incl`) | 95–283 | 2 |
| `section Measures` + `section StratumIdentity` (`rhoT` … `measureReal_box_ne_zero`) | 285–438 | 3 |
| `section Generic` + `section LocalIntegrals` (`integrable_of_forall_setIntegral_norm_le` … `inv_measure_mul_setIntegral_integralOffSet_finprod_eq`) | 440–600 | 4 |
| rest of `section LocalIntegrals` (`integrableOn_finprod_stratumSet` … `multipliable_normalized_integral`) | 601–749 | 5 |
| the headline | 750–841 | 6 |

The pin's `namespace FiniteAdelicFactorization` is kept (dropping only the `P2MW.S_…` prefix):
engines declare in `namespace EisensteinGeneral` / `namespace FiniteAdelicFactorization`; the
façade declares the headline at the wrapper's dotted name `EisensteinGeneral.Factorization.…`
(after `end EisensteinGeneral`, as `LocalRam.lean`/`LocalUnr.lean` do). The pin's `p2m_*`
scaffolding is dropped.

## 3. The declarations, module by module

### M1 — `ProductMeasure.lean` (pin 26–98)

`section Recognition`, variables
`{G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Y : Type*} [MeasurableSpace Y]`:

| pin | declaration |
|---:|---|
| 26 | `exists_eq_prod_of_forall_map_add_left` (73 lines) — a measure on `G × Y` invariant under `(a + ·, ·)` is `μ.prod σ` |

This is the only `Recognition` declaration. Note `T2Space G` is a *local* hypothesis of the
theorem (`[T2Space G]` in the binder list), not a section variable.

### M2 — `Stratum.lean` (pin 99–283)

`section Places`, `variable (F : Type) [Field F] [NumberField F]`. **32 declarations**, in this
order (all `private` in the pin, all public in the port):

| pin | declaration |
|---:|---|
| 99 | `countable_heightOneSpectrum` (21 lines) |
| 120 | `isOpen_adicCompletionIntegers` |
| 124 | `Stratum` (`abbrev`, the `Πʳ` restricted product at the level `𝓟 (Tᶜ)`) |
| 128 | `cofinite_le` (`omit [NumberField F] in`) |
| 132 | `incl` (`def`, `RestrictedProduct.inclusion _ _ (cofinite_le F T)`) |
| 136 | `incl_apply` (`@[scoped simp]`, `variable {F} in`) |
| 139 | `isOpenEmbedding_incl` |
| 142 | `stratumSet` (`def`) |
| 145 | `GT` (`abbrev`) |
| 147 | `YT` (`abbrev`) |
| 151 | `mem_of_not_mem` |
| 155 | `range_incl` |
| 165 | `isOpen_stratumSet` |
| 171 | `glue` (`def`, `open scoped Classical in`) |
| 176 | `glue_of_mem` |
| 181 | `glue_of_not_mem` |
| 186 | `splitFun` (`def`) |
| 189 | `splitInv` (`def`) |
| 195 | `splitInv_apply` |
| 199 | `splitFun_fst` |
| 203 | `coe_splitFun_snd` |
| 209 | `splitInv_splitFun` |
| 218 | `splitFun_splitInv` |
| 224 | `continuous_splitFun` |
| 229 | `continuous_glue` |
| 238 | `continuous_splitInv` |
| 241 | `split` (`def`, a `≃ₜ` homeomorph `Stratum F T ≃ₜ GT F T × YT F T`) |
| 249 | `split_apply` (`@[scoped simp]`) |
| 253 | `split_symm_apply` (`@[scoped simp]`) |
| 258 | `incl_add` |
| 263 | `incl_sub` |
| 267 | `split_add_symm` (30 lines) |

Keep the pin's `variable {F} in` / `omit [...] in` / `open scoped Classical in` prefixes and the
`@[scoped simp]` attributes where they appear (they are part of the text the checker compares for
the theorem statements only, but the attributes matter for elaboration).

**`attribute [local instance] countable_heightOneSpectrum`** (pin 118) follows the theorem: re-emit
it in every module that needs the `Countable (HeightOneSpectrum (𝓞 F))` instance, since `local
instance` attributes do not cross module boundaries.

### M3 — `Measure.lean` (pin 287–438)

`section Measures` (`variable (F) … [ν.IsAddHaarMeasure]`, the full instance context of the
headline) and `section StratumIdentity`:

| pin | declaration |
|---:|---|
| 297 | `measurableEmbedding_incl` (`omit [∀ v, BorelSpace …] in` — keep the clause) |
| 300 | `rhoT` (`def`, `(ν.comap (incl F T)).map (split F T).toMeasurableEquiv`) |
| 305 | `setIntegral_stratumSet_eq` (`omit [ν.IsAddHaarMeasure] in`) |
| 316 | `integrableOn_stratumSet_iff` (`omit [ν.IsAddHaarMeasure] in`) |
| 332 | `comap_incl_map_add_left` |
| 349 | `rhoT_map_add_left` |
| 364 | `rhoT_prod_univ_lt_top` |
| 372 | `exists_rhoT_eq_prod` (51 lines — applies M1) |
| 423 | `measureReal_integers_ne_zero` |
| 432 | `measureReal_box_ne_zero` |

### M4 — `Integrability.lean` (pin 442–600)

`section Generic` then `section LocalIntegrals`:

| pin | declaration |
|---:|---|
| 442 | `integrable_of_forall_setIntegral_norm_le` (41 lines; `omit` three instance arguments as the pin does) |
| 483 | `exists_exhaustion` |
| 497 | `stratumSet_mono` |
| 504 | `exists_mem_stratumSet` |
| 517 | `iUnion_stratumSet_eq_univ` |
| 531 | **`integralOffSet` — do NOT port**: it is `NumberField.TateGlobal.ShellSupport.integralOff` (`NumberField/TateGlobal/ShellSupport.lean:44`), the same definition (`{x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}`). Import it and use `integralOff` in the proofs; the register then has one copy, not two. |
| 534 | `finprod_incl_split_symm` |
| 552 | `inv_measure_mul_setIntegral_integralOffSet_finprod_eq` (49 lines) |

### M5 — `Tprod.lean` (pin 601–749)

| pin | declaration |
|---:|---|
| 601 | `integrableOn_finprod_stratumSet` |
| 625 | `setIntegral_norm_finprod_stratumSet_eq` (40 lines) |
| 665 | `measureReal_integers_le_integral_norm` |
| 682 | `norm_normalized_integral_sub_one_le` (42 lines) |
| 724 | `multipliable_normalized_integral` (26 lines — the product-convergence input) |

### M6 — `Factorization.lean`, the façade (pin 750–864)

One declaration: the wrapper's headline, verbatim, proved by the pin's `solution` body (92
lines). State it at `EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod`.

## 4. What is already in the port — import, never re-prove

| pin name | port home |
|---|---|
| `integralOffSet` | `NumberField.TateGlobal.ShellSupport.integralOff` (**substitution**, see M4) |
| `AdelicBox.integralFiniteAdeles`, `…isOpen_integralFiniteAdeles`, `…isCompact_integralFiniteAdeles` | `NumberTheory/AdelicLevel/IdealBall.lean:159,186,225` and `NumberTheory/AdelicBox.lean:374,378` |
| `RestrictedProduct.{inclusion, isOpenEmbedding_inclusion_principal, continuous_eval, continuous_rng_of_principal, ext, add_apply}` | mathlib `Mathlib/Topology/Algebra/RestrictedProduct/*` (+ the port's `Topology/Algebra/RestrictedProduct/Basic.lean`) |
| `Homeomorph.toMeasurableEquiv`, `MeasurableEmbedding.{map_comap, integral_map, integrable_map_iff, comap_apply, map_apply}`, `integral_map_equiv`, `Measure.comap`, `Measure.prod`, `Measure.real`, `Multipliable`, `tprod`, `finprod` | mathlib |

The pin's four imports are mathlib files the port also has:
`Mathlib.MeasureTheory.Measure.Haar.Unique`, `Mathlib.MeasureTheory.Integral.Pi`,
`Mathlib.Analysis.SpecialFunctions.Log.Summable`, `Mathlib.Topology.Algebra.InfiniteSum.Order`.
Import them explicitly (do not rely on transitivity) plus the port's AdelicBox/IdealBall/ShellSupport
modules.

Read `ShellSupport.integralOff`'s statement before relying on the substitution; if its definition
is not the pin's `integralOffSet` verbatim, **stop and report** rather than adapt a statement.

## 5. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect. Diagnose
> it (`set_option diagnostics true`, `trace.Meta.synthInstance true` on that one declaration, in
> a scratch copy under `tmp/`), fix the inference, re-run. Never raise `maxHeartbeats`, never add
> a module `set_option maxHeartbeats`. When a file is done,
> `flock .lake/flt_build.lock timeout 300 lake build <module>`. Every `lake build` serialized and
> bounded. **Never a bare whole-tree `lake build`.**

**Hub prohibition.** Do not edit `TateGlobal/ShellSupport.lean`, `NumberTheory/AdelicBox.lean`,
`NumberTheory/AdelicLevel/*`, `Topology/Algebra/RestrictedProduct/*`, `EisensteinGeneral/*`
(Set A/B and the engines you write), or any other existing module. If you believe a promotion or
a new helper in an existing module is required, **stop and report** with the declaration, host
and `build_ladder.py --edit` price.

**Drift surface.** All of it is mathlib `v4.33.1 → v4.34.0`, in the measure/Haar/integral API:
`Measure.comap`/`map` lemmas, `MeasurableEmbedding.map_comap`/`integral_map`/`integrable_map_iff`,
`Homeomorph.toMeasurableEquiv` and its coercion lemmas, `integral_map_equiv`,
`MeasureTheory.Measure.prod` and `prod_apply`, `haar`-uniqueness names, `Multipliable`/`tprod`/
`finprod` (including `Multipliable.tprod_mul`-style lemmas and
`Summable` ↔ `Multipliable` bridges), `Measure.real`, `Real.rpow`/`Complex.ofReal_cpow`, and
`RestrictedProduct.*`. Expect a handful of renames; adapt proofs, **never** statements.

## 6. Verification

| check | expected |
|---|---|
| tier-0 edit loop, all six modules | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.EisensteinGeneral.Factorization` | green (builds all five engines) |
| `#print axioms` on the headline | `[propext, Classical.choice, Quot.sound]` |
| checker | the manager wires it and reconciles the delta against the modules' public surface (expect ≈ **+56**, i.e. every declaration except the substituted `integralOffSet`) |
| `git status` | only the six new modules |

## 7. Report shape

1. The six module paths, final line counts, and the declaration names per module.
2. Each module's import block, with one clause per import.
3. Every proof adaptation (pin line → port spelling) with pin line numbers; say what failed first.
4. The `integralOffSet` substitution: the exact port name used and the statement you read.
5. Tier-0 results per module and the tier-1 result, with wall times.
6. The pin line of every `-- pin:` marker.
7. Anything left undone, any deviation, and any place where you stopped rather than edit an
   existing module.

## 8. Results as landed (2026-10-18)

| | |
|---|---|
| modules | `Factorization/{ProductMeasure,Stratum,Measure,Integrability,Tprod}.lean` — 113 / 269 / 220 / 224 / 209 lines, 1 / 32 / 10 / 8 / 5 public declarations |
| façade | `EisensteinGeneral/Factorization.lean` — 145 lines, 1 headline |
| checker | 10,388 → **10,445 identical**, 0 mismatched / 0 missing, 10,781 checked (delta **+57**) |
| promoted-from-pin-private | 718 → 774 |
| axioms | headline `[propext, Classical.choice, Quot.sound]` |
| tier-0 / tier-1 | 0 warnings on all six (3.6–5.7 s each); `lake build FLTForHuman.EisensteinGeneral.Factorization` green, 3,943 jobs |
| register | unchanged (all six listed) |
| existing modules edited | none by this order |

Deviations and corrections, all recorded:

1. **`integralOffSet` is a one-line alias** of `NumberField.TateGlobal.ShellSupport.integralOff`
   (not dropped, as §3 first said): the pin's statement of
   `inv_measure_mul_setIntegral_integralOffSet_finprod_eq` spells the name, and the checker compares
   statement text.
2. **Two statements keep the pin's `AdelicBox.integralFinteAdeles` spelling** after review: the port
   has that name as a port-only `@[reducible]` alias in `NumberTheory/AdelicHaar/PlaceMeasure.lean:48`
   (from an earlier landing), so `Measure.lean` now imports it and the two statements are the pin's
   text. The first checker run had flagged them.
3. **The wrapper is listed before the `S_` file in `SOURCES`**: the headline's pin-private twin in
   the `S_` file inherits `F` from a section variable and would otherwise shadow the wrapper by last
   name (flagged as a MISMATCH on the first run).
4. **Proof adaptations**: `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right`; `Finset.prod_le_prod`
   → `Finset.prod_le_prod₀` (v4.34 dropped the `0 ≤` argument and needs `[MulLeftMono ℝ]`); the pin's
   `open scoped RestrictedProduct ENNReal NNReal` kept (v4.34 makes `∞`/`ℝ≥0∞` scoped).
5. **One style residual**: `set_option linter.style.haveILetI false` is *file-level* in the six
   modules (24 load-bearing `haveI` sites); the column's preference is declaration-scoped. Recorded
   in [logs/eisenstein-factorization.md](../../../logs/eisenstein-factorization.md) §6.

The two anonymous `scoped instance`s of `Stratum.lean` (the pin's `private scoped instance` pair at
pin 280/281) are public but unnameable, so they carry no `-- pin:` marker and are the only
declarations of the set the checker does not see.
