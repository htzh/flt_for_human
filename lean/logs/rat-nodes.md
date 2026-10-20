# The two `Rat*` proof nodes

**Landed 2026-10-20, WORKORDER-RN1.** The two proof bodies that sit on the `Rat*` definition
gates are homed whole, each at the wrapper's headline name and each wired to both its `S_` proof
file and its `Thm` wrapper. Nothing existing was edited: the two gate modules, the box/level
layer, the premise modules and every legacy module are untouched. `port_advise` reported 0
substitutions and 0 shared preludes for the pair, and the transcription bears that out — no name
is proved in both modules.

## 1. What landed

| module | pin source | declarations (port) | build | checker |
|---|---|---:|---:|---|
| `FLTForHuman/NumberTheory/RatAdele/DenseRange.lean` (372 lines) | `P2M/Sol/S_RatAdele_denseRange_algebraMap_add_adeleSingleAt.lean` (309 lines) + `Theorems/Thm_RatAdele_denseRange_algebraMap_add_adeleSingleAt.lean` (13 lines) | 21 (1 public headline + 20 `private`) | 3715 jobs, 8.2 s wall, 0 warnings | **1 ok, 0 mismatch, 0 missing, 0 own** |
| `FLTForHuman/NumberTheory/RatIdele/ClassCharNorm.lean` (376 lines) | `P2M/Sol/S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow.lean` (312 lines) + `Theorems/Thm_RatIdele_exists_norm_apply_eq_ideleNorm_rpow.lean` (12 lines) | 49 (1 public headline + 35 `private` theorems + 9 `private` defs + 4 `private scoped instance`s) | 3716 jobs, 8.9 s wall (5.8 s compile), 0 warnings | **1 ok, 0 mismatch, 0 missing, 0 own** |

The public surface of each module is exactly the headline, so the checker reports one row each
(`RatAdele.denseRange_algebraMap_add_adeleSingleAt` → the `Thm` wrapper's row;
`RatIdele.exists_norm_apply_eq_ideleNorm_rpow` → its wrapper's row). Both statements are the
wrapper's, byte for byte; no `own:` marker and no `spec/decl_markers.tsv` entry is used.

Declaration-count note: the pin's `S_RatIdele` file carries **49** corpus rows, not the 45 the
work order quotes — 45 is the count *excluding* the four `private scoped instance`s (`CompactSpace
unitWindow`, `TotallyDisconnectedSpace 𝔸ℚf`, `(𝔸ℚf)ᵐᵒᵖ`, `(𝔸ℚf)ˣ`). All 49 are reproduced. The
`S_RatAdele` file's 21 (1 + 20) reproduce exactly.

Axioms (`#print axioms`, `lean/tmp/ax_dense.lean`, `lean/tmp/ax_rat.lean`):

```
'RatAdele.denseRange_algebraMap_add_adeleSingleAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RatIdele.exists_norm_apply_eq_ideleNorm_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry` (`grep -c sorry` = 0 in both), no `import Mathlib`, no module `set_option
maxHeartbeats`, no `-- pin:` comments (all provenance prose is in the leading `/- … -/` block).

## 2. What they sit on

Both modules import only already-landed material:

* `DenseRange`: the gate `LanglandsTunnell/StandardLocalConstantsAt.lean`
  (`adeleSingleAt`, `finAdeleSingleAt`, `finAdeleSingleAt_apply_self`,
  `finAdeleSingleAt_apply_of_ne`), `NumberTheory/AdelicBox.lean`
  (`infiniteBox`, `adelicBox`, `existsUnique_algebraMap_add_mem_adelicBox`,
  `exists_forall_norm_apply_le_of_mem_infiniteBox`), the finite half
  `AdelicLevel/integralFiniteAdeles` from `AdelicLevel/{Level,IdealBall}.lean`, and
  `Topology/Algebra/RestrictedProduct/TopologicalSpace.lean` for
  `RestrictedProduct.mem_nhds_iff_of_cofinite`. `WithZero`, `Valued`,
  `Valuation.restrict_lt_iff_lt_embedding`, `MonoidWithZeroHom.ValueGroup₀.embedding`,
  `HeightOneSpectrum.{intValuation,intValuation_le_one,intValuation_lt_one_iff_mem,
  intValuation_eq_one_iff_mem_primeCompl,valuation_of_algebraMap,mem_adicCompletionIntegers,
  valuedAdicCompletion_eq_valuation'}` and `Rat.ringOfIntegersEquiv` are mathlib `v4.34.0`.
* `ClassCharNorm`: `NumberTheory/RatIdele/Normalizer.lean` (`ρ`, `ρ_spec`, `ρ_ne_zero`,
  `archCoord` and its laws, `finPart`, `valued_snd_mul`, `valued_snd_inv_mul`,
  `algebraMap_adeleRing_snd`, `valued_algebraMap_rat`), the three ported premises
  (`AdelicHaar/PlaceMeasure.lean`'s product formula, `AdelicModulus.lean`'s
  `distribHaarChar_algebraMap`, `NumberField/TateGlobalContinuousIdeleNorm.lean`'s
  `continuous_ideleNorm`), `AutomorphicForm/Adelic/LsXi.lean` for `IsIdeleClassChar`, and
  `AdelicLevel/{HeckeGen,Level,IdealBall}.lean` for `finIncl`, `integralFiniteAdeles`,
  `one_mem_integralFiniteAdeles`, `mul_mem_integralFiniteAdeles`,
  `isCompact_integralFiniteAdeles`. Everything else (`Submonoid.units`,
  `Submonoid.units_isCompact`, `TateGlobal.{archUnitHom,ideleNorm,ideleNorm_mul,ideleNorm_pos}`,
  `AdelicVolume.archCentralUnit_{fst_self,fst_of_ne,snd}`, `map_real_smul`) is `v4.34.0`.

## 3. The `attribute [-instance]` decision (RatIdele)

**Dropped whole, and never needed.** The pin's line names thirteen mathlib 4.30 instances,
eleven of them spelled with the pin's `…_definitions` mangling
(`instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions`,
`instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions`,
`IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRing…_definitions`, …);
those names do not exist in `v4.34.0` and copying the line cannot elaborate. The module was
elaborated **without** it before any other change was made, and instance search neither diverged
nor came near the 200 000-heartbeat cap (whole-module edit-loop check: ~6 s wall, `EXIT 0`,
first try after the two fixes in §4). No narrowed re-statement of the block was needed, so none
is present; the pin's local-instance environment is reproduced by the plain `v4.34.0` instances.

## 4. Drift, per module (proof/body only; no statement changed)

### `DenseRange`

1. **Scaffolding.** `import P2M.Util`, every `p2m_*` command, and the pin's
   `namespace P2MW.S_RatAdele_denseRange_algebraMap_add_adeleSingleAt` wrapper are gone; the pin's
   `RatAdeleDensityAux` namespace is kept at the root and the headline is declared at the
   wrapper's dotted name `RatAdele.denseRange_algebraMap_add_adeleSingleAt`.
2. **Imports.** The pin's `Definitions/Def_LanglandsTunnell_StandardLocalConstantsAt` and
   `Definitions/Def_NumberField_AdelicBox` are the port's homed gates;
   `Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace` is the port's
   `FLTForHuman/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean`, which is where the
   pin's `RestrictedProduct.mem_nhds_iff_of_cofinite` lives in this tree (it is **not** a mathlib
   `v4.34.0` lemma; that import is load-bearing).
3. **One namespace drift.** `AdelicBox.integralFiniteAdeles` (pin: the finite adèles lived inside
   the box module) is `AdelicLevel.integralFiniteAdeles` in the port; one occurrence, in
   `hBbox`. This is the drift `logs/rat-def-gates.md` already anticipated.
4. **`valued_algebraMap_adicCompletion`.** The pin's two-branch `first | exact
   HeightOneSpectrum.valuedAdicCompletion_eq_valuation' i (algebraMap ℚ ℚ q) | (rw
   [HeightOneSpectrum.algebraMap_adicCompletion]; exact …)` keeps only the first branch: in
   `v4.34.0` it succeeds, so the fallback is dead and emits both the unused-tactic and the
   unreachable-tactic warnings.
5. **`haveI` kept, linter off.** `exists_generator`'s `haveI :=
   isPrincipalIdealRing_ringOfIntegers_rat` is load-bearing for instance search;
   `v4.34.0`'s style linter flags `haveI` only because the surrounding goal is a proposition, so
   the module sets `linter.style.haveILetI false` (the same recourse as
   `NumberTheory/AdelicBox.lean`). The hypothesis is not dropped, which would change the proof
   term's instance environment.
6. **`open scoped RestrictedProduct` dropped** — the proof names
   `RestrictedProduct.mem_nhds_iff_of_cofinite` outright (`hS_sub` consumes the `∀ᶠ`-form, not the
   scoped product notation), so the pin's `open scoped` is inert.

Not hit, though on the work order's stop-early list: no `WithZero`/`Valuation.restrict` API drift
(every `WithZero.log`/`exp`/`pow`, `Valuation.restrict_lt_iff_lt_embedding` and
`MonoidWithZeroHom.ValueGroup₀.embedding` name matched), and no `AdelicBox.adelicBox`
membership/decomposition drift (the pin's `hB`/`hBbox` projection through `adelicBox K = {x |
x.1 ∈ infiniteBox K ∧ x.2 ∈ integralFiniteAdeles …}` is unchanged in `v4.34.0`).

### `ClassCharNorm`

1. **Scaffolding.** `import P2M.Util`, the two `p2m_reactivate` commands and the pin's
   `namespace P2MW.S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow` wrapper are gone; the pin's
   `ModuleOfIdeleClassCharacter` namespace is kept at the root, with its `local notation` and
   `noncomputable section`.
2. **The `attribute [-instance]` line is dropped** (see §3).
3. **One import added:** `Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected`. The pin's
   `private scoped instance : TotallyDisconnectedSpace 𝔸ℚf` needs
   `[TotallyDisconnectedSpace (∀ w, w.adicCompletion ℚ)]` (via `Pi.totallyDisconnectedSpace`),
   whose per-place half comes from `NonarchimedeanAddGroup.instTotallySeparated` — a lemma of that
   mathlib module. The pin reached it through `Def_NumberField_TateGlobalZeta`'s import cone; the
   port's homed premise modules do not pull it, so the import is explicit. Without it the
   instance declaration is the only error in the file (`failed to synthesize instance of type
   class TotallyDisconnectedSpace ((a : HeightOneSpectrum (𝓞 ℚ)) → …)`); nothing else depends on
   the module.
4. **The product-formula premise is `_impl`.** The pin calls
   `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one ℚ (archUnit r)
   (coe_archUnit_snd r)`; the port's engine name for that `Theorems/` headline is
   `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one_impl` (same
   statement, `F` explicit — the name `AutomorphicForm/Adelic/{PeterssonSlabPairing,
   WeylIntegrable/Assembly}.lean` also use). One call site, in `ideleNorm_archUnit`; no statement
   differs, so no `own:` marker.
5. **`coe_archCentralUnit_eq` is proved by `rfl`.** The pin's proof case-splits on
   `w = Rat.infinitePlace` and rewrites with `Function.update_self` /
   `Function.update_of_ne`, then closes with `archCentralUnit_fst_self` / `_fst_of_ne`. In
   `v4.34.0` the goal after `Prod.ext`/`funext` is `(↑(archCentralUnit …)).1 w = …`, which is
   only type-correct at *default* transparency (`AdeleRing` is a `def`, so the `.1` projection
   needs its unfolding while `rw` matches at implicit transparency), so both `rw` steps fail with
   "not type-correct under the `implicit` transparency level". The statement is definitional —
   `archCentralUnit`'s `val` *is* that `Function.update` pair — so the whole helper is `rfl`.
   Same statement, shorter proof; the pin's three `archCentralUnit_*` lemmas stay used by the
   neighbouring helpers.
6. **`letI`/`haveI` kept, linter off.** `ideleNorm_principal`'s
   `letI : MeasurableSpace 𝔸ℚ := borel 𝔸ℚ` and `haveI : BorelSpace 𝔸ℚ := ⟨rfl⟩` are
   load-bearing for `distribHaarChar_algebraMap`'s `[MeasurableSpace 𝔸] [BorelSpace 𝔸]`
   binders; the style linter flags them only because the goal is a proposition, so the module
   sets `linter.style.haveILetI false`. The pin's two `open scoped Classical in` blocks are kept.
7. **Everything else verbatim**, including the `Submonoid`/`Subgroup` window construction
   (`integralSubmonoid`, `unitWindow`, `mem_unitWindow_iff` via `Submonoid.mem_units_iff`,
   `Submonoid.units_isCompact`), the four `private scoped instance`s, the `eR` real-place
   identification (`ringEquivRealOfIsReal`, `isometryEquivRealOfIsReal`), the `expUnit`/`rayLog`
   machinery and the `modulus`/`ideleNormHom` comparison.

Not hit, though on the stop-early list: no instance-inference blow-up (every declaration
elaborates well inside the 200 000-heartbeat edit cap; no per-declaration `maxHeartbeats` is set
anywhere in either module), and the `distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one`
premise's *statement* is identical (`(a : 𝔸)ˣ`, `ha : a.2 = 1`, conclusion
`(distribHaarChar 𝔸 a : ℝ) = ∏ w, ‖a.1 w‖ ^ w.mult`), only the port's `_impl` name differs.

## 5. Verification commands

```
cd lean
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/NumberTheory/RatAdele/DenseRange.lean                       # EXIT 0, 0 warnings
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/NumberTheory/RatIdele/ClassCharNorm.lean                    # EXIT 0, 0 warnings
flock /tmp/flt.lake.lock timeout 90 lake build FLTForHuman.NumberTheory.RatAdele.DenseRange
flock /tmp/flt.lake.lock timeout 90 lake build FLTForHuman.NumberTheory.RatIdele.ClassCharNorm
python3 spec/check_port.py FLTForHuman/NumberTheory/RatAdele/DenseRange.lean
python3 spec/check_port.py FLTForHuman/NumberTheory/RatIdele/ClassCharNorm.lean
lake env lean tmp/ax_dense.lean    # #print axioms on the DenseRange headline
lake env lean tmp/ax_rat.lean      # #print axioms on the ClassCharNorm headline
```

Every `lake build` was taken under `/tmp/flt.lake.lock` (another agent shares the tree); no
whole-tree build was run. Wall times above include the flock wait: `DenseRange` 8.2–8.7 s
(3715 jobs) across its two builds, `ClassCharNorm` 7.2 s then 8.9 s for the pair (3716 jobs).

## 6. State

Both nodes are ported and green; nothing about them is blocked. No existing module needed an
edit, and none was made.
