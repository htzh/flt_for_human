# The Vélu port — measured record

Pin `anthropics/fermats-last-theorem@aa2d8b3`, mathlib `v4.34.0`. The plan is
[../topics/velu/TOPIC-port-plan.md](../topics/velu/TOPIC-port-plan.md); the
structure study is
[../../studies/velu-cluster-structure.md](../../studies/velu-cluster-structure.md).
This record is appended per home as the phases land.

## H0 — the generic-point bridge (2026-10-04)

**Scope.** The four-declaration bridge the pin inlines into every `S_` file that
needs it: `yGen`, `polyToFunctionField_eq_aeval`,
`equation_map_polyToFunctionField_yGen`,
`transcendental_polyToFunctionField_X`. The plan's H0 row calls it the
972-line block with ten target files — the highest fan-in in the slice.

**Result.** Landed in the existing home
`FLTForHuman/WeierstrassCurve/FunctionFieldQuadratic.lean` (+61 lines: a
55-line `section GenericPoint`, twelve of them the doc header). Checker
`4436 → 4440 identical (150 promoted), 0 mismatched, 0 missing, 30 own`.
Consumer `spec/WeierstrassCurveConsumer.lean` exit `0`; `#print axioms` on all
four is `[propext, Classical.choice, Quot.sound]`.

### The 972 was span, not content

This is the plan §4 warning in its purest form. The tool's per-declaration spans
in the pin (`transcendental_polyToFunctionField_X` 641, `yGen` 190,
`equation_map_polyToFunctionField_yGen` 128, `polyToFunctionField_eq_aeval` 13)
are measured declaration-to-next-declaration, and the pin separates these
declarations with *empty* `<section>` skeletons (`GenericPoint`,
`CoordinateIdentification`, `Transcendence`, `Certificate`, `Inclusion`,
`Integrality`, `Assembly`, each with only a `variable` line). The transcriptions
are:

| declaration | pin span | port lines |
|---|---:|---:|
| `polyToFunctionField_eq_aeval` | 13 | 12 |
| `yGen` | 190 | 1 (+3 doc) |
| `equation_map_polyToFunctionField_yGen` | 128 | 14 |
| `transcendental_polyToFunctionField_X` | 641 | 6 |
| **once block** | **972** | **36** |

So H0 costs 36 written lines, not 972. The 641-line span of
`transcendental_polyToFunctionField_X` is a 6-line proof followed by the rest of
the pin file's empty section skeleton (a dozen-odd `<section>` blocks whose only
content is a `variable` line). The plan already prices the *slice* by deduped
content (§0–§1); this is the per-block version of the same correction, and it
means Phase A's home order is right (H0 unblocks everything, cheaply) but the
home sizes in §2's table are upper bounds on content, not on written lines.

### `yGen` is `yCoord`

The pin's `def yGen (W : Affine F) : W.FunctionField := algebraMap … (mk W Y)` is
byte-identical to the public `yCoord` of
`Definitions/Def_WeierstrassCurve_FunctionFieldQuadratic.lean`; the two names
belong to different pin modules (the `Defs/` module uses `yCoord`, the inlined
`S_` preludes use `yGen`) and never meet in the pin. The port therefore writes
the pin's statement verbatim with the body `yCoord W`, which keeps `yGen` a
`def` (not an `abbrev`, so the checker's kind match holds) and keeps the pin's
`show yGen W = algebraMap … from rfl` idiom working by unfolding. The port's
consumer composes `yGen` with the generation theorem across modules
(`adjoin (RatFunc F) {yGen W} = ⊤`, via `show yGen W = yCoord W from rfl` and
`adjoin_yCoord_eq_top`).

### Checker wiring

The four have no `Theorems/` wrapper, so the comparable copy is a `P2M/Sol/S_`
file. All ten copies are identical; the smallest one carrying all four publicly
is `S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean`
(1,336 lines), appended last to `SOURCES` so no earlier last-name match can
flip. Per-declaration authority remains
`tools/deps/port_advise.py`; the block came from the plan's `velu_plan.txt`.

### Not this topic

The other nine homes, the four big theorems and the ~40 small consumers of the
plan §5 phases B–D. `yGen` is not yet consumed by any *library* statement (the
consumer zone is a `spec/` wire test); H2 (`Velu/Engine.lean`) is its first real
consumer.

## H2 scoping — the plan's H2 is five homes, and a prerequisite was missing (2026-10-04)

Not a port; a measurement round whose output is
[../topics/velu/TOPIC-H2-engine.md](../topics/velu/TOPIC-H2-engine.md) and a
revision of the plan's §2 and §5. Three findings.

**The block is 373 declarations / 7,248 lines / 65 in port** — the plan's
figure, confirmed. But clustered by subject it is not one engine: formulas
(A–D ≈ 1,240), the cleared-polynomial degree engine (E ≈ 1,600), the
generic-point/translation layer (F ≈ 990), the deficit-fun discharge (G ≈ 1,230)
and the odd-order combinatorics (H ≈ 630). The intra-block call graph (498
edges, 17 layers) has the clusters *mutually* dependent (E↔F, C↔D), so sets must
be cut by object, not by layer.

**H1 is not the dictionary the plan assumed.** Nine of the block's 53
dictionary declarations are the deferred Weierstrass `CoordinateRing` dictionary
(`exists_eq_XYIdeal_of_isMaximal`, `isDedekindDomain_of_Δ_ne_zero`,
`deg_placeOfEquation`, …) — i.e. CARRY-FORWARD entry #1, ≈941 content lines,
whose trigger is exactly this cluster. The port has no `XYIdeal` and no
`exists_eq_XYIdeal`; `placeOfPoint` in `AlgebraicCurve/P1/Dictionary.lean` is the
`RatFunc`/`P¹` dictionary. So the true first home is a new **H1w**, and the
plan's Phase A item 3 becomes "H1w, then the five H2 homes".

**H5/H6 are parallel in principle, sequential by decision.** The
`IsogenyEndDatum` and base-change files contain zero `veluDeficit`/`veluXCorr`
and hundreds of `IsFinitePlace` (713 / 405 / 525) and `placeOfEquation`
(47 / 29 / 86): they need the dictionary and not the Vélu engine. The run is
kept sequential anyway.

**Set count: three** — SET-1 (dictionary + formulas A–D), SET-2 (E+F), SET-3
(G+H), then the manager's H3/H4 capstone. E and F must be one module
(`Velu/Engine.lean`): they interleave in the pin and mutual imports are
impossible. One scout is required before SET-2: one
`*ClearedPoly_natDegree_lt` identity in `Scratch.lean` at the global heartbeat
cap, to confirm the pin's huge `linear_combination` calls transcribe.

**Build discipline is the cost model.** Every module the three sets write is
new, so `lake build <module>` re-elaborates one file and cascades nowhere. That
is why A2's general lemmas go into a new
`AlgebraicCurve/Defs/PlaceCalculus.lean` instead of extending an existing AC
hub: measured with `build_ladder.py --edit`,
`Defs/PlaceEvaluationAlgebra.lean` has a 30-module / 15,783-line dependent
cascade (≈191 s) and `Defs/PushPull.lean` 79 modules / 38,031 lines (≈465 s).
Editing an existing file is a stop-and-report condition; a bare `lake build` is
a single milestone gate, never a per-set one. The full block is
[../topics/velu/TOPIC-H2-engine.md](../topics/velu/TOPIC-H2-engine.md) §4.

## SET-1 — the place dictionary, the Vélu vocabulary and the formulas (2026-10-04)

**Scope.** The four modules below, all new, so no existing file was touched.

| module | lines | pin source |
|---|---|---|
| `AlgebraicCurve/Defs/PlaceCalculus.lean` | 293 | the general `Place` additions (A2) |
| `WeierstrassCurve/Place/Dictionary.lean` | 844 | A1, `S_…hasPrincipalDivisors_functionField.lean` |
| `WeierstrassCurve/Velu/Defs.lean` | 299 | the four `Def_WeierstrassCurve_Velu*` / `_OddOrderSummingSet` files |
| `WeierstrassCurve/Velu/Formula.lean` | 776 | B + C + D of the map/res `S_` files |

**Result.** Checker `4440 → 4617 identical (197 promoted from pin-private
declarations), 0 mismatched, 0 missing, 30 own` (4,647 port declarations
checked). All four `lake build <module>` green; `spec/WeierstrassCurveConsumer.lean`
exit `0`; `#print axioms` on the sixteen headline declarations is
`[propext, Classical.choice, Quot.sound]` (two of them drop `Classical.choice`);
no `sorry` in any of the four files.

### Distribution and the missing §A2 list

`tmp/velu/set1-decl-lists.md` has no `## A2` section (the work order's pointer
`§A2` does not resolve), so the A2 surface was reconstructed from the pin's
general `AlgebraicCurve.Place.*`/`WeierstrassCurve.Affine.*` private additions:
`evalAt_{zero,add,neg,sub,sum,pow,natCast,ofNat,div'}`, `ord_{div,pow}`,
`min_ord_le_ord_add`, `ord_add_eq_min`, `ord_ringHom_eq_natDegree_mul`,
`le_ord_ringHom_of_natDegree_le`, `ord_sub_evalAt_pos`, `mem_smul_iff_symm_mem`,
`ord_smul_of_fixed`, `ord_nonneg_of_ord_smul_nonneg`. Two A2 names
(`isFinitePlace_smul_iff_forall_symm_mem`,
`forall_place_ord_nonneg_iff_finite_and_not_finite`) mention `IsFinitePlace`, so
they cannot live in module 1 (which must precede the dictionary that defines it);
they are transcribed in `Dictionary.lean` instead. The five ord lemmas
(`min_ord_le_ord_add` … `le_ord_ringHom_of_natDegree_le`) appear in the A1 list
but are general `Place` lemmas, so they also live in `PlaceCalculus.lean` and are
imported by the dictionary.

### Checker-relevant adaptations (statements still verbatim)

* **Kinds matter.** The checker compares the declaration *kind* too, and the pin
  is inconsistent: `veluX_sub_self_eq_sum_veluXCorr`,
  `veluY_sub_self_eq_sum_veluYCorr`, `veluXCorr_mul_r`,
  `veluX_sub_self_mul_r` are `theorem` in the map file, while `eval_Ψ₃_eq_b'`,
  `veluDeficitLinearTerm_mul_cube`, `eval_Ψ₃_eq'` and
  `veluDeficitCrossQuad_eq_alphaSq_add_cubeBeta` are `lemma`. The port follows
  the map file in each case.
* `xOrZero` was left `private` by SET-1, matching the pin, because the checker's
  chunk for the pin's pattern-matching `def` swallows the following `p2m_export`
  line (no `:=` to cut at), so a public copy cannot match textually. **Review
  reversed this**: the pin itself re-exports the name (`p2m_export`) and the
  odd-order layer's `kw_veluX_xOrZero_add_gen_odd` statement names
  `(P + Q).xOrZero`, so SET-3 could not be written without it. It is now public
  in `Velu/Formula.lean` with the pin's statement and body verbatim, and
  exempted in `OWN_PROOFS` (last name, unique) with the extraction bug recorded
  as the reason. The promotion moves the checker from `30 own` to `31 own` and
  leaves `4617 identical / 0 / 0` unchanged — the expected promotion signal.

### Review corrections (manager, after SET-1)

* the `xOrZero` promotion above;
* **the A2 list was never written** (`tmp/velu/set1-decl-lists.md` had no `## A2`
  section), so SET-1 reconstructed A2 from "general `Place` lemmas" and missed
  the rational-point-map API. A coverage sweep of all 373 shared names against a
  fresh port index found it: 85 ported, 288 unassigned, and 0 unaccounted after
  the sweep. The rational-point map (`some_congr`, `ratPointMap*`, `ratPointHom`,
  `coordsOrZero_ratPointMap`) and `map_map_algHom_toRingHom_eq_self` are now an
  explicit carry-over in SET-2's order; the place/`XYIdeal` membership and
  `*_of_not_isFinitePlace` group in SET-3's. The two lists were regenerated as
  the complete assignment.
* the consumer's header said "three zones" with four present — fixed.

### Friction

* `R⁰` needs `open scoped nonZeroDivisors`; the pin's `import Mathlib` hides that,
  and a bare `FractionalIdeal R⁰ K` fails with "expected token".
* Declaring a theorem *inside* `namespace FractionalIdeal` makes the bare name
  `FractionalIdeal` resolve to the namespace, so `(𝔪 : FractionalIdeal R⁰ K)`
  fails to parse. `isUnit_coeIdeal_of_forall_isMaximal` /
  `isUnit_of_forall_isMaximal` are therefore declared one level up and the
  `FractionalIdeal.` qualifier is explicit in their proofs (namespace-independent
  for the checker).
* Section `variable`s are scoped to the current *section*, not the namespace: a
  `variable {F} [Field F] {W}` declared inside `namespace CoordinateRing` goes
  out of scope at `end CoordinateRing`, so the dictionary declares its
  `universe u`/`{F} [Field F] {W : Affine F}` at the `Affine` level.
* `Point.some` / `Affine.slope_of_X_ne` need `WeierstrassCurve.Affine.Point` /
  `Affine` opened; the pin gets this from its `p2m_open` walls.
* The pin's `VeluPointMap` splits `veluXNum`/`veluYNum`/`velu_singleton_equation_cleared`
  (`CommRing`) from `veluY`/`veluX_singleton`/`veluY_singleton`/`velu_singleton_map_equation`
  (`Field`); keeping that split is what makes `x₀ y₀ x : R` rather than `: F` in
  the statements. The huge `linear_combination` in
  `velu_singleton_equation_cleared` transcribes unchanged on v4.34.0.
* `W.veluQuotient`'s `map`/`ext` proofs need the `veluQuotient_a₁/a₂/a₃` `rfl`
  lemmas before `map_simp`; the pin's `map_simp` macro is transcribed locally.

### Deferred (reported, not weakened)

* `veluDeficitBracket_genericPoint_mem_of_not_isFinitePlace` and
  `coordsOrZero_ratPointMap` are the two B/C/D declarations whose proofs consume
  the function-field / `kwVelu`/`ratPointMap` engine that SET-2 (`Velu/Engine.lean`)
  and SET-3 bring; they are **not** ported here. All other C-cluster declarations
  are present.
* The RR/class-group/Abel block (`rrParam`, `RRSpace`, `basisAux`,
  `geomPlaceOfPoint`, `unitIdealOf*`, `AbelTheorem`, `isPrincipal_of_geomDivisorSum_eq_zero'`,
  `instAbelTheorem`) is out of scope as the work order states, so the three A1
  lemmas whose proofs consume it (`mem_iff_natDegree_norm_le`,
  `deg_eq_one_of_not_isFinitePlace`, `exists_smul_sub_natDegree_norm_lt`) are not
  carried; the map/res files that consume this dictionary do not reference them.
* The four big headlines (`velu_map_equation_*`,
  `exists_veluFunctionFieldHom_restrictAlong_*`) are untouched, as instructed.

## SET-2 — the cleared-polynomial engine and the generic point (2026-10-04)

**Scope.** One new module, `FLTForHuman/WeierstrassCurve/Velu/Engine.lean`
(**2,404 lines**, 204 declarations), clusters E + F in the pin's declaration
order. It imports SET-1's `Velu/Formula.lean` and `Place/Dictionary.lean`, plus
`AlgebraicCurve/Defs/Divisor.lean` (for `AlgebraicCurve.HasPrincipalDivisors`,
needed by the Liouville bridge) and the same mathlib modules SET-1 already
carries. No existing module was edited.

**Result.** Checker `4617 → 4810 identical (297 promoted from pin-private
declarations), 0 mismatched, 0 missing, 31 own` (4,841 port declarations
checked). `flock /tmp/flt_build.lock lake build
FLTForHuman.WeierstrassCurve.Velu.Engine` → `Build completed successfully (2718
jobs)`; `spec/WeierstrassCurveConsumer.lean` (Zone 5 added) exit `0`; `#print
axioms` on the fifteen headline declarations
(`veluDeficitSingletonSumClearedPoly_natDegree_lt`,
`veluDeficitCrossQuadAlphaSqClearedPoly_natDegree_lt`,
`veluDeficitCrossQuadBetaSqConstS2ClearedPoly_natDegree_lt`,
`Affine.exists_equation_of_isAlgClosed`, `Affine.adjoin_addFun_eq_top`,
`Affine.isIntegral_addYFun_adjoin_addXFun`, `Affine.addXFunTranscendental`,
`genericPoint_ne_zero`, `genericPoint_notMem_zmultiples_ratPointHom`,
`Affine.translationAlgEquivOf`, `translationAlgEquivOf_veluDeficitFun`,
`coordsOrZero_ratPointMap`, `Affine.functionField_liouville_of_equation`,
`kw_infinite_of_isAlgClosed`, `kw_hDDTerm`) is
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

### Scout gate

Prototyped `veluDeficitSingletonSumClearedPoly_natDegree_lt` in `Scratch.lean`
at the global heartbeat cap: exit `0` in **3.1 s**, transcription **direct** (no
normal-form / `field_simp` fallback). The pin's reported "very large
`linear_combination` degree bounds" are actually in the companion
`*_mul_prodPow_eq` / `*_sDecomp` identities, not in the `*_natDegree_lt` proofs,
which are structural `natDegree`/`degree` computations. Every identity
transcribed unchanged; `linear_combination` at the 4,000,000 cap handled the
`AlphaSq`/`AlphaCube`/`AlphaBeta`/`BetaSq` decomposition bodies.

### Extras ported (not in `tmp/velu/set2-decl-lists.md`)

The SET-2 list is not closed under dependencies: F's tail needs the function
field / discharge vocabulary the topic document assigns to SET-3/G. To keep the
tree green with one module, Engine also carries (all public, all present in the
pin `SOURCES`, so the checker still reports `0 missing`):

* `liftSummingSet`, `veluDeficitFun` (G's core definitions, res 3953/3958);
* `polyToFunctionField_X_ne_algebraMap`, `algebraMap_polynomial_eq_mk_C`
  (`Affine` function-field API used throughout F);
* `ord_X_eq_neg_two_of_not_isFinitePlace`, `ord_Y_eq_neg_three_of_not_isFinitePlace`
  and the `OrdPins` chain (`ord_X_sub_algebraMap_of_not_isFinitePlace`,
  `X_sub_algebraMap_ne_zero`, `inv_/X_mul_inv_/yGen_mul_inv_ ...`,
  `natCast_mem`) needed by the three listed `*_genericPoint_mem_of_not_isFinitePlace`;
* `algHom_toRingHom_comp_algebraMap`, `not_isFinitePlace_smul_of_symm_X_notMem`,
  `algebraMap_coordinateRing_ne_zero`, `IsFinitePlace.mem_centre_iff_ord_ne_zero`.

**Consequence for SET-3.** These names now live in `Velu/Engine.lean`. SET-3's
`Velu/Discharge.lean` imports Engine, so it must *use* them rather than
redeclare them (`liftSummingSet`, `veluDeficitFun`, the `OrdPins` helpers and
`polyToFunctionField_X_ne_algebraMap` are on its list). The manager should
amend SET-3's work order accordingly.

### Friction / API drift (mathlib v4.34.0)

* **`private` + `_root_` naming.** The pin's inlined prelude declares E/F helpers
  `private ... _root_.WeierstrassCurve.foo`; the port promotes them public so
  the checker's promoted-from-pin-private lookup verifies them (297 promoted
  hits).
* **Section variables are load-bearing for the checker.** The pin relies on the
  `p2m_open` walls for `Point`/`Affine`/`CoordinateRing`/`Polynomial.Bivariate`.
  In the port `Point.some`, `Y` (`Bivariate`), `XClass`/`YClass` must be opened
  explicitly, and `AlgebraicCurve.HasPrincipalDivisors` had to be spelled
  `AlgebraicCurve.HasPrincipalDivisors` (the checker strips the prefix) because
  the top-level `namespace WeierstrassCurve` shadows the root namespace.
* **Auto-included section variables.** Lean 4 includes *unused* instance
  variables declared by `variable`, which made several helper signatures carry
  `[IsDedekindDomain W.CoordinateRing]` and produced "typeclass instance problem
  is stuck `IsDedekindDomain (CoordinateRing ?m)`" at call sites whose `W` was
  not yet fixed. Fixed with `omit [IsDedekindDomain W.CoordinateRing] in` on the
  instance-free helpers (`X_sub_algebraMap_ne_zero`, `natCast_mem`), and by
  scoping `[IsDedekindDomain]` to only the `OrdPins`/`Corrections` sections that
  need `ord_X_eq_neg_two`.
* **`isFinitePlace_smul_iff_forall_symm_mem`** (SET-1's Dictionary) keeps the
  `[IsAlgClosed F] [W.IsElliptic] [W.InfinitePlace]` section variables in its
  signature, so the two `not_isFinitePlace_smul_*` / `..._of_centre` helpers
  carry them too (the pin's copies did as well); they are declared as section
  variables, so no statement text changes.
* **Deprecated `Ideal.eq_bot_of_comap_eq_bot`.** `translationCoordHom_injective`
  uses `Ideal.eq_bot_of_under_eq_bot` + `Ideal.under_def` + `RingHom.comap_ker`
  (the old name is a deprecated alias).
* **`CoordinateRing.exists_smul_basis_eq`** must be qualified (mathlib keeps it
  in `WeierstrassCurve.Affine.CoordinateRing`, not `Affine`); `Polynomial.Y`
  needs `open scoped Polynomial.Bivariate`; `@[simps]` on `ratPointHom` supplies
  `ratPointHom_apply` as in the pin.

### Deferred / omitted

None of the 179 listed declarations is missing. `kw_infinite_of_isAlgClosed`
and `kw_hDDTerm` (requested in the work order but absent from the regeneration
of `set2-decl-lists.md`) are ported. `eq_algebraMap_of_forall_ord_nonneg`
itself is *inlined* as a `private` helper instead of imported from
`AlgebraicCurve/ResidueTheorem/RRAssembly.lean` (whose import graph is out of
scope); `Divisor.degree_eq_sum` supplies the degree computation. The four
headline theorems, `IsogenyEndDatum`, base change and SET-3's G/H remain out of
scope. `SOURCES` needed no change — SET-1 already lists the map/res
`_of_isAlgClosed` files the checker diffs against.

### SET-2 fidelity fix — section instance variables (2026-10-04, follow-up)

The checker compares only the text after the declaration keyword, so it cannot
see `variable`-declared section binders; several declarations carried section
instances the pin does not have. Fixed to the pin map's sections:

* `Velu/Engine.lean`: `OrdAtInftyValues`, `OrdPins`, `Corrections` drop
  `[IsDedekindDomain W.CoordinateRing]`; `TransportEngine` drops
  `[IsAlgClosed F] [W.IsElliptic] [W.InfinitePlace]`; `CombinedDischarge` keeps
  only `[DecidableEq F]` + `hΔ`/`hA`.
* `Place/Dictionary.lean`: `isFinitePlace_smul_iff_forall_symm_mem` now omits
  all four instances (pin map 7809 is in the plain `TransportEngine` section).
  Because the pin's base ord lemmas are general,
  `isFinitePlace_of_mem`, `ord_X_neg_of_not_isFinitePlace`,
  `two_mul_ord_Y_eq_three_mul_ord_X`, `natDegree_norm_smul_basis_{left,right,max}`
  (and the private `ne_arith`/`two_mul_min_arith`) had to be weakened too before
  `two_mul_ord_eq_of_not_isFinitePlace` could be; otherwise the Engine
  `OrdAtInftyValues` proof cannot be stated instance-free. That is one more
  Dictionary family than the follow-up's single-entry table, forced by the pin's
  own general sections.
* `Velu/Discharge.lean`: removed the persistent
  `variable [IsDedekindDomain W.CoordinateRing]` from the whole `Affine` region
  (pin map 4766–5030 has no such variable), so `veluDeficitFun_mem_...`,
  `ord_veluDeficitFun_nonneg_...` and the `OrdPins`/`LaurentLift`/`Corrections`
  helpers are all instance-free.
* `Velu/OddOrder.lean`: `kw_veluDeficitFunOrdNonnegAtInftyAt_odd` drops the
  hidden `[IsAlgClosed F]` and its now-unneeded `haveI` Dedekind instance.

Whole-tree `lake build` green (4,968 jobs); checker `4913 identical
(303 promoted), 0 mismatched, 0 missing, 31 own` (4,944 checked); consumer exit
`0`; no `sorry`.





## Phase A close-out — the Vélu engine and the four headline theorems (2026-10-04)

The effort ran as three sequential sets (SET-1/2/3) plus three follow-up sets the
wire test forced (H5a, H5b, H4b), one subagent at a time, each reviewed by the
manager before the next dispatch. Checker trajectory `4436 → 5132` identical,
`0 mismatched / 0 missing` at every gate; consumer green; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

### Modules

| module | lines | contents |
|---|---:|---|
| `AlgebraicCurve/Defs/PlaceCalculus.lean` | 293 | A2 general `Place`/`evalAt`/`ord` additions |
| `WeierstrassCurve/Place/Dictionary.lean` | 844 | A1 deferred Weierstrass `CoordinateRing` dictionary |
| `WeierstrassCurve/Velu/Defs.lean` | 299 | the pin's Vélu definition modules |
| `WeierstrassCurve/Velu/Formula.lean` | 776 | local formulas + deficit expansion (B/C/D) |
| `WeierstrassCurve/Velu/Engine.lean` | 2,404 | cleared-polynomial engine + generic point (E/F) |
| `WeierstrassCurve/Velu/Discharge.lean` | 1,307 | deficit-fun `ord`/`evalAt` discharge (G) |
| `WeierstrassCurve/Velu/OddOrder.lean` | 657 | odd-order combinatorics (H) |
| `WeierstrassCurve/Velu/MapEquation.lean` | 443 | **headline** map equation (general + plain) |
| `WeierstrassCurve/Velu/RestrictAlong.lean` | 2,197 | engine + **headline** restrictAlong (general + plain) |
| `WeierstrassCurve/GenusOnePlaceGate.lean` | 402 | `GenusOnePlaceGate`, `IsCentred`, `AbelTheorem`, `placeOfPoint`, `genusOnePic0Equiv` (H5a) |
| `WeierstrassCurve/Isogeny/ConditionalCurrency.lean` | 245 | `pointMapOfPushforward`, `IsogenyEndDatum`, `IsogenyHomDatum` (H5a) |
| `WeierstrassCurve/Isogeny/NatCard.lean` | 806 | `natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong` + helpers (H5b) |

### Findings that changed the plan or the instruments

- **H1 was not the dictionary the plan assumed.** The Weierstrass
  `CoordinateRing` dictionary was the deferred CARRY-FORWARD entry #1, not the
  port's `P¹` dictionary: it became SET-1's `Place/Dictionary.lean`.
- **The definition-module layer was unbudgeted.** The four `S_` files import
  `Def_WeierstrassCurve_Velu*`/`_OddOrderSummingSet` (292 lines / 52 decls); the
  plan prices only `S_` lines. SET-1 got a fourth module for it.
- **The declaration lists were not the whole slice, and not route-closed.**
  SET-3 needed four small cross-column blocks the plan's own §2 table listed but
  the work orders did not carry; H3 needed `kw_veluHPDSupplier` + three
  `kw_no6_hroute_*`; H4b needed a **char-free norm formula and separability
  chain (~400 transcribed lines)** that neither `NatCard` nor the list covered.
  The rule now recorded in `TOPIC-H2-engine.md` §5: a set's list is the *route
  closure* of its deliverable, not the cluster intersection of its files.
- **The checker cannot see section variables.** SET-2's `Engine` carried
  `[IsAlgClosed F] [W.IsElliptic] [W.InfinitePlace]` and
  `[IsDedekindDomain W.CoordinateRing]` where the pin's sections have none, while
  the checker reported "identical"; H4's engine substituted the port's
  `InfinitePlace` for the pin's `[GenusOnePlaceGate] [IsCentred] [AbelTheorem]`.
  Both were found by `#check` review and fixed (all 24 public declarations of the
  touched sections now carry the pin's classes and no `InfinitePlace` binder).
- **The checker did not match `class` at all.** `DECL_RE` now includes it (with
  field extraction), which immediately verified 15 more classes — including the
  three the H4 wrapper's hypotheses name — and exposed four **pre-existing**
  Patching-port deviations, registered in `CARRY-FORWARD.md` and exempted by
  dotted name.
- **The lock path was wrong.** Every tool call runs under `bwrap --tmpfs /tmp`,
  so `flock /tmp/...` serializes nothing; the build lock is now
  `lean/.lake/flt_build.lock`.
- `xOrZero` was promoted public (the odd-order layer names it) with an
  `OWN_PROOFS` exemption for the checker's polluted extraction.

### Residuals (not part of the goal)

1. **Extras relocation.** `Velu/Discharge.lean`/`Velu/OddOrder.lean` carry a
   delimited `section Prerequisites` with the A1 dictionary group
   (`mk_mem_XYIdeal_iff`, `ord_placeOfEquation_*`, `centre_placeOfEquation`,
   `isRational_placeOfEquation`) that belongs in `Place/Dictionary.lean` (H5 must
   not import Vélu), and `exists_some_of_ne_zero` should fold back to a single
   public copy in `Velu/Formula.lean`.
2. **H5 / H6** (the plan's `IsogenyEndDatum` engine and the base-change/tensor
   block) are not ported; H5a/H5b ported only what the H4 headline's route
   closure needed.
3. **~400 lines of `private` transcription in `RestrictAlong.lean`** (the
   char-free norm formula, the fibre-centre argument re-run without
   `[CharZero F]`, the separability chain) are proof-internal and therefore
   invisible to the statement checker. They compile and are `sorry`-free, but
   their statements are not diffed.
4. The two seam statements keep the pin's text `= InfinitePlace.place` via an
   anonymous gate-derived instance, because the port's `InfinitePlace` is a
   `class` while the pin's is a namespace.

## H5r — the dictionary extraction (2026-10-04)

**Scope.** A pure move plus one dedup: no new mathematics, no statement changed.
The `IsogenyEndDatum`/base-change homes need the Weierstrass place dictionary and
must not import the Vélu modules, so the declarations SET-1/SET-2/SET-3 had
parked in delimited `Prerequisites` sections were relocated to
`WeierstrassCurve/Place/Dictionary.lean`:

* from `Velu/Discharge.lean`: `mk_mem_XYIdeal_iff`,
  `ord_placeOfEquation_ne_zero_iff`, `ord_placeOfEquation_nonneg`,
  `ord_placeOfEquation_pos_iff`, `centre_placeOfEquation`,
  `isRational_placeOfEquation`;
* from `Velu/Engine.lean`: `algebraMap_coordinateRing_ne_zero`,
  `IsFinitePlace.mem_centre_iff_ord_ne_zero` (the `centre_placeOfEquation`
  dependency) and `algebraMap_polynomial_eq_mk_C`;
* from `Velu/RestrictAlong.lean`: `eq_placeOfEquation_of_le_centre`,
  `ord_polyToFunctionField_pos_iff`, `ord_polyToFunctionField_eq_zero_iff`;
* `exists_some_of_ne_zero` folded from the public duplicate in
  `Velu/OddOrder.lean` back to one public copy in `Velu/Formula.lean`.

The plan's H5r row named only the A1 group; the move needed its dependency
closure. `centre_placeOfEquation` forced `IsFinitePlace.mem_centre_iff_ord_ne_zero`
(and its helper `algebraMap_coordinateRing_ne_zero`) out of `Velu/Engine.lean`,
and the `ord_polyToFunctionField_*` bridge the base-change files use pulled
`algebraMap_polynomial_eq_mk_C` and the RestrictAlong `Affine` prerequisites with
it. All four groups are in the pin's `IsogenyEndDatum`/base-change files
(`centre_placeOfEquation` 5, `mem_centre_iff_ord_ne_zero` 5,
`algebraMap_polynomial_eq_mk_C` 6, `eq_placeOfEquation_of_le_centre` 5).

**Result.** Checker `5133 → 5133 identical (305 promoted), 0 mismatched, 0
missing, 35 own` — the net-zero signal of a move plus a one-for-one dedup
(`exists_some_of_ne_zero` lost its duplicate public copy and gained the promoted
one). Every affected module `lake build` green; whole tree `lake build` green
(4,973 jobs); `spec/WeierstrassCurveConsumer.lean` exit `0`; `#print axioms` on
the two restrictAlong headlines `[propext, Classical.choice, Quot.sound]`; no
`sorry`.

### Fidelity

The section instances were the thing to get right, because the checker is
text-only and cannot see them. Every moved declaration was `#check`ed against the
pin's own section shape: `mk_mem_XYIdeal_iff`, `algebraMap_coordinateRing_ne_zero`,
`IsFinitePlace.mem_centre_iff_ord_ne_zero` and `algebraMap_polynomial_eq_mk_C`
carry none (declared under `omit [IsDedekindDomain W.CoordinateRing]`);
`ord_placeOfEquation_*`, `centre_placeOfEquation` and
`eq_placeOfEquation_of_le_centre` each carry exactly one
`[IsDedekindDomain W.CoordinateRing]`; `isRational_placeOfEquation` keeps the
pin's section-variable shape; `ord_polyToFunctionField_*` inherit the instance.
The `omit … in` + explicit-binder form reproduces the Discharge `PrerequisitesA1`
scope inside a `Dictionary.lean` section where `[IsDedekindDomain]` is already a
section variable, and the probe showed no overlapping-instance diagnostics.

### Not this topic

`isRational_of_deg_eq_one` stays in `Velu/Discharge.lean`. It was used only by
the moved `isRational_placeOfEquation`, so it is now unconsumed there; it remains
a public pin name in the P¹ branch (`AlgebraicCurve/P1/Dictionary.lean`), which
still verifies it. H5 can use `Place.isRational_iff_deg_eq_one` (reachable from
the dictionary); promote the wrapper when a proof wants the name. The rest of the
Engine-side dictionary the `IsogenyEndDatum` route may pull
(`polyToFunctionField_X_ne_algebraMap`, the `OrdPins` chain, …) is H5's own
scoping, not this refactor.

## H5 scoping — the column is three sets, and a second extraction is needed (2026-10-04)

Not a port; a measurement round whose output is
[../topics/velu/TOPIC-H5-engine.md](../topics/velu/TOPIC-H5-engine.md) and the
SET-1 work order. Four findings.

**The two `S_` files split 196 / 183 / 105.** Intersecting the declaration names
of `S_…exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean` (379 decls /
9,906 lines) and `S_…exists_restrictAlong_placeOfPoint_eq_add.lean` (301 / 7,255)
gives 196 names in both (the shared engine plus already-ported dictionary/H0
names), 183 dual-only (`kw_dcao_*`, `cmm*`, `idDatum`/`compDatum`, `endst20`
tail) and 105 res-only (the `es1a9_*`/`es1a10_*` non-collinear engine). That is
the set cut: SET-1 shared engine, SET-2 dual-only + headline 1, SET-3 res-only +
headline 2.

**`Def_DualIsogenyAPI.lean` was unbudgeted.** Both `S_` files and both `Thm_`
wrappers import it — 316 lines / ~50 declarations (`AddMonoidHom.IsDualPair`,
`AddMonoid.End.DualEndData`, `ofCharPoly`/`intLinComb`/`symm`), mathlib-only, and
none of it is ported. It is SET-1's first new module.

**A second extraction is needed (H5r-2).** H5 must not import Vélu, and exactly
eight pin names it uses are declared only in Vélu modules:
`ord_X_eq_neg_two_of_not_isFinitePlace` (`Velu/Engine.lean` → `Place/Dictionary.lean`)
and `Place.mem_restrictAlong_iff` / `Place.ramificationIndexAlong_pos` /
`Place.ord_restrictAlong_ne_zero_iff` / `isIntegral_algHomId` /
`finiteAlong_algHomId` / `restrictAlong_algHomId` (`Velu/RestrictAlong.lean` → a
new `AlgebraicCurve/Defs/RestrictAlongAPI.lean`), plus
`normFormulaAlong_of_elliptic`, which is a **same-name/different-statement** pair:
the pin's H5 section is `[CharZero F]` with no `hsep`, the port's H4 copy in
`Velu/RestrictAlong.lean` is the char-free `hsep` version. The H5 copy follows the
pin's H5 binders; the two stay in disjoint import branches (flagged as a risk).

**The extraction goes into a new leaf, not `Correspondence.lean`.** The three
`Place.*` lemmas already sit in a delimited `Prerequisites: the restrictAlong
place calculus` block at the top of `Velu/RestrictAlong.lean`; adding them to
`Correspondence.lean` would cascade every WeilExchange/ModularCurve importer, so
the home is a new `RestrictAlongAPI.lean` and the three existing modules are
edited once, in SET-1. All of SET-2/SET-3 is new files, so the column's only
cascade is SET-1's single wave.

**Dispatch.** SET-1 (the substrate: extraction + `DualAPI.lean` + the shared
`IsogenyEndDatum/Engine.lean`) is dispatched to one subagent; SET-2's order is
written only after the manager reviews SET-1, and no two sets run at once.

## H5 SET-1 — the substrate landed, and a fourth node was hiding (2026-10-04)

**Result.** Checker `5133 → 5310 identical (305 → 311 promoted), 0 mismatched, 0
missing, 35 → 36 own` (+177 identical, +6 promoted, +1 exemption). The whole tree
`lake build` was re-verified green after the set's one wave of existing-module
edits (58 s cascade); no `sorry`; `#print axioms` on the ported surface is
`[propext, Classical.choice, Quot.sound]`.

Modules: new `AlgebraicCurve/Defs/RestrictAlongAPI.lean` (the six
`Place.*`/`algHomId` declarations moved out of `Velu/RestrictAlong.lean`), new
`WeierstrassCurve/Isogeny/DualAPI.lean` (the whole `Def_DualIsogenyAPI.lean`,
48/48), new `WeierstrassCurve/IsogenyEndDatum/Engine.lean` (**130 of the 136**
validated declarations + the H5 `normFormulaAlong_of_elliptic`),
`ord_X_eq_neg_two_of_not_isFinitePlace` moved from `Velu/Engine.lean` to
`Place/Dictionary.lean`, and the checker wiring (`SOURCES` += the two H5 `S_`
files; `PORT_FILES` += Engine; one `OWN_PROOFS` entry for
`instInfinitePlace`).

**The three left behind are a finding, not a gap.** `kw_hk5f_addSumCoordSeamDataNCAt_proved`,
`kw_hk5f_addGeomMorphSupply_proved` and `kw_hk5f_addDatumSupply_proved` need
`WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place`, whose
canonical home is a **separate node the scout never counted**:
`P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean`,
**3,061 lines / 115 declarations**. It is not in the port and not in the 42-node
slice — the same class of miss as `Def_DualIsogenyAPI` (H2 §2). Its 115
declarations are exactly the `restrictAlong`-column engine (`es1a9_*`,
`es1a10_*`, `es1a11_*`), and **all 115 also occur in
`S_…exists_restrictAlong_placeOfPoint_eq_add.lean`** (which inlines the node), so
porting the node once covers the res engine. The subagent stopped and reported
rather than pulling it in.

**`InfinitePlace` needed a carrier.** The pin declares `place`,
`not_isFinitePlace`, `eq_of_not_isFinitePlace` as `InfinitePlace` **namespace**
lemmas; the port's `Place/Dictionary.lean` has a `class InfinitePlace` whose
fields carry those names, so they cannot be re-declared. Engine defines the
recovering instance from the gate so the pin's `S_` text still elaborates; it is
the set's one new `OWN_PROOFS` entry.

**Revision.** The specialist node folds into SET-2, which is now the whole
`restrictAlong` column (specialize node + res-only engine + the three producers
re-appended to Engine + the additivity headline); SET-3 is the dual column, which
consumes `kw_hk5f_addDatumSupply_proved` and therefore waits on SET-2. Three sets
still. Order in [../topics/velu/TOPIC-H5-engine.md](../topics/velu/TOPIC-H5-engine.md)
§5.

**SET-2 corrections (2026-10-04).** Two, both found by the worker and accepted:
the three `kw_hk5f_*_proved` producers cannot live in Engine because their proofs
go through the specialize node's `es1a9`/`es1a10` engine and `RestrictAlongAdd`
imports Engine — they stay in `RestrictAlongAdd.lean`, and SET-3 will import that
module alongside Engine. And the set was re-dispatched to a **fresh** subagent:
the SET-1 worker's turns were being cut short (it was resumed many times), so the
first worker's context was the constraint, not the task. SET-2 runs without
artificial batching bounds.

## H5 SET-2 — the `restrictAlong` column landed (2026-10-04)

**Result.** `WeierstrassCurve/IsogenyEndDatum/RestrictAlongAdd.lean` (2,504 lines,
**102 public declarations** + one `private theorem solution`). Checker
`5310 → 5412 identical (311 promoted), 0 mismatched, 0 missing, 36 own` (+102);
whole-tree `lake build` green (3 s cached); no `sorry`; `#print axioms` on the
headline, the node, both producers and three sample proofs is
`[propext, Classical.choice, Quot.sound]`.

It carries the canonical `addX_addY_specialize_at_place` node (97 new of its 115;
18 were already in Engine), the res-only extras (`kw_hk5f_addGeomMorphSupply_proved`,
`kw_hk5f_addDatumSupply_proved`, `placeOfPointEquiv_symm_eq`), and the headline
`exists_restrictAlong_placeOfPoint_eq_add`.

**Friction worth keeping.**
* The specialize `S_` file's public `solution` cannot keep that name: the dual
  `S_` file also declares a public `solution` earlier in `SOURCES`, so a public
  `solution` would diff against the wrong statement. It stays `private theorem
  solution` and the wrapper name
  `WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place` is
  exposed instead; both wrappers were appended to `SOURCES` (the headline's last
  name occurs in no `S_` file).
* `attribute [local instance] ModularCurve.Es1a1.instDecEqFunctionFieldEs1a6Add`
  must be active at file scope: Engine's instance is cross-module reachable by
  name, and without it `es1a6_addSumX` unfolds with one instance while a written
  `slope` term synthesizes another, so `rfl`/`ring` see distinct atoms.
* Pin `W.isUnit_Δ.ne_zero` → port `isElliptic_Δ_ne_zero (W := W)`.
* The ncVertical and es1a9 blocks transcribed pin-proof-verbatim (minus their
  local-instance commands) and compiled first try.

**SET-3 dispatched** to a fresh subagent: the dual-end-data column
(`DualEndData.lean`) plus the H5 vocabulary tail (`Vocabulary.lean`:
`pointEnd_apply_eq_sub`, `pointHom_apply_eq_sub`, `exists_pointEnd_eq_add`,
`exists_pointHom_comp_eq_of_ker_le_of_isCentred`,
`aeval_j_diag_eq_zero_of_finrankAlong_eq`, the plain `natCard` sibling). It imports
`RestrictAlongAdd.lean` for the shared producers. Order in
[../topics/velu/TOPIC-H5-engine.md](../topics/velu/TOPIC-H5-engine.md) §6.

## H5 SET-3 — the dual column landed; H5 closed (2026-10-04)

**Result.** New `DualEndData.lean` (3,959 lines after the density pass; 138 of the
183 dual-only declarations) and `Vocabulary.lean` (177 lines; four of six
vocabulary declarations). Checker `5412 → 5555 identical (313 promoted), 0
mismatched, 0 missing, 36 own` (+143); whole tree green; no `sorry`; axioms
`[propext, Classical.choice, Quot.sound]`. **Both H5 big theorems are now in the
port**: `exists_dualEndData_dual_mem_and_norm_eq_finrankAlong` here and
`exists_restrictAlong_placeOfPoint_eq_add` in SET-2.

**Density pass.** 5,590 → 3,959 lines (blank 30% → 3.5%; 45 empty `namespace`/`end`
stubs merged), no declaration, namespace or binder changed; checker and build
unchanged at 0/0.

**Two vocabulary nodes stopped and deferred** (Phase D, with prerequisites):
`IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred` (needs
`exists_algEquiv_restrictAlong_placeOfPoint_eq_add`, 4,271 lines, and
`algHom_ext_of_forall_restrictAlong_placeOfPoint_eq`, 988) and
`IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq` (needs the `PeriodPair`
uniformization ladder plus the `exists_intermediateField` / base-change /
`eval_jLattice` / `IsAddCyclic` chain). They are H5's only unfinished business.

**Friction.** Three by-name "in port" labels were false — `degree` (collides with
`AlgebraicCurve.Divisor.degree`), `finiteAlong_comp` (dual specialization vs the
general form) and `ord_ofHeightOneSpectrum_eq_neg_log` (general
`AlgebraicCurve.Place` form vs the port's `RationalFunctionField` form) — and had
to be ported. Three unported pin `Theorems/` imports were re-proved locally
rather than pulled in: `finite_torsionBy_of_natCast_ne_zero` and
`Point.exists_zsmul_eq_of_isAlgClosed` from
`FLTForHuman.Elliptic.{card_torsion_of_isAlgClosed,smul_surjective}`, and
`cmm5_dp_natCard_ker_natCast` directly, avoiding
`nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` and the pin-private
`nonempty_pointTorsionBy_zmod` (whose generic `AddCommGroup` lemma is 378 lines).
The pin's `S13_instIsDedekindDomainCoordinateRing` referenced a nonexistent
`CoordinateRing.isDedekindDomain` and became
`CoordinateRing.isDedekindDomain_of_Δ_ne_zero`.

**Recommendation recorded.** Two of the three re-proofs are worth promoting (the
`finite_torsionBy_aux` one is glue — it only specialises the ported
`card_torsion_of_isAlgClosed` — and stays private): `Point.exists_zsmul_eq_of_isAlgClosed`
(a fidelity gap — the pin is char-free, the port's local `surjective_zsmul_of_ne_zero`
adds `[CharZero K]`) and `nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`
(the structural "`E[n]` is `(ZMod n)²`"; its pin proof is a 23-line wrapper over
the generic `AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`,
a 378-line node absent from the port that **7 other pin `S_` nodes import,
including both of H6's base-change nodes**). Add both `Theorems/` wrappers to
`SOURCES` (undiffed today). Actionable entry:
[TOPIC-port-plan.md](../topics/velu/TOPIC-port-plan.md) §5 item 5.





