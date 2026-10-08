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

## Torsion-API promotion — the two H5 re-proofs landed (2026-10-05)

**Result.** New `FLTForHuman/Algebra/ZModTorsion.lean` (392 lines; the generic
"`A[n] ≅ (ZMod n)²`" classification, `Mathlib`-only) and
`FLTForHuman/Elliptic/TorsionZMod.lean` (192 lines; the char-free
`nsmul_surjective_charfree` / `exists_zsmul_eq` and the two wrapper headlines).
Checker `5555 → 5572 identical (313 promoted), 0 mismatched, 0 missing, 36 own`
(+17 = 18 new − 1 deleted); whole tree green (1 m 20 s); no `sorry`; axioms
`[propext, Classical.choice, Quot.sound]`.

**What landed is the fidelity fix, not just reuse.** The pin's
`Point.exists_zsmul_eq_of_isAlgClosed` is char-free; the port's local
`surjective_zsmul_of_ne_zero` added `[CharZero K]`. The promoted declaration has
the pin's signature (no `CharZero`), and `DualEndData.lean` deleted the local copy
and switched its one use in `kw_pointEnd_mul_cancel`. The generic classification
now exists for H6: **7 other pin `S_` nodes import it, including both of H6's
base-change nodes**. `finite_torsionBy_aux` stays private (glue).

**Mathlib audit (recorded negative).** Neither ingredient is in mathlib `v4.34.0`:
no `ZMod n × ZMod n ≃+ Submodule.torsionBy` classification in
`Algebra/Module/Torsion/`, `GroupTheory/`, `Algebra/Module/ZMod/` or the
elliptic-curve tree, and no `Divisible` instance or nsmul/zsmul surjectivity for
elliptic points over an algebraically closed field. mathlib's `Submodule.torsionBy`
/ `torsionBy_isInternal` API is the substrate the ported proof builds on.

**Friction.** One self-inflicted structural slip: after deleting the local theorem
a now-empty `namespace WeierstrassCurve` opener was left without its `end`,
re-nesting everything after it (`unknown identifier` for `KwDualTraceWitness` /
`kw_dcao_*`); removed. `if_neg` is deprecated in v4.34.0 (used `ite_eq_right`,
body-only). No missing `Elliptic/` piece.

## V1 SET-1 — the order-two column (2026-10-05)

**Scope.** Two new leaf modules, both namespace `WeierstrassCurve`, both
importing only `Velu/Defs.lean` (plus the mathlib
`EllipticCurve.Affine.{Formula,Point}` modules and
`FieldTheory.IsAlgClosed.Basic`; never `import Mathlib`):

* `FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean` (**524 lines**, 38 public
  declarations) — the `Def_WeierstrassCurve_VeluOrderTwo` /
  `Def_WeierstrassCurve_VeluPointMap2` vocabulary (`veluQuotient2` with its
  `a₁…a₆`/`b₂` projections, `velu2QuadDisc` with `_def`,
  `_eq_disc_cofactor`, `map_velu2QuadDisc`; `velu2XNum`/`velu2YNum`,
  `velu2XNum_eq_mul`, `velu2_equation_cleared_four`, `velu2X`/`velu2Y`,
  `velu2X_eq_div`, `velu2Y_eq_div`, `velu2_map_equation`,
  `velu2_map_nonsingular`, `veluPointMap2` and its three projection lemmas),
  `Δ_mul_j` from `Def_…_VeluQuotientJInvariant.lean:17–18` (the one declaration
  of that file the order-two `S_` files reference), and the twelve headline
  nodes of §4.2. Two proof-local helpers are `private`
  (`velu2TangentAddX_assemble`, `twoTorsionPair`).
* `FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean` (**1,428 lines**, 1
  public declaration) — the wire test
  `exists_addMonoidHom_coe_eq_veluPointMap2` plus its 60 proof-local helpers,
  all `private`.

No existing library module was edited; `spec/check_flt_statements.py` and
`spec/WeierstrassCurveConsumer.lean` were appended to only.

**Result.** Checker **`5572 → 5611` statements identical (313 promoted from
pin-private declarations), 0 mismatched, 0 missing, 36 own-proof declarations
exempted** (`5608 → 5647` port declarations checked; the +39 is exactly the
38 + 1 public declarations above). `flock .lake/flt_build.lock lake build
FLTForHuman.WeierstrassCurve.Velu.OrderTwoMap` → `Build completed successfully
(2718 jobs)`; `spec/WeierstrassCurveConsumer.lean` exit `0`; `#print axioms` on
`exists_addMonoidHom_coe_eq_veluPointMap2` and on `veluQuotient2_Delta_eq` is
`[propext, Classical.choice, Quot.sound]`; no `sorry`; no statement adapted.

### The scout gate (the set's stop-early risk)

Per §4.5 the *smallest* identity, `velu2_tangent_negAddY_cleared_identity`, was
prototyped in `ScratchSet1.lean` before the module was written, at the frozen
`-DmaxHeartbeats=4000000 -DautoImplicit=false`. **First run: `maximum recursion
depth has been reached` at 53 s**, inside `field_simp [hsd]` — the default
`maxRecDepth 1000`. The pin's own `S_` file carries
`set_option maxRecDepth 8000 in` next to `set_option maxHeartbeats 16000000 in`;
`maxRecDepth` is not the frozen knob, so it is kept. **Second run: exit 0 in
3 m 32 s wall / 3 m 18 s user.** The pin's 16,000,000-heartbeat bump is
therefore slack for this identity and every `maxHeartbeats` line of the set is
dropped: **all thirteen nodes close at the port's 4,000,000 cap.** The probe was
confirmed by the module builds below (a third run using `-o /tmp/…` was blocked
by the file sandbox — EXIT 124 at the 400 s bound with ~0.5 s user CPU, a denied
write, not a prover timeout).

### Measured table

`lake env lean` runs a whole file, so per-declaration wall time is only
available where a declaration was isolated in a `Scratch*.lean`; the `lake
build` numbers are the authoritative module measurements.

| declaration (all landed) | statement source | isolated `lake env lean` |
|---|---|---:|
| vocabulary, 26 decls (`veluQuotient2` … `veluPointMap2_some_of_ne`) | `Def_…_VeluOrderTwo`, `Def_…_VeluPointMap2` | — (in module) |
| `Δ_mul_j` | `Def_…_VeluQuotientJInvariant:17–18` | — |
| `veluQuotient2_cFour` | wrapper | — |
| `Delta_eq_veluGx_sq_mul_velu2QuadDisc` | wrapper | — |
| `veluQuotient2_Delta_eq` | wrapper | — |
| `velu2_tangent_addX_cleared_identity` | wrapper | sub-second (`elaboration took 650ms`) |
| `velu2_secant_negAddY_cleared_identity` | wrapper | **43 s** (`ScratchSecant.lean`, warm import) |
| `velu2_tangent_negAddY_cleared_identity` | wrapper | **3 m 32 s** (the scout) |
| `veluGx_ne_zero_of_two_torsion` | wrapper | — |
| `velu2QuadDisc_ne_zero_of_two_torsion` | wrapper | — |
| `veluQuotient2_Delta_ne_zero` | wrapper | — |
| `isElliptic_veluQuotient2_of_isElliptic` | wrapper | — |
| `veluQuotient2_j` | wrapper | — |
| `exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero` | wrapper | — |
| `exists_addMonoidHom_coe_eq_veluPointMap2` | wrapper | — (in module) |

| module | lines | public (+ `private`) | `lake env lean` | `lake build` |
|---|---:|---:|---:|---:|
| `Velu/OrderTwo.lean` | 524 | 38 (+2) | 5 m 21 s (pre-shape-fix; the final file also passed a profiler pass at 3 m 26 s) | **248 s** |
| `Velu/OrderTwoMap.lean` | 1,428 | 1 (+60) | **7 m 49 s** | **552 s** |
| whole wave | 1,952 | 39 (+62) | — | **12 m 47 s** |

Phase profile (`set_option profiler true` on a copy; totals 190 s / 449 s):

| phase | `OrderTwo` | `OrderTwoMap` |
|---|---:|---:|
| `share common exprs` | 44.9 s | 69.5 s |
| `linting` | 40.7 s | 106 s |
| `ring` | 40.9 s | 37.2 s |
| `type checking` | 36.1 s | 80.5 s |
| `process pre-definitions` | 32 s | 57.2 s |
| `elaboration` | 22.6 s | 56.6 s |
| `typeclass inference` | 13.6 s | 2.9 s |

The pin's per-piece `maxHeartbeats` bumps are 8 M (`SecantXContent` neighbour,
`TangentYContent`), 16 M (`TangentXAlign` 32 M, the two `*Align` pieces 160 M);
every piece closes at 4 M, so the bumps are ≥2× slack. Most of the wall time is
`linting` / `type checking` / `share common exprs`, not the two big
`linear_combination`s.

### Checker wiring

`PORT_FILES` gained the two modules and `SOURCES` the thirteen `Theorems/`
wrappers **plus the three `Definitions/` files** (`Def_…_VeluOrderTwo`,
`Def_…_VeluPointMap2`, `Def_…_VeluQuotientJInvariant`) — the vocabulary has no
wrapper, so without them its 26 declarations and `Δ_mul_j` read `MISSING IN
FLT`. The pin's `S_` files are *not* listed: every proof-local helper is
`private`, so the checker sees only the wrappers' public surface. All entries
appended last.

### Consumer

`spec/WeierstrassCurveConsumer.lean` (474 lines) gained the zone "V1 SET-1 —
the order-two quotient column": the 2-torsion curve
`y² = x³ - x` over `Q` as `WeierstrassCurveConsumer.W2`, with private witnesses
`W2_equation`, `W2_veluGy`, `W2_two_ne_zero`, `W2_veluQuotient2_Δ_ne_zero`,
`W2_isElliptic`. Executed: `(W2.veluQuotient2 0 0).a₄ = 4`,
`(W2.veluQuotient2 0 0).b₂ = W2.b₂`,
`W2.veluGx 0 0 * W2.velu2QuadDisc 0 ^ 2 = -4096`,
`(W2.veluQuotient2 0 0).Δ = -4096`, a cross-module composition with
`Velu/Defs.lean` (`veluQuotient_empty` under `congrArg`), the three
discriminant/ellipticity nodes, and `∃ φ : W2.toAffine.Point →+ …` produced by
`exists_addMonoidHom_coe_eq_veluPointMap2`, additivity-checked with `map_add`
and with its coercion pinned to `veluPointMap2`, plus
`veluPointMap2 … 0 = 0`. **Error count 0** (exit 0). Two `#print axioms` probes
added; the file's older zones are unchanged.

### Friction

* **`maxRecDepth`, not `maxHeartbeats`.** The stop-early gate fired on the
  *right* knob being wrong: the pin's `velu2_tangent_negAddY_cleared_identity`
  needs `set_option maxRecDepth 8000 in`; the default 1000 aborts `field_simp`
  in 53 s. This is not the frozen knob, so it is kept (as the work order's
  "adapted proofs" allow). Every `maxHeartbeats` bump is dropped.
* **The checker diffs the declaration's own binder/statement text**, not the
  elaborated signature: 8 of the 13 wrappers hoist their binders into
  file-level `variable` commands while the `S_` files write them inline. First
  wiring: `8 mismatched`. Fixed by building those eight nodes from the
  wrapper's `variable` prelude + bare statement and splicing the `S_` proof
  body in (`veluQuotient2_cFour` keeps no binders at all; the `{x₀ y₀}`-only
  and `(hQ)(hgy)`-only shapes are reproduced verbatim). This is §4.2's "the
  wrapper wins" made mechanical. The other five wrappers (the
  `velu2_*_cleared_identity` trio, the enumeration, the map headline) write
  their binders inline and matched first try.
* **`private` name resolution is by exact name path.** A `private`
  declaration is resolvable only at precisely the namespace path where it was
  declared, so the pin's per-piece `namespace WeierstrassCurve` blocks had to
  be kept (helper paths `WeierstrassCurve.…`), which in turn forces the port's
  header *not* to pre-open `WeierstrassCurve` (otherwise the path doubles to
  `WeierstrassCurve.WeierstrassCurve.…` and the headline reports
  `unknown identifier` for every helper). The headline is wrapped in its own
  `namespace WeierstrassCurve`. A wrong first attempt — deleting the body's
  namespace pairs instead — surfaced the mirror error: Lean's `end A.B` closes
  *two* scopes, so `end WeierstrassCurve.Affine` became `Invalid name after
  end` once the intervening namespace was removed.
* **P2M tooling dropped, not translated.** `p2m_open`, `p2m_open_scoped … in`,
  `p2m_export`, the one-line
  `namespace Point p2m_export "…" "…" end Point` wrappers and the gate-disabling
  `attribute [-instance] WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4`
  / `attribute [-simp] WeierstrassCurve.veluX_empty` (the `VeluQuotientJGates`
  curve and the pin's `IsElliptic` gates are not ported) all disappear; a
  single file-scope `open Polynomial WeierstrassCurve WeierstrassCurve.Affine`
  replaces them. The `kw_*_axiomAnchor : True` declarations and the
  `_root_`-prefixed private `abbrev`s (`KwVeluOrderTwoSecantCompatDiffAvoidAt`,
  `KwVeluOrderTwoTangentCompatAt`, `KwVeluOrderTwoAddCompatAt`,
  `KwVeluOrderTwoTangentYAlignAt`) are kept, the latter as ordinary `private
  abbrev`s. `set_option Elab.async false` is kept as the pin had it.
* **`Δ_mul_j` route recorded.** mathlib has `j : R := W.Δ'⁻¹ * W.c₄ ^ 3` and
  `@[simp] coe_Δ' : W.Δ' = W.Δ` (`Weierstrass.lean:389`, `:383`); the pin's
  ring-level `V.Δ * V.j = V.c₄ ^ 3` follows by `rw [j, ← coe_Δ', ← mul_assoc,
  ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]`, transcribed
  verbatim. mathlib's `j_eq` (`W.j = W.Δ⁻¹ * W.c₄ ^ 3`, fields only, `:402`) is
  a different statement and was not used.
* **Negative re-checked.** mathlib `v4.34.0` still has no `veluQuotient2`,
  `velu2QuadDisc`, `velu2X`/`velu2Y`, `veluPointMap2` or any Vélu declaration.
* **Checked negative on `Point`.** The pin's map `S_` file uses `-P`, `P + Q`
  and `nsmul` on `W.toAffine.Point` without any `[W.IsElliptic]`; that is
  correct in `v4.34.0` — only `Point.mk`/`pointEquivSubtype` sit in
  `Point.lean`'s `section IsElliptic` (`:543–:602`), while `Neg`/`Add`/
  `AddCommGroup` (`:627`, `:665`, `:807`) are outside it. No instance binder
  had to be added.
* **Deprecations kept verbatim.** `dif_pos`/`dif_neg` warn in `v4.34.0`
  (suggesting `dite_eq_left`/`dite_eq_right`) in
  `veluPointMap2_some_of_eq`/`_some_of_ne`, and `linter.style.haveILetI` fires
  on the pin's `haveI` in `veluQuotient2_j`; both are body-only noise and were
  left as transcribed.
* **Nothing left out.** All 13 nodes, the full vocabulary, `Δ_mul_j` and the
  wire test landed; no declaration was weakened or deferred, and no
  prerequisite sat outside the port.

The two modules were assembled from the pin by `lean/tmp/build_set1.py` and
`lean/tmp/build_set1_map.py` (untracked), which copy the giant
`linear_combination` coefficient blocks byte-for-byte rather than retyping
them; the modules are the deliverable, the scripts only a record of the
transcription.






## V1 SET-2 — the discriminant identity (2026-10-05)

**Scope.** Three new modules, namespaces `WeierstrassCurve` / `ZMod` /
`AddCommGroup` as the pin has them:

* `FLTForHuman/WeierstrassCurve/Velu/Equivariance.lean` (**300 lines**, 27
  public declarations) — the variable-change definition layer:
  `Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean:6–154` (the
  `vcX`/`vcY`/`vcXInv`/`vcYInv`/+`_vcXInv`/`_vcYInv` block, `equation_`/
  `nonsingular_variableChange_iff`, `Point.vcFun`/`vcInvFun`/+zero/left/right
  inverse, `variableChangeEquiv`, `equivOfVariableChangeEq` — a **strict
  prerequisite** of the next file, and absent from the port; see the friction
  entry below) and `Definitions/Def_WeierstrassCurve_VeluVariableChange.lean`
  whole (112 lines: `vcInvEmbedding`, `vcInvEmbedding_apply`,
  `variableChange_velu{Gy,Gx,T,U,W,TSum,WSum}`).
* `FLTForHuman/WeierstrassCurve/Velu/Discriminant.lean` (**3,589 lines**, 3
  public declarations) — `isOddVeluSet_oddOrderSummingSet`, the identity
  `veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow` (the pin's 3,566-line
  `S_` body with its 203 proof-local helpers, all `private` here), and
  `veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq`.
* `FLTForHuman/WeierstrassCurve/Velu/CyclicCount.lean` (**476 lines**, 3 public
  declarations) — `ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi`,
  `AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy`,
  `WeierstrassCurve.exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero`;
  every helper of the two counting `S_` files is `private`.

No existing library module was edited; `spec/check_flt_statements.py` and
`spec/WeierstrassCurveConsumer.lean` were appended to only.

**Result.** Checker **`5611 → 5644` statements identical (313 → 312 promoted
from pin-private declarations), 0 mismatched, 0 missing, 36 own-proof
declarations exempted** (`5647 → 5680` port declarations checked; the +33 is
exactly the 27 + 3 + 3 public declarations above). `lake build` of the wave →
`Build completed successfully (8967 jobs)`; `spec/WeierstrassCurveConsumer.lean`
exit `0` (error count 0); `#print axioms` on the identity and on the enumeration
is `[propext, Classical.choice, Quot.sound]`; no `sorry`; no statement adapted.

### The scout gate

§5.5/rule 7 asked for the identity's hardest private block, prototyped first.
The answer turned out to be "none of them": the whole 3,589-line
`Discriminant.lean` elaborates under the mandated options in **24.0 s wall /
77.8 s user** (first run, before the two import fixes, 18.7 s), so an isolated
prototype of a 1,000-plus-line dependency closure was unnecessary. To *name* the
heaviest block anyway, a `set_option profiler true` copy (`ScratchProfSet2.lean`)
was elaborated in 26.6 s wall / 77.3 s user: the heaviest single step is a `rw`
of **2.24 s** inside `N5IDAux1.norm_identity'` (the `degree_sub_lt` step of
`Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq`, generated line 1400); the
next heaviest events are a 0.60 s `field_simp` and a 0.38 s `linting`; the
344-line `core_assembly` is a chain of ≤0.36 s steps. **The pin's `maxRecDepth` is
not needed anywhere in this set**: unlike SET-1's `velu2_*_cleared_identity`
trio, the identity's `S_` file carries no `maxRecDepth` line, and the frozen
4,000,000 `maxHeartbeats` cap was never approached. The pin's only bump,
`set_option maxHeartbeats 4000000 in` on `expansion_core`, restates the pin's own
**global** cap (`fermats-last-theorem/lakefile.lean:7` is also 4,000,000), so
dropping it is a no-op; no bump was kept.

### Measured table

`lake env lean` runs a whole file, so its number is the per-module elaboration
wall time; the `lake build` numbers are single-module builds from a clean
artifact state, and the wave is the three modules built together from clean
artifacts (all serialized with `flock .lake/flt_build.lock`).

| module | lines | public (+ `private`) | `lake env lean` | `lake build` |
|---|---:|---:|---:|---:|
| `Velu/Equivariance.lean` | 300 | 27 (+6) | 7.5 s | **7.7 s** |
| `Velu/Discriminant.lean` | 3,589 | 3 (+~210) | 24.0 s (77.8 s user) | **25.4 s** |
| `Velu/CyclicCount.lean` | 476 | 3 (+~20) | 51.8 s | **80.0 s** |
| whole wave | 4,365 | 33 | — | **95 s** (1 m 35 s) |

The three modules are far cheaper than SET-1's (which needed 5–8 min `lake env
lean` and 248/552 s builds): this column is many small `ring`/`field_simp`/
`linear_combination` steps rather than a handful of giant coefficient-block
identities. `CyclicCount` spends most of its wall time loading the
`ModularCurve/Gamma0Index.lean` import chain (system time dominates user time).

### Checker wiring

`PORT_FILES` gained the three modules **last**. `SOURCES` gained, **last**: the
four odd-order wrappers
(`Thm_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet`,
`…_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow`,
`…_discriminant_ne_zero_of_addOrderOf_eq`,
`…_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero`), the two
counting wrappers (`Thm_ZMod_natCard_…`, `Thm_AddCommGroup_natCard_…`), and the
`Definitions/` files this set ports: `Def_…_VeluVariableChange.lean` (whole),
`Def_…_VeluEquivariance.lean` (whole file listed; see the friction entry — the
port carries the `map_velu*` block from `Velu/Formula.lean`, not from this set),
and `Def_…_VariableChangePointEquiv.lean` (the prerequisite core). Without the
`Definitions/` entries the 27 vocabulary declarations read `MISSING IN FLT` —
SET-1's friction, repeated as §5.3 warned.

### Consumer

`spec/WeierstrassCurveConsumer.lean` (474 → **580 lines**) gained the zone
"**Zone (V1 SET-2): the odd-order discriminant column**" with one sub-zone per
module, all executed, no `#check`, no `sorry`:

* (a) `Velu/Equivariance.lean` — the curve `W3 : y² = x³ + 1` as
  `WeierstrassCurveConsumer.W3`; `variableChange_veluU` at `(x, y) = (1, 1)`
  composed with `Velu/Defs.lean`'s `veluU 1 1 = (veluGy 1 1)² = 4` (concrete
  RHS `((C.u⁻¹ : ℚˣ) : ℚ)^6 * 4`), and `map_veluQuotient` under
  `RingHom.id ℚ` reducing to `W3.veluQuotient S`.
* (b) `Velu/Discriminant.lean` — `W3.Δ = -432`, `W3.IsElliptic`,
  `(W3.veluQuotient ∅).Δ = -432` (`veluQuotient_empty`), the product rewrite
  `∏_{P∈S} veluU = ∏_{P∈S} Ψ₂Sq.eval` through
  `isOddVeluSet_oddOrderSummingSet` + `Velu/Defs.lean`'s `veluU_eq_Ψ₂Sq_eval`, the
  identity and `…_discriminant_ne_zero_of_addOrderOf_eq` at an order-three point
  (`n = 1`, so `Δ^3`).
* (c) `Velu/CyclicCount.lean` — concrete ψ via `#eval ModularCurve.dedekindPsi 6`
  → `12` and `… 12` → `24`; both counting headlines executed; the enumeration at
  `ℓ = 3` over an algebraically closed field of characteristic zero composed with
  (b)'s nonvanishing node (`Fintype.card ι = 4`).

Two `#print axioms` probes added for the identity and the enumeration. **Error
count 0** (exit 0). The file's older zones are unchanged.

### Friction

* **A prerequisite was missing, and the work order's import line could not
  hold.** §5.3 says `Equivariance.lean` "imports `Velu/Defs.lean` only", but the
  pin's `Def_…_VeluVariableChange.lean` imports
  `Def_…_VariableChangePointEquiv.lean`, and the port did not have
  `vcX`/`vcY`/`vcXInv`/`vcYInv`/`vcFun`/`vcInvFun`/`variableChangeEquiv` at all
  (§6.2 assigns them to SET-3). They are used by `vcInvEmbedding`'s definition and
  injectivity proof and by the identity's private `SummingSetTransport`/
  `variableChangeAddEquiv` block, so the set cannot be built without them. Rather
  than restate or weaken, they were ported **publicly and verbatim** here
  (lines 6–154 of that pin file), and the pin file was added to `SOURCES`.
  **Action for the manager: SET-3's `VariableChangePoint.lean` order must be
  amended** — it should import `Equivariance.lean` and carry only
  `WeierstrassCurve.Affine.Point.vcInvFun_add` (plus any consumer-specific tail,
  e.g. `equivOfVariableChangeEq` if still wanted), not redeclare the core; a
  redeclaration would be a cross-module duplicate.
* **The `map_velu*` block was already in the port.** §5.2/rule 3 order the port of
  `Def_…_VeluEquivariance.lean:1–60` into `Equivariance.lean`, but
  `Velu/Formula.lean` already declares `map_velu{Gx,Gy,T,U,W}`,
  `map_veluTSum`/`WSum`/`Quotient` with identical statements (transcribed by the
  earlier H5 work). A first build did carry them and it cost 8 silent
  cross-module duplicates: Lean accepted the whole library and the consumer, but
  only one copy survives when both modules are imported, and the checker counted
  the names twice. The block was removed from `Equivariance.lean`; the pin file
  stays in `SOURCES`, which is the one visible benefit — `Velu/Formula.lean`'s
  `map_veluQuotient` moved from *promoted (pin-private)* to *public-source
  matched*, the `313 → 312` promoted delta.
* **mathlib import drift.** The identity's private polynomial engine uses
  `Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq` / `…_index_eq`
  (`Mathlib.LinearAlgebra.Lagrange`) and
  `WeierstrassCurve.IsCharNeTwoNF`/`toCharNeTwoNF`/`toCharNeTwoNF_spec`
  (`Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms`); neither module was in
  `Velu/OddOrder.lean`'s closure (`import Mathlib` in the pin had hidden it), so
  both are imported explicitly. With them, plus `Point.neg_zero` for the one
  `neg_zero` ambiguity that opening `WeierstrassCurve.Affine.Point` creates, the
  identity compiled with no proof-body change.
* **De-duplication as §5.2 prescribes.** The identity's `S_` file carries its own
  private `exists_some_of_ne_zero` and `veluGy_ne_zero_of_two_nsmul_ne_zero`; both
  were dropped in favour of the port's public copies in `Velu/Formula.lean` and
  `Velu/OddOrder.lean`. `isOddVeluSet_oddOrderSummingSet` is the port's own proof
  (not a transcription): `hp.eq_two_or_odd'`, `omega`, then the promoted
  `kw_isOddVeluSet_oddOrderSummingSet_odd`.
* **Namespace/name resolution.** The pin's outer `namespace P2MW.…` is dropped so
  each `private` helper lands at its natural root path (the pin's helpers are
  reached as `N5IDAux1.…`, `N5IDAux4.…`, `N5IDCharTwo…`, `N5IDC2Aux4.…`, and the
  identity's own private `seam_*`/`variableChange_veluQuotient` at
  `WeierstrassCurve.…`); the headlines are wrapped in `namespace WeierstrassCurve`
  / `namespace ZMod` / `namespace AddCommGroup`. The pin leaves the
  `AddCommGroup` counting `S_` file's namespace unclosed (its `P2MW` wrapper is
  unclosed too), which initially nested the enumeration headline — caught by
  `#check` and fixed by closing the namespace. `p2m_open`/`p2m_export`/
  `p2m_reactivate`, the `attribute [-instance]`/`[-simp]` gates and the
  `namespace X p2m_export … end X` wrappers are dropped as in SET-1.
* **Checker namespace tracking is naive about dotted `end`.** `end Affine.Point`
  pops one stack frame in `namespace_events`, not two, so the checker reads the
  two `Discriminant.lean` headlines as
  `WeierstrassCurve.WeierstrassCurve.…` although Lean's name is single-level
  (`#check @WeierstrassCurve.veluQuotient_…` confirms). The last-name + statement
  match is unaffected (`0 mismatched`), and `promoted_key` already reduces to the
  last two components, so this was recorded rather than worked around; the file
  was *not* reshaped to satisfy the tracker.
* **Deprecations kept verbatim** (body-only noise): `push_neg` in
  `nonsingular_variableChange_iff`; `Set.mem_setOf_eq`, `Set.Infinite.diff`,
  `Polynomial.degree_sub_lt` and the `linter.style.haveILetI` hint on the pin's
  `haveI`. No `sorry`, no weakened statement, no `OWN_PROOFS` entry needed, and
  nothing was left out.

The three modules were assembled from the pin by `lean/tmp/build_set2_equiv.py`,
`…/build_set2_disc.py` and `…/build_set2_cyc.py` (untracked), which copy the pin
byte-for-byte and apply only the mechanical transforms above; `ScratchSet2.lean`
holds the scout and the consumer-zone prototype. The modules are the deliverable,
the scripts only a record of the transcription.

## V1 SET-3 — the quotient `j` column (2026-10-05)

**Scope.** Two new modules, both under `Velu/` (the variable-change point
vocabulary now lives in `Velu/Equivariance.lean`, so its additivity node follows it
rather than opening a new area directory for one declaration); namespaces
`WeierstrassCurve` / `WeierstrassCurve.Affine.Point` as the pin has them:

* `FLTForHuman/WeierstrassCurve/Velu/VariableChangePoint.lean` (**213 lines**, 1
  public declaration + 12 `private`) — `WeierstrassCurve.Affine.Point.vcInvFun_add`,
  the one **off-subject prerequisite** of V1, carried by the `ucl` rule
  (`S_WeierstrassCurve_Affine_Point_vcInvFun_add.lean`, 188 / solution 184). Its
  module header says so and names its pin source. The
  `VariableChangePointEquiv` core it is stated in (`vcX`/`vcY`/`vcXInv`/`vcYInv`,
  `equation_variableChange_iff`, `nonsingular_variableChange_iff`, `vcFun`,
  `vcInvFun`, `vcFun_leftInverse`, `vcFun_rightInverse`) is **imported** from
  SET-2's `Velu/Equivariance.lean` and not redeclared — the §6.2 amendment.
* `FLTForHuman/WeierstrassCurve/Velu/CyclicQuotientJ.lean` (**840 lines**, 54
  public declarations + 58 `private`) — the pin's
  `Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean` (207 lines) whole:
  `xVeluT`/`xVeluU`/`xVeluW` and the three `xVelu*_eq_velu*` bridges,
  `absSum`/`absSum_of_{finite,infinite}`, `xVeluCurve`/`xVeluX` + their six `a₁…a₆`
  projections, `twoTorsionY`, `xVeluG`, `twoVeluCurve`/`twoVeluX` + the six
  projections, `kernelXSet`/`coKernelXSet`, `stepCurve`/`stepX` + the four branch
  lemmas, `subgroupOfX`/`stepSubgroup`, `CQJState`/`cqjStep`/`cqjIterate`/
  `cyclicQuotientCurve`/`cyclicQuotientJ` and the eleven unfoldings (`…_def`,
  `…_one`, `cqjStep_apply`, `length_primeFactorsList_eq_succ`, `…_eq_of_two_le`,
  `cyclicQuotientJ_eq_j`); and the two headline nodes
  `cyclicQuotientJ_variableChange_eq` /
  `cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed`, with every helper of
  `P2MKcCQJvc` (31 declarations) and `P2MKcCQJbc` (27) `private`. This is the set's
  wire test.

No existing library module was edited; `spec/check_flt_statements.py` and
`spec/WeierstrassCurveConsumer.lean` were appended to only.

**Result.** Checker **`5644 → 5699` statements identical (312 → 312 promoted from
pin-private declarations), 0 mismatched, 0 missing, 36 own-proof declarations
exempted** (`5680 → 5735` port declarations checked; the +55 is exactly the
1 + 52 + 2 public declarations above). `lake build` of the two-module wave →
`Build completed successfully (2721 jobs)`; `spec/WeierstrassCurveConsumer.lean`
exit `0` (error count 0); `#print axioms` on both headlines is
`[propext, Classical.choice, Quot.sound]`; no `sorry`; no statement adapted.

The column is **two orders of magnitude cheaper than SET-1/SET-2**. There was no
scout gate to run: the largest single proof here is 41 lines (`subgroupOfX_vc`),
the heaviest declaration is `cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed`'s
private `subgroupOfX_map` (whose `IsAlgClosed.splits` root-lifting block is the
pin's), and the whole 840-line module elaborates in **5.8 s wall / 12.6 s user**.
The pin carries **no** `maxHeartbeats` and **no** `maxRecDepth` line in these three
`S_` files (the only `set_option` is `autoImplicit false` in the definition file),
so nothing had to be kept and nothing dropped; the frozen 4,000,000 cap was never
approached. `xVeluG_map` consumes the public `map_veluGx`, so `Velu/Formula.lean`
is imported, not re-ported (SET-2's 8-duplicate lesson); SET-1's `Velu/OrderTwo.lean`
is imported per §6.3.1 even though no node here names `veluQuotient2` (the `ℓ = 2`
branch goes through the local `twoVeluCurve`).

### Measured table

`lake env lean` is the warm per-module elaboration wall time (it does not write an
`.olean`); the `lake build` numbers are single-module builds from a deleted
artifact; the wave builds the two modules together from deleted artifacts. All
builds serialized with `flock .lake/flt_build.lock`.

| module | lines | public (+ `private`) | `lake env lean` | `lake build` |
|---|---:|---:|---:|---:|
| `Velu/VariableChangePoint.lean` | 213 | 1 (+12) | 4.8 s | **6.3 s** (4.4 s module) |
| `Velu/CyclicQuotientJ.lean` | 840 | 54 (+58) | 5.8 s (12.6 s user) | **6.3 s** (5.5 s module) |
| whole wave | 1,053 | 55 | — | **11.0 s** (repeat 12.8 s) |

### Checker wiring

`PORT_FILES` gained the two modules **last**. `SOURCES` gained, **last**: the three
wrappers (`Thm_WeierstrassCurve_Affine_Point_vcInvFun_add`,
`Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq`,
`Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed`) and the
`Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean` source. Without that
`Definitions/` entry the 52 vocabulary declarations read `MISSING IN FLT` — SET-1's
friction, repeated for the third time as §6.3 prescribes. The pin's two `S_` files
are *not* listed: their entire content is `private` in the port, so the checker
never sees it, and no `OWN_PROOFS` entry was needed. The `SOURCES` order is
immaterial for these four files (no last name is shared between a wrapper and the
definition file), but the wrappers are listed first so the statement authority
stays explicit.

**Measured correction to §6.2.** The work order (and the plan's referenced-fraction
table) calls `Def_..._CyclicQuotientJ.lean` a **46-declaration** file; it has **52
public declarations** (20 `def`, 31 `theorem`, 1 `abbrev`). The six-theorem gap is
exactly the six `@[simp] theorem xVeluCurve_a₁/a₂/a₃` and
`@[simp] theorem twoVeluCurve_a₁/a₂/a₃` projections: the table's regex anchors on
`^(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?(?:def|theorem|…)`, which
cannot see an attributed declaration on one line, while the checker's `DECL_RE`
gained its `attrs` group in the SET-3 T5 round and can. All 52 are transcribed
(+6 against the 46 estimate), and the `+55` checker delta reconciles as
1 + 52 + 2.

### Consumer

`spec/WeierstrassCurveConsumer.lean` (580 → **679 lines**) gained the zone
"**Zone (V1 SET-3): the quotient `j` column**" with one sub-zone per module, all
executed, no `#check`, no `sorry`:

* (a) `Velu/VariableChangePoint.lean` — `vcInvFun_add` bundled into a genuine
  `→+` (`vcAddHom`) and exercised with `map_add`; then composed with SET-2's
  `Velu/Equivariance.lean` core: `vcFun C W (vcAddHom C W P) = P` by
  `vcFun_rightInverse`. Numeric anchor: the inverse coordinates of the variable
  change `⟨1, 5, 0, 7⟩` at `(9, 11)` are `(4, 4)` (`vcXInv`/`vcYInv`, by `norm_num`).
* (b) `Velu/CyclicQuotientJ.lean` — the SET-1 curve `W2 : y² = x³ - x` over `ℚ`
  with the `zmultiples` subgroup of its 2-torsion point `(0, 0)`:
  `W2.cyclicQuotientJ (AddSubgroup.zmultiples W2P) 1 = 1728` (`#eval`-free numeric
  check: `c₄ = 48`, `Δ = 64`); the `N = 2` recursion through
  `cyclicQuotientJ_eq_of_two_le`; the `ℓ = 2` branch `stepCurve_two` exposing
  `Velu/Defs.lean`'s `twoVeluCurve`; the `ℓ ≠ 2` branch `stepCurve_of_ne_two`
  exposing `xVeluCurve`; the base-change headline applied at complex conjugation
  (`W2R : WeierstrassCurve ℝ`, `A = B = ℂ`, `f = Complex.conjAe`) giving Galois
  invariance of the quotient `j`; and the base change along `ℝ → ℝ` preserving the
  numeric anchor (`(W2R.baseChange ℝ).cyclicQuotientJ ⊥ 1 = 1728`).

Two `#print axioms` probes added for the two headlines. **Error count 0**
(exit 0). The file's older zones are unchanged.

### Friction

* **The 46-vs-52 declaration count** above: a measurement artefact of the
  referenced-fraction regex, not a scope miss. Recorded because the *estimate* was
  low by six declarations and the checker delta had to be reconciled against it.
* **Proof-local duplication with SET-2, not a checker duplicate.** SET-2's
  `Discriminant.lean` already carries a `private` copy of the whole
  `vcInvFun_add` helper chain (`vcX_injective`, `vcY_injective`,
  `vcAdd_partialX_aux`/`Y_aux`, `negY_variableChange`, `Yeq_variableChange_iff`,
  `slope_variableChange`, `addX_variableChange`, `addY_variableChange`,
  `some_eq_some'`, `vcFun_add`, `variableChangeAddEquiv`) because the odd-order
  discriminant transport needed it. Those copies are `private`, hence distinct
  Lean constants with per-file names: no cross-module duplicate, no `MISSING IN
  FLT`, and the checker's promoted count is unchanged (`312 → 312`). The *proof
  code* is nevertheless written twice in the tree. The work order forbids editing
  the closed `Discriminant.lean` and forbids promoting the chain (a public
  `vcFun_add` would want its own `SOURCES` entry and would then collide with the
  SET-2 module's copy), so the duplication stands. The clean fix, if V2 wants one
  home, is a future refactor moving the `variableChangeAddEquiv` chain public into
  `VariableChangePoint.lean` and having `Discriminant.lean` import it.
* **mathlib drift (proof body only).** The pin's `V.baseChange_nonsingular` is not a
  `WeierstrassCurve` projection in `v4.34.0`; the affine form is
  `WeierstrassCurve.Affine.map_nonsingular` (`…baseChange_nonsingular` needs an
  `AlgHom`, not a `RingHom`). Used in `ptMap_some` and `subgroupOfX_map`.
* **`WeierstrassCurve.Affine.Point.map` is indexed on the base ring — an
  instantiation limit, not an instance diamond.** The base-change headline's
  `f : A →ₐ[R] B` forces `E : WeierstrassCurve R`, so it cannot be applied at
  `E : WeierstrassCurve ℚ` with the natural `f : ℂ →ₐ[ℝ] ℂ`. The consumer's Galois
  zone therefore uses `W2R : WeierstrassCurve ℝ`. Trying the ℚ-curve form does not
  fail cleanly: the elaborator loops in instance search and dies at the frozen
  4,000,000 cap with `(deterministic) timeout at 'whnf'`. **The library node is
  unaffected** — both modules close under the cap — but the failure mode is worth
  recording so no later agent re-tries it or blames the frozen knob.
* **A numeric anchor over `ℂ` blew the cap.** `(W2.baseChange ℂ).cyclicQuotientJ ⊥ 1
  = 1728` by `norm_num` (with `map_c₄`/`map_Δ`) ran ~4 min and then hit the same
  `whnf` timeout; dropped. The required concrete computation is over `ℚ` and closes
  instantly; the base-change zone keeps the `ℝ → ℝ` numeric instead. `maxHeartbeats`
  was not raised.
* **§6.5's "composition with `Velu/MapEquation.lean`" is not natural for this
  column.** `MapEquation.lean` is the explicit-map-equation engine (`veluDeficit`,
  `veluXCorr`, the `VeluThmOneOddAt` carrier), disjoint from the quotient
  iteration, and no declaration of this column mentions it. Rather than manufacture
  a link, the consumer zone composes with what the column actually consumes:
  `Velu/Defs.lean` (`xVeluCurve`/`twoVeluCurve`/`kernelXSet`, and the six `a₁…a₆`
  projections), SET-2's `Velu/Equivariance.lean` (`vcFun_rightInverse`) and SET-1's
  curve vocabulary. Nothing was left out of the work order's deliverable list; the
  only deliberate substitutions are the `ℂ` anchors above.
* **Deprecations kept pin-verbatim** (body-only noise; `lake build` marks the module
  `⚠`): `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` (the four
  `stepCurve_*`/`stepX_*` branch lemmas, and again in the base-change
  `stepCurve_map`/`stepX_map`); `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (the
  `kernelXSet_vc`/`coKernelXSet_vc`/`kernelXSet_map`/`coKernelXSet_map` set
  extensions); and the `linter.style.haveILetI` hint on the pin's
  `letI : Algebra A B := f.toAlgebra` in `ptMap`. No `sorry`, no weakened statement,
  no `OWN_PROOFS` entry needed.
* **Namespace tracking is clean here.** Because the `P2MKcCQJvc`/`P2MKcCQJbc`
  helpers are all `private`, the checker's naive `end`-tracking never reads them,
  and `CyclicQuotientJ.lean` uses no dotted `end A.B`, so its 54 public declarations
  match 54/54 with no `WeierstrassCurve.WeierstrassCurve.…` artefact (the
  `Discriminant.lean` situation is not repeated).

The two modules were transcribed by hand from the pin (the one mechanical pass —
prefixing the 58 proof-local helpers with `private` — was applied inline);
`ScratchSet3.lean` holds the scouted definition layer and `ScratchConsumer3.lean`
the consumer-zone prototype (both untracked, gitignored).

## V1 close-out — the three ready columns landed (2026-10-05)

**Manager's review of the wave.** V1 is complete: three sets, one subagent each, run
in series with the manager reviewing the tree between sets. The wave is the first
part of the Vélu port delivered as **new files only** — seven modules, no existing
library module edited — so no set cascaded and the only whole-tree build was this
milestone.

| set | modules | written | est. | checker delta |
|---|---|---:|---:|---|
| V1-SET-1 | `Velu/OrderTwo.lean`, `Velu/OrderTwoMap.lean` | 1,952 | 1.73 k | +39 |
| V1-SET-2 | `Velu/Equivariance.lean`, `Velu/Discriminant.lean`, `Velu/CyclicCount.lean` | 4,365 | 4.27 k | +33 |
| V1-SET-3 | `Velu/VariableChangePoint.lean`, `Velu/CyclicQuotientJ.lean` | 1,053 | 1.05 k | +55 |
| **V1** | **7 modules** | **7,370** | **7.0 k** | **5611 → 5699 identical** |

Checker at the milestone: `5699 statements identical (312 promoted from pin-private
declarations), 0 mismatched, 0 missing, 36 own-proof declarations exempted (5735
port declarations checked)`. Whole-tree build green, **9,289 jobs, 14.1 s** (warm;
only the wave's own `.olean`s were missing). Consumer `spec/WeierstrassCurveConsumer.lean`
679 lines, exit 0, 0 errors. `#print axioms` on all five V1 headlines:

```
exists_addMonoidHom_coe_eq_veluPointMap2
veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
cyclicQuotientJ_variableChange_eq
cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
  ⟹ [propext, Classical.choice, Quot.sound]
```

**Plan vs actual.** The line estimates held to +13% / +2% / 0% — inside the
playbook's ±10% expectation once SET-1's heavy cleared identities are counted. The
**definition-layer estimate was wrong twice**, in opposite directions, and both
errors are the same class: a referenced-fraction table measures *what is
referenced*, not *what the module imports* and not *what the port already has*.

* `Def_…_VeluVariableChange` imports `Def_…_VariableChangePointEquiv`, which no V1
  order had assigned — SET-2 found it only by reading the definition module's
  imports, ported its core publicly in `Equivariance.lean`, and SET-3's order was
  amended to import it. Third instance in this block of the rule that a work order's
  source list is the route closure of its deliverable, not the tool's node list.
* The `map_velu*` commutation block was already public in `Velu/Formula.lean` from
  the H4 work, so SET-2's definition layer cost ≈0 rather than the ≈60 budgeted;
  SET-2's first build produced eight silent cross-module duplicates before the agent
  grepped the port by name and removed them.

**The heaviness ranking is not the line count.** SET-1's 1,952 lines cost 5–8 min
per `lake env lean` and 248–552 s per `lake build` (wave 12 m 47 s); SET-2's 4,365
lines cost 8–52 s and a 95 s wave; SET-3's 1,053 lines cost ≈6 s each and an 11 s
wave. The cost sits in the pin's enormous cleared `linear_combination` identities,
and their binding knob is the pin's **`maxRecDepth 8000`, not `maxHeartbeats`** —
SET-1's scout died at the default 1000 inside `field_simp`. Every pin
`maxHeartbeats` bump in all three sets was dropped and every node closed at the
frozen 4,000,000.

**Friction carried into the record.** (1) The checker's `SOURCES` needs the
`Definitions/` entries for vocabulary-only modules, or the vocabulary reads
`MISSING IN FLT`; all three sets hit this. (2) The checker reads a declaration's own
text, so a wrapper that hoists binders into file-level `variable`s must have that
prelude spliced onto the `S_` proof — SET-1: 8 of 13 mismatched until it was.
(3) The checker's `end`-tracker pops one frame on a dotted `end A.B`, so
`Discriminant.lean`'s headlines read as `WeierstrassCurve.WeierstrassCurve.…` in the
tracker while Lean's names are single-level; matching is unaffected and the file was
not reshaped to please the tracker. (4) `Point.map` is indexed on the base ring, so
the base-change headline cannot be applied at `W2 : WeierstrassCurve ℚ` with
`f : ℂ →ₐ[ℝ] ℂ`; the wrong form does not fail cleanly — it loops in instance search
and dies at the frozen cap (the same `whnf` timeout killed a `ℂ`-valued `norm_num`
numeric anchor). Both were worked around in the consumer, not in the statement.

**Refactor-round item (V2).** `Discriminant.lean` and `VariableChangePoint.lean`
each carry a `private` copy of the `vcInvFun_add` helper chain: private ⇒ distinct
constants, no checker impact and no `MISSING IN FLT`, promoted count unchanged
(312 → 312), but the code is written twice. Both files are frozen for this wave;
the clean fix is a refactor promoting `variableChangeAddEquiv` public into
`VariableChangePoint.lean` and deleting the copy in `Discriminant.lean`.

**What V2 inherits.** The full order-two vocabulary and point map; the discriminant
identity and the ψ-counting/enumeration pair; `cyclicQuotientCurve`/`cyclicQuotientJ`
with both well-definedness lemmas; `Velu/Equivariance.lean` as the home of the
variable-change/core vocabulary and `Velu/Formula.lean` as the home of `map_velu*`;
and a warm tree. V2's remaining targets are the two gateways
(`exists_pointEnd_eq_of_mem_isogenyEndSubring` → `exists_sq_lt_four_mul…`) and the
Ribet-side completion, to be scoped against these modules.

## V2 SET-1 — the two Mazur gateways (2026-10-06)

**Scope and re-measurement.** V2 was scoped against the tree V1 left (the plan's
§1.1 table predated V1). A fresh frontier run gives 17 remaining nodes; the four V2
targets are unchanged. The name sweep is what changed the budget: the gateway-1
`S_` file has 143 declarations of which **117 are already public** (the H5
`IsogenyEndDatum/Engine.lean` port of two other pin `S_` files), leaving 26; and three
closure members priced at 1,246 / 911 / 58 lines were already in the port under other
names (`Divisor.pushforwardNormFormula` minus `[CharZero F]`;
`hasPrincipalDivisors_of_finiteDimensional_of_isSeparable` with different binder
spelling; `pointMapOfPushforward_surjective_of_separableAlong'`). The whole
definition layer was already ported, so V2 had no `Definitions/` work.

**The set, as measured.** Four new modules, 1,134 lines:

| module | lines | `lake env lean` | `lake build` | decls (pub/priv) |
|---|---:|---:|---:|---|
| `WeierstrassCurve/Place/CoordinateRingDedekind.lean` | 83 | 1 m 22 s | 3.4 s | 2 / 1 |
| `Elliptic/TorsionCardLight.lean` | 55 | 10.6 s | 2.3 s | 2 / 0 |
| `WeierstrassCurve/IsogenyEndDatum/PointEndSubring.lean` | 416 | 55.7 s | 59 s | 23 / 1 |
| `WeierstrassCurve/IsogenyEndDatum/CharPolySquare.lean` | 580 | 1 m 05 s | 74 s | 19 / 0 |

Plus a **new** `spec/IsogenyEndDatumConsumer.lean` (178 lines, exit 0 / 1 m 10 s).
The edit loop's fixed cost dominated: a tiny file importing the SET-1 cone takes
**1 m 37 s** before any work (`DualEndData.olean` is 8.1 MB), so the agent batched
declarations and never `lake build`-ed in the loop. No declaration came near the
frozen 4,000,000 cap; the pin's 25,600,000 bump was dropped.

**Milestone.** Checker `5750 → 5796 identical` (+46: 46 new public declarations — the
`promoted → ok` flip of `IsogenyEndDatum.pointEnd_eq_geomMorph_sub_geomMorph_zero`
contributes 0, since `promoted` is a subset of `identical`), promoted `312 → 311`,
`0 mismatched / 0 missing`. Whole-tree build green, **9,298 jobs, 12.7 s** (+4 jobs =
the four leaves, **no cascade**). `#print axioms` clean on all seven headlines.

**Drops, all by count.** The pin's three `scoped instance instFactNatPrime{2,3,7}_s13e2`
are invisible to the checker's `DECL_RE` (140 declarations extracted vs 144 counted by
hand) and unnecessary; the pin's primed `Divisor.pushforwardAlong_pushforwardAlong'`
is pin-`private` and a one-line instance of the port's public general lemma; the pin's
`IsogenyEndDatum.comp` is pin-`private` (the port lands it private, the pin's
`p2m_export` had made it look public). `KwIsogenyEndAddDatumSupply` was already public
in `Engine.lean:228`.

**Two findings.**

1. **A third module-import collision, of the same family as the plan's §2.1 one.**
   `Velu/RestrictAlong.lean` and `IsogenyEndDatum/Engine.lean` both declare
   `WeierstrassCurve.Affine.normFormulaAlong_of_elliptic`, so SET-1's consumer cannot
   import `spec/WeierstrassCurveConsumer.lean`'s cone and lives in its own spec file.
   Then, inside SET-1, `GenusOnePlaceGateCentred.lean`'s `Place/RRSpace.lean`
   (`scoped instance instInfinitePlace`) proved unimportable beside `Engine.lean`
   (plain `instInfinitePlace`), so the consumer's gateway zone states the three gate
   instances as hypotheses rather than discharging them from
   `exists_genusOnePlaceGate_isCentred_and_abelTheorem`. Both are registered in
   `CARRY-FORWARD.md`; the fix is a refactor round.
2. **A name-extraction regex is an aid, not an authority.** `isIntegral_comp_ι` was
   nearly mis-swept because a Greek-letter suffix truncates; and the checker's own
   `raw_declarations` disagrees with a hand count on `scoped instance`. Use the
   checker's extractor for any sweep a work order depends on.

**Consumer.** `spec/IsogenyEndDatumConsumer.lean`, four zones: the coordinate-ring
pair (with `exists_eq_XYIdeal` composed into `XYIdeal_isMaximal`), the torsion aliases
at `n = 3` feeding the `ZMod n × ZMod n` classification, gateway 1 with `hNs`
**discharged** from `IsogenyEndDatum.normFormulaAlong_auto` and `ψ = 1` realised in
`isogenyEndSubring` through `one_mem_range_pointEnd`, and gateway 2 in hypothesis form
plus two concrete `Ws13S7` prelude uses.

## V2 SET-2 — the Ribet-side completion (2026-10-06)

**The set, as measured.** Five new modules, 537 lines, plus one **additive**
reconciliation:

| file | lines | `lake env lean` | `lake build` | decls (pub/priv) |
|---|---:|---:|---:|---|
| `FieldTheory/SeparableOfCoprime.lean` | 54 | 6.9 s | 4.7 s | 1 / 0 |
| `AlgebraicCurve/PrincipalDivisors/SeparableRatFunc.lean` | 46 | 5.1 s | 5.0 s | 1 / 0 |
| `WeierstrassCurve/PrincipalDivisorsSeparable.lean` | 181 | 4.3 s | 5.9 s | 2 / 7 |
| `WeierstrassCurve/Isogeny/PointMapSurjective.lean` | 56 | 5.7 s | 6.4 s | 1 / 0 |
| `WeierstrassCurve/Velu/PointMapOddOrder.lean` | 200 | 5.0 s | 4.3 s | 2 / 0 |
| `WeierstrassCurve/Velu/RestrictAlong.lean` (edit) | 2,108 → 2,147 | 54.4 s | 60 s | +2 public wrappers, **+39 / −0** |

The reconciliation was made **purely additive** by reading the file first: each of
the two privates (`Divisor.pushforwardNormFormula_of_finiteDimensional` at 1,749 and
`kw_normFormulaAlong_of_separableAlong_cf` at 1,776) has exactly one caller, both
inside the file, so the pin names could be added as public wrappers with no rename
and no caller edit. The private char-free proofs stay the bodies. The alternative
home (`PrincipalDivisors/Transcendence.lean`) was priced first: **52 modules / ≈405 s**
against **0 library modules / ≈25 s** here.

`spec/WeierstrassCurveConsumer.lean` grew 760 → 926 lines, six new zones; the checker
gained the five modules in `PORT_FILES` (last) and **nine** `Theorems/` wrappers plus
the two headline `S_` files in `SOURCES` (last) — nine, not the order's eight, because
the §5.2 prerequisite table lists seven prerequisites and two headlines.

**Milestone.** Checker `5796 → 5805 identical` (+9: +2 reconciliation, +1
`of_coprime_finrank_expChar`, +1 ratFunc alias, +2 function-field pair, +1 point-map
surjective, +2 headlines), promoted unchanged `311 → 311`, `0 mismatched / 0 missing`.
Whole-tree build green, **9,303 jobs, 12.3 s** (+5 jobs = the five leaves, no
cascade). `spec/WeierstrassCurveConsumer.lean` exit 0 (63 s). `#print axioms` clean on
all four headlines.

**The predicted checker trap bit once, and was fixed.** The first run after wiring
gave 1 mismatched: `hasPrincipalDivisors_functionField_of_two_ne_zero_or` had
inherited the file-level `variable {F} [Field F] {W : Affine F}`, so its declaration
text omitted `{F} [Field F]` and spelled `Affine F`, while the wrapper inlines them and
spells `WeierstrassCurve.Affine F`. Inlining the wrapper's binders verbatim fixed it —
the same rule V1 SET-1 measured on 8 of 13 wrappers.

**The pin's primed helpers are declarations nowhere.** `pushforwardAlongDegZero_pointDivisor'`,
`pushforwardAlongHom_pointClass'` and `pointMapOfPushforward_eq_of_seam'` occur only in
`p2m_export` strings; their content is public in `Velu/RestrictAlong.lean` as the `_cf`
names (lines 1,870 / 1,878 / 1,892), which the set uses directly. Nothing was
redeclared.

**Friction.** `Nat.Prime.eq_two_or_odd'` now returns `Odd p` (the pin's
`⟨k, hk⟩` destructuring needed an `obtain`); `Algebra.IsSeparable.of_integral` needed
an explicit `Algebra.IsIntegral` (synthesized from `Module.Finite` in the pin, so the
port supplies it for provenance and it compiles without); the ported generic transfer
takes `{K}` implicit and `(E)` explicit, so the pin's `F W.FunctionField` became
`(K := F) W.FunctionField`; and the target-4 body carries the pin's five
`dif_pos`/`dif_neg` deprecation warnings verbatim, as the existing `RestrictAlong`
body already does.

**Consumer.** Six new zones in `spec/WeierstrassCurveConsumer.lean`: the char-free HPD
pair in two characteristics, `of_coprime_finrank_expChar` at a concrete coprime pair,
the two separable norm-formula wrappers composed with the restrictAlong headline,
`pointMapOfPushforward_surjective`, and the two odd-order headlines in hypothesis form.

## V2 close-out — the gateways and the Ribet side landed (2026-10-06)

**Manager's review of the wave.** V2 is complete: two sets, one subagent each, run in
series with the manager reviewing the tree between them. Nine new modules and one
additive reconciliation; **no library module with dependents was edited**, so no set
cascaded and the only whole-tree builds were the two milestone gates.

| set | modules | written | est. | checker delta |
|---|---|---:|---:|---:|
| V2-SET-1 | 4 new + 1 new consumer | 1,134 (+178) | 1.2 k | +46 |
| V2-SET-2 | 5 new + 1 additive edit | 537 (+39 edit, +166 consumer) | 0.4 k | +9 |
| **V2** | **9 new modules** | **1,671** (+344 consumer) | **1.6 k** | **5750 → 5805 identical** |

Checker at the milestone: `5805 statements identical (311 promoted from pin-private
declarations), 0 mismatched, 0 missing, 36 own-proof declarations exempted (5841 port
declarations checked)`. Whole-tree build green, **9,303 jobs, 12.3 s** (the pre-V2
baseline was 9,294 / 13.6 s — exactly +9 jobs, the nine leaves). Both consumers exit 0
(71 s and 63 s). `#print axioms` on all eleven V2 headlines returns
`[propext, Classical.choice, Quot.sound]`; no `sorry`. The checker's one-token mutation
probe was run by the manager on `CoordinateRingDedekind.exists_eq_XYIdeal`
(`P ≠ ⊥` → `P ≠ ⊤`): exactly `5804 identical / 1 mismatched / 0 missing`, reverted to
`5805 / 0 / 0`.

**What the wave bought.** The two Mazur gateways
(`exists_pointEnd_eq_of_mem_isogenyEndSubring`, and its number-theoretic consumer
`exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq`) and the Ribet-side
completion of the odd-order Vélu quotient
(`exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples`,
`exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed`), plus the separable
principal-divisors interface at the pin names and the characteristic-free
function-field principal divisors they need.

**What the wave taught** (the generalizable part is folded into
[../porting-playbook.md](../porting-playbook.md), the specifics are in
[../CARRY-FORWARD.md](../CARRY-FORWARD.md) and
[../topics/velu/TOPIC-V2-gateways-and-ribet.md](../topics/velu/TOPIC-V2-gateways-and-ribet.md §9)):

- **`ucl` overstates, and the names it cannot see are the port's own.** Three closure
  members priced at 1,246 / 911 / 58 lines were already in the port under other names,
  and the shared "269-line" pair cost ≈15 lines. A `ucl`-only budget would have said
  ≈4 k where the truth was 1.6 k.
- **Co-import collisions are a class, invisible to every tool.** Two pairs of library
  modules cannot be imported into one environment; they forced a separate consumer
  file for SET-1 and cost its gateway zone a discharged instance.
- **The reconciliation belongs in the file with no dependents**, and the build-ladder
  tool answers that before a line is written (25 s vs 405 s).
- **A definitions file's imports are its source list**, and a name-extraction regex is
  an aid: `scoped instance` and a Greek-letter suffix both defeat it.

**Remaining slice after V2** (unchanged, tracked and out of scope): the `PeriodPair`
uniformization ladder gating `aeval_j_diag_eq_zero_of_finrankAlong_eq`; the
`fullKernelHom` and `reduceHom`/reduction columns; the H6 base-change trio (all of its
consumers are in the slice and reach FLT only through the parked node); and the
far-end modular-polynomial bijection. The three collisions and the second private
char-free norm formula in `PrincipalDivisors/Transcendence.lean` are the refactor
round's work.

## V3 — the translation automorphism of the function field (2026-10-06)

**Result.** One new module and one appended consumer zone; checker
`5805 → 5807 identical` (311 promoted unchanged), `0 mismatched / 0 missing`, 36
own-proof exempted, 5,843 checked; whole-module `lake build` green (9,024 jobs,
160.6 s under `flock`); consumer exit 0; both headlines
`[propext, Classical.choice, Quot.sound]`; no `sorry`. The two sibling headlines of
`TOPIC-V3-translation-place-action.md` §0 are one theorem: the wrappers differ by
one instance and both pin `solution` bodies are the same characteristic-free proof.

Modules: new `WeierstrassCurve/IsogenyEndDatum/TranslationAlgEquiv.lean` (1,123
lines, one import `…IsogenyEndDatum.DualEndData`, 54 `private` + the two public
headlines), `spec/IsogenyEndDatumConsumer.lean` 178 → 253 (zone 5 = 68 lines).

| round | cone | `lake env lean` wall / user / sys |
|---|---|---|
| recon `#check` sweep | `Engine` | 23.7 / 2.6 / 6.7 |
| taylor + ord batch (errors) | `Engine` | 5.2 |
| + `kwTISD*`, ord chain (2 errors) | `Engine` | 36.7 |
| full module after the amendment (24 errors) | `DualEndData` | 115.3 |
| full module, clean | `DualEndData` | **149.0 / 80.2 / 38.0** |
| `lake build`, `flock`ed | `DualEndData` | **160.6 / 90.9 / 48.6** |
| axioms probe | `DualEndData` | 59.4 / 4.6 / 17.5 |
| consumer (manager re-run) | `DualEndData` | **70.4 / 6.2 / 19.8**, exit 0 |

**The route amendment is the wave's finding.** The order first said `import …Engine`
and transcribe the pin's block privately. The dependency closure of the pin's new
chain (L3320–4272) reaches exactly two declarations the port holds only in
`DualEndData` — `ord_ofHeightOneSpectrum_eq_neg_log` and
`ord_placeOfEquation_XClass_self` — and the second drags in `XClass_notMem_XYIdeal_sq`
and its five-lemma support chain. There is no shortcut: the new chain's own
generalization `kw_taseq_ord_ge_of_mem_XYIdeal_pow_charFree` gives only the lower
bound from `XYIdealⁿ` membership. On the `Engine` cone that chain is ~130 lines of
private duplication; on the `DualEndData` cone it is one import, at 1 m 21 s per
check against 23.5 s. The worker had written the duplication by line 319 of 319
when the amendment landed, and deleting it was exact.

**Friction, as it happened.**

1. **`port_advise`'s substitution test is name-anchored** (`by_name` on the last
   name component), so "already in the port" is a **lower bound**. Two declarations
   the order expected to transcribe are ported under other names:
   `mk_mem_XYIdeal_iff_evalEval_eq_zero` ≡ `Place/Dictionary.lean:567`
   `mk_mem_XYIdeal_iff`, and `kw_addSeam_restrictAlong_eq_placeOfEquation_charFree`
   ≡ `IsogenyEndDatum/Engine.lean:979` `es1a6_addSeam_restrictAlong_eq_placeOfEquation`
   (same statement, same proof). A name sweep is an aid; check the statement.
2. **Span estimates overstate a pin `S_` file.** `Point.translateFF_zero` is a
   one-line `rfl` carrying a 101-line span of `p2m_reactivate` lines and empty
   `section … end` stubs (`Pullback`, `MillerGen`, `DivisorWeil`, `TorsionWrapper`).
   Price from declarations, not from spans.
3. **Dropping the pin's empty section skeleton is not free.** The two
   `kw_ord_*_sub_add*_pos` lemmas take `p q : F` from a section head; without the
   skeleton they need an explicit `variable {p q : F}`. Cost: 24 errors and one
   115 s round.
4. **Two pin-local tactics/APIs do not transpose.** `C_simp` is pin-local and was
   inlined as `simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]`;
   `Submodule.pow_mem_pow`'s first explicit argument is the submodule on v4.34.0,
   so `mk_taylorRemainder₂_mem_XYIdeal_sq` uses
   `simpa only [sq] using Ideal.mul_mem_mul hX hX`.
5. **`Place.ramificationIndexAlong` takes an `AlgHom`, not the `AlgEquiv`** — the
   consumer's `.trans` had to pass `τ.toAlgHom`.
6. **A private declaration cannot be exercised by name from `spec/`.** §3.3 of the
   order asked the consumer to "check `Point.translateFF_zero`"; it is `private` per
   §3.2, so the zero case is discharged through the headline at `R = 0` (which is
   `restrictAlong_algHomId`). Deviation from the wording, not the intent.
7. **The pin's `maxHeartbeats 3200000` / `25600000` and
   `synthInstance.maxHeartbeats 1600000` bumps and the unused
   `variable [HasPrincipalDivisors F W.FunctionField]` were all dropped**; the
   global 4,000,000 cap was not touched and nothing blew it.

**Refactor item carried forward.** The second-order `XYIdeal` block
(`derivative_polynomial` … `XClass_notMem_XYIdeal_sq`, `ord_placeOfEquation_XClass_self`)
and `ord_ofHeightOneSpectrum_*` now have two cones that need them and live in the
`DualEndData` hub. Extracting them to `Place/` would let this module drop its 8.1 MB
import. Registered in [../CARRY-FORWARD.md](../CARRY-FORWARD.md).

## V4 — the isogeny kernel controls the range (2026-10-06)

**Result.** The last two nodes of the H5 vocabulary tail landed in one file: checker
`5807 → 5809 identical` (311 promoted unchanged), `0 mismatched / 0 missing`, 36
own-proof exempted, 5,845 checked; wave build green (3 modules, 245 s, the 2-module
cascade re-run at 11 s); consumer exit 0; both headlines
`[propext, Classical.choice, Quot.sound]`; no `sorry`. The chain is
`algHom_ext_of_forall_restrictAlong_placeOfPoint_eq` (function-field rigidity, layer
0) → `IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred` (kernel-to-range,
layer 1); the headline's fixed-points argument runs on V3's translation automorphism.

Modules: `IsogenyEndDatum/Vocabulary.lean` 177 → 643 (the append the plan chose, its
own header having named these nodes as the missing tail, and its pre-existing private
`normFormulaAlong_of_finiteAlong_aux` being the pin's `normFormulaAlong_of_finiteAlong`);
`spec/IsogenyEndDatumConsumer.lean` 253 → 313 (zone 6); `check_flt_statements.py` +7.

| round | `lake env lean` wall |
|---|---|
| scout, 197-line scratch (rigidity core) | 104.7 s (contended) |
| full scratch, 499 lines | 54.4 s |
| edit loop on `Vocabulary.lean` (643 lines) | 56 s → 75 s |
| consumer | 58 s agent / **84.8 s manager** |
| axioms probe | clean |
| wave `flock lake build Vocabulary && CharPolySquare` | 245 s (3 modules) |

**Friction, as it happened.**

1. **The work order's reuse pointer was a statement mismatch, and the §2.3 rule
   caught it.** `finite_setOf_ord_ne_zero_of_finiteDimensional` is public at
   `P1/EnginePrelude.lean:652` and private at `Transcendence.lean:387`, but *both* are
   the minpoly/`RatFunc` statement, not the pin `S_` file's `[HasPrincipalDivisors K F']`
   form. The statement-identical public copy is
   `finite_setOf_ord_ne_zero_of_hasPrincipalDivisors` (`Isogeny/NatCard.lean:73`). The
   order has been amended. This is the V3 lesson paying for itself: a correct-looking
   pointer derived from a *name* lookup is not a reuse decision.
2. **Three more declarations the order listed as new work were already public at the
   same FQN**: `AlgebraicCurve.Place.isUnit_mk_of_ord_eq_zero`,
   `residue_ne_zero_of_ord_eq_zero`, `evalAt_ne_zero_of_ord_eq_zero`, all in
   `Defs/PlaceEvaluationAlgebra.lean`. Plus the pin's `ord_sub_evalAt_pos`
   (`PlaceCalculus.lean:209`), `ord_nonneg_of_mem`/`mem_of_ord_nonneg`
   (`PushPull.lean:43/60`), `restrictAlong_congr` (`Correspondence.lean:318`),
   `restrictAlong_algHomId` (`RestrictAlongAPI.lean:71`),
   `restrictAlong_restrictAlong` (`Transport.lean:76`), `isRational_of_deg_eq_one`
   (`P1/Dictionary.lean:59`), `point_infinite` (`Engine.lean:382`), and the module's
   own `natCard_ker_pointMapOfPushforward_eq_finrankAlong`.
3. **The private-vs-public probe trap.** Both the worker and the manager first
   mutated the *private* `no3ahbad_*` copy of the conclusion `φ₁ = φ₂`; the checker
   correctly reported `0 mismatched` because it never reads `private` declarations.
   The public occurrence gave exactly `5808 / 1 / 0`. Anyone writing a mutation probe
   must target the public declaration.
4. **A pre-existing silent duplicate, not a collision.** `isRational_of_deg_eq_one`
   is public at the same FQN in `AlgebraicCurve/P1/Dictionary.lean:59` and
   `WeierstrassCurve/Velu/Discharge.lean:38`. Unlike the three `instInfinitePlace` /
   `normFormulaAlong_of_elliptic` pairs, the two copies are byte-identical, so Lean
   merges them silently and the co-import succeeds (verified: `exit 0`). Registered in
   `CARRY-FORWARD.md` as a dedup, with the corrected statement of the hazard: a
   same-FQN pair is unimportable **only if the declarations differ**.
5. **The pin's section stubs cost an instance again.** The scoped
   `instHasPrincipalDivisorsFunctionField_s13` went with the skeleton, and
   `no3ahbad_…_finite_ord_ne_zero` supplies `[HasPrincipalDivisors F V.FunctionField]`
   from `hasPrincipalDivisors_functionField V` instead. Same class of friction as V3
   (see above).
6. **One route adaptation.** `no3ahbad_…_ord_pos_of_restrictAlong_ord_pos` calls the
   ported public `Place.ramificationIndexAlong_pos` rather than the pin's inline
   `unfold …; letI …; exact_mod_cast`; the inline form is kept verbatim in the
   headline step.
7. **API drift.** `Set.mem_setOf_eq` is deprecated on v4.34.0 → `Set.mem_ofPred_eq`
   (both files warning-free). `maxHeartbeats` never raised; every build under
   `flock lean/.lake/flt_build.lock`.

**Phase D status.** The H5 vocabulary tail is closed. The one remaining Phase D item
is `IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq`, still gated on the
`PeriodPair` uniformization ladder.

---

## P-1b — the `PeriodPair` lattice/scale prelude dedup (close-out, 2026-10-06)

Work order: [topics/velu/WORKORDER-P1b-lattice-prelude-dedup.md](../topics/velu/WORKORDER-P1b-lattice-prelude-dedup.md).
A consolidation, not new mathematics: `0 mismatched / 0 missing` before and after.

**What landed.** The lattice/scale/discriminant prelude had three implementations:
public in `Elliptic/PeriodPair/Discriminant.lean`, public at the root namespace in
`ModularForms/WeightOne/Defs/PeriodPair.lean`, and a 53-line `private` block plus a
private `periodPairOfTau` in `ModularForms/WeightOne/FrickeFunction.lean`. It now has
one home, `FLTForHuman/Elliptic/PeriodPair/Lattice.lean` (260 lines, namespace
`PeriodPair`, imports only `Basic.lean`, 30 public + 9 `private` declarations).
`Discriminant.lean` (326 → 248 lines) imports `Lattice` and keeps the
discriminant-specific tail; `Defs/PeriodPair.lean` (98 → 23 lines) re-exports the
root-level names; `FrickeFunction.lean` (2926 → 2869 lines) drops the private block
(196–248) and the private `periodPairOfTau` (967).

**One proof per fact.** The scale law is proved once for `L.scale α`; the pin's
`smul` spelling is *defined* as `smulPeriodPair a ha L := L.scale (Units.mk0 a ha)`,
so `G_smulPeriodPair` follows from `G_scale` by
`simpa only [smulPeriodPair, Units.val_mk0, inv_pow]`, `latticeDisc_smulPeriodPair`
from `discriminant_scale`, and `g₂_smulPeriodPair`/`g₃_smulPeriodPair` from
`G_smulPeriodPair`. `smulLatticeEquiv` derives from `scaleLatticeEquiv`
(`(L.scaleLatticeEquiv (Units.mk0 a ha)).toEquiv`), `mem_smulPeriodPair_lattice` is
the pin's `mem_lattice` proof, and `G_of_lattice_eq`/`g₂_of_lattice_eq`/
`g₃_of_lattice_eq` are one-line restatements of `G_eq_of_lattice_eq`/
`g₂_eq_of_lattice_eq`/`g₃_eq_of_lattice_eq`. Only `weierstrassP_smulPeriodPair`
and `weierstrassP_of_lattice_eq` keep a genuine proof.

**Declarations deleted, with survivors** (`grep -c` over the port before the cut;
"pin copies" counts the pin's public + private duplicates).

| deleted copy | was | survivor | pin copies |
|---|---|---|---|
| `latticeEquivOfEq` | `private` Fricke 196; `private` Discriminant 230 | `PeriodPair.latticeEquivOfEq` (`private`, home) | 2 |
| `latticeEquivOfEq_coe` | `private` Fricke 203 | `PeriodPair.latticeEquivOfEq_coe` (`private`, home) | 2 |
| `weierstrassP_of_lattice_eq` | `private` Fricke 206 | `PeriodPair.weierstrassP_of_lattice_eq` (public, home) | 1 |
| `G_of_lattice_eq` | `private` Fricke 212 | `PeriodPair.G_of_lattice_eq` (public, home) | 1 |
| `G_smulPeriodPair` | `private` Fricke 218 | `PeriodPair.G_smulPeriodPair` (public, home) | 1 |
| `g₂_smulPeriodPair` | `private` Fricke 226 | `PeriodPair.g₂_smulPeriodPair` (public, home) | 1 |
| `g₃_smulPeriodPair` | `private` Fricke 230 | `PeriodPair.g₃_smulPeriodPair` (public, home) | 1 |
| `latticeDisc` | `private` Fricke 234 | `PeriodPair.latticeDisc` (public, home) | 1 |
| `latticeDisc_smulPeriodPair` | `private` Fricke 236 | `PeriodPair.latticeDisc_smulPeriodPair` (public, home) | 1 |
| `g₂_of_lattice_eq` | `private` Fricke 240 | `PeriodPair.g₂_of_lattice_eq` (public, home) | 1 |
| `g₃_of_lattice_eq` | `private` Fricke 243 | `PeriodPair.g₃_of_lattice_eq` (public, home) | 1 |
| `latticeDisc_of_lattice_eq` | `private` Fricke 246 | `PeriodPair.latticeDisc_of_lattice_eq` (public, home) | 1 |
| `periodPairOfTau` | `private` Fricke 967 | `PeriodPair.periodPairOfTau` = `ofTau`; root re-export | 5 |
| `periodPairOfTau_ω₁`/`_ω₂` | `private`? no — root `Defs` | `PeriodPair.periodPairOfTau_ω₁`/`_ω₂` | 5 |
| `scale_lattice`, `scaleLatticeEquiv`, `scaleLatticeEquiv_apply`, `G_scale`, `g₂_scale`, `g₃_scale`, `discriminant_scale`, `mulLeftR`/`mulLeftZ` block | `Discriminant` | `PeriodPair.*` (home) | 1 |
| `G_eq_of_lattice_eq`, `g₂_eq_of_lattice_eq`, `g₃_eq_of_lattice_eq` | `Discriminant` | `PeriodPair.*` (home) | 1 |
| `periodPairOfTau`, `smulPeriodPair`, `smulPeriodPair_ω₁`/`_ω₂`, `mem_smulPeriodPair_lattice`, `smulLatticeEquiv`, `smulLatticeEquiv_coe`, `weierstrassP_smulPeriodPair`, `periodPair_eq_of_ω` | root `Defs` | root re-export of `PeriodPair.*` (home) | 5 |

`latticeEquivOfEq` and `latticeEquivOfEq_coe` stay `private` in the home (internal
helpers); everything else the pin declares public is public there.
`periodPair_eq_of_ω`'s pin copies are the private ones in
`S_ModularForm_weierstrassP_torsion_qExpansion_package.lean:172` and
`S_WLight_levelN_structure_package.lean:1106`; the home's public copy matches
through the checker's dotted fallback (`promoted`).

**Checker delta reconciled.** Baseline P-SET-1: `5853 identical (313 promoted, 4
renamed), 0 mismatched, 0 missing, 36 own, 5889 checked`. After:
`5864 identical (313 promoted, 4 renamed), 0 mismatched, 0 missing, 36 own, 5900
checked`. Delta **+11 identical / +11 checked**, no mismatch, no missing, no drop
in promoted. The 11 are exactly the newly-public promotions out of the
`FrickeFunction` private block — `weierstrassP_of_lattice_eq`, `G_of_lattice_eq`,
`G_smulPeriodPair`, `g₂_smulPeriodPair`, `g₃_smulPeriodPair`, `latticeDisc`,
`latticeDisc_smulPeriodPair`, `g₂_of_lattice_eq`, `g₃_of_lattice_eq`,
`latticeDisc_of_lattice_eq` — plus `discriminant_scale` (private in the port,
public in the pin). The move of 8 names from `Discriminant.lean` to `Lattice.lean`
and of 11 root names from `Defs/PeriodPair.lean` (now `export`) to `Lattice.lean`
nets to zero, because the same statements are still counted once each. There is
no public deletion, so no expected `−1`. The 4 `RENAMED` rows are unchanged.

**Consumers and axioms.** `spec/PeriodPairConsumer.lean` exit 0 (4.1 s);
`spec/WeightOneConsumer.lean` exit 0 (6.1 s). `#print axioms` on
`PeriodPair.discriminant_ne_zero` and `PeriodPair.isUniformization_toPoint`:
`[propext, Classical.choice, Quot.sound]` — unchanged.

**Build jobs and cascade.** Wave whole-tree `flock .lake/flt_build.lock lake build`:
**9308 jobs, green, 5 m 00.5 s wall** (14 m 11 s user, 1 m 17 s sys). Cached
milestone re-run: **9308 jobs, green, 7.4 s**. Cascade (import closure measured on
the port): `Defs/PeriodPair.lean` — 13 direct importers, **34 transitive
dependents / 28,531 lines**; `FrickeFunction.lean` — 8 direct importers,
**27 transitive dependents / 21,730 lines**; union **34 modules / 28,531 lines`.
The wave build re-elaborated that union (plus the two edited files themselves)
before the cached re-run.

**Friction / deliberate deviations.**

1. **`Defs/PeriodPair.lean` is an `export` shim, not literal `def` aliases.** The
   work order's first shape — keep root-level `def`/`lemma` aliases beside a home
   that also declares the same last names in `namespace PeriodPair` — makes every
   unqualified use ambiguous in any file that `open PeriodPair`s (Lean reports
   `Ambiguous term`, verified against both root and `PeriodPair.smulPeriodPair`).
   `export PeriodPair (…)` creates root names that *are* the home's constants, so
   there is no second declaration, no ambiguity, and the importers are untouched.
   The checker now finds the declarations in `Lattice.lean` (in `PORT_FILES`)
   rather than in `Defs/PeriodPair.lean`; the count is unchanged.
2. **`discriminant_scale` is public in the home** (it was `private` in
   `Discriminant.lean`, public in the pin). `discriminantNeZero_scale_iff` stays in
   `Discriminant.lean` (§4.2) and consumes it across the new module boundary, so it
   cannot be `private`. This is the forced part of the +11.
3. **`latticeEquivOfEq`/`latticeEquivOfEq_coe` stay private** even though the pin's
   `WLight` copy is public: they are internal helpers, so the home's public surface
   is the union of the *ported* public names, not the pin's. Recorded so the
   `promoted` count is not read as a loss.
4. **The pin's `smulPeriodPair` binder shape is definitional, not a bridge.**
   `smulPeriodPair a ha L := L.scale (Units.mk0 a ha)`; `units`' anonymous
   `⟨a, ha⟩` constructor does not elaborate for `ℂˣ` (needs `Units.mk0`), contrary
   to the work order's illustrative alias. No `periodPair_eq_of_ω` bridge is needed;
   the lemma is carried as the pin's public name.
5. **Stale `.olean` trap confirmed.** After the promotion, `lake env lean` on
   `FrickeFunction.lean` reported `Unknown constant periodPairOfTau` and three
   `rfl` failures against the *stale* `Defs/PTorsion`/`Fricke` oleans; rebuilding
   those dependencies made every error vanish and the file check clean in 30 s. The
   defeq itself was verified independently (`with_unfolding_all rfl` between the
   old explicit-field `periodPairOfTau` and `ofTau`).
6. **`FrickeFunction.lean` needed no use-site rewrite.** The promoted names resolve
   through the section's existing `open PeriodPair`, and the root `smulPeriodPair`
   is the home's constant (via `export`), so the `frickePrefactor_smulPeriodPair`
   `simp only` set is unchanged. The block and the private `periodPairOfTau` are the
   only deletions.
7. **`latticeDisc` keeps the pin's inline `g₂ ^ 3 - 27 * g₃ ^ 2` body** (the
   checker diff is textual); its equality with the dictionary's
   `weierstrassCurve_Δ` is stated once, privately, as
   `latticeDisc_eq_weierstrassCurve_Δ`. `weierstrassP_of_lattice_eq`, which has no
   `scale`-spelled counterpart, is promoted to the home (public) rather than left
   private in `FrickeFunction.lean`.

## P-SET-2 — the `PeriodPair` `j`-line (close-out, 2026-10-06)

**Scope.** The subject's second row: `PeriodPair.jLattice_ofTau`
(`(ofTau τ).jLattice = E₄ τ ^ 3 / Δ τ`) and `PeriodPair.jLattice_surjective`
(`PeriodPair.JSurjective`: every complex number is the `j`-invariant of a lattice).
Pin `anthropics/fermats-last-theorem@aa2d8b3`; mathlib `v4.34.0`. Two new modules and
one promotion:

```
ModularForms/JInvariant.lean            NEW — the neutral home of `ModularForm.j` /
                                        `ModularForm.j_surjective` (40 lines)
  └─ Elliptic/PeriodPair/JLine.lean     NEW — the two headlines + the `kw_`-stripped
                                        `jLattice_ofTau_eq` (90 lines); imports
                                        `JInvariant` upward (leaf: diamond, not cycle)
ModularForms/WeightOne/LevelField.lean  EDITED — `WLight.j` / `WLight.j_surjective`
                                        become one-line shims over `ModularForm.*`
```

**The scout's finding, and why this is 130 lines and not 1,264.** The pin's
`S_PeriodPair_jLattice_surjective.lean` (1,054 lines) proves `j`-surjectivity itself,
by the `E₄³ − c·Δ` pencil argument: `kwQepw115c_jH_surjective` and the
`kwQepw123c_*` / `kwQepw124b_*` / `kwQepw129c_*` / `kwQepw116c_*` / `kwQepw117c_*` /
`kwQepw119c_*` / `kwQepw121c_*` scaffolding (≈45 declarations). **All of it is already
in the port**: the third conjunct of the landed `WLight.levelOne_hauptmodul_package` is
exactly `Function.Surjective (fun τ : ℍ => E₄ τ ^ 3 / Δ τ)`, and `LevelField.lean` named
it `WLight.j_surjective`. The pin's `S_PeriodPair_jLattice_ofTau.lean` (210 lines) is
`kw_jLattice_ofTau_eq` plus the already-ported `kw_g₂_ofTau` / `kw_g₃_ofTau` /
`kw_discriminant_ofTau_eq`. `port_advise`/`port_plan` priced the pair at 796 net-new
lines; the actual port is 130 written lines, the pin's proof body replaced by three
short derivations. The pin's `kw_E4cube*` q-expansion block is mathlib's
`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`.

**Promotion out of `WLight`.** `j` / `j_surjective` are generic level-one facts, not
weight-one-package API, so they moved to the neutral `ModularForm` namespace in the new
`ModularForms/JInvariant.lean`; `LevelField.lean` keeps the pin names as shims
(`def j : ℍ → ℂ := ModularForm.j`, `theorem j_surjective := ModularForm.j_surjective`),
so `LevelN.lean` and the ~20 in-file uses are untouched. This inverts the P-1b
directory direction on purpose: `JLine.lean` (a leaf in `Elliptic/PeriodPair/`) imports
the neutral modular-forms module, which imports `WeightOne`; nothing imports `JLine`,
so the graph is a diamond, not a cycle, and the pin's `PeriodPair.*` statements stay in
their directory.

**Measured table.**

| | pin raw | port |
|---|---:|---:|
| `S_PeriodPair_jLattice_ofTau.lean` | 210 | `JLine.lean` (90) — both headlines + `jLattice_ofTau_eq` |
| `S_PeriodPair_jLattice_surjective.lean` | 1,054 | reused wholesale from `levelOne_hauptmodul_package`; not re-proved |
| neutral `j` / `j_surjective` | — | `JInvariant.lean` (40) |
| `WLight.j` / `WLight.j_surjective` | 2 decls | shims in `LevelField.lean` |

Public declarations landed (all `private` otherwise, `ofTau_discriminant_eq`):
`ModularForm.j`, `ModularForm.j_surjective`, `PeriodPair.jLattice_ofTau_eq`,
`PeriodPair.jLattice_ofTau`, `PeriodPair.jLattice_surjective`.

**Checker wiring.** Four `SOURCES` entries for the j-line (wrappers before `S_` files:
`Thm_PeriodPair_jLattice_ofTau`, `S_PeriodPair_jLattice_ofTau`,
`Thm_PeriodPair_jLattice_surjective`, `S_PeriodPair_jLattice_surjective`) and two
`PORT_FILES` (`ModularForms/JInvariant.lean`, `Elliptic/PeriodPair/JLine.lean`),
appended last. Baseline P-1b: `5864 identical (313 promoted, 4 renamed), 0 mismatched,
0 missing, 36 own, 5900 checked` → **`5869 identical (313 promoted, 5 renamed), 0
mismatched, 0 missing, 36 own, 5905 checked`**. The **+5** is exactly the five new
public declarations; the new `RENAMED` row is
`PeriodPair.jLattice_ofTau_eq → P2MW.S_PeriodPair_jLattice_ofTau.PeriodPair.kw_jLattice_ofTau_eq`,
the first promotion at the no-`kw` stripped name (the checker already followed the new
convention).

**Consumer and axioms.** `spec/PeriodPairConsumer.lean` gains zone 4:
`jLattice_ofTau` at `(I, 1)` feeding `ModularForm.j`, the `jLattice_ofTau_eq` spelling,
`jLattice_surjective 0`, and `ModularForm.j_surjective 1728`; exit 0 (4.0 s).
`#print axioms` on `PeriodPair.jLattice_ofTau` and `PeriodPair.jLattice_surjective`:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

**Builds.** Wave whole-tree `flock .lake/flt_build.lock lake build` **9310 jobs, green,
4 m 37.7 s wall** (13 m 58 s user, 1 m 17 s sys); cached milestone **9310 jobs, 9.3 s**.
The +2 jobs over P-1b's 9308 are the two new modules; the cascade is `LevelField.lean` →
`LevelN` and its dependents (the two shims' statements are unchanged, so the checker
verdict on them did not move).

**Friction / deviations.**

1. **The checker's statement diff is textual, not elaborated.** Three declarations had
   to be re-spelled to the *source the checker should match*: the headlines must use the
   wrapper's `PeriodPair.ofTau` / `PeriodPair.JSurjective` qualification (the `norm`
   pass strips only `ModularCurve.` / `AlgebraicCurve.`), while the stripped promotion
   `jLattice_ofTau_eq` must mirror the `S_` file's unqualified `ofTau` / `E₄` / `E₆`.
   The first draft mixed them and produced 3 mismatches / 1 missing.
2. **A `def` alias must keep the pin's binder shape.** The generic `j` first went in as
   `def j (τ : ℍ) : ℂ`, which the checker read as `(τ : ℍ) : ℂ` against the pin's
   `def j : ℍ → ℂ`; the port now writes the pin's `def j : ℍ → ℂ := fun τ => …`.
3. **`def` vs `abbrev` matters at a promotion.** The shim could not be an `abbrev`
   (`WLight.j`'s pin kind is `def`), so `LevelField.lean` keeps a real `def`; the one
   `simp only [j]` site became `simp only [j, ModularForm.j]` to see through it.
4. **The `PeriodPair` ladder is on the D-S capstone cone.** `frontier.py --target
   DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` lists 14 unported
   `PeriodPair.*` nodes / 9,071 lines, `jLattice_surjective` among them (reached through
   `eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward` →
   `exists_variableChange_smul_weierstrassCurve_eq`), correcting the CARRY-FORWARD
   reading that the 54-target D-S slice had no `PeriodPair` node.

## P-2 — the base-change / descent column (D-1…D-5 landed, 2026-10-06)

The D row of the `PeriodPair` ladder, in
[../topics/velu/WORKORDER-P2-basechange.md](../topics/velu/WORKORDER-P2-basechange.md).
Six nodes, all premised from the start and mutually independent of the S row. Whole-row
dedup: 17,280 raw lines / 696 declarations across the six `S_` files → 350 distinct
declarations, 95 already public in the port (3,220 lines), 15 promotable (121), **240 new
(5,470)**. The two `…isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom` /
`…exists_algHom_baseChange_…` files are 5,357 / 5,338 lines and share **163 of their 176
declarations (4,926 removable lines)** — the reason the column was scheduled around them.

| set | module | lines | public/private | checker |
|---|---|---:|---|---|
| D-1 | `WeierstrassCurve/Isogeny/BaseChange.lean` | 1,151 | 73 / 5 | +73 → 5942 |
| D-2 | `WeierstrassCurve/Isogeny/IntermediateField.lean` | 1,124 | 9 / 72 | +9 → 5951 |
| D-3a | `WeierstrassCurve/Isogeny/BaseChangeAlgHom.lean` | 67 | 1 / 0 | +1 |
| D-3b | `WeierstrassCurve/Isogeny/VariableChangeAlgEquiv.lean` | 315 | 24–28 / 0 | +28 → 5980 |
| D-4 | `WeierstrassCurve/Isogeny/KernelCyclicTransfer.lean` | 472 | 19 / 0 | +19 → 5999 |
| D-5 | `WeierstrassCurve/Isogeny/KernelBaseChange.lean` | 1,377 | 34 / 0 | +32 → 6037 |

**D-1 (the shared prelude).** New file, no headline: the `pointPullback` column, the
`TreeIsogenyEndDatum` datum and its `degree`, the function-field tensor base change in both
`General` and `NoAC` spellings, and the `IsogenyEndDatum` base-change block, written once so
D-2…D-5 import instead of each re-proving 2,393 shared lines. D-1's own slice: 2,740 raw pin
lines across three files → 1,569 once ⇒ **1,171 duplicate lines eliminated**. Already
public and imported, not re-proved: `yGen`, `polyToFunctionField_eq_aeval`,
`equation_map_polyToFunctionField_yGen`, `transcendental_polyToFunctionField_X`,
`algebraMap_polynomial_eq_mk_C`, `CoordinateRing.algebraMap_eq_mk_C_C`,
`ofHeightOneSpectrum_injective` (the last dropped despite a binder-spelling difference,
because the port's copy is the pin's `Definitions/` copy, already in `SOURCES`).

**D-2 (the countable descent).** `exists_intermediateField_countable_map_eq_and_finrankAlong_eq`
plus its descent block; 72 of its 81 declarations are `private` at content names, so the
port surface is the headline and the eight pin-public `KwIsogenyEndDatum*` predicates.
The work order's "93 node-unique / 1,878 pin lines" counted the whole pin region; the
measured slice is 795 transcribed pin lines with **1,061 imported** (39 declarations / 895
lines from D-1, 6 / 166 from earlier homes) — the duplicate lines eliminated. Dropped with a
`grep -c`: `Countable.of_module_finite` → mathlib `Countable.of_moduleFinite` (2/2), and the
pin's anonymous `Countable K` instance (mathlib has none; `Countable ℚ` comes from
`Rat.Encodable`).

**D-3 (base change to ℂ and the variable-change equiv).** Two modules. `port_plan` priced
the pair at 555 net-new before the set; D-1 having landed the `bcff` prelude, the written
total is **382 raw / 309 code lines**. 1,599 pin lines over 60 declarations were dropped as
already present (985 → `BaseChange.lean`, 475 → `FunctionFieldQuadratic.lean`, 139 →
`Place/Dictionary.lean`), every survivor confirmed by `grep -c` ≥ 1. D-3b's 27 public
`mrtw60a*` declarations keep their pin names: the prefix is a solution-file token, not a
`kw_` promotion token.

**D-4 (the conjugation headline and its seam).** `Isogeny/KernelCyclicTransfer.lean`, new:
472 lines written (`wc -l`; 407 non-blank, 328 code), **19 public declarations and no `private`
helpers**. The headline `isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj` (the
conjugation invariance of the isogeny kernel, at the wrapper statement), the
`ModularCurve.KwD5BetweenCurvesPMOPConjKerEquiv` `Prop`, the `kw_fdn2_qephod_hend21_*`
conjugation block, the `kw_surgehgf4_pck_*` engine (12 theorems + the `axiomAnchor`) and the
pin's `pck_s17` alias. Every name is a pin-**public** transcription (the `kw_` prefix is a
solution-file token here, not a promotion), so the checker counts them all `identical`, not
`renamed`: `5980 (313 promoted, 61 renamed) → 5999`, `0/0` both sides, `6016 → 6035` checked
— exactly +19, reconciling to the module's whole surface.

`port_advise` scores 64 of the node's 117 declarations as substitutions (≈828 lines); the
measured pre-D-4 split is **50 of the 116 declarations (632 pin lines) with an
identical-statement port copy** — imported, not re-proved — and 46 whose pin copies are
binder-spelling variants of ported declarations (`finiteAlong_comp` lives as
`AlgebraicCurve.finiteAlong_comp` in `WeilExchange/Transport.lean:254` and is called with
its two explicit map arguments; `pushforwardAlong_pushforwardAlong`,
`restrictAlong_restrictAlong`, `inertiaDegAlong_comp`, `mem_restrictAlong_iff`, the
`Place` calculus, the `PeriodPair`/`Uniformization` prelude and the `InfinitePlace` block
are D-1/P-SET material). D-4's own slice is **19 declarations / 382 pin lines**; the
duplicate lines eliminated are the other 632 (plus the 20 declarations the pin file shares
with D-5's silos that the advise's `port once` section lists, which stay with D-5).

Drops, each with a survivor and a `grep -c`:

| dropped pin declaration | survivor | why |
|---|---|---|
| `kw_fdn2_qephod_hend7_pmopKerCard_proved` (the `Nat.card … = finrankAlong K ι` form, `conj:600`) | `Isogeny/NatCard.lean:785` owns the *name* (a different statement, `: KwD5PointMapOfPushforwardKerCard.{u}`); the port's `IsogenyEndDatum/Vocabulary.lean:161` `natCard_ker_pointMapOfPushforward_eq_finrankAlong` is the identical statement | the name is one environment-level key and `NatCard.lean` is in every D module's cone, so the second copy is undeclarable (`grep -c` in the port: 1, the `NatCard` one) |
| `KwD5BetweenCurvesHoloLift` (`conj:969`) | D-5's home; the port has no `PeriodPair.kw_toPointHom` (`grep -c` = 0) | see `CARRY-FORWARD.md` |
| the 32 other `PeriodPair`/`InfinitePlace`/`Place`/`Divisor` prelude copies | D-1 and P-SET-1/P-SET-2 homes | identical statements or binder-spelling variants; `grep -c` ≥ 1 for every survivor |

**D-5 (the two `IsAddCyclic` kernel silos, one home).** `Isogeny/KernelBaseChange.lean`,
new, 1,377 lines (1,340 Lean + 37 header), **34 public / 0 private** (32 checker-visible; the
parser does not read `scoped instance`). Both headlines at the wrappers' binders, keeping the
asymmetry: `isAddCyclic_…` quantifies `(R₀ : Type u)` and concludes a conjunction,
`exists_algHom_baseChange_…` quantifies `(R₀ : Type)` and concludes
`∃ ι₁ …, ∀ hN₁, …`. This is the set the column was scheduled around: the two pin files are
**10,695 raw lines / 176+176 declarations and share 163 of their 176 declarations (≈4,926
removable lines)**; `port_advise` scores 238 declarations (≈7,252 lines) as substitutions and
names the 163 shared by both. The module is the "once" side of that. The work order's "~2,300
once lines" was an over-estimate: the module is 1,377, and ~950 of the difference is pin
*prelude* copies that D-5's own content does not use and that the port already owns
(`mem_scale_lattice_iff`, `jLattice_scale`, `jLattice_eq_of_lattice_eq`, `gate_scale_mul`, the
`kw_isUniformization`/`kw_toPoint_*` chain, `deg_eq_one`, `evalAt_div`, …) — importing them is
the dedup, not a gap.

**Step 1 (§1.5, the prerequisite set).** Six declarations promoted publicly at stripped names
into `Elliptic/PeriodPair/Uniformization.lean` (+50 lines), all verified `RENAMED`:
`PeriodPair.{toPointHom, toPointHom_apply, ker_toPointHom, toPointAddEquiv,
toPointAddEquiv_mk}` plus **`discriminantNeZero`** — one more than the plan's five-name table,
because `toPointHom_apply`'s statement mentions `L.kw_discriminantNeZero`. The pin declares
the family `private … p2m_export`, so all six are promotions. `toPointAddEquiv` is P-SET-1's
`isUniformization_toPoint` repackaged. `apply_eq_apply_of_continuous_of_mapsTo_lattice` was
**not** promoted: D-5 does not use it (its consumer is the S row's
`exists_smul_mem_and_apply_eq_of_forall_sub_mem`). Hard rule honoured:
`ModularCurve.kw_fdn2_qephod_hend7_pmopKerCard_proved` is **not** declared in either form; both
pin call sites use the imported `natCard_ker_pointMapOfPushforward_eq_finrankAlong`.

Drops, top of the table (full list in `tmp/d5/drops.txt`; `grep -c` over the two pin files):

| dropped pin declaration | survivor |
|---|---|
| `kw_functionFieldMapAlongGeneral` ×100, `…HomGeneral` ×44, `pointPullbackHomTo` ×38, `…TensorFracEquivGeneral` ×18, `…TensorIsDomain_dischargeGeneral` ×16, `…algHom_ext` ×14, `…NoAC` ×26 | `Isogeny/BaseChange.lean` (D-1) |
| `placeOfPoint_some` ×72, `placeOfPoint_zero` ×66, `normFormulaAlong_of_elliptic` ×42, `restrictAlong_eq_infinitePlace` ×4, `pointEnd_eq_pointEnd'` ×2 | `IsogenyEndDatum/Engine.lean` |
| `kw_fdn2_qephod_hend7_pmopKerCard_proved` ×10 | `IsogenyEndDatum/Vocabulary.lean:161` (imported lemma; the *name* stays with `NatCard.lean`) |
| `geomMorphBC` ×8, `placeOfPoint_geomMorphBC` ×10, `pmop_eq_geomMorphBC_sub` ×6, `placeOfPoint_injective` ×2 | `Isogeny/NatCard.lean` |
| the place dictionary (`isFinitePlace_placeOfEquation` ×22, `heightOneSpectrumOfEquation` ×18, `ord_placeOfEquation_pos_iff` ×12, `centre_placeOfEquation` ×10, `algebraMap_polynomial_eq_mk_C` ×8, `isFinitePlace_of_mem` ×6, `exists_sub_algebraMap_mem` ×4) | `Place/Dictionary.lean` |
| `transcendental_polyToFunctionField_X` ×16, `equation_map_polyToFunctionField_yGen` ×16, `yGen` ×2 | `FunctionFieldQuadratic.lean` |
| `XClass` ×55, `YClass` ×58 | mathlib `CoordinateRing.XClass`/`YClass` |
| the `PeriodPair` prelude (`scaleLatticeEquiv` ×12, `kw_isUniformization` ×8, `kw_countable_lattice` ×6, `sub_fract_mem_lattice` ×6, `apply_eq_apply_of_differentiable_of_forall_periodic` ×6, `toPoint_add`/`_surjective`/`_eq_zero_iff`/`_add_mem`/`_neg`, `latticeEquivOfEq` ×4, `discriminantNeZero_scale_iff` ×2, `exists_smul_mem_and_apply_eq_of_forall_sub_mem` ×2) | `Elliptic/PeriodPair/{Uniformization,Lattice,Discriminant}.lean` |

### The `instInfinitePlace` co-import collision, and its resolution

`WeierstrassCurve.Affine.instInfinitePlace` was declared twice: `Place/RRSpace.lean` (the
pin's own `scoped instance`, `[IsAlgClosed F] [IsDedekindDomain W.CoordinateRing]
[HasPrincipalDivisors …]`) and `IsogenyEndDatum/Engine.lean` (a plain `instance`, the port's
invention, `[W.IsElliptic] [GenusOnePlaceGate W] [IsCentred W]`). No environment can import
both (`environment already contains '…instInfinitePlace._proof_4'`), which blocked the whole
column: D-1 and D-2 need the gate *classes*, D-4/D-5 need `Engine`'s seam lemmas. Resolution
was not a rename but an import choice: `GenusOnePlaceGateCentred.lean` is the *producer*
(`exists_genusOnePlaceGate_isCentred_and_abelTheorem`) and the only importer of `RRSpace` in
that chain, while the classes live in the lighter `GenusOnePlaceGate.lean`, which every pin
hypothesis supplies as an argument. D-1 now imports `GenusOnePlaceGate.lean`; the Engine
pairing compiles, and D-4/D-5 are unblocked. The producer module still cannot be co-imported
with `Engine`, which is why `spec/IsogenyEndDatumConsumer.lean` keeps those gate instances as
hypotheses.

### The `kw_` strip, and the checker's in-statement erasure

The promotion policy is to name a promoted helper at the prefix-stripped pin name, verified
through the checker's `stripped_source` fallback and counted in `renamed`; the criterion is
*promotion*, not the pin's `private` marker (all five original `renamed` sources are
pin-public). D-1's 56 pin-public `kw_` helpers and its 4 `scoped instance`s were stripped in
place. That needed one checker change: `norm` now erases `kw_` **inside statements** on both
sides, as it already erased `ModularCurve.`/`AlgebraicCurve.` qualification. Twenty of the 56
have statements that mention a promoted map —
`functionFieldMapAlongGeneralNoAC_polyToFunctionField_X` states
`functionFieldMapAlongGeneralNoAC W F F' (polyToFunctionField (W⁄F) X) = polyToFunctionField (W⁄F') X`
— so renaming the map moved the statement text and the diff failed (measured: 20 `missing`).
With the erasure the strip moved exactly the 56 and nothing else: `5942 identical (313
promoted, 5 → 61 renamed), 0/0`. A one-token probe still fires (5942 → 5941), surfacing as
`missing` rather than `mismatched` for a promoted declaration — read both.

**D-5's completion of the erasure.** The lookbehind still excluded a preceding `.` at first,
which made a *method-style* reference to a promoted helper unmatchable: the pin's
`private theorem PeriodPair.kw_toPointHom_apply` states
`L.kw_toPointHom z = L.toPoint L.kw_discriminantNeZero z`, while the port's promotion states
`L.toPointHom z = …`, and the diff reported 5 `missing`. Dropping `.` from the lookbehind
(`spec/check_flt_statements.py`, `(?<![\w'ₐ-ₜ])kw_`) fixed it: `6000 (313, 62) / 5 missing`
became `6005 (313, 67) / 0 missing`, and no pre-existing row moved. The change is monotone —
both sides are normalised identically, and `find` only ever returns a candidate whose kind
and statement already match — so it can turn a mismatch into a match but never the reverse.
Without it, "stripped names + 0 missing" is impossible for any promotion whose statement is
method-style.

### D-1's universe defect (found by D-3)

D-1 had monomorphised the prelude's universes (`universe u`; `F : Type u`, `F' : Type u`),
where the pin's `bcff` file is `universe u v w` with `R₀ : Type u`, `F : Type v`,
`F' : Type w` (`:76`, `:696–699`) and the wrapper spells `(F : Type v)`/`(F' : Type w)`; a
second section, `section PointPullbackTo`, pinned `{L : Type u}` where the pin writes
`{L : Type*}` (`:404`). At `v ≠ w` the pinned `L` made the unifier chase a `whnf` loop and
two `def`s — exactly the ones the pin guards with `set_option maxHeartbeats 51200000 in` —
died at the port's 4 M cap (a 497 s failed build). Fixed by carrying the pin's spelling
(`universe u v w`, `F : Type v`, `F' : Type w`, `{L : Type*}`) and naming the implicits at
the application sites in the two bodies, which removes the search so no budget bump is
needed. Section-variable universes never enter the checker's statement diff, so the
mechanical check is blind to this class of defect; only the consumer's elaboration catches
it. Lesson recorded in P-2 §6: **a `whnf` heartbeat timeout in a shared block usually means
a universe was pinned too tight, not that the proof is heavy.**

### Twice the same pin name, twice a *different* statement (found by D-4)

The seam vocabulary of the pin is not stable across the five `S_` files that carry it, and
two of the collisions are genuine statement differences, not copies:

1. **`KwD5BetweenCurvesHoloLift`.** The work order's "different bodies (748 lines in the
   silos, 151/83 in the S row, 25 in `conj`)" is a *span* artefact. The `def … : Prop`
   bodies in all five files are **byte-identical** — `sha256` of the extracted
   `def KwD5BetweenCurvesHoloLift …` text is `e7b7d5fe7857b0a5…` in
   `S_PeriodPair_exists_differentiable_toPoint_…`, `S_PeriodPair_exists_scale_lattice_…`,
   `S_…exists_algHom_baseChange_…`, `S_…of_algEquiv_conj` and `S_…of_baseChange_algHom`. The
   differing line counts are the surrounding `p2m_reactivate` scaffolding. So there is no
   "general vs specialisation" question to settle; D-4 nevertheless does **not** declare it,
   because its body needs `PeriodPair.kw_toPointHom`, which the port does not have in any
   form (`grep -c` = 0), and because declaring it here would collide with D-5's own copy in
   the same `ModularCurve` namespace. Registered in `CARRY-FORWARD.md`.
2. **`ModularCurve.kw_fdn2_qephod_hend7_pmopKerCard_proved`.** Two pin files declare *this*
   name with different statements: the `natCard_…_eq_finrankAlong` file has
   `theorem … : KwD5PointMapOfPushforwardKerCard.{u}`, while the two D-5 silos, the two S-row
   files and the `conj` file each have
   `theorem … (K : Type*) … : Nat.card (pointMapOfPushforward ι …).ker = finrankAlong K ι`.
   The port kept the `Prop`-valued copy (`Isogeny/NatCard.lean:785`, which landed with the
   `natCard` node), and since a declaration name is one environment-level key, the second
   copy is **undeclarable** in any module whose cone contains `NatCard.lean` — i.e. the whole
   D column. Nothing is lost: the second copy's *content* is the already-ported
   `WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong`
   (`IsogenyEndDatum/Vocabulary.lean:161`), which is exactly its proof term. D-4 drops it and
   uses the imported lemma; the silos should do the same.

Lesson for the column: **a pin name shared across `S_` files is not evidence of a shared
statement.** Diff the *normalized declaration bodies*, not the spans, before choosing a
home; and before *declaring* a copy, check that the name is not already taken by a
differently-stated declaration in the cone — the checker cannot see that failure mode,
because the error is an elaboration-time `has already been declared`.

### Builds

`BaseChange+IntermediateField+VariableChangeAlgEquiv+BaseChangeAlgHom`: **2730 jobs, 1 m
21.5 s** (1 m 54.4 user / 8.5 sys) after the fix — the same chain took 497 s and failed
before it. Whole tree: **9314 jobs, green**, cached **6.4 s**. Consumers:
`spec/BaseChangeConsumer.lean` exit 0 (4.4 s, now zones 1–6 incl. D-3),
`spec/IntermediateFieldConsumer.lean` exit 0 (1.6 s); deletion probes executed for both new
D-3 modules. `#print axioms` on all four column headlines: `[propext, Classical.choice,
Quot.sound]`.

**D-4.** `KernelCyclicTransfer.lean` `lake env lean` clean (`1 m 44 s` wall, 14.2 s user /
25.0 s sys — the time is the 83-module `Engine` cone's olean I/O, not the file), then
`flock`ed `lake build FLTForHuman.WeierstrassCurve.Isogeny.KernelCyclicTransfer`: green
(94 s module, 9030 jobs of replay in a partly-stale tree). Whole tree after D-4:
**9315 jobs, green**, cached **11.0 s** (9.2 user / 12.1 sys) — +1 job over the D-3 figure,
i.e. one leaf and no cascade. `spec/KernelCyclicTransferConsumer.lean` exit 0 (1 m 40 s
wall, 7.3 user / 27.1 sys — again cone I/O), four zones; the deletion probe (module `.lean`
**and** its `.olean` moved aside) fails the consumer with exactly
`object file '…KernelCyclicTransfer.olean' … does not exist`, then both are restored
byte-exact. Checker: `5980 (313 promoted, 61 renamed) → 5999 (313, 61)`, `0 mismatched /
0 missing`, `6016 → 6035` checked; a one-token statement mutation reproduces
`5998 / 1 mismatched / 0 missing`. `#print axioms` on the headline:
`[propext, Classical.choice, Quot.sound]`.

### Friction

1. **`ps` lies across tool calls.** A background build showed a live `lake build` 5 s in and
   no process 4 min later while still producing output; two builds serialised invisibly on
   `flock`, one 10-minute foreground call making no progress because an earlier "dead" job
   held the lock. The log file is the ground truth; long builds belong in a background job
   with output redirected to a file, polled by `tail`. Two sets building in one tree contend
   rather than parallelise, and a `lake build` cut mid-flight left `BaseChange.olean` absent,
   so one builder holds the lock for a whole chain.
2. **`port_advise`'s substitution test is name/type-anchored.** It scored four rows in D-3
   that are not substitutions: `mrtw60a_pXFwd`/`mrtw60a_pYLinFwd` matched on the bare type
   `F[X]` and the two `def … : Prop` predicates matched on `Prop`. Never drop a `def … :
   Prop` or a bare-type `def` on the tool's word; `grep -c` the body first. D-4 adds the
   mirror image: `KwD5BetweenCurvesHoloLift` *is* scored as a substitution (against
   `PeriodPair.DiscriminantNeZero`, on `Prop`) while being **absent** from the port, and the
   genuinely identical cross-file copies are scored inconsistently (64 rows where 50 have an
   identical statement). The tool's *counts* price the work; its *rows* still need a diff.
3. **Two D-1 generalisations were needed, not one** — the `F`/`F'` sections and then the
   `L : Type*` section; the second only surfaced once the first was applied, as a heartbeat
   timeout rather than a type error.
4. **A `def` used as a section variable hides its binders from the checker, so a
   transcription must decide where they are written** (D-4). The pin's
   `kw_fdn2_qephod_hend7_pmopKerCard_proved` writes `K`, `E`, `E'` as explicit theorem
   binders; the `kw_fdn2_qephod_hend21_*` block and the `kw_surgehgf4_pck_*` block write them
   as `variable`s. The checker reads only the source text after the declaration name, so
   moving a binder into a `variable` silently drops it from the compared statement. Check the
   pin's own copy for each declaration; do not restructure into a shared `variable` block for
   tidiness.
5. **Transcribing the pin's proofs verbatim cost nothing, including the `rfl`s.** The two
   `set_option maxHeartbeats 102400000`/`25600000` bumps in the pin are *not* transcribed; the
   port's 4 M cap suffices at every declaration (module `lake env lean` 14 s user), because
   the pin's bumps guard the `kw_surgehgf4_pck_proved` underscore-lambda and
   `proved_core`'s `hker_iff`, both of which the port writes identically. Contrast D-1's
   `whnf` blow-up, which was a *universe* pin, not a heavy proof. The pin's `have _ :=
   kw_surgehgf4_pck_axiomAnchor` lines are kept, which is why `#print axioms` reports
   exactly the standard three.




## P-3 — the two-curve countable descent (set D-6, **landed**, 2026-10-06)

**Resolved.** The module now elaborates: `lake env lean -DmaxHeartbeats=4000000` green in
**4 m 49 s**, `lake build` of the module 9,039 jobs, consumer exit 0, axioms
`[propext, Classical.choice, Quot.sound]`, no `sorry`, and the checker unmoved at
`6054 (313, 83), 0/0, 36 own, 6090`. The diagnosis below in "The `baseChange`-at-`R₀` defeq" is
**superseded** — `WeierstrassCurve.baseChange` is a semireducible `def` in *both* pinned mathlibs,
so no reducibility difference and no cap raise was involved. The four fixes that landed (one
`Algebra ℚ K`; the pin's `⁄`-spelling bridges in the goal's exact spelling; intermediate goals
restated in the plain spelling; the pin's own 48M/8M budget for `gateDescent_of_descent`, plus the
pin's `subst` for the `DecidableEq` clash and `letI` for the gate-instance bridges) and the method
(a low-`maxHeartbeats` diagnostic loop) are recorded in
[../topics/velu/WORKORDER-P3-two-curve-descent.md](../topics/velu/WORKORDER-P3-two-curve-descent.md) §9.

The D row's tail, in
[../topics/velu/WORKORDER-P3-two-curve-descent.md](../topics/velu/WORKORDER-P3-two-curve-descent.md).
One new leaf module `WeierstrassCurve/Isogeny/TwoCurveDescent.lean` (1,299 lines) plus a
ten-declaration promotion set in `WeierstrassCurve/Isogeny/IntermediateField.lean`; the
target is

    WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward

which the frontier ranked first at **3,729 silo lines** with an unported closure of 0. The
pin's `S_` file is the D row restated in two-curve form: `port_advise` finds 107 of its 183
declarations already in the port, and its `kw_surgehgf4_hfgkd_bc*` engine is the pin's **`NoAC`**
spelling of the `kw_surge_hgf4_bc*` block D-5 landed — the same proof one generality level down,
*not* a duplicate, and **not** importable (see "The `General`/`NoAC` split in the base-change
engine" below). **The file was not ported**; the set transcribed only
what the node's demand needs. The route decisions are in the module header and §3 of the
order: the pin's `KwD5*`/`KwD5BC*` staging, its `s13_exists_gate`/`s13GlobalGate` device and
the capstone are **not** landed (the headline's own conclusion quantifies the gate
instances the proof needs).

### Status: statements checked, elaboration open

**Faithfulness is settled.** `python3 spec/check_flt_statements.py`:
**`6054 statements identical (313 promoted from pin-private declarations, 83 renamed), 0
mismatched, 0 missing, 37 own-proof declarations exempted (6091 port declarations checked)`**,
exit 0. Against the pre-D-6 baseline `6037 (313, 67), 0/0, 36 own, 6073` that reconciles
exactly: +1 `renamed` for each of the six `iotaDescent*` promotions and the ten
`IntermediateField` promotions (all sixteen appear as `RENAMED` rows through the
`stripped_source` fallback), +1 `identical` for the headline (matched against its wrapper
text, including the `letI : Algebra ℚ K` and the `∀ [DecidableEq] [gate instances] (hN₀)`
block), +1 `own` for `ModularCurve.exists_twoCurveDescent`, 0 mismatch, 0 missing. The route
decisions cost nothing at the checker.

**Elaboration does not close at the frozen cap.** `lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false` on the module is red. The module *is* left in
place, deliberately, rather than truncated, so the next round continues from the checked
statements. Remaining error sites (line numbers in the shipped file):
`:842`, `:850`, `:853`, `:912` (the `finrankAlong` path at `F = K₀`), `:937`/`:938` (the
`letI : Algebra ℚ K` vs the ambient `Algebra ℚ K` at the `Exists.intro` of the descent
instance), `:1007` (a missing `IsScalarTower (↥K₀) F₁ (W⁄K).FunctionField` in
`twoCurve_chiCompChiEqPhi`), `:1034`, `:1142`–`:1145` (the `hχ` block of
`gateDescent_of_descent`), with `:953`/`:1183` the `unknown constant` cascades.
Whole-tree `flock`ed `lake build`: **9,317 jobs, one failing target
(`FLTForHuman.WeierstrassCurve.Isogeny.TwoCurveDescent`), wall 660.7 s (11 m 01 s), user
1467.6 s / sys 94.4 s** — every other module in the tree was cached and green, which is why
the run stops at the leaf. `lake env lean` on the module: wall 1,119 s in the failing
configuration (the file is 1,227 lines), against 225 s for the same file with only the
engine and the descent construction.

### The `General`/`NoAC` split in the base-change **engine** (found 2026-10-06)

The one real discovery of this set. D-5's landed engine carries, by its own section
variables at `WeierstrassCurve/Isogeny/KernelBaseChange.lean:133–141`, `[IsAlgClosed F]
[IsAlgClosed F']` and the four `GenusOnePlaceGate`/`IsCentred`/`AbelTheorem` blocks, so
`kw_surge_hgf4_bcIota₁` and its `_finiteAlong`/`_isIntegral`/`_finrankAlong`/`_compat`
**cannot be instantiated at `F := K₀`**. The pin's engine is the gate-free,
`IsAlgClosed`-free `NoAC` spelling and it is called at exactly that instantiation twice:
`bcIota₁NoAC E₀ E₀' (↥K₀) K ι'` in the finrank step (`A:3598`) and `… (↥K₀)
(AlgebraicClosure (↥K₀)) …` in the kernel step (`A:2952`). The `NoAC` engine therefore had
to be transcribed here, `private`, at port-own content names, over D-1's `NoAC` primitives
(`functionFieldTensorFracEquivGeneralNoAC`, `functionFieldMapAlongGeneralNoAC`,
`functionFieldTensorIsDomain_dischargeGeneralNoAC`) — that is the playbook's §3.7 handling
(a frozen file is not reopened mid-set; the promotion is a refactor round). Registered as an
open follow-up in [../CARRY-FORWARD.md](../CARRY-FORWARD.md).

### The `baseChange`-at-`R₀` defeq, and the three instance fixes — **SUPERSEDED**

> The heading and the paragraph below record the third-pass diagnosis. It is **wrong** and kept
> only as a record of the misdiagnosis: `WeierstrassCurve.baseChange` is a semireducible `def` in
> both pinned mathlibs (`Weierstrass.lean:236`), `Affine.baseChange` is an `abbrev` in both, and
> the residue was four port-introduced spelling/instance defects, not a tower-defeq cost. See the
> "Resolved" note above and the work order's §9.

The pin's two-curve development is written at `F = K₀ = R₀`, so it constantly needs
`(E₀⁄K₀) ≡ E₀` and `(E₀'⁄K₀) ≡ E₀'`; FLT's `baseChange`/`map` are reducible there, the
port's are not. Three instance facts had to be made available or the unifier spins instead
of failing (the D-1 lesson): `[DecidableEq (AlgebraicClosure ↥K₀)]`, `[DecidableEq ↥K₀]`
and `[CharZero ↥K₀]` (the pin supplies the first with a global scoped instance
`s13DecEqAlgebraicClosure := Classical.decEq _`, `A:603`), and
`Module.IsTorsionFree (↥K₀) K := (Module.isTorsionFree_iff_algebraMap_injective).mpr
(algebraMap (↥K₀) K).injective` for `IsAlgClosed.lift`. With those in place the ~25
`failed to synthesize DecidableEq (AlgebraicClosure ↥K₀)` errors and the
`IsTorsionFree` timeout disappear; the residue is the `whnf`/`isDefEq` block above, which is
the *cumulative* cost of that defeq in the two-curve context (the pin guards this region
with `maxHeartbeats 6400000`/`19200000` and `synthInstance.maxHeartbeats 3200000`, none of
which the port transcribes). Per the order's §7 this is a stop-and-report condition, not a
bisect-inline one.

### What did land (and compiles)

* the pin's public `ModularCurve.iotaDescent{Curve_map_FF,Phi,Phi_equation,Phi_transcendental,
  Phi_X,Phi_yGen}` at the prefix-stripped names (six `RENAMED` rows);
* the gate-free `NoAC` base-change engine, `private`, at content names
  (`descentBCTensorIota*`, `descentBCTensorFracIota*`, `descentBCIota*`), a verbatim
  transcription of `A:2501–2839` with the `kw_` prefix stripped and D-1's `NoAC` spellings;
* the two-curve descent's construction, `private`: `twoCurveGenSet`, `twoCurveK₀{,_fg,_mem_E,
  _mem_E'}`, `twoCurve_ffCoeffSet_subset_{X,Y}`, `twoCurveE₀{,_map,_isElliptic}`, `twoCurveE₀'`
  (same), `twoCurveCoeffsHyp`, `twoCurve_xP`/`_yP`/`_spec`, `twoCurve_equation`,
  `twoCurve_transcendental`, `twoCurve_ι'{,_X,_yGen}`, `twoCurve_phiE'_{X,yGen}`,
  `twoCurve_phiCompat{,_apply}`, `finiteAlong_pointPullbackHomTo` (D-2's exchange argument at
  the abstract carriers, so that its instance search is cheap), `twoCurve_finiteAlong`,
  `twoCurve_isIntegral`, and the two spellings' bridge `twoCurve_phi_eq_iotaDescentPhi`;
* the ten promotions in `IntermediateField.lean`: `iA_crCoeffsIn`, `iA_phi`,
  `iA_ffDescend_exists`, `iCa_ffNum`, `iCa_ffDen`, `iCa_ffCoeffSet`,
  `iCa_crCoeffsIn_of_ffCoeffSet_subset`, `iPFA_finiteDimensional_adjoin_transcendental`,
  `iPFE_functionField_ringHom_ext`, `iotaSubd_countable_of_fg` — two more than the amended
  order's seven, because `iCa_crCoeffsIn_of_ffCoeffSet_subset`'s *statement* names
  `iCa_ffNum`/`iCa_ffDen` (leaving them private would leak a private name into a public
  statement) and the headline needs `Countable K₀` through `iotaSubd_countable_of_fg`.
  `lake build FLTForHuman.WeierstrassCurve.Isogeny.IntermediateField` green (42 s module,
  2720 jobs, wall 45.9 s; the smoke test on `iA_phi` alone took wall 52.7 s).
* `spec/TwoCurveDescentConsumer.lean` (three zones) is **not executed**: it imports the red
  module, so it cannot run until the module elaborates.

### Dedup, both figures

The pin `S_` file is **3,729 raw lines**; the written module is **1,227 lines** (of which
~340 are the `NoAC` engine transcription the amended order prices separately). `port_advise`
prices the whole node at 1,975 net-new and finds 107 of its 183 declarations already in the
port; the measured saving is everything the five P-2 pin files already carry (the D-2 descent
helpers, the D-5 seam, the place dictionary, the `pointPullback`/tensor prelude) plus the
~290 lines of the pin's `KwD5*`/`s13GlobalGate` staging that this set does not write.

## S-1 — the ℂ-analytic seam (landed, 2026-10-07)

**Landed.** One new leaf module `Elliptic/PeriodPair/HoloLift.lean` (**931 lines**, 20 public
declarations + 9 `private` helpers) and a `spec/` probe. The pin is
`P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean`
(2,673 lines, 133 declarations); the statement authority is the 24-line `Theorems/` wrapper.
The whole target is

    PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint

and the work is the chain that proves `ModularCurve.KwD5BetweenCurvesHoloLift` (which is
**imported** from D-5's `Isogeny/KernelBaseChange.lean`, never redeclared — the near-twin
warning in the order was right: the class is a `def … : Prop` proved nowhere else).

### What was written, and what was imported

Written: the four pin-public chain `Prop`s
(`KwD5BetweenCurves{LocallyHoloLift,CocountableHoloLift,CocountableAffineHoloCoords,
CocountableAffineHoloCoordsWeak}`), the nine `kw_surgehgf4_hH2*` reduction lemmas, the
constructive `kw_surgehgf4_hH2f_betweenCurvesCocountableAffineHoloCoordsWeak` (≈195 lines,
the analytic base), the three `geomMorphBC` atoms, the two `kw_fdn2_qephod_hend10_*`
finite-kernel lemmas, `WeierstrassCurve.Affine.kw_evalAt_placeOfEquation_mk`, the headline,
and the `private` covering-map layer.

Imported, not re-proved (pin-file occurrence counts from a `grep -c` on the `S_` file, as
§2.4 requires of every drop):

| dropped | occurrence count | reason / port home |
|---|---|---|
| `kw_fdn2_qephod_hend7_geomMorphBC`, `…_placeOfPoint_geomMorphBC`, `…_pmop_eq_geomMorphBC_sub` | 11 / 6 / 3 | `Isogeny/NatCard.lean` — the ported generalisation (`hN` explicit; no `IsElliptic`/`IsCentred`) |
| `kw_fdn2_qephod_hend7_pmopKerCard_proved` | 2 | `Isogeny/NatCard.lean` (`KwD5PointMapOfPushforwardKerCard`, with an extra `hsep`; see Friction 4) |
| `mmr73_cs_evalAt_eq_of_ord_sub_pos`, `mmr73_cs_ord_neg` | 3 / 2 | `IsogenyEndDatum/Engine.lean` |
| `kw_toPointHom` / `_apply` / `kw_ker_toPointHom` / `kw_toPointAddEquiv` / `_mk` / `kw_discriminantNeZero` | 35 / 7 / 6 / 8 / 1 / 10 | `Elliptic/PeriodPair/Uniformization.lean` (D-5 §1.5 promotions, prefix-stripped) |
| the place dictionary and `placeOfEquation` algebra (`IsFinitePlace.*`, `placeOfPoint_*`, `InfinitePlace.*`, `or d_placeOfEquation_*`, `mk_mem_XYIdeal_iff`, `polyToFunctionField*`, `yGen`, `evalAt_div'`, `ord_div`, `min_ord_le_ord_add`, `mem_restrictAlong_iff`, `restrict_fiber_finite`, `ord_restrictAlong`, `ramificationIndexAlong_pos`, `isRational_placeOfEquation`, …) | — | `Place/Dictionary.lean`, `FunctionFieldQuadratic.lean`, `AlgebraicCurve/Defs/*`, `IsogenyEndDatum/Engine.lean` |
| `analyticOnNhd_weierstrassP`, `analyticOnNhd_derivWeierstrassP`, `deriv_weierstrassP`, `isClosed_lattice`, `equation_weierstrassP` | — | mathlib `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` |

Two pin-`private` prelude names did **not** survive the module split: `countable_lattice` and
`toPoint_surjective` are `private` in `Uniformization.lean` (the pin has them in-file, so it
reuses them freely). `countable_lattice` is re-derived in one line; `surjective_toPointHom` is
re-proved from the public `toPointAddEquiv`. A pin-private prelude name is *not* importable
across a module boundary even when the port keeps the same name privately.

### Measured table

| metric | value |
|---|---|
| pin file (raw / `port_advise` substitutions / **written**) | 2,673 / 78 subst. ≈ 1,203 / **931** lines |
| declarations | 20 public (4 `Prop`s + 9 chain + 3 atoms + 2 finite-kernel + 1 evalAt bridge + 1 headline), 9 `private` |
| edit-loop `lake env lean` (final) | wall 44.2 s / user 19.9 / sys 12.5 (import-dominated; first cold run 130 s) |
| module `lake build` | 67 s (9,038 jobs); 103 s after the last comment edit; flocked, `timeout 300` |
| cascade (`build_ladder --edit`) | **0** dependent modules / 0 lines — a leaf |
| whole-tree `flock`ed `lake build` | green, 9,318 jobs, wall 11.25 s / user 8.56 / sys 12.14 |
| checker before | `6054 (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own, 6090 checked` |
| checker after | `6074 (313, 83), 0 mismatched, 0 missing, 36 own, 6110 checked` |
| checker `--prop-bodies` | 258 identical, 6 textual (advisory, all pre-existing; none of the four S-1 classes) |
| consumer | `spec/PeriodPairHoloLiftConsumer.lean`, exit 0, wall **67.2 s** (`timeout 90`) |
| axioms | `[propext, Classical.choice, Quot.sound]` (headline, chain lemma, `Weak`) |
| `sorry` | 0 |

The checker delta reconciles exactly: **+20 `identical` = the 20 public declarations**, with
`promoted`/`renamed`/`own` unmoved and 0 mismatch/missing. The four classes compare as
`identical` in the main pass (a `def … : Prop`'s type is `Prop`) and their **bodies** sit in
the `--prop-bodies` identical set — the four are genuinely distinct propositions, not
restatements: `Weak` (no `Y z ≠ 0`) → `Coords` (adds it) → `Cocountable` (replaces the
point coordinates by a lift `G` through `toPointHom`) → `Locally` (drops the countable
exceptional set `S`, fixing a point `z₀`) → `HoloLift` (drops the neighbourhood, glues to one
global `F : ℂ → ℂ`). Each step deletes exactly one defect; `grep -c` in the pin file gives
3 / 4 / 4 / 4 occurrences and each has exactly one declaration home in the port.

### Checker wiring

`PORT_FILES`: `FLTForHuman/Elliptic/PeriodPair/HoloLift.lean` appended last. `SOURCES`: the
`Theorems/Thm_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean`
wrapper inserted **immediately above** the `S_` entry (the one non-appended `SOURCES` entry of
the port), because the wrapper is the headline's statement authority and the `S_` file
declares no `PeriodPair.exists_…` at all. It carries one declaration whose name the `S_`
entry already serves, so no other row's lookup can move; confirmed by a checker run before
and after. Both intermediate states were measured: with `HoloLift.lean` in `PORT_FILES` but
the wrapper **absent** the checker reports `6073 (313, 83), 0 mismatched, 1 missing, 36 own
(6110)` — the one `missing` is the headline, which has no pin declaration to match against
(the `S_` file declares only `…solution`) — and the wrapper turns it into the final
`6074 (313, 83), 0/0, 36 own (6110)`.

### Friction

1. **`IsCoveringMap (ℂ → ℂ/Λ)` came out exactly as the pin has it.** `isDiscrete_lattice` is
   `isDiscrete_iff_discreteTopology` applied to mathlib's own `DiscreteTopology L.lattice`
   instance; `isCoveringMap_mk_lattice` is the one line
   `(AddSubgroup.isAddQuotientCoveringMap_of_comm L.lattice.toAddSubgroup ‹discrete›).isCoveringMap`;
   the global lift is mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts` in its
   `SimplyConnectedSpace` form. The order's §5 measurement held exactly; no scout was needed
   and none of it cost a round.
2. **How much mathlib absorbed.** The entire topological foundation — discreteness, the
   covering map, unique lifting, `Set.Countable.isPathConnected_compl_of_one_lt_rank` +
   `Complex.rank_real_complex`, ℘-analyticity/`IsZLattice` — is mathlib's, and
   `kw_differentiable_of_locallyDifferentiable_lift_through_mk` is a 25-line transcription
   (`Metric.mem_nhds_iff` + `convex_ball`'s `IsPreconnected.constant_of_mapsTo`). What is *not*
   mathlib is the analytic chain itself: the local-inverse/local-coordinate argument in
   `…hH2d…` and the rationality argument in `…hH2f…_Weak` transcribe essentially verbatim.
3. **The `mmr73`/`geomMorphBC` blocks were importable.** `mmr73_cs_evalAt_eq_of_ord_sub_pos` and
   the `ModularCurve.kw_fdn2_qephod_hend7_geomMorphBC*` block are in
   `IsogenyEndDatum/Engine.lean` / `Isogeny/NatCard.lean` and were used as-is. Only the three
   pin-public `kw_surgehgf4_hH2f_geomMorphBC*` atoms had to be written; they are Engine's
   datum-general `mmr73_cs_geomMorph_{ne_zero,some_coords}` and the fibre-finiteness lemma
   specialised back to a bare `ι, hι` (≈110 lines, no new mathematics).
4. **The port's kernel-cardinality `Prop` is not the pin's.** `KwD5PointMapOfPushforwardKerCard`
   (NatCard) carries an explicit `hsep : SeparableAlong K ι` and `hN`, where the pin's
   `kw_fdn2_qephod_hend7_pmopKerCard_proved K E E' ι hι hfin` uses the canonical
   `normFormulaAlong_of_elliptic`. The finite-kernel lemma therefore derives `SeparableAlong`
   the way `normFormulaAlong_of_elliptic` does (`letI := algebraAlong` + `isScalarTower_along`
   + `CharZero` of the base) rather than calling the pin's wrapper.
5. **A pin-private prelude name is not importable across a module split.** See above.
6. **`Y` is a token in `Polynomial.Bivariate`'s scope.** `open scoped Polynomial.Bivariate`
   makes `Y` a `scoped notation`, so `∃ X Y : ℂ → ℂ, …` and `⟨…, X, Y, …⟩` are parse errors
   (`X` still parses, which is what makes it confusing). Fixed by not opening the scope
   file-wide and spelling `(Polynomial.X : Polynomial K[X])` where the bivariate variable is
   needed. Folded into playbook §6.
7. **`--` line comments shift the checker's namespace tracker.** `namespace_events` runs a
   second comment-stripping pass that `strip_comments` does not, so a `--` comment made every
   later declaration attribute to the next namespace (the chain lemma came out as
   `PeriodPair.kw_surgehgf4_hH2f_betweenCurvesHoloLift`). All last-name lookups still matched
   `0/0`, but a dotted lookup (`OWN_PROOFS`, `dotted_source`) would have missed. Fixed by
   writing the header prose as a `/- … -/` block; folded into playbook §4.
8. **Drift** (`v4.34.0`): `eventually_of_mem` is namespace-qualified
   (`Filter.eventually_of_mem`); `continuous_add_right` is gone (`continuous_id.add
   continuous_const`); the pin's `unfold yGen` needs `unfold yGen yCoord` in the port, because
   `yGen` wraps the `def yCoord` where the pin had them inlined. `Polynomial.induction_on`'s
   `monomial` step changed shape (`motive (C a * X^n) → motive (C a * X^(n+1))`) but the pin's
   proof transcribes unchanged. All three added to playbook §7.
