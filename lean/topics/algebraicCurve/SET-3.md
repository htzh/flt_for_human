# SET 3 — the AlgebraicCurve layer's next D-S wave: descent, places, and the pointwise dictionary

**Status (2026-10-27): orders 1 and 2 dispatched and running; order 3's ground prep is done and it
is dispatched when they land (it edits modules they build against).**

This is the run brief for the next coding set on the `AlgebraicCurve` layer, cut from the
D–S column's ready shelf after the correspondence base change landed. The shelf reading is
`python3 frontier.py --ds --ready --rank-by silo --top 0`: **106 ready candidates, 24 of them
`AlgebraicCurve.`** — 4,972 silo lines, 183 `S_` declarations + 24 wrappers (207), **4,087 net
new math lines** after 198 dedup and 230 already-in-port lines (`port_plan`).

## 0. What the reconnaissance settled (measured 2026-10-27)

- **No intra-cluster citation edges.** The 24 nodes cite none of each other, so every set is
  independently landable and the three orders can run concurrently without a scheduling
  constraint.
- **Definition layer complete.** All twelve pin `Def_*` modules in the closure
  (`DivisorClassGroup` 63 declarations, `DivisorPushPull` 70, `PlacesOverDVR` 45,
  `Correspondence` 39, `AdelicIndex` 68, `Repartitions` 19, `PlaceEvaluation` 14,
  `IsCurveOver` 10, `RegularProlongation` 7, `CanonicalDivisor` 5, `ModularCurve/CanonicalDivisor`
  16, `…Uniformizer` 4) are already ported — 2,555 lines of their surface match a port
  declaration. **No definition needs porting for this cluster**; the four known drops
  (`fiber_eq_fiberOver`, `card_fiberOver_eq`, `finite_setOf_forall_mem_and_ord_pos`,
  `AbelJacobiCard`) are recorded deliberate omissions in the host modules' own headers.
- **21 declarations are already public in the port** (≈249 lines to import, not re-prove) and
  every one of them is public — **no promotion is required** for any of the three sets.
- **BC2 is one development written three times.** The pin copies a 105-line prelude into each
  of the three `exists_constantFieldDescent*` files (`descent_abstract` 45,
  `isAlgebraic_of_rational_relation` 34, `nonempty_ringHom_complex` 26; plus
  `aeval_mem_of_repr`/`aeval_mem_of_lift` twice). It is written **once** in the new module,
  public at the pin's names.
- **`descent_abstract` has two statements** across the trio (`_correspondence` and `_finset`
  spell it differently). Both have consumers; the two spellings get two namespaces in the one
  module — the checker matches statements by hash, and the pin's own precedent for
  same-last-name/different-statement pairs is a namespace split, never a merge.
- **Nine binder-variant names** (`mem_of_ord_nonneg` in 37 pin files, `ord_nonneg_of_mem` in 36,
  `evalAt_algebraMap` in 7, …): take the `Theorems/` wrapper's binders.
- **Three same-name/different-statement items** to keep apart: `residue_ne_zero_of_ord_eq_zero`,
  `isUnit_mk_of_ord_eq_zero`, `descent_abstract`.
- **Machine namespaces to rectify** (§3.1): `W4B`, `W7XDesc` (BC2); `W7XL2`, `W7XChildE` (the
  invariants wave); `W7XChildL`, `WC1bSolAW`, `INTGlue` (BC4/BC5).
- **The legacy hosts are migrated** (ground prep, before BC5 was dispatched). `Defs/PlaceEvaluation`
  now carries a seven-source wire over its pin Def module and the six `S_` files that hold its
  `evalAt`/`isRational` algebra (**21 ok**); `Defs/PushPull` a six-source wire (**63 ok**),
  `Defs/PlacesOverDVR` its pin Def module (**36 ok**), `Defs/PoleDivisorPackage` its pin Def
  module (**10 ok**). All four are removed from `spec/old_check_stmts.py`'s `PORT_FILES` with a
  `MIGRATED` note; their `SOURCES` entries stay, since other listed modules still match against
  them. Two unwired non-legacy hosts were wired in the same pass: `IsCurveOver/Transcendental`
  (**4 ok**) and `RegularProlongation` (**7 ok**), so no declaration BC5 adds lands in an
  unchecked module. After every removal the frozen checker re-ran green: **7,393 identical,
  0 mismatched, 0 missing, 35 own-proof exempted, 294 registered-unwired**; the six touched
  modules build with **0 warnings**.
- **`Differential/Coefficient` needed no migration**: it was handed to `check_port` on
  2026-10-24 (38 ok / 0 / 0, 1 own) and its `PORT_FILES` line was already only a comment.
- **Two Def-layer drops are registered**, not fixed here: `Place.fiber_eq_fiberOver` and
  `Place.finite_setOf_forall_mem_and_ord_pos` are live in the pin (5 and 4 consumers) but absent
  from the port, whose sites inline the argument. They are in
  [CARRY-FORWARD.md](../CARRY-FORWARD.md) with their price.

## 1. The cut

| order | work order | object | pin nodes | net lines | home |
|---|---|---|---|---:|---|
| 1 | [WORKORDER-BC2-descent.md](WORKORDER-BC2-descent.md) | descent to a countable algebraically closed constant field (Lefschetz) | 3 | ≈950 | new `IsCurveOver/ConstantFieldDescent.lean` |
| 2 | [WORKORDER-BC4-cfe-ramification.md](WORKORDER-BC4-cfe-ramification.md) | places over a constant field extension: embedding counts, ramification one, prescribed orders, no cancellation | 5 | ≈1,240 | new `Place/ConstantFieldExtensionRamification.lean` |
| 3 | [WORKORDER-BC5-pointwise-dictionary.md](WORKORDER-BC5-pointwise-dictionary.md) + [BC5b](WORKORDER-BC5b-rehomed-leaves.md) | the pointwise dictionary: `ord`/integrality/derivative regularity/`evalFun` algebra | 10 | ≈430 | five existing modules (+ two hubs edited by the manager) and two new modules above the norm block |
| — | not this set | constant-field-extension invariants: `finrankAlong`/trace, `finrank_le`/`natCard_places`, `Pic0.natCard_torsion`, index of specialty, separable adjoin | 5 | ≈1,375 | next wave (the torsion node alone is 541 lines / 33 declarations) |
| — | not this set | `Place.connectedSpace_of_chartedSpace_…_complex` | 1 | ≈256 | the complex dictionary chain; its only consumer is `exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` |

**The cut was made one read short, and the second read is the canonical one.** The table above is
`--ds --ready`; the tool's own help says to pair `--ds` with `--include-leaves` for the full D–S
read, and that read **adds five `AlgebraicCurve` rows this cut did not carry** (measured
2026-10-27, after the three modules landed):

| node | silo | prem | pin lines | consumers |
|---|---:|---:|---:|---:|
| `AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence` | 925 | 6 | 925 | 2 |
| `AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support` | 60 | 1 | 60 | **8** |
| `AlgebraicCurve.mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain` | 51 | 1 | 51 | 1 |
| `AlgebraicCurve.Place.ordDiff_eq_ordDifferential` | 44 | 4 | 44 | 5 |
| `AlgebraicCurve.SemilinearAut.pushforward_smul` | 21 | 2 | 21 | 1 |

They are graph leaves (they cite nothing unported), which is why `--ready` hides them; the first
of them is a 925-line node — "constant reduction commutes with a correspondence and its base
change" — so the leaf tail is ≈1,100 silo lines, not a rounding error. **They are the next set
(BC6), not this one**: BC5's scope was fixed at dispatch. The `--ds --include-leaves` reading also
moves the headline figure: `needed [F terminal]` **1,103 nodes / 421,670 lines → 1,090 / 419,020**
once this wave's three modules are on disk.

The six rows the ordinary (non-`--ds`) read shows and this one does not (1,610 lines:
`sum_fiber_ord_eq_finrank`, `exists_isUnit_det_evalAt_differentialCoeff`,
`analyticCoord_of_agree`, `ord_eq_zero_…_aeval_inv_div`, `degree_canonicalDivisor_eq_of_isAlgClosed`,
`ramificationIndexAlong_eq_ord_sub_…`) are **not D-S work**: their consumers are the avoided
complex-analytic supply (`exists_dissectionScaleData`, `exists_pairedCellFamily`,
`ModularCurve.ComplexPlaceDictionaryOf.*`).

## 2. Order 1 (BC2) — landed 2026-10-27

| item | value |
|---|---|
| module | `IsCurveOver/ConstantFieldDescent.lean`, **921** lines, 15 public declarations |
| pin | 1,134 raw lines over three `S_` files; the 105-line prelude they all copy is written once, and the two `descent_abstract` / two `core` spellings live in two sub-namespaces |
| checker | **15 ok** / 0 mismatch / 0 missing (16 before the dedup below) |
| build | 26 s, **0 warnings**, 0 sorries |
| axioms | the three headlines `[propext, Classical.choice, Quot.sound]` |
| consumer | `spec/AlgebraicCurveSet3Consumer.lean` zone C, **0 errors** |

**The one dedup.** The pin's `nonempty_ringHom_complex` (copied into all three files) is
already public in the port as `Field.nonempty_ringHom_complex_of_countable`
(`FieldTheory/NonemptyRingHomComplex.lean`), statement-identical. The copy was deleted and the
three call sites re-pointed: **−26 lines**, the checker's count 16 → 15 with 0 mismatch / 0
missing (nothing to diff, since the module no longer declares it), axioms unchanged. This is the
`port_advise` name-anchored false negative in the act: the tool reported `prelude 0/23` because
the port's copy carries a different name.

**Build policy, as ruled for this set: no tree build.** The gate is one targeted build of exactly
the ten modules the set created or edited, serialized with `flock`:

```
lake build FLTForHuman.AlgebraicCurve.{IsCurveOver.ConstantFieldDescent,
  Place.OrderArithmetic, Place.ConstantFieldExtensionRamification,
  Defs.PlaceEvaluation, Defs.PushPull, Defs.PlacesOverDVR, Defs.PoleDivisorPackage,
  PrincipalDivisors.Transcendence, IsCurveOver.Transcendental, RegularProlongation}
```

→ all ten up to date or built (`ConstantFieldDescent` 26 s), **0 warnings from any of them** (the
11 replayed warnings in the log are `Defs/LocalResidue.lean`'s 3 and `Genus/Stichtenoth.lean`'s 8,
pre-existing). No dependent module is rebuilt for this wave.

## 3. Order 2 (BC4) — landed 2026-10-27

| item | value |
|---|---|
| modules | `Place/OrderArithmetic.lean` (**722** lines, 27 declarations), `Place/ConstantFieldExtensionRamification.lean` (**684** lines, 23 declarations) |
| pin | 1,413 raw lines over five `S_` files; the two modules are 1,406, the difference being the dedup below |
| checker | **8 ok** / 0 / 0 and **23 ok** / 0 / 0 |
| build | 6.2 s and 7.9 s, **0 warnings**, 0 sorries |
| axioms | all five headlines `[propext, Classical.choice, Quot.sound]` |
| `dedup.py` / `move_dead.py` | 0 clusters / 0 dead, both modules |
| consumer | `spec/AlgebraicCurveSet3Consumer.lean` zones A and B, **0 errors** |

**The one substantive decision, and how it was paid down.** `ramificationIndex_eq_one_of_forall_dvd_ord`'s
frozen hypotheses do not include `[HasPrincipalDivisors K L]`, and the port's only public norm
formula carries it, so the worker first reproduced the pin's ~150-line norm block privately. The
manager settled it the other way: the pin's `private` engine `Place.ord_norm_eq_sum_fiberOver`
(`S_…pushforwardNormFormula_of_finiteDimensional.lean:582`, the identity
`ord (norm f) = ∑_{w|v} inertiaDeg · ord f`, general in `F'`) is **promoted to public** in
`PrincipalDivisors/Transcendence.lean`, that module is wired and migrated off the frozen checker
(6 ok / 0 / 0; the promotion matches through the pin-private promotion tier), and the worker's
copy plus a now-redundant private re-derivation were deleted: **−214 lines**, with both call
sites instantiating the promoted statement unchanged. The checker's declaration counts did not
move.

**Recorded, not cut.** The port now states `exists_digit` twice — the pinned
`ConstantFieldPlaceLift.exists_digit` (`[IsCurveOver]` plus the `(o = 0 → o' = 0)` conjunct) and
BC4's general public form under `[Module.Finite K v.ResidueField]`; the fusion is an edit in the
direction opposite to the import edge and waits for that hub's next refactor
([CARRY-FORWARD.md](../CARRY-FORWARD.md)).

**Other deviations** (all proof-side, statements untouched): `exists_digit`'s transcription as
above; the pin's `WC1bSolAW.exists_forall_ord_eq_finset` helper merged into the headline (same
statement, one namespace); `SpecialisationCount.restrict_restrict` re-exported over the ported
`BifibreDev.restrict_restrict`; `@[scoped simp]` → `@[simp]` (attributes are not statements);
`set_option linter.deprecated false` for `Ideal.inertiaDeg'_eq_inertiaDeg`, and
`linter.unusedVariables false in` on the one headline whose frozen statement carries three
unused hypotheses.

## 4. Order 3 (BC5 + BC5b) — all ten landed, three re-homed

| module | change | checker | build |
|---|---|---|---|
| `IsCurveOver/Transcendental.lean` | `isCurveOver_iff_exists_transcendental_finiteDimensional` | 4 → **5 ok** / 0 / 0 | 0 warnings |
| `Differential/Coefficient.lean` | `localUnitDerivativeRegular_of_isCurveOver` | 38 → **39 ok** / 0 / 0, 1 own | 0 warnings |
| `Defs/PlaceEvaluation.lean` | `Divisor.evalFun_mul`, `evalFun_zpow_left` | 21 → **23 ok** / 0 / 0 | 0 warnings |
| `Place/OrdCalculus.lean` | `Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg`, `isIntegral_adjoin_of_forall_ord_nonneg` | 21 → **23 ok** / 0 / 0 | 0 warnings |
| `RegularProlongation.lean` | `RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue` | 7 → **9 ok** / 0 / 0 | 0 warnings |
| `PrincipalDivisors/Transcendence.lean` | manager: `count_normalizedFactors_span_singleton` promoted to public, `Divisor.pushforward_div` added | 6 → **8 ok** / 0 / 0 | 10 s |
| `Place/IntegralClosureAtFiber.lean` (new) | `Place.exists_integralClosureAt_of_ord_fiber_nonneg` | **1 ok** / 0 / 0 | 0 warnings |
| `PrincipalDivisors/PoleDivisor.lean` (new) | `exists_poleDivisor_of_transcendental` | **1 ok** / 0 / 0 | 0 warnings |

All ten nodes are now in: the seven of the first round, `Divisor.pushforward_div` beside the
formula, and the two re-homed leaves filled by BC5b from the pin's proofs (one proof-glue change
each, both to keep the module at 0 warnings: the pin's `haveI : IsCurveOver …` as a `have` with the
principal-divisor datum taken by projection, and the pin's `haveI : P.IsPrime` as an explicit
`HeightOneSpectrum` field).

Axioms: the seven delivered headlines, the two promoted nodes and `pushforward_div` all
`[propext, Classical.choice, Quot.sound]`. All edits are insertions; no existing declaration was
restructured. `dedup.py`: 0 clusters in five of the modules; the two clusters it reports in
`IsCurveOver/Transcendental` and `PrincipalDivisors/Transcendence` are wrapper-over-engine pairs
of the pin's own (`isCurveOver_of_transcendental` / `…_of_isSeparable`, and the norm formula's
hypothesis-free engine under its documented spurious-hypothesis wrapper) — deliberately not cut.

### The homing error, and the fix

Three nodes could not be placed where the order put them, and the worker was right to stop:
each proof needs material *above* its assigned module.

| node | order's home | why it cannot live there | new home |
|---|---|---|---|
| `Divisor.pushforward_div` | `Defs/PushPull.lean` | the pin's proof is one line from `Divisor.pushforwardNormFormula`, public only above `PushPull` | `PrincipalDivisors/Transcendence.lean`, beside the formula (3 lines) |
| `Place.exists_integralClosureAt_of_ord_fiber_nonneg` | `Defs/PlacesOverDVR.lean` | needs `count_normalizedFactors_span_singleton` (private then) and the fibre dictionary above `PlacesOverDVR` | new `Place/IntegralClosureAtFiber.lean` |
| `exists_poleDivisor_of_transcendental` | `Defs/PoleDivisorPackage.lean` | pin's first line is `isCurveOver_of_isAlgClosed_of_transcendental`, above that module | new `PrincipalDivisors/PoleDivisor.lean` |

The lesson for the next order: **a node's home is a mathematical decision, but the *module* must
be above the pin declarations its proof uses**, and that is a fact to check when writing the
order, not after. The two new modules were stubbed by the manager (header, imports, statement at
the pin's inline binder spelling, statement-checked `1 ok / 0 / 0` each — the section-variable
spelling of a binder block the wrapper writes inline is a `MISMATCH`), and their two proofs are
dispatched as [WORKORDER-BC5b](WORKORDER-BC5b-rehomed-leaves.md) and landed.

**Two promotions in the same pass** (pin nodes hidden as private, the same §5 repair as BC4's
norm identity): `Place.count_normalizedFactors_span_singleton` — a pin node with its own wrapper
— and `RegularProlongation.coeff_mem_of_aeval_mem_integers` — a pin node with nine pin consumers
— are now public at the pin's names and diffed; the latter had been transcribed privately under
an invented `_aux` suffix.

## 5. Definition of done, per order

- **build policy: no tree build, ever.** The gate is a single targeted build of exactly the
  modules this set created or edited (BC2's module, BC4's two, and the seven ground-prep
  modules), each serialized with `flock` and bounded with `timeout`; a module's *dependents* are
  not rebuilt for a statement-checking wave;
- module builds with **0 warnings**, no `sorry`/`admit`/`axiom`, no `set_option maxHeartbeats`;
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** (every public
  declaration diffed against the pin, or carrying a `pin:`/`own:` row in `spec/decl_markers.tsv`
  that the manager adds);
- `#print axioms` on the headline(s) → `[propext, Classical.choice, Quot.sound]`;
- `dedup.py` and `move_dead.py` clean (or the residue recorded with its reason);
- a `spec/` consumer zone that exercises the headline in a real cross-module composition;
- the set's own row in this brief updated with its measured numbers.

## 6. What to report back

One message per set, in the work order's format: build status and warnings, the checker
summary line, the axioms lines, any deviation from the pin beyond a tactic rename, and
blockers at first belief (never a statement weakened, never a hub module edited by a worker).
