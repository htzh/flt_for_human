# Blueprint: the `AlgebraicCurve` layer for `ModularCurve.heckeOperatorsCommuteBar`

**Status (2026-09-23): the effort is complete and verified — AC0, T1–T9 and the
T7 capstone.** This is the third Lean port and the
first that targets the *generic* curve layer rather than a modular instance. It is
opened as `PORTING-FFG.md` runs down (T19–T20), because the two efforts share the
`ModularCurve/Defs` vocabulary and the same verification machinery, and because
`math/009-hecke-jacobian-commute.md`'s theorem is the natural consumer that makes
the `AlgebraicCurve` layer worth building.

| set | topics | result |
|---|---|---|
| SET 1 | AC0, T1–T4 | 12 modules / 3,244 lines / 269 public decls; build 4,022 jobs; checker 586; consumer Zones A–E |
| SET 2 | T5, T6, T8, T9 | 5 modules / 1,780 lines; checker 617; consumer Zones A–I |
| capstone | T7 (the human reviewer) | `WeilExchange/DivisorExchange.lean`, 137 lines; checker 618; consumer Zone J |

Final: `lake build` **4,034 jobs, 0 warnings, no `sorry`**; checker **618
identical (34 promoted from pin-`private`), 0 mismatched, 0 missing**, 14
exempted; consumer `spec/AlgebraicCurveConsumer.lean` **Zones A–J at 0 errors**;
`#print axioms` on the divisor exchange, the local exchange, the bifibre count and
`hasPrincipalDivisors_of_transcendental` all `[propext, Classical.choice,
Quot.sound]`; no commits. The effort wrote **5,553 module lines**, inside §4.3's
≈5.1k–5.9k written budget. **Every generic input of `math/009`'s exchange
reduction is now a ported theorem**: the Weil exchange, `separableAlong_of_charZero`,
and `HasPrincipalDivisors` for the modular function field. The measured record is
[logs/ac-port.md](logs/ac-port.md).

The run briefs are
[topics/algebraicCurve/SET-1.md](topics/algebraicCurve/SET-1.md) and
[topics/algebraicCurve/SET-2.md](topics/algebraicCurve/SET-2.md), and the per-topic
work orders are [topics/algebraicCurve/TOPIC-*.md](topics/algebraicCurve/). What
remains for the *target theorem* is the `ModularCurve` Hecke layer named in §0's
table, not this layer.


Four records feed this blueprint, all read-only and already written for other
purposes:

- [math/009](../math/009-hecke-jacobian-commute.md) — the mathematics of the
  target. Source of truth for *what the proof says*.
- [studies/hecke-commute-bar-survey.md](../studies/hecke-commute-bar-survey.md) —
  the reduction chain, the two degeneracy maps, the local bifibre identity, and
  §9's list of what the note must not claim.
- [studies/flt-function-field-theory-and-mathlib.md](../studies/flt-function-field-theory-and-mathlib.md) —
  the repository-wide FLT↔mathlib seam map for the curve layer.
- [topics/ffg-retrospective.md](topics/ffg-retrospective.md) — the process
  lessons from the FFG effort. Its transfers are applied in **§3.5** (the
  mathematical core and the recorded negatives), **§4.4** (the budget is named
  shape risks, not lines), **§6.1** (what is deliberately not cut), **§7.2** (the
  conditional capstone built first) and **§7.3** (the friction log).

Companion records: [topics/algebraicCurve/SET-1.md](topics/algebraicCurve/SET-1.md)
is the SET-1 run brief, `topics/algebraicCurve/TOPIC-*.md` are the per-topic work
orders (SET 1 written, SET 2 written after SET 1 is reviewed), and `logs/ac-port.md`
is the measured record once work starts. The reusable method is
[porting-playbook.md](porting-playbook.md); this document inherits §7–§8 of it
wholesale and records only what is new.

FLT line numbers and paths are against `anthropics/fermats-last-theorem@aa2d8b3`.
mathlib is our pinned `v4.34.0`.

## 0. Scope, and where this sits under `math/009`

**The target is the whole `AlgebraicCurve` cone of
`ModularCurve.heckeOperatorsCommuteBar`** — measured with the local pin graph
(refresh recipe in §9.1) at **63 `AlgebraicCurve.*` theorem nodes in 5,210 `S_`
lines, 7 `Def_AlgebraicCurve_*` modules in 2,867 lines, and 2 generic
group-theory nodes (`MulAction.ncard_orbit_inter_orbit_mul_card` 165,
`Subgroup.exists_eq_mul_of_index_inf_eq` 48) that the bifibre count needs and that
are neither `AlgebraicCurve` nor mathlib**. The AC layer is the *generic* half of
`math/009`: places, divisors, `Pic0`, push/pull, correspondences and the Weil
exchange lemma, with no schemes and no curve axiom. (The three `Polynomial.*`
engine lemmas the closure also contains are already ported in
`FLTForHuman/FieldTheory/CommonRoot.lean`.)

**What this port is not.** `math/009`'s theorem needs three more slices that are
*not* `AlgebraicCurve` and are not in this scope. They are listed here so the aim
is honest, not because they are being planned now:

| slice | nodes | status |
|---|---|---|
| `ModularCurve` Hecke layer — `DegeneracyTower`, `HeckeOperatorTotal`, `HeckeModule`, the roof square | defs + ~40 nodes | unported |
| `modularPolynomialFamily` / `ModularPolynomialData` at every prime | 39-node cone | partly ported by the Φ_p sub-effort |
| `hasPrincipalDivisors_modularFunctionFieldBar`, `heckeRoof_adjoin_range_union_eq_top`, `finrankAlong_towerSubstBar_comp_heckeAlphaBar` | 3 nodes + cones | unported |
| **`AlgebraicCurve` exchange + principal divisors** | **65 nodes + 6 def modules** | **this blueprint** |

`functionFieldGeneration` (FFG's capstone) is a direct premise of the hecke
theorem too, and is being finished by the FFG effort. Nothing in the hecke
solution file imports an `IsCurveOver` instance, a `CurveModel`, a scheme, or the
Riemann–Roch layer — see §3.4 — so the AC slice is genuinely independent of
`CurveModelConstruction` and the adelic theory.

**Why the AC layer is worth porting on its own.** Unlike the FFG cone, the AC
layer is a *library*: its top declarations are cited from outside the hecke cone
at high indegree (`Place.mem_iff_ord_nonneg` 184 external citers,
`Place.ord_algebraMap` 142, `Place.mem_of_ord_nonneg` 106,
`separableAlong_of_charZero` 84 — §2.3). The gain test of
[PORTING-FFG §2](topics/PORTING-FFG.md) therefore scores differently here: mathlib
alignment is real (the whole layer sits on mathlib's `ValuationSubring` /
`DedekindDomain` / `Kaehler` API, §3.4), the interface is broad rather than
concentrated, and organization is the main product — FLT's `AlgebraicCurve` layer
is 72 definition modules and 1,577 proof files, and this port takes the 7 + 63 that
the Hecke theory actually uses.

## 1. Organization for math clarity

The rules of [PORTING-FFG §1](topics/PORTING-FFG.md) and playbook §7.1–§7.2 govern
unchanged. The AC-specific statements:

- **Namespace `AlgebraicCurve`** (and its existing sub-namespaces `Place`,
  `Divisor`, `Pic0`, `RationalFunctionField`, `SemilinearAut`), matching FLT, so
  declaration names line up and the statement checker's map stays mechanical.
- **A module is a mathematical role.** FLT's `Def_AlgebraicCurve_DivisorClassGroup`
  (484 lines) covers `Place`, `ord`, `Divisor`, `Pic`, `Pic0` and the Galois
  `SMul`; it becomes four port modules. `Def_AlgebraicCurve_DivisorPushPull` (735)
  covers ramification/inertia, pushforward, pullback and the fundamental identity;
  it becomes one. The split is recorded in §6.
- **Adopt mathlib's types as the interface from the first declaration.** `Place` is
  FLT's, but it *is* a `ValuationSubring`, and every downstream object
  (`HeightOneSpectrum`, `adicValuation`, `IsDiscreteValuationRing`,
  `Ideal.relNorm`, `RatFunc.inftyValuation`) is mathlib's. Do not invent a parallel
  vocabulary; write monomorphic restatements of the generic mathlib lemma when a
  `rw` needs one (playbook §3.5).
- **Drop the pin's machinery, not its mathematics.** Every `S_` file is ~35%
  `import`/`attribute`/`p2m_*` scaffolding (§4.2); `p2m_open`, `p2m_export`,
  `p2m_reactivate`, `p2m_exact_reverting`, the `[-instance]`/`[-simp]` walls and the
  generated `rowMain`/`solution` pair are all dropped. The statements to match are
  the `Theorems/` wrappers (§7.1).
- **A shared private prelude gets one public home** (playbook §1, "no
  self-consumed lemmas; count before dropping"). Here the dominant case is a
  356-line fibre-centre block that FLT copies into three files; the port writes it
  once (§4.1). A promotion is recorded, not silent.
- **Count before dropping.** The name-referenced fraction of each definition module
  is measured in §2.2; anything not ported gets a `grep -c` count recorded in the
  topic's work order, as FFG does.

## 2. The measured cone

### 2.1 The 65 theorem nodes, by route group

Regenerate with the script in §9.1. `raw` is the whole `S_` file; `content`
excludes imports, `attribute` lines, namespace/`section`/`variable` lines, `p2m_*`
lines, comments and blank lines.

| group | nodes | raw | content |
|---|---|---|---|
| **T1** `Place` ord/valuation interface | 19 | 818 | 399 |
| **T2** fibre dictionary, `fiberOver`, `le_finrank`, `inertiaDeg_pos` | 3 | 1,096 | 834 |
| **T3** Galois ramification/inertia | 7 | 304 | 160 |
| **T4** along-map transport + `Pic0` descent | 16 | 245 | 120 |
| **T5** bifibre count, `card_fiberOver`, `exists_restrict_eq` + the generic orbit/index engine | 5 | 676 | 465 |
| **T6** local exchange + normal closure | 1 | 255 | 174 |
| **T7** divisor exchange (capstone, human) | 1 | 121 | 99 |
| **T8** rational function field `P¹` | 11 | 1,024 | 643 |
| **T9** `HasPrincipalDivisors` via transcendence | 2 | 884 | 641 |
| **total** | **65** | **5,423** | **3,535** |

The T5 row absorbs the blueprint's former `T5g` row: the two generic engine nodes
are proved as part of T5 because their only consumer is its bifibre count. T2 owns
`inertiaDeg_pos` (it consumes the same promoted dictionary but no other T2
declaration); `exists_restrict_eq` and `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`
are T5's, not T1/T4's, because T5 is their first consumer. This assignment is the
one the work orders are written against and it sums to the measured totals.


The two heaviest *developments* are the two halves of one story:
`hasPrincipalDivisors_of_transcendental` (799 raw) and the fibre-centre block
shared by the `sum_ramificationIndex_mul_inertiaDeg_*` files. §4 removes the
duplication; the numbers above do not.

**All 65 are on the proof path.** Every AC node is reachable from the hecke
solution's 16 direct imports (`S_ModularCurve_heckeOperatorsCommuteBar.lean:1-16`),
including the two that looked like trailing corollaries: `le_finrank` (443) and
`inertiaDeg_pos` (214) enter through
`finrankAlong_towerSubstBar_comp_heckeAlphaBar` →
`relfinrank_laurentBaseChange` → `finrank_adjoin_jqNModC_eq_of_prime`. The two
generic group nodes enter through the bifibre count (`T5`). There is no off-path
node to prune.

### 2.2 The 7 definition modules

| module | lines | decls | name-referenced by the cone |
|---|---|---|---|
| `Def_AlgebraicCurve_DivisorClassGroup` | 484 | 72 | 38 |
| `Def_AlgebraicCurve_DivisorPushPull` | 735 | 71 | 18 |
| `Def_AlgebraicCurve_Correspondence` | 346 | 39 | 26 |
| `Def_AlgebraicCurve_PlacesOverDVR` | 506 | 50 | 29 |
| `Def_AlgebraicCurve_RatFuncPlaces` | 397 | 39 | 22 |
| `Def_AlgebraicCurve_BaseChangeGalois` | 355 | 51 | 28 |
| `Def_AlgebraicCurve_RatFuncPlaceInfty` | 44 | 3 | 2 |
| **total** | **2,867** | **325** | **163** |

"Name-referenced" is a lower bound: it greps the AC cone's `S_` files plus the
hecke solution for each module's declaration names, so it sees direct uses but not
declarations reachable only through another definition's statement. The
`DivisorPushPull` number is low (18/70) because its pushforward/pullback lemmas are
mostly invoked from the `Theorems/` wrappers and from `Correspondence`, but those
declarations are load-bearing; the honest reading is "the port takes a majority of
each module and counts the rest per topic". Two declarations the cone needs are not
in these six modules. `Place.ord_algebraMap` lives in
`Def_AlgebraicCurve_ConstantReduction.lean:57` (risk 7) and, with the port's home
decision, goes into `Defs/Place.lean`. `RationalFunctionField.placeInfty` and
`nontrivial_valueGroup_inftyValuation` live in the 44-line
`Def_AlgebraicCurve_RatFuncPlaceInfty.lean`, which the table above omitted; the port
adds it to `Defs/RatFuncPlaces.lean` and to the checker's `SOURCES`.

### 2.3 The outbound interface tier

External indegree = citers *outside* the hecke closure. This is the reusable
library surface, and it is much broader than FFG's concentrated nine-lemma tier:

| ext. | total | raw | declaration |
|---|---|---|---|
| 184 | 189 | 57 | `Place.mem_iff_ord_nonneg` |
| 142 | 143 | 44 | `Place.ord_algebraMap` |
| 106 | 107 | 36 | `Place.mem_of_ord_nonneg` |
| 104 | 108 | 43 | `Place.ord_nonneg_of_mem` |
| 84 | 85 | 12 | `separableAlong_of_charZero` |
| 45 | 46 | 51 | `Place.mem_toValuationSubring_of_isIntegral_adjoin` |
| 34 | 36 | 41 | `Place.exists_restrict_eq` |
| 23 | 24 | 799 | `hasPrincipalDivisors_of_transcendental` |
| 23 | 24 | 23 | `Divisor.pushforwardAlong_pushforwardAlong` |
| 23 | 24 | 22 | `Place.ord_smul_of_ne_zero` |

The four `ord` lemmas plus `separableAlong_of_charZero` are 12–57-line leaves and
carry most of the layer's external weight; T1 and T4 should expose them first, for
the same reason FFG's interface topic came before the heavy proofs.

## 3. The two routes, and the mathlib seam

### 3.1 Route A — the exchange (T1–T7)

`ModularCurve.heckeOperatorsCommuteBar`'s proof calls
`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`
at `S_ModularCurve_heckeOperatorsCommuteBar.lean:42`, on the Hecke roof square.
The 121-line proof reduces, for a single place `wA` of `A`, to the local identity

```lean
AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange
    ... (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
  ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ = w₁.inertiaDeg F * w₂.ramificationIndex F
```

The mathlib content is thin; the work is FLT's own `Place` calculus and a
place-theoretic counting argument. The chain is:

```
T7 divisor exchange  (121)
  └─ T6 local exchange  (255)         -- normal closure `Env F E`, Galois bifibre count
       └─ T5 bifibre  (375)            -- `resHom`/Galois-orbit count over the bifibre
            ├─ T4 card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (47)
            │    └─ T2 sum_..._fiberOver (439)   -- the fibre-centre prelude
            └─ T3 Galois ramification (SemilinearAut.*, exists_algEquiv_smul_eq_of_restrict_eq)
```

`T4`'s 47-line node is the bridge: it pins the cardinality of a fibre of an
integral extension by the `PlacesOverDVR` fibre-centre equivalence, which is why
`PlacesOverDVR` (506 lines) is in the cone at all.

### 3.2 Route B — principal divisors (`T8`–`T9`)

The exchange lemma's *statement* is unconditional in its degree/principality
hypotheses, but the Hecke instance discharges them, and the one that is not free is
`HasPrincipalDivisors`. `hasPrincipalDivisors_modularFunctionFieldBar` is a direct
premise of the hecke theorem and is proved by FLT in two layers:

1. **T8, the `P¹` case.** For `K` a field, classify the places of `RatFunc K`:
   the finite places are `Place.ofHeightOneSpectrum w` for
   `w : HeightOneSpectrum K[X]` (`finitePlace`, `heightOneSpectrumOfIrreducible`),
   the infinite one is `placeInfty`, and
   `degree_eq_zero_of_forall_eq_ord(_algebraMap)` checks the degree-zero property
   for a principal divisor of a polynomial/rational function. The work is
   `finite_setOf_ord_ne_zero` (the support is finite) and the
   `deg_ofHeightOneSpectrum`/`deg_eq_one_of_forall_ne_ofHeightOneSpectrum` pair
   (residue degree = `p.natDegree`, and degree 1 at infinity).

2. **T9, the finite-extension transfer.** `hasPrincipalDivisors_of_transcendental`
   proves `HasPrincipalDivisors K F` for `K` of characteristic zero and `F` a
   finite separable extension of `K(t)` with `t` transcendental, by showing the
   norm `Ideal.relNorm` of the fibre-centre ideals computes `w.ord` — the
   `relNorm_fiberCenter`/`relNorm_span_singleton`/`ord_norm_eq_sum_fiberOver`
   block — and then transfers finiteness and degree from `P¹`.
   `hasPrincipalDivisors_adjoin_of_transcendental` packages the `adjoin` form.

The whole of T9's 588 content lines, minus the shared fibre-centre prelude, is
real mathematics that mathlib does not have: `Ideal.relNorm` exists, but the
"norm of the fibre-centre is the maximal ideal to the inertia degree" computation
does not.

### 3.3 The two routes are independent after `T2`

`T2`'s fibre-centre block (the 356-line private `fiberCenter` prelude) is used by
*both* routes — by `sum_ramificationIndex_mul_inertiaDeg_fiberOver` and by
`hasPrincipalDivisors_of_transcendental`. After it, Route A (`T3`–`T7`) and
Route B (`T8`–`T9`) share nothing but `T1`. That is the scheduling freedom this
plan has and FFG's does not.

### 3.4 The mathlib seam, measured

mathlib v4.34.0 has no curve theory — survey §4.2: zero hits for `RiemannRoch`,
`genus`, `WeilPairing`, and no function-field places or divisors. The AC cone's
dependence is at exactly two seams, both mathlib's:

- **the valuation/Dedekind seam** — `ValuationSubring` (which `Place` *is*),
  `Valuation`, `IsDiscreteValuationRing`, `HeightOneSpectrum`,
  `HeightOneSpectrum.valuation` / `intValuation` / `adicCompletion`,
  `Ideal.relNorm`, `normalizedFactors`, `Ideal.inertiaDeg'`, `IsRankOneDiscrete`,
  `IsTrivialOn`;
- **the field-theory seam** — `IntermediateField.normalClosure`,
  `IsGalois`, `IsScalarTower`, `Algebra.IsIntegral`, `Module.Finrank`,
  `Polynomial.minpoly`, `Polynomial.aeval`, `RatFunc.inftyValuation` and
  `RatFunc.intDegree`.

Nothing in the cone touches `Scheme`, `CurveModel`, `KaehlerDifferential` or
`IsCurveOver`. The `attribute [-instance] AlgebraicCurve.IsCurveOver.*` lines in
the pin are *disables* inherited from the shared `P2M/Util` prelude, not uses. The
port's import list can therefore stay inside `Mathlib.RingTheory.Valuation.*`,
`Mathlib.RingTheory.DedekindDomain.*`, `Mathlib.FieldTheory.*` and
`Mathlib.FieldTheory.RatFunc.*`, per playbook §7.2 ("do not re-import the whole
library").

One absorbed case worth naming: `Place.adicValuation` is
`v.heightOneSpectrum.valuation F`, so `isEquiv_adicValuation_ofHeightOneSpectrum`
and `ord_eq_neg_log_of_valuationSubring_eq` are mathlib-shaped already;
`RatFunc.inftyValuation` is mathlib's, so
`toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` should be stated against
it, not against a port-local copy.

### 3.5 The mathematical core, and the recorded negatives

The FFG retrospective
([topics/ffg-retrospective.md](topics/ffg-retrospective.md) §3) records that "the
mathematics is three abstract lemmas, not 3.8k lines". The AC cone has the same
shape: the exchange (T6–T7) assembles two statements, and the principal-divisors
theorem (T9) is a third plus the ℙ¹ base case.

- **the fibre-over identity** $`\sum_{w \mid v} e\,f = [F' : F]`$ — mathlib's
  `Ideal.sum_ramification_inertia_eq_finrank` read through the fibre-centre
  dictionary (T2);
- **the orbit-intersection count** $`|H_1x_1 \cap H_2x_2| \cdot |X| = |H_1x_1| \cdot |H_2x_2|`$
  and the **index product** $`H_1H_2 = G`$ — the two generic statements (T5) for
  which mathlib has the orbit–stabiliser and index ingredients but not the
  statements;
- **the norm formula** $`\mathrm{ord}_v(N_{F'/F} f) = \sum_{w \mid v} e\,f\,\mathrm{ord}_w(f)`$
  (T9), built on the fibre-centre dictionary and `Ideal.relNorm`.

The rest of the cone is concretisation: places, divisors, and the two transports
that let these be stated for the modular function fields. Pricing the port is
pricing these routes, not the 4k lines around them.

**Recorded negatives** (searches that found nothing, kept so a future session does
not repeat them):

- mathlib has no `Place`, divisor or curve API (survey §4.2); the whole layer is
  FLT's.
- no mathlib statement of `MulAction.ncard_orbit_inter_orbit_mul_card` or
  `Subgroup.exists_eq_mul_of_index_inf_eq`; only their ingredients
  (`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`,
  `Subgroup.index_inf_le`, `Subgroup.relIndex_mul_index`).
- `Def_AlgebraicCurve_RatFuncPlaces`'s `placeOfPoint` and `Place.Congr` sections
  are **not** used by this cone — they occur only in `attribute [-simp]` noise —
  so leaving them out is a measured saving, not a gap.
- `Ideal.relNorm_eq_pow_of_isMaximal` requires `[PerfectField (FractionRing R)]` in
  v4.34; there is no characteristic-zero variant to reach for, so the port must
  make the instance fire rather than weaken a statement.

## 4. Deduplication, scaffolding, and the measured budget

### 4.1 The shared fibre dictionary — a 4-way copy

`le_finrank` (443) and `fiberOver` (439) are the *same file*: the 401-line block at
lines 24–424 differs only in the `p2m_*` namespace strings and the final
`solution` (a 5-line corollary for `le_finrank`, a 3-line re-export for
`fiberOver`); the diff is 24 lines, all `p2m_*`. That block is four nested
developments:

| sub-block | raw lines | copies |
|---|---|---|
| Uniqueness + ValuationDictionary | 24–206 (183) | 3 |
| ResidueDictionary | 208–378 (171) | **4** |
| Assembly (`sum_..._fiberOver`) | 380–424 (45) | 2 |

The ResidueDictionary also sits at `inertiaDeg_pos.lean:28-198` (171 raw,
byte-identical) and at the head of `hasPrincipalDivisors_of_transcendental`
(the 17-declaration block listed below); the full 24–378 prelude sits in
`le_finrank`, `fiberOver` and `hasPrincipalDivisors_of_transcendental`.

The 17 declarations copied into at least three files are:

`eq_ord_of_addHom_of_nonneg_iff`, `neg_log_valuation_fiberCenter_eq_ord`,
`le_ord_iff_mem_pow_fiberCenter`, `ramificationIndex_eq_ramificationIdx_fiberCenter`,
`toValuationSubringOfRestrictEq`, `coe_toValuationSubringOfRestrictEq`,
`residueOfCenter`, `residueOfCenter_apply`, `ker_residueOfCenter`,
`surjective_residueOfCenter`, `residueFieldEquivQuotientCenter`,
`residueFieldEquivQuotientCenter_mk`, `placeCongrEquiv`, `coe_placeCongrEquiv`,
`restrictResidueFieldEquiv`, `restrictResidueFieldEquiv_residue`,
`inertiaDeg_eq_inertiaDeg_fiberCenter`.

Measured: **2 × 296 + 145 = 737 content lines never written.** This block is not
private mathematics — it is the dictionary between the fibre-centre ideal of
`PlacesOverDVR` and the residue field of a place — so the port promotes it into
one public module (`Defs/PlaceDictionary.lean`) with a single home. That is the
biggest single simplification the AC port has, and it is only possible because the
helpers are `private` in FLT and re-exported by name mangling.

A second duplication is the **`P¹` classification prelude**, copied three times
across `finite_setOf_ord_ne_zero` (196), `subsingleton_setOf_forall_ne_ofHeightOneSpectrum`
(158) and `exists_forall_ne_ofHeightOneSpectrum` (138): a `Place` adic-valuation
bridge (~58 lines), the `PlaceInfty`/`inftyValuation` block (37 lines), and the
`ofHeightOneSpectrum`-or-`placeInfty` dichotomy (11 lines). The first two are
3-way, the dichotomy 2-way: **≈214 content lines never written.** These helpers
are propositionally identical to the public declarations already in
`Def_AlgebraicCurve_RatFuncPlaces`, so the port states them once against the
public names.

Secondary duplication, all measured by cross-file declaration count:

| duplicated | copies | save (content) |
|---|---|---|
| fibre dictionary (full prelude ×2, ResidueDictionary ×1) | 2/2/4 | 737 |
| `P¹` classification prelude | 3/3/2 | 214 |
| `restrict_restrict` (tower restriction) | 3 (`bifiber`, `exchange`, `divisor exchange`) | ≈16 |
| `inertiaDegAlong_congr`, `isIntegral_toAlgHom`, `toAlgHom_comp_toAlgHom`, `ramificationIndex_eq_mul_ramificationIndex_restrict`, `inertiaDeg_eq_mul_inertiaDeg_restrict` | 2 (`bifiber`, `exchange`, renamed `BifibreDev`/`BifibreW2`) | ≈60 |

Two further duplications fall *outside* the 5,210-line cone but matter for the
library: `hasPrincipalDivisors_of_transcendental`'s hard core
(lines 32–751, ~720 lines) is byte-identical to the separate
`S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean`
(lines 31–750), and `deg_ofHeightOneSpectrum`'s `WFf` residue-field block
(file lines 25–118) is a copy of `Def_AlgebraicCurve_RatFuncPlaces:128-232`
(FLT marks the wrapper `P2M.Dup`). The port writes each once.

**Deduplicated `S_` content: ≈2,508 lines** — 3,535 minus the 1,027-line
fibre-dictionary / `P¹`-classification / bifibre duplication, with the 16-line
`restrict_restrict` saving allocated across T4–T7 (which is why the topic table's
column sums to ≈2,520).

### 4.2 Scaffolding never written

Of the 5,423 raw `S_` lines, 1,888 (35%) are imports, `attribute` walls, namespace
/`section`/`variable` lines, `p2m_*` lines, comments and blanks. The `p2m_*`
machinery is FLT-internal namespace surgery (`P2M/Util.lean`); the
`attribute [-instance]`/`[-simp]` walls disable instances that the port either
does not import or wants. None of it is ported. Per-file this is the difference
between the `raw` and `content` columns of §2.1.

### 4.3 The budget

| correction | lines |
|---|---|
| 65-node structural sum (`S_` raw) | 5,423 |
| scaffolding never written | −1,888 |
| fibre dictionary (2 full prelude + 1 `ResidueDictionary` extra copies) | −737 |
| `P¹` classification prelude (3/3/2 copies) | −214 |
| `bifiber`/`exchange` shared prelude | −60 |
| `restrict_restrict` copies | −16 |
| **deduplicated `S_` content** | **≈2,508** |
| 7 definition modules, raw | 2,867 |
| definition declarations the cone does not use (≈45%) | −≈1,270 |
| **deduplicated structural total** | **≈4,060** |

Measured ratios from the first two ports run 1.14–1.64, with the FFG proof topics
clustering at 1.14–1.46. At 1.25–1.45 the port is **≈5.1k–5.9k written lines**.
This is a structural count, not a proof budget — T8 and T9 of FFG both showed
lines are not effort — and each topic re-measures against its own route before it
is priced, per the standing rule (PORTING-FFG §7.9, playbook §7.3).

The size is comparable to the FFG remainder, and that is the honest headline: the
AC layer is a *library* port, so a larger fraction of what it writes is reusable
outside the hecke cone (§2.3) than FFG's remainder was.

### 4.4 The budget unit is the named shape risk

The FFG retrospective
([topics/ffg-retrospective.md](topics/ffg-retrospective.md) §6) is explicit that
"cost is shape risk, not line count": its Layer 0 budgeted 20 rounds and took 1,
its 2,002-line T19 was the right size while its *route* was the whole decision,
and its one unplanned adaptation was a single mathlib signature change. The line
count above is context, not the budget. Each topic's work order must open with its
route decision, and progress should be tracked in the named shape risks below.

| topic | named shape risks (what can actually stall it) |
|---|---|
| **AC0** | the `Place`↔`ValuationSubring`↔`HeightOneSpectrum` bridge chosen once; the `@[reducible]` `valuationSubringAlgebra`/`integralClosureAt`; `abbrev` unfolding |
| **T1** | the `exp`/`log` `rfl` identifications; the deprecated `Ideal` aliases; `DecidableEq` |
| **T2** | the 4-way dictionary's `letI`/`haveI` walls; the reducibility the `IsFractionRing` instance needs |
| **T3** | `SemilinearAut`'s `MulSemiringAction`; mathlib's `Ideal.exists_smul_eq_of_isGaloisGroup`/`galRestrict` |
| **T4** | the `algebraAlong` definitional unfolding that the `eA`/`fB`/`fF`/`eF` `rfl` bridges depend on |
| **T5** | the orbit-intersection count and the index product (no mathlib statement); the `resHom`/`MulAction` packaging |
| **T6** | the normal-closure instance block (`Env`, `algebraEnv`, six `IsScalarTower`s) |
| **T7** | `Finsupp.addHom_ext` + `Finset.sum_apply'` plumbing; `DecidableEq (Place K E)` |
| **T8** | Ostrowski in mathlib's shape; the `P2M.Dup` duplicate; `DecidableEq (RatFunc K)` |
| **T9** | `Ideal.relNorm` of the fibre-centre; the `normalizedFactors` factorisation; `PerfectField` firing |

Two predicted **non-events** are recorded so they are not budgeted for: the
`p2m_*`/`attribute` scaffolding is dropped wholesale and cannot bite, and the
"rewrite-search gap" FFG predicted and never hit is not expected here either (the
pin's proofs are already written against the same mathlib API).

## 5. The topics

The cut is by mathematical object, one shared development per topic. Prerequisites
are real dependencies, not the pin's section order.

| topic | object | pin nodes | dedup content | ≈ port | prereq | work order |
|---|---|---|---|---|---|---|
| **AC0** | the vocabulary | 8 def modules | ≈1,550 | ≈1,900–2,200 | mathlib | [SET 1](topics/algebraicCurve/TOPIC-ac0-vocabulary.md) |
| **T1** | `Place` ord/valuation interface | 19 | 399 | ≈520–580 | AC0 | [SET 1](topics/algebraicCurve/TOPIC-t1-ord-interface.md) |
| **T2** | fibre dictionary, `fiberOver`, `le_finrank`, `inertiaDeg_pos` | 3 | 388 | ≈500–570 | AC0, T1 | [SET 1](topics/algebraicCurve/TOPIC-t2-fibre-dictionary.md) |
| **T3** | Galois ramification/inertia | 7 | 160 | ≈210–240 | AC0, T1, T2 | [SET 1](topics/algebraicCurve/TOPIC-t3-galois-ramification.md) |
| **T4** | along-map transport + `Pic0` descent + the shared prelude | 16 | 120 | ≈160–190 | AC0, T1, T2, T3 | [SET 1](topics/algebraicCurve/TOPIC-t4-transport.md) |
| **T5** | bifibre count + the generic orbit/index engine | 5 | 410 | ≈560–650 | T2, T3, T4 | [SET 2](topics/algebraicCurve/TOPIC-t5-bifibre.md) |
| **T6** | local exchange + normal closure | 1 | 174 | ≈230–270 | T4, T5 | [SET 2](topics/algebraicCurve/TOPIC-t6-local-exchange.md) |
| **T7** | divisor exchange (**capstone, human**) | 1 | 99 | ≈130–160 | T6 | [SET 2](topics/algebraicCurve/TOPIC-t7-divisor-exchange.md), **done by the reviewer** |
| **T8** | `P¹` places and degree | 11 | 429 | ≈560–680 | AC0, T1 | [SET 2](topics/algebraicCurve/TOPIC-t8-ratfunc-degree.md) |
| **T9** | `HasPrincipalDivisors` via transcendence | 2 | 345 | ≈450–540 | T8, T2 | [SET 2](topics/algebraicCurve/TOPIC-t9-transcendence.md) |
| **total** | | **65** | **≈2,520** | **≈5.1k–5.9k** | | |

T3's prerequisite list now names T2: `exists_algEquiv_smul_eq_of_restrict_eq` consumes
the promoted fibre dictionary (`fiberCenter`, `mem_fiberCenter_iff_ord_pos`,
`eq_of_fiberCenter_eq`), which the earlier dependency sketch missed. AC0 is eight
definition modules, not six: `RatFuncPlaceInfty` is added (see §2.2) and
`Place.ord_algebraMap` lands in `Defs/Place.lean`. T5 absorbs the former `T5g` row;
T2 owns `inertiaDeg_pos`, T5 owns `exists_restrict_eq` and
`card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`.

### 5.1 SET 2's measured outcomes

| topic | module(s) | port lines | public decls | note |
|---|---|---|---|---|
| T5 | `FieldTheory/FiniteGroupAction` + `WeilExchange/Bifibre` | 264 + 361 | 2 + 12 | the two generic statements transcribed unchanged (scout 3.2 s); 7 helpers `private` |
| T6 | `WeilExchange/LocalExchange` | 206 | 3 | `Env`/`algebraEnv`/`isScalarTower_env_*` `private`; the two stages public |
| T8 | `PrincipalDivisors/RatFuncDegree` | 435 | 10 | `deg_ofHeightOneSpectrum` was already AC0's, so 10 of 11 nodes are new; no `'`-copy prelude |
| T9 | `PrincipalDivisors/Transcendence` | 514 | 4 | the finite-dimensional theorem exposed publicly (§8 risk 9); norm block `private` |

SET 2 wrote **1,780 module lines against the work orders' 1,800–2,140 estimate**
(low end; 2,029 including the consumer). The predicted savings are measured, not
assumed: T8 wrote no `'`-copy prelude (the pin repeats an ≈90-raw-line private
bridge in each of three files and AC0 already publishes all but the dichotomy — a
saving *larger* than §4.1's ≈214 estimate), and T9 restated none of T2's ≈350-line
dictionary.

Four further drifts and decisions, all recorded in
[logs/ac-port.md](logs/ac-port.md):

- **`RatFunc.inftyValuation` now takes `[DecidableEq (RatFunc F)]`** in v4.34, so
  T8's private `WFg` helper carries it and `deg_eq_one…` opens `classical`;
  `Polynomial.degree_sub_lt` is deprecated → `degree_sub_lt_left`;
  `UniqueFactorizationMonoid.prime_of_normalized_factor` and
  `IntermediateField.finiteDimensional_adjoin` are the new names.
- **T9's `PerfectField` fired with no help** (§8 risk 5): a private
  `CharZero v.toValuationSubring` instance plus `IsFractionRing.charZero` →
  `PerfectField.ofCharZero`. No statement weakened, no hypothesis added.
- **The norm block is irreducible to mathlib `relNorm` lemmas** — the §10 question's
  measured negative: mathlib has `relNorm`, `Ideal.relNorm_eq_pow_of_isMaximal` and
  `Ideal.relNorm_singleton`, but not the fibre-centre inertia computation nor the
  `normalizedFactors` factorisation. Keeping the block was right.
- **One statement divergence, resolved in the wrapper's favour:**
  `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber`'s wrapper makes the
  compositum explicit (`{K F F₁ F₂ E} (M : Type*) …`) where the `S_` file binds
  `M` implicitly, so the five T5 wrappers are listed **before** the pin's `bifiber`
  `S_` file in `SOURCES`. No port statement mismatched its wrapper at the end.

Notes that change the shape of a topic:

- **AC0 is a definitions layer and gets the FFG Layer-0 treatment.** Transcribe
  bottom-up, build after every module, promote the shared prelude once. The
  measured risk is low: it is `structure`/`def`/`abbrev` work over mathlib's
  valuation API, and the pin's own proofs for the ord lemmas are short.
- **T1 is the interface topic and should go first among the proofs.** Four of its
  leaves carry 536 external citers between them (§2.3). It is also where the port
  must decide the `Place`↔`ValuationSubring`↔`HeightOneSpectrum` bridge once.
- **T2 owns the promoted fibre dictionary.** Write `Defs/PlaceDictionary.lean`
  once (the Uniqueness + ValuationDictionary + ResidueDictionary block), then
  `sum_ramificationIndex_mul_inertiaDeg_fiberOver`, then the `le_finrank`
  corollary (`Finset.sum_le_sum_of_subset_of_nonneg` +
  `Place.subset_fiberOver_of_forall_restrict_eq`). `inertiaDeg_pos` and T9 consume
  the same dictionary, which is why it is the first thing to write. The dictionary
  is exactly where the port meets mathlib's ramification theory: the FLT-native
  `Place.ramificationIndex`/`inertiaDeg` are proved equal to `Ideal.ramificationIdx'`/
  `Ideal.inertiaDeg'` of `(fiberCenter F' v hw).asIdeal`, and the assembly applies
  `Ideal.sum_ramification_inertia_eq_finrank` (see risk 4 below on the deprecated
  alias the pin uses).
- **T5 is the hard one and the one to scout before pricing.** It is 452 AC content
  lines plus two generic group nodes, and it is the only new mathematics in the
  sense of a proof mathlib does not already shape. The pin's `bifiber` proof is a
  Galois-orbit argument: `resHom`, a `MulAction (M ≃ₐ[F] M)` on places,
  `card_range_resHom`, `index_range_resHom`, `orbit_range_resHom_eq`,
  `orbit_gal_eq`, and the final `forall_apply_algebraMap_eq_of_adjoin_eq_top`. The
  two generic nodes are `MulAction.ncard_orbit_inter_orbit_mul_card` (165 raw — the
  orbit-intersection count $`|H_1 x_1 \cap H_2 x_2| \cdot |X| = |H_1 x_1| \cdot |H_2 x_2|`$) and
  `Subgroup.exists_eq_mul_of_index_inf_eq` (48 raw — turning the index hypothesis
  into `H₁H₂ = Gal`). mathlib has the orbit–stabiliser ingredients
  (`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`,
  `Subgroup.relIndex_mul_index`) but not these exact statements, so they are real
  work; home them in `FLTForHuman/FieldTheory/FiniteGroupAction.lean` beside
  `CommonRoot.lean`, where the other generic engine lives. Route-check T5 as FFG's
  T9 was route-checked.
- **T6 is where the normal closure enters.** `Env F E :=
  IntermediateField.normalClosure F E (AlgebraicClosure E)`, `isGalois_env`, and a
  block of `IsScalarTower` instances built with `letI`/`algebraEnv`. The
  mathematics is "prove the bifibre count in the Galois case, then reduce the
  separable case to it"; mathlib supplies `IsGalois.tower_top_of_isGalois`,
  `IntermediateField.normalClosure`, `IsAlgClosure.normal` and
  `IntermediateField.isSeparable_iSup`. No `CommonRoot`-style engine lemma is
  needed, but this is the most instance-fragile block in the cone (risk 3).
- **T8's mathematical heart is mathlib's Ostrowski theorem.** The finite/infinite
  dichotomy is `RatFunc.valuation_isEquiv_infty_or_adic`; `placeInfty` is
  `RatFunc.inftyValuation`'s valuation subring, the finite places are mathlib
  `HeightOneSpectrum`s of `K[X]` via `Place.ofHeightOneSpectrum`, and
  `deg_ofHeightOneSpectrum` uses `finrank_quotient_span_eq_natDegree`. What is
  *not* mathlib is the packaging: the `Place`-level dichotomy, the finiteness of
  `{v | v.ord f ≠ 0}`, and the explicit degree-zero divisor
  `single(finitePlace, 1) + single(vinf, -p.natDegree)`. `placeOfPoint` and the
  whole `Place.Congr` section of `Def_AlgebraicCurve_RatFuncPlaces` are **unused**
  here (they appear only in `attribute [-simp]` noise), so T8 should drop them.
- **T8 and T9 are independent of the exchange chain** (only T1/T2 in common) and
  can be scheduled in parallel with T3–T7.
- **T9 is a finite-extension transfer by norms, and its one mathlib risk is
  `PerfectField`.** The route is $`\mathrm{ord}(N_{F'}(f)) = \sum_{w \mid v} \mathrm{inertiaDeg}(w)\cdot \mathrm{ord}_w(f)`$,
  built from `relNorm_fiberCenter` / `relNorm_span_singleton` /
  `ord_norm_algebraMap_integralClosureAt` / `ord_norm_eq_sum_fiberOver`, then
  transferred to the `P¹` case. In v4.34.0 `Ideal.relNorm_eq_pow_of_isMaximal`
  requires `[PerfectField (FractionRing R)]`; the pin supplies only `[CharZero F]`,
  so the port must make `PerfectField` fire (characteristic zero implies perfect).
  The pin also has a *separate* `_of_isSeparable` route using `sum_ramification ×
  inertia` and `Divisor.degree_eq_sum`; do not fold it into T9 unless it is needed.

## 6. Module layout

One directory per theory, shared vocabulary in `Defs/`, per playbook §8. The area
`AlgebraicCurve/` is new; the Hecke-exchange theory and the principal-divisors
theory sit beside each other.

```text
lean/FLTForHuman/AlgebraicCurve/
  Defs/
    Place.lean            -- Place, ResidueField, deg, adicValuation, ord (+ basic ord lemmas)
    Divisor.lean          -- Divisor, degree, degZero, IsPrincipal, principal, HasPrincipalDivisors
    PushPull.lean         -- ramificationIndex, restrict, inertiaDeg, pushforward, pullback, fiber, FundamentalIdentity, SumRamificationInertia
    PlacesOverDVR.lean    -- center, integralClosureAt, fiberCenter, placeOfPrime, fiberEquiv, fiberOver, card_fiberOver_eq, fiber_eq_fiberOver
    PlaceDictionary.lean  -- the promoted Uniqueness + ValuationDictionary + ResidueDictionary block (T2/T5/T9)
    Correspondence.lean   -- algebraAlong, FiniteAlong, finrankAlong, pullbackAlong, pushforwardAlong, restrictAlong, ramificationIndexAlong, inertiaDegAlong, SeparableAlong, fiberAlong
    SemilinearAut.lean    -- SemilinearAut + the Place action and its ord/ramification/inertia lemmas
    RatFuncPlaces.lean    -- adic bridge, heightOneSpectrumOfIrreducible, placeInfty, deg_ofHeightOneSpectrum
  WeilExchange/
    FiberOverCount.lean   -- T2
    GaloisRamification.lean -- T3
    Transport.lean        -- T4 (incl. the shared prelude T5/T6/T7 import)
    Bifibre.lean          -- T5 (incl. the orbit/index argument)
    LocalExchange.lean    -- T6
    DivisorExchange.lean  -- T7
  PrincipalDivisors/
    RatFuncDegree.lean    -- T8
    Transcendence.lean    -- T9
lean/FLTForHuman/FieldTheory/
    FiniteGroupAction.lean -- T5's two generic engine nodes, beside CommonRoot.lean
lean/spec/
  AlgebraicCurveConsumer.lean   -- the consumer; outside every library
```

Two layout decisions made when SET 1's work orders were written:

- **T1 has no `OrdInterface.lean`.** The FFG interface-tier precedent
  (`functionFieldGeneration/TOPIC-interface-tier.md` §1) settled that the interface
  is a *usage* property and the modules are named for *mathematical roles*, so a
  lemma goes beside the object it is about: T1's declarations live in
  `Defs/Place.lean` (the `ord`/valuation leaves and `Place.ord_algebraMap`),
  `Defs/RatFuncPlaces.lean` (the `ofHeightOneSpectrum` bridge) and a new
  `Defs/IntegralAdjoin.lean` (the three generic `isIntegral_adjoin_*` transport
  facts, also consumed by T5 and T9).
- **`Defs/PlaceDictionary.lean` holds the whole 17-declaration block, public.** The
  pin keeps it `private` in four files; the checker verifies the promoted names
  through its dotted fallback, so no `OWN_PROOFS` exemption is needed. T2 writes the
  single copy of the Assembly in `WeilExchange/FiberOverCount.lean`.

`Defs/SemilinearAut.lean` and `Defs/RatFuncPlaces.lean` are the two pin modules
the port can trim, and both trims are measured. From
`Def_AlgebraicCurve_BaseChangeGalois` (355 lines) the cone needs `SemilinearAut`,
its `Place` action, and `ord_smul`/`deg_smul`; the whole `Divisor`/`Pic0`
action-and-torsion section (lines 203–355, including `torsionRep`) is for other
consumers. From `Def_AlgebraicCurve_RatFuncPlaces` (397 lines) the cone needs the
adic-valuation bridge, `isEquiv_adicValuation_ofHeightOneSpectrum`,
`ord_ofHeightOneSpectrum_ne_zero_iff`, `heightOneSpectrumOfIrreducible`,
`placeInfty`/`inftyValuation`, and one copy of the residue-field equivalence plus
`deg_ofHeightOneSpectrum`; **`placeOfPoint` and the entire `Place.Congr` section
(lines 236–391) are unused** — they occur only in the pin's `attribute [-simp]`
noise, which a non-attribute grep confirms. `finitePlace`/`deg_finitePlace` can be
dropped too: T5's `degree_eq_zero_of_forall_eq_ord_algebraMap` defines a local
`finitePlace` and the pin's `deg_ofHeightOneSpectrum` and its `Def_` copy are the
same development shipped twice (the wrapper is marked `P2M.Dup`), so write one.

`Def_AlgebraicCurve_DivisorClassGroup` also carries a Galois `SMul` on `Place`,
`Divisor` and `Pic0` and the `Pic`/`Pic0`/`torsion`/`AbelJacobiCard` block. The
exchange cone needs **none** of the Galois `≃ₐ`-action (`F ≃ₐ[K] F`, a different
action from `Defs/SemilinearAut.lean`'s `SemilinearAut K F`; both serve the modular
Hecke/Galois-rep layer, not this one). From the `Pic`/`Pic0` block it
needs only `Pic0.mk`/`mk_surjective` — needed for T4's `Pic0` descent — not `Pic`,
`torsion` or `AbelJacobiCard`. The `zsmul_mk`/`mk_eq_zero_iff`/`addOrderOf` lemmas
T4 uses are separate cone nodes, not part of that block.

Directory and namespace differ on purpose, as in FFG: the path is
`...AlgebraicCurve.WeilExchange.LocalExchange`, the declarations are
`AlgebraicCurve.*`.

### 6.1 What is deliberately not cut

Following the FFG retrospective's §5, the port records what it leaves in place
rather than golfing:

- **The `relNorm`/`normalizedFactors` block of T9.** FFG's `rval_aux` was measured
  at ~64% irreducible and only ~50 lines were recovered by cleanup; the AC analogue
  is T9's norm computation, presumed irreducible until §10's route audit says
  otherwise. Golfing it without that audit would be a false economy.
- **The parts of the pin definition modules other consumers need.** The Galois
  `≃ₐ`-action on `Place`/`Divisor`/`Pic0`, the
  `Pic`/`Pic0`/`torsion`/`AbelJacobiCard` block, `SemilinearAut`'s action on
  `Pic0`-torsion and `Place.finite_setOf_forall_mem_and_ord_pos` are outside this
  cone but are real API for the modular Hecke/Galois-rep and Riemann–Roch layers.
  They are deferred, not judged worthless.
- **`placeOfPoint`/`Place.Congr`** is the one genuine cut, and it is measured
  (unused; attribute noise only), not assumed.
- **`Place.card_fiberOver_eq` and `Place.fiber_eq_fiberOver`** are deferred with a
  `grep -c 0` in the corpus. SET 1 did not write them; T5's
  `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` is their first plausible
  consumer, so T5 may re-add the first. `finite_setOf_forall_mem_and_ord_pos` is
  deferred the same way (Riemann–Roch API, not this cone).
- **Repo-wide prelude dedup.** The AC port writes the fibre dictionary once for its
  own cone; deduplicating the whole `AlgebraicCurve` layer across FLT is a larger,
  separate effort.

## 7. Verification

The instruments are the ones FFG built; nothing new is required.

### 7.1 The statement checker

`spec/check_flt_statements.py` currently diffs 293 FFG declarations against the
pin. The AC effort appends its `Theorems/Thm_AlgebraicCurve_*.lean` wrappers to
`SOURCES` — most of the 63 AC nodes have one, as do the two generic engine nodes
(`Theorems/Thm_MulAction_ncard_orbit_inter_orbit_mul_card.lean`,
`Theorems/Thm_Subgroup_exists_eq_mul_of_index_inf_eq.lean`) — and for the promoted
private dictionary the comparison falls back to the dotted `S_` name exactly as it
does for FFG's promotions. Four refinements carry over from the FFG record:

- **the checker's `norm` must strip `AlgebraicCurve.` as well as `ModularCurve.`**
  (it currently strips only the latter); without it every AC statement written
  under `namespace AlgebraicCurve` diffs against the pin's unqualified wrapper;
- the AC definition modules are diffed against `Definitions/Def_AlgebraicCurve_*.lean`,
  appended **after** every existing source (the checker keys by last name component
  and first occurrence wins); `Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean`
  is one of them (see §2.2);
- take the declaration's binders from the `Theorems/` wrapper, not the `S_` file
  (playbook §7.4); the wrappers above are the source of the statements in §3;
- the pin uses `P2M.Dup.AlgebraicCurve.*` aliases for a handful of
  `RationalFunctionField` statements (`deg_ofHeightOneSpectrum` is one) as a
  `#p2m_type_eq_warn` check; match the *unaliased* `AlgebraicCurve.*` name;
- every declaration the port *authors* rather than transcribes goes on an explicit
  exemption list with its reason, so "0 missing" keeps meaning something (FFG's
  list is `inputs`/`hall_all`/`gen_prime`). The AC layer is mostly transcription,
  so this list should be short — the promoted dictionary keeps its pinned names
  and is checked by the dotted fallback, not exempted.

**SET 1's measured resolution** (what the above turned into; see
[logs/ac-port.md](logs/ac-port.md) §1.4):

- the two pin `S_` files are appended to `SOURCES` for the declarations that have
  no wrapper: `S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean`
  (the promoted dictionary's dotted fallback) and
  `S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean` (the
  T4 shared prelude — `restrict_restrict`, `isIntegral_toAlgHom`,
  `toAlgHom_comp_toAlgHom`, `inertiaDegAlong_congr`, matched by last name);
- `BaseChangeGalois` is listed **before** `DivisorClassGroup`: the latter carries
  the *dropped* second Galois action whose `smul_def`/`ord_smul`/`deg_smul` share
  last names with the `SemilinearAut` block the port transcribes;
- the one AC `OWN_PROOFS` entry is **`correspondence`**: the pin declares
  `Divisor.correspondence` and `Pic0.correspondence` with the same last name and
  the checker keeps the first, so no ordering can verify the second. Both port
  copies were manually diffed against `Def_AlgebraicCurve_Correspondence.lean`
  and match. The predicted `restrict`/`mk`/`deg`/`ord`/`ext` collisions did not
  bite;
- three AC statements carry the pin's deprecated primed `Ideal` text under
  `set_option linter.deprecated false` (risk 4 above), and the promoted
  dictionary is **16 public declarations plus `eq_ord_of_addHom_of_nonneg_iff`
  kept `private`** — it has no consumer outside `neg_log_valuation_fiberCenter_eq_ord`,
  so the whole-block surface decision settles at "public except the internal
  uniqueness step".

### 7.2 The consumer

`spec/AlgebraicCurveConsumer.lean`, outside every library, with an error count as
the deliverable metric and a cross-module composition as the wire test. Planned
zones:

- **Zone A `[vocab]`** — `Place`, `Divisor`, `Pic0` are inhabited; the
  `Place`/`HeightOneSpectrum`/`ValuationSubring` bridge typechecks; `#check` against
  the pinned signatures.
- **Zone B `[interface]`** — T1's leaves at their pinned statements, plus a
  cross-module wire test: a concrete `ord`/degree computation that consumes a
  `Place` lemma from one port module and a `Divisor` lemma from another.
- **Zone C `[dictionary]`** (after T2) — the promoted dictionary's
  `ramificationIndex_eq_ramificationIdx_fiberCenter` and
  `inertiaDeg_eq_inertiaDeg_fiberCenter` at their pin statements, plus
  `sum_ramificationIndex_mul_inertiaDeg_le_finrank` on an abstract separable
  extension. **Zone D** (T3, `[galois]`) — the Galois action/invariance checks.
  **Zone E** (T4, `[transport]`) — `finiteAlong_comp`/`separableAlong_of_charZero`
  on a concrete tower and a `Pic0` descent. **Zone F `[bifibre]`** (T5) and
  **Zone G `[exchange]`** (T6) — the generic orbit count instantiated concretely,
  and the local exchange on an abstract square. **Zone H `[principal]`** (T8) and
  **Zone I `[transcendence]`** (T9) — the `P¹` classification/degree and
  `HasPrincipalDivisors` composed. **Zone J `[exchange]`** (the human's T7) — state
  `Divisor.pullbackAlong_pushforwardAlong_eq_...`, apply it to an abstract square,
  and compose it with T4's `Divisor.correspondence_correspondence` by discharging
  that theorem's `hex` hypothesis with the capstone.
- **There is no `Spine.lean`-style conditional capstone for AC, and that is a
  finding.** FFG needed one because its capstone had seven unported premises; here
  every premise of T7 is an explicit argument or a `HasPrincipalDivisors` instance
  that T9 *proves*. So the AC work is unconditional, and the analogue of the
  conditional capstone is the consumer itself: Zone J's abstract-square wire test
  fixes the outbound interface, and the only debt (the `ModularCurve` Hecke layer,
  which is out of scope) is named in §0's table rather than bundled.

### 7.3 Axioms, build discipline, definition of done

`#print axioms` on `Divisor.pullbackAlong_pushforwardAlong_eq_...` and on
`hasPrincipalDivisors_of_transcendental` must return only
`propext, Classical.choice, Quot.sound`. Every build runs under
`timeout 60 lake env lean <file>` / `timeout 120 lake build <module>`; a
non-return at 60 s is a blow-up to bisect, never a reason to raise
`maxHeartbeats` (playbook §3.11). `Scratch.lean` (gitignored) carries probes.
**Note the lakefile sets `maxHeartbeats` to 4,000,000 globally**, so a blow-up does
*not* error at the default cap's ~20 s; the `timeout` bound is what quarantines it,
and it is the first thing in every work order.

Definition of done: `lake build` green with 0 warnings and no `sorry`; the AC
consumer at 0 errors; the checker extended and reporting 0 mismatched / 0 missing;
the two `#print axioms` clean; and the **friction log** kept current — the FFG
retrospective calls it the highest-value artifact because it is the one thing not
derivable from the code. At that point every generic input of
`math/009`'s exchange reduction — the Weil exchange lemma, `finiteAlong_comp`,
`separableAlong_of_charZero` and `HasPrincipalDivisors` for the modular function
field — is a ported theorem rather than a reference, and the remaining work on the
note is the ModularCurve Hecke layer of §0.

## 8. Risks, in the order they will bite

1. **T5's Galois-orbit count is the one genuinely new proof — resolved, and it was
   cheap.** Everything else is transcription against a mathlib API; the bifibre
   argument re-derives an orbit-stabiliser count in a place-theoretic setting, and
   its two generic engine nodes (`MulAction.ncard_orbit_inter_orbit_mul_card`,
   `Subgroup.exists_eq_mul_of_index_inf_eq`) have no direct mathlib statement. SET 2
   ran the work order's scout gate first: the pin's proof of both statements
   **transcribed unchanged** against mathlib v4.34's orbit–stabiliser API
   (`MulAction.index_stabilizer`/`index_stabilizer_of_transitive`,
   `QuotientGroup.eq`, `Equiv.sigmaFiberEquiv`, `Subgroup.card_mul_index`) in a
   **3.2 s** `Scratch.lean` build, all seven private helpers unchanged. This is the
   strongest instance yet of the FFG rule that *statements dictated ⇒ cheap*, even
   for a generic proof mathlib does not have: the cost was the transcription, not
   the mathematics. Recorded as a positive, not a lucky escape.
2. **The `Place`↔mathlib bridge is a one-time decision in AC0/T1.** `Place` wraps
   a `ValuationSubring` with an `isPrincipalIdealRing'` field that `placeOfPrime`
   needs, plus a bespoke `Algebra`/`IsScalarTower` pair; the classification proofs
   cross between `v.toValuationSubring` and `(v.adicValuation).valuationSubring`
   via `Place.ext` and `Valuation.isEquiv_iff_valuationSubring`. Changing the
   `Algebra` instance breaks `algebraMap` defeq in T9 and T4's `eA`/`fB`/`fF`/`eF`
   bridges. Recommend keeping the FLT shape (a switch to raw
   `HeightOneSpectrum`/`FractionalIdeal` would redo the whole `Place` API, and
   keeping `HasPrincipalDivisors` is the lower-risk fork of the same question).
3. **`letI`/`haveI` instance walls, and reducible definitions they depend on.**
   T6's `Env` block builds `algebraEnv` (marked `@[reducible]`) plus six local
   `Algebra`/`IsScalarTower` instances whose tower proofs are `Subtype.ext` chains;
   T4/T7's setup builds six more from `algebraAlong`. `PlacesOverDVR`'s
   `@[reducible] valuationSubringAlgebra` and `abbrev integralClosureAt` are
   load-bearing for the `IsFractionRing` instance. Transcribe literally, keep the
   reducibility attributes, and expect the module-level `linter.style.haveILetI`
   disable the FFG cone-algebra topics used.
4. **The pin's mathlib aliases are deprecated — and the replacement is *not* a
   rename (measured in SET 1).** `Ideal.inertiaDeg'`, `Ideal.inertiaDeg_algebraMap`,
   `Ideal.inertiaDeg'_pos` and `Ideal.ramificationIdx_spec` warn; their documented
   replacements are `Ideal.inertiaDeg` (different argument order),
   `Ideal.inertiaDeg'_algebraMap` (still primed), `Ideal.inertiaDeg_pos` and
   `Ideal.ramificationIdx'_spec`. `Ideal.ramificationIdx'` is **not** deprecated.
   The pin's `Ideal.sum_ramification_inertia` lives only in
   `Mathlib.NumberTheory.RamificationInertia.Basic`, a **deprecated module** whose
   import warning cannot be silenced (options cannot precede imports), and v4.34's
   `Ideal.sum_ramification_inertia_eq_finrank` changed the statement shape
   (`∑ q : p.primesOver S` with `Fintype`, RHS `Module.finrank R S`, against the
   pin's `∑ P ∈ primesOverFinset p S`, `Module.finrank K L`). The settled handling
   (T2, and T9's norm block): keep the pin's **statement** text so the checker stays
   an exact diff, carry `set_option linter.deprecated false` with a one-line reason
   in the affected module, and migrate the **proofs** using three bridges —
   `IsFractionRing.finrank_eq`, `Finset.sum_subtype` +
   `IsDedekindDomain.coe_primesOverFinset`/`mem_primesOverFinset_iff`, and
   `Ideal.ramificationIdx'_eq_ramificationIdx`/`Ideal.inertiaDeg'_eq_inertiaDeg`.
   The residual item is to migrate the statements themselves at the next pin.
5. **`Ideal.relNorm_eq_pow_of_isMaximal` needs `PerfectField (FractionRing R)` in
   v4.34 — resolved, fired without help.** The pin's T9 supplies only
   `[CharZero F]`; SET 2 installs a private `CharZero v.toValuationSubring`
   instance and `PerfectField (FractionRing v.toValuationSubring)` synthesizes from
   `PerfectField.ofCharZero` via `IsFractionRing.charZero`. No statement weakened,
   no hypothesis added. This is the reason the pin's separate `_of_isSeparable`
   route exists, and it is why T9's norm block should not be merged with it.
6. **Instance diamonds in the `P¹` route — did not materialize.** T8 kept exactly
   one instance set (AC0's), wrote no `'` copies of the
   `IsRankOneDiscrete`/`IsTrivialOn` bridge, and needed no `synthInstance` help;
   `toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` consumes Ostrowski
   (`RatFunc.valuation_isEquiv_infty_or_adic`) directly. The only P¹-route drift
   that did appear was `RatFunc.inftyValuation` now requiring
   `[DecidableEq (RatFunc F)]` (see §5.1).
7. **`Place.ord_algebraMap` lives outside the six modules.** It is at
   `Def_AlgebraicCurve_ConstantReduction.lean:57`, in a heavy unrelated module, and
   is consumed only by T8's base-degree file; port it as a standalone lemma in
   `Defs/Place.lean` (its proof needs only `ord_coe_unit`).
8. **`Finset`/`Finsupp` ext plumbing and `DecidableEq` in T7.** The divisor
   exchange is `Finsupp.addHom_ext` plus `Finset.sum_apply'`; the split needs
   `DecidableEq (Place K E)` for the `Finset.filter` on `fiberAlong`, so keep the
   `classical` open and make the instance explicit if the port's `Place` does not
   synthesize it.
9. **The out-of-cone duplicate — resolved by exposure.**
   `hasPrincipalDivisors_of_transcendental`'s ~720-line core equals
   `S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean` (and
   `deg_ofHeightOneSpectrum`'s `WFf` block equals `Def_RatFuncPlaces:128-232`,
   which AC0 wrote once). SET 2 exposed
   `hasPrincipalDivisors_of_finiteDimensional_ratFunc` publicly and the checker
   verifies it against the pin's second wrapper;
   `deg_ofHeightOneSpectrum` was not rewritten at all.
10. **`HasPrincipalDivisors` is stated at `K`-level, not `ℚ`-level.** The
    statement is generic in `K` of characteristic zero and `F` a finite separable
    extension of `K(t)`. Keep it generic; do not specialise to
    `AlgebraicClosure ℚ` in the port, or the FFG/ModularCurve consumers cannot
    instantiate it.

## 9. Reproduction recipes

### 9.1 Regenerate the cone, the groups and the outbound tier

```bash
cd tools/deps && python3 - <<'PY'
import sys, re
from pathlib import Path
sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); FLT = Path.home() / 'proj' / 'fermats-last-theorem'
def closure(i):
    seen, stack = set(), [i]
    while stack:
        j = stack.pop()
        if j in seen: continue
        seen.add(j); stack.extend(d.cites(j))
    return seen
cap = d.index['ModularCurve.heckeOperatorsCommuteBar']
cl = closure(cap)
ac = [n for n in cl if d.qual(n).startswith('AlgebraicCurve.')]
# the generic engine; the three Polynomial.* nodes are already ported (CommonRoot.lean)
gen = [n for n in cl if not d.qual(n).startswith(('AlgebraicCurve.', 'ModularCurve.', 'Polynomial.'))]
sc = re.compile(r'^\s*(import |attribute |namespace |end\b|open |p2m_open|p2m_export|p2m_alias|p2m_reactivate|section\b|variable\b|#|/-|--|\s*$)')
def raw(i): return sum(1 for _ in open(FLT / f"P2M/Sol/S_{d.stem_of[i]}.lean", encoding='utf-8'))
def content(i):
    return sum(1 for l in open(FLT / f"P2M/Sol/S_{d.stem_of[i]}.lean", encoding='utf-8') if not sc.match(l))
for n in sorted(ac, key=lambda n: -raw(n)):
    ext = sum(1 for j in d.cited_by[n] if j not in cl)
    print(f"{raw(n):5d} raw {content(n):5d} content  ext={ext:4d}  {d.qual(n)}")
print("-- generic engine --")
for n in gen:
    print(f"{raw(n):5d} raw {content(n):5d} content  {d.qual(n)}")
print(f"TOTAL AC={sum(raw(n) for n in ac)}/{sum(content(n) for n in ac)} "
      f"generic={sum(raw(n) for n in gen)}/{sum(content(n) for n in gen)}")
PY
```

### 9.2 Regenerate the definition-module need and the duplication

```bash
cd ~/proj/fermats-last-theorem/P2M/Sol
# the fibre-centre prelude is byte-identical between these two files
diff <(sed -n '17,436p' S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank.lean) \
     <(sed -n '17,436p' S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean) | wc -l   # 24, all p2m_*
```

### 9.3 The two existing surveys

```bash
python3 tools/deps/explore.py ModularCurve.heckeOperatorsCommuteBar   # the note's theorem
```

## 10. Open questions

- **Is AC0 + T1–T7 enough to make the exchange *useful* without T8–T9?** Yes as a
  conditional: `HeckeExchangeAt` is a hypothesis of
  `heckeOperatorsCommuteBar_of_heckeExchangeAt`, so the AC exchange lemma plus the
  free separability/degree inputs reduce the theorem to `hP` and the ModularCurve
  generation/roof facts. If the effort were stopped early, it would be after T7,
  with `HasPrincipalDivisors` left as the bundled hypothesis — the exact analogue
  of FFG's conditional capstone.
- **Does T8 need the full `RatFuncPlaces` public API? — answered: no.** A
  non-attribute grep shows `placeOfPoint` and the whole `Place.Congr` section are
  unused (only `attribute [-simp]` noise), and `finitePlace`/`deg_finitePlace` are
  re-defined locally by the degree file. The remaining choice is which of the two
  copies of `deg_ofHeightOneSpectrum` (the `S_` file's `WFf` block, or
  `Def_RatFuncPlaces:128-232`) to keep; write exactly one.
- **How much of the promoted fibre dictionary should be public? — answered by
  SET 1: public except the internal uniqueness step.** `Defs/PlaceDictionary.lean`
  exposes 16 declarations at the pinned names under `AlgebraicCurve.Place` and
  keeps `eq_ord_of_addHom_of_nonneg_iff` `private` (its only consumer is
  `neg_log_valuation_fiberCenter_eq_ord`). The whole block is verified: the pin's
  `S_..._fiberOver.lean` is in `SOURCES` and the checker matches the promoted
  names by last name / dotted fallback. The narrower-interface option was
  rejected, as the FFG `Defs/PhiAtSlot.lean` precedent suggested.
- **Is there a mathlib `Ideal.relNorm` route that skips the `normalizedFactors`
  block? — answered: no (measured negative).** T9's `relNorm_span_singleton`
  factors an ideal over the fibre-centre primes by hand. SET 2's audit: mathlib has
  `Ideal.relNorm`, `Ideal.relNorm_eq_pow_of_isMaximal` and
  `Ideal.relNorm_singleton`, but not the fibre-centre inertia computation
  (`relNorm (fiberCenter) = maximalIdeal ^ inertiaDeg`) nor the
  `normalizedFactors` factorisation, so none of the ten norm-block declarations is
  reducible. Keeping the block was the right call; the recorded negative saves a
  future search.

## 11. Links

The 63 AC nodes, the two generic engine nodes and their `Theorems/` wrappers are
listed in §2; the seven definition modules and the two studies in the header.
Load-bearing public statements quoted above:

- [`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L10)
- [`AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L10)
- [`AlgebraicCurve.hasPrincipalDivisors_of_transcendental`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean)
- [`AlgebraicCurve.Place.ord_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap.lean)
- [`Def_AlgebraicCurve_DivisorClassGroup`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L224)
- [`Def_AlgebraicCurve_DivisorPushPull`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean)
- [`Def_AlgebraicCurve_Correspondence`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean)
