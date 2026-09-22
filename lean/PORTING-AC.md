# Blueprint: the `AlgebraicCurve` layer for `ModularCurve.heckeOperatorsCommuteBar`

**Status (2026-09-22): scoped, not started.** This is the third Lean port and the
first that targets the *generic* curve layer rather than a modular instance. It is
opened as `PORTING-FFG.md` runs down (T19–T20), because the two efforts share the
`ModularCurve/Defs` vocabulary and the same verification machinery, and because
`math/009-hecke-jacobian-commute.md`'s theorem is the natural consumer that makes
the `AlgebraicCurve` layer worth building.

Three records feed this blueprint, all read-only and already written for other
purposes:

- [math/009](../math/009-hecke-jacobian-commute.md) — the mathematics of the
  target. Source of truth for *what the proof says*.
- [studies/hecke-commute-bar-survey.md](../studies/hecke-commute-bar-survey.md) —
  the reduction chain, the two degeneracy maps, the local bifibre identity, and
  §9's list of what the note must not claim.
- [studies/flt-function-field-theory-and-mathlib.md](../studies/flt-function-field-theory-and-mathlib.md) —
  the repository-wide FLT↔mathlib seam map for the curve layer.

Companion records once work starts: `logs/ac-port.md` (the measured record) and
`topics/algebraicCurve/TOPIC-*.md` (one work order per topic). The reusable method
is [porting-playbook.md](porting-playbook.md); this document inherits §7–§8 of it
wholesale and records only what is new.

FLT line numbers and paths are against `anthropics/fermats-last-theorem@aa2d8b3`.
mathlib is our pinned `v4.34.0`.

## 0. Scope, and where this sits under `math/009`

**The target is the whole `AlgebraicCurve` cone of
`ModularCurve.heckeOperatorsCommuteBar`** — measured with the local pin graph
(refresh recipe in §9.1) at **63 `AlgebraicCurve.*` theorem nodes in 5,210 `S_`
lines, 6 `Def_AlgebraicCurve_*` modules in 2,823 lines, and 2 generic
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
is 72 definition modules and 1,577 proof files, and this port takes the 6 + 63 that
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
| **T2** fibre-centre + `fiberOver`/`le_finrank` | 2 | 882 | 684 |
| **T3** Galois ramification/inertia | 7 | 304 | 160 |
| **T4** along-map transport + `Pic0` descent | 16 | 245 | 120 |
| **T5** bifibre count + `exists_restrict_eq` | 4 | 677 | 452 |
| **T6** local exchange + normal closure | 1 | 255 | 174 |
| **T7** divisor exchange | 1 | 121 | 99 |
| **T8** rational function field `P¹` | 11 | 1,024 | 643 |
| **T9** `HasPrincipalDivisors` via transcendence | 2 | 884 | 641 |
| **T5g** generic orbit/index engine | 2 | 213 | 163 |
| **total** | **65** | **5,423** | **3,535** |

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

### 2.2 The 6 definition modules

| module | lines | decls | name-referenced by the cone |
|---|---|---|---|
| `Def_AlgebraicCurve_DivisorClassGroup` | 484 | 72 | 38 |
| `Def_AlgebraicCurve_DivisorPushPull` | 735 | 71 | 18 |
| `Def_AlgebraicCurve_Correspondence` | 346 | 39 | 26 |
| `Def_AlgebraicCurve_PlacesOverDVR` | 506 | 50 | 29 |
| `Def_AlgebraicCurve_RatFuncPlaces` | 397 | 39 | 22 |
| `Def_AlgebraicCurve_BaseChangeGalois` | 355 | 51 | 28 |
| **total** | **2,823** | **322** | **161** |

"Name-referenced" is a lower bound: it greps the AC cone's `S_` files plus the
hecke solution for each module's declaration names, so it sees direct uses but not
declarations reachable only through another definition's statement. The
`DivisorPushPull` number is low (18/70) because its pushforward/pullback lemmas are
mostly invoked from the `Theorems/` wrappers and from `Correspondence`, but those
declarations are load-bearing; the honest reading is "the port takes a majority of
each module and counts the rest per topic". One declaration the cone needs is not
in these six modules at all: `Place.ord_algebraMap` lives in
`Def_AlgebraicCurve_ConstantReduction.lean:57` (risk 7).

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
| 6 definition modules, raw | 2,823 |
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

## 5. The topics

The cut is by mathematical object, one shared development per topic. Prerequisites
are real dependencies, not the pin's section order.

| topic | object | pin nodes | dedup content | ≈ port | prereq |
|---|---|---|---|---|---|
| **AC0** | the vocabulary | 6 def modules | ≈1,550 | ≈1,900–2,200 | mathlib |
| **T1** | `Place` ord/valuation interface | 19 | 399 | ≈520–580 | AC0 |
| **T2** | fibre centre, `fiberOver`, `le_finrank` | 2 | 388 | ≈500–570 | AC0, T1 |
| **T3** | Galois ramification/inertia | 7 | 160 | ≈210–240 | AC0, T1 |
| **T4** | along-map transport + `Pic0` descent | 16 | 120 | ≈160–190 | AC0, T1, T2, T3 |
| **T5** | bifibre count + the generic orbit/index engine | 6 | 410 | ≈560–650 | T2, T3, T4 |
| **T6** | local exchange + normal closure | 1 | 174 | ≈230–270 | T4, T5 |
| **T7** | divisor exchange | 1 | 99 | ≈130–160 | T6 |
| **T8** | `P¹` places and degree | 11 | 429 | ≈560–680 | AC0, T1 |
| **T9** | `HasPrincipalDivisors` via transcendence | 2 | 345 | ≈450–540 | T8, T2 |
| **total** | | **65** | **≈2,520** | **≈5.1k–5.9k** | |

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
    OrdInterface.lean     -- T1
    FiberOverCount.lean   -- T2
    GaloisRamification.lean -- T3
    Transport.lean        -- T4
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

## 7. Verification

The instruments are the ones FFG built; nothing new is required.

### 7.1 The statement checker

`spec/check_flt_statements.py` currently diffs 293 FFG declarations against the
pin. The AC effort appends its `Theorems/Thm_AlgebraicCurve_*.lean` wrappers to
`SOURCES` — most of the 63 AC nodes have one, as do the two generic engine nodes
(`Theorems/Thm_MulAction_ncard_orbit_inter_orbit_mul_card.lean`,
`Theorems/Thm_Subgroup_exists_eq_mul_of_index_inf_eq.lean`) — and for the promoted
private dictionary the comparison falls back to the dotted `S_` name exactly as it
does for FFG's promotions. Two refinements carry over from the FFG record:

- take the declaration's binders from the `Theorems/` wrapper, not the `S_` file
  (playbook §7.4); the wrappers above are the source of the statements in §3;
- the pin uses `P2M.Dup.AlgebraicCurve.*` aliases for a handful of
  `RationalFunctionField` statements (`deg_ofHeightOneSpectrum` is one) as a
  `#p2m_type_eq_warn` check; match the *unaliased* `AlgebraicCurve.*` name.

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
- **Zone C `[exchange]`** — state `Divisor.pullbackAlong_pushforwardAlong_eq_...`
  and apply it to a concrete abstract square (the `algebraAlong`/`IsScalarTower`
  setup is itself the wire test), then compose with
  `Pic0.correspondence_correspondence_comm`.
- **Zone D `[principal]`** — `HasPrincipalDivisors K (RatFunc K)` and the
  transcendence statement, and a composition of the two.
- **Zone E `[hecke-inputs]`** — the conditional capstone: package the AC
  hypotheses that `HeckeExchangeAt` needs (`hP`, `hsep`, and the exchange at every
  roof) and show they imply `HeckeExchangeAt` *given* the ModularCurve layer as a
  hypothesis. This is the AC-side analogue of FFG's `Spine.lean`: it fixes the AC
  port's outbound interface before the heavy proofs land.

### 7.3 Axioms, build discipline, definition of done

`#print axioms` on `Divisor.pullbackAlong_pushforwardAlong_eq_...` and on
`hasPrincipalDivisors_of_transcendental` must return only
`propext, Classical.choice, Quot.sound`. Every build runs under
`timeout 60 lake env lean <file>` / `timeout 120 lake build <module>`; a
non-return at 60 s is a blow-up to bisect, never a reason to raise
`maxHeartbeats` (playbook §3.11). `Scratch.lean` (gitignored) carries probes.

Definition of done: `lake build` green with 0 warnings and no `sorry`; the AC
consumer at 0 errors; the checker extended and reporting 0 mismatched / 0 missing;
and the two `#print axioms` clean. At that point every generic input of
`math/009`'s exchange reduction — the Weil exchange lemma, `finiteAlong_comp`,
`separableAlong_of_charZero` and `HasPrincipalDivisors` for the modular function
field — is a ported theorem rather than a reference, and the remaining work on the
note is the ModularCurve Hecke layer of §0.

## 8. Risks, in the order they will bite

1. **T5's Galois-orbit count is the one genuinely new proof.** Everything else is
   transcription against a mathlib API; the bifibre argument re-derives an
   orbit-stabiliser count in a place-theoretic setting, and its two generic engine
   nodes (`MulAction.ncard_orbit_inter_orbit_mul_card`,
   `Subgroup.exists_eq_mul_of_index_inf_eq`) have no direct mathlib statement. Scout
   it before pricing, and if the route is expensive but the clarity gain real, take
   the route and record the cost, as FFG's T9 did.
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
4. **The pin's mathlib aliases are deprecated.** `Ideal.sum_ramification_inertia`
   (`le_finrank:388`), `Ideal.ramificationIdx_spec` (`:197`),
   `Ideal.inertiaDeg_algebraMap` (`:352`) and `Ideal.inertiaDeg'_pos`
   (`inertiaDeg_pos:213`) are deprecated in v4.33/v4.34; write the port against
   `Ideal.sum_ramification_inertia_eq_finrank`, `Ideal.ramificationIdx'`,
   `Ideal.inertiaDeg'` and the new unprimed API from the first declaration, or the
   library carries warnings now and breaks at the next pin.
5. **`Ideal.relNorm_eq_pow_of_isMaximal` needs `PerfectField (FractionRing R)` in
   v4.34.** The pin's T9 supplies only `[CharZero F]`; the port must let
   `PerfectField` fire (a characteristic-zero field is perfect) rather than weaken
   the statement. This is the reason the pin's separate `_of_isSeparable` route
   exists, and it is why T9's norm block should not be merged with it.
6. **Instance diamonds in the `P¹` route.** `Def_AlgebraicCurve_RatFuncPlaces:34-39`
   declares global `IsRankOneDiscrete`/`IsTrivialOn` instances for
   `adicValuation`; the pin's `S_` files disable them and re-prove `'` copies in
   three files. The port must have exactly one instance set, or `synthInstance`
   loops — the pin's sibling separable route already needs
   `synthInstance.maxHeartbeats 1600000`.
7. **`Place.ord_algebraMap` lives outside the six modules.** It is at
   `Def_AlgebraicCurve_ConstantReduction.lean:57`, in a heavy unrelated module, and
   is consumed only by T8's base-degree file; port it as a standalone lemma in
   `Defs/Place.lean` (its proof needs only `ord_coe_unit`).
8. **`Finset`/`Finsupp` ext plumbing and `DecidableEq` in T7.** The divisor
   exchange is `Finsupp.addHom_ext` plus `Finset.sum_apply'`; the split needs
   `DecidableEq (Place K E)` for the `Finset.filter` on `fiberAlong`, so keep the
   `classical` open and make the instance explicit if the port's `Place` does not
   synthesize it.
9. **The out-of-cone duplicate is a library-consolidation win, not a cone saving.**
   `hasPrincipalDivisors_of_transcendental`'s ~720-line core equals
   `S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean`, and
   `deg_ofHeightOneSpectrum`'s `WFf` block equals `Def_RatFuncPlaces:128-232`;
   expose the finite-dimensional theorem publicly once so both consumers share it.
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
- **How much of the promoted fibre dictionary should be public?** It has low
  external indegree (it is `private` in all four pin copies), but T2, T5 and T9 all
  consume it, so it gets one home (`Defs/PlaceDictionary.lean`). The open part is
  the surface: the FFG precedent (`Defs/PhiAtSlot.lean`) exposes the whole block
  and lets the checker verify it; a narrower interface (only
  `inertiaDeg_eq_inertiaDeg_fiberCenter` and `ramificationIndex_eq_ramificationIdx_fiberCenter`)
  would be smaller but would leave the uniqueness and residue-iso lemmas private
  and unverified. Decide when the module is written, and record the `grep -c`.
- **Is there a mathlib `Ideal.relNorm` route that skips the `normalizedFactors`
  block?** T9's `relNorm_span_singleton` factors an ideal over the fibre-centre
  primes by hand. mathlib has `Ideal.relNorm`, `Ideal.inertiaDeg'` and
  `Ideal.count_normalizedFactors_eq`; whether the 100-line block is reducible to a
  mathlib `relNorm`-of-a-power lemma is the one "route not mathematics" question
  in T9, and should be audited the way T19's slot counting was.

## 11. Links

The 63 AC nodes, the two generic engine nodes and their `Theorems/` wrappers are
listed in §2; the six definition modules and the two studies in the header.
Load-bearing public statements quoted above:

- [`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L10)
- [`AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L10)
- [`AlgebraicCurve.hasPrincipalDivisors_of_transcendental`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean)
- [`AlgebraicCurve.Place.ord_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap.lean)
- [`Def_AlgebraicCurve_DivisorClassGroup`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22-L224)
- [`Def_AlgebraicCurve_DivisorPushPull`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean)
- [`Def_AlgebraicCurve_Correspondence`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean)
