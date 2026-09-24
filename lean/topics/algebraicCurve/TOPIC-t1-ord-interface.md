# T1 — the `Place` ord/valuation interface (19 nodes)

**Status (2026-09-22): work order written, not started.** Second topic of SET 1;
read [SET-1.md](SET-1.md) first (build discipline in §2, conventions in §3, the
checker work in §5). Depends on **AC0**.

**Audience.** A fresh session continuing the `AlgebraicCurve` port after AC0's
`Defs/` vocabulary builds green and consumer Zone A is at 0 errors. The method is
[porting-playbook.md](../../porting-playbook.md) §3–§5; the plan is
[PORTING-AC.md](../PORTING-AC.md) §5 (T1's note) and §8 (risks 2 and 4).

**Goal.** Expose the cone's **outbound interface**: the `ord`/valuation lemmas the
rest of FLT reaches the `AlgebraicCurve` layer through, plus the two generic
`isIntegral (Algebra.adjoin K {j})` transport lemmas and the
`adicValuation`-bridge identities. Nineteen nodes, 818 raw / 399 content `S_`
lines, all leaves or near-leaves. Four of them carry **536 of the layer's external
citers between them** (`mem_iff_ord_nonneg` 184, `ord_algebraMap` 142,
`mem_of_ord_nonneg` 106, `ord_nonneg_of_mem` 104), so this is where the port buys
its library surface.

## 1. Why this topic, and what is settled

- **Settled: the declarations live with their objects, not in an
  `WeilExchange/OrdInterface.lean`.** `PORTING-AC.md` §6 names an
  `OrdInterface.lean` for T1, but the FFG interface-tier topic
  ([functionFieldGeneration/TOPIC-interface-tier.md](../functionFieldGeneration/TOPIC-interface-tier.md) §1)
  settled the general rule the other way: the interface is a *usage* property and
  the modules are named for *mathematical roles*, so a lemma goes beside the object
  it is about. Here that means `Defs/Place.lean` (the `Place`-ord lemmas), a new
  `Defs/IntegralAdjoin.lean` (the three generic `isIntegral_adjoin_*` facts, which
  are pure `Algebra.adjoin`/`IsIntegral` algebra and are also consumed by T5 and
  T9), and `Defs/RatFuncPlaces.lean` (the `ofHeightOneSpectrum` bridge). **Report
  this deviation from the blueprint**; do not create an interface-only module.
- **Settled: statements are the wrappers', verbatim.** All nineteen have a
  `Theorems/Thm_AlgebraicCurve_*.lean` wrapper. The checker is textual, so take the
  binders from the wrapper (§4 below lists them), and use the `S_` file only for
  the proof.
- **Settled: the `Place` shape AC0 chose is not revisited.** If a T1 proof seems to
  need a different shape, stop and report.
- **Settled: `Place.ord_algebraMap` lands in `Defs/Place.lean`,** not in an
  unrelated module. Its pin home is `Def_AlgebraicCurve_ConstantReduction.lean:57`,
  a heavy module the port never imports (`PORTING-AC.md` §8 risk 7); its proof needs
  only `ord_coe_unit`.

## 2. The scouted inventory — all 19, with statements

`raw`/`c` are the `S_` file's raw and content lines; `ext` is external indegree
(citers outside the hecke closure). Every `S_` path is
`P2M/Sol/S_<dotted name with `_`>.lean` and every wrapper is
`Theorems/Thm_<dotted name with `_`>.lean`.

### 2.1 The ord interface — home `Defs/Place.lean`

| declaration | raw/c | ext | pin proof notes |
|---|---|---|---|
| `Place.ord_nonneg_of_mem` | 43/18 | 104 | `IsDiscreteValuationRing.exists_irreducible`, `eq_unit_mul_pow_irreducible`, then `ord_unit_smul_zpow` |
| `Place.mem_of_ord_nonneg` | 36/11 | 106 | `exists_unit_mul_zpow` + `Int.toNat_of_nonneg` + `pow_mem` |
| `Place.mem_iff_ord_nonneg` | 57/28 | 184 | the `rowMain`/`solution` pair; in the port it is one theorem directly |
| `Place.ord_algebraMap` | 44/15 | 142 | private `isUnit_algebraMap`, `adicValuation_algebraMap` via `adicValuation_coe_eq_one_iff`, then `log_one` |
| `Place.ord_smul_of_ne_zero` | 22/15 | 23 | `algebraMap K F c • x`; reduce to `ord_algebraMap`/`ord_mul` |
| `Place.mem_toValuationSubring_of_isIntegral_adjoin` | 51/31 | 45 | private `placeSubalgebra`, `mem_placeSubalgebra`, `valuationSubring_integers`; `IsIntegral.map_of_comp_eq` + `isIntegral_iff_v_le_one` |
| `Place.ord_eq_zero_of_isIntegral_adjoin` | 23/15 | 11 | from the previous two |
| `Place.mem_iff_adicValuation_le_one` | 45/18 | 11 | `v.toValuationSubring.valuation` bridge |
| `Place.mem_maximalIdeal_iff_adicValuation_lt_one` | 53/24 | 2 | `IsLocalRing.mem_maximalIdeal` + the previous |
| `Place.adicValuation_valuationSubring` | 39/14 | 0 | `IsDiscreteValuationRing.exists_lift_of_le_one` |
| `Place.isEquiv_adicValuation_of_valuationSubring_eq` | 48/21 | 0 | `Valuation.isEquiv_iff_valuationSubring` |
| `Place.ord_eq_neg_log_of_valuationSubring_eq` | 54/32 | 13 | a `le_exp_neg_one_of_lt_one` helper over `ℤᵐ⁰`, then `WithZero.log_zpow`/`log_exp` |
| `Place.adicValuation_isRankOneDiscrete` | 31/6 | 0 | **mathlib's instance**: `IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F` (there is no `HeightOneSpectrum.valuation_isRankOneDiscrete`) |
| `Place.adicValuation_isTrivialOn` | 50/21 | 0 | `IsScalarTower` + `placeSubalgebra` |

### 2.2 The `ofHeightOneSpectrum` bridge — home `Defs/RatFuncPlaces.lean`

| declaration | raw/c | ext | pin proof notes |
|---|---|---|---|
| `Place.isEquiv_adicValuation_ofHeightOneSpectrum` | 59/24 | 0 | `Valuation.isEquiv_iff_valuationSubring` + `ofHeightOneSpectrum_toValuationSubring` |
| `Place.ord_ofHeightOneSpectrum_ne_zero_iff` | 79/41 | 3 | `ord = -log ∘ adicValuation`; needs `adicValuation_coe` and the `asIdeal` bridge |

### 2.3 The generic `Algebra.adjoin` transport — home `Defs/IntegralAdjoin.lean`

| declaration | raw/c | ext | pin proof notes |
|---|---|---|---|
| `isIntegral_adjoin_intermediateField_mk` | 44/37 | 21 | `IsIntegral` under the `IntermediateField` subtype; `Subtype` coercion plumbing |
| `isIntegral_adjoin_map_algHom` | 22/16 | 12 | push `IsIntegral` along an `AlgHom` |
| `isIntegral_adjoin_of_isScalarTower` | 18/12 | 10 | `IsIntegral.of_le` along `IsScalarTower` |

Total: 19 nodes, 818 raw / 399 content.

### 2.4 The statements, verbatim from the wrappers

Take these from the wrapper files; they are reproduced here so a mismatch is
visible *before* the checker is run. (`P2M.Dup.AlgebraicCurve.*` in a wrapper
means: match the unaliased `AlgebraicCurve.*` name.)

```lean
theorem AlgebraicCurve.Place.ord_nonneg_of_mem {K F} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f

theorem AlgebraicCurve.Place.mem_of_ord_nonneg {K F} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring

theorem AlgebraicCurve.Place.mem_iff_ord_nonneg {K F} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ≠ 0) : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f

theorem AlgebraicCurve.Place.ord_algebraMap {K F} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0

theorem AlgebraicCurve.Place.ord_smul_of_ne_zero {K F} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x

theorem AlgebraicCurve.Place.mem_toValuationSubring_of_isIntegral_adjoin {K F} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring)
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring

theorem AlgebraicCurve.Place.ord_eq_zero_of_isIntegral_adjoin {K F} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring)
    (hx : IsIntegral (Algebra.adjoin K {j}) x) (hx' : IsIntegral (Algebra.adjoin K {j}) x⁻¹) :
    v.ord x = 0

theorem AlgebraicCurve.Place.mem_iff_adicValuation_le_one {K F} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} : f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1

theorem AlgebraicCurve.Place.mem_maximalIdeal_iff_adicValuation_lt_one {K F} [Field K] [Field F]
    [Algebra K F] (v : Place K F) (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1

theorem AlgebraicCurve.Place.adicValuation_valuationSubring {K F} [Field K] [Field F]
    [Algebra K F] (v : Place K F) : v.adicValuation.valuationSubring = v.toValuationSubring

theorem AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq {K F} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {Γ} [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) : w.IsEquiv v.adicValuation

theorem AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq {K F} [Field K] [Field F]
    [Algebra K F] (v : Place K F) (w : Valuation F (WithZero (Multiplicative ℤ)))
    (hw : w.valuationSubring = v.toValuationSubring) {π : F}
    (hπ : w π = WithZero.exp (-1 : ℤ)) {f : F} (hf : f ≠ 0) : v.ord f = -WithZero.log (w f)

theorem AlgebraicCurve.Place.adicValuation_isRankOneDiscrete {K F} [Field K] [Field F]
    [Algebra K F] (v : Place K F) : v.adicValuation.IsRankOneDiscrete

theorem AlgebraicCurve.Place.adicValuation_isTrivialOn {K F} [Field K] [Field F] [Algebra K F]
    (v : Place K F) : v.adicValuation.IsTrivialOn K

theorem AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum {K F} [Field K] [Field F]
    [Algebra K F] {R} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (Place.ofHeightOneSpectrum (K := K) w).adicValuation

theorem AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff {K F} [Field K] [Field F]
    [Algebra K F] {R} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) {q : R}
    (hq : q ≠ 0) : (Place.ofHeightOneSpectrum (K := K) (F := F) w).ord (algebraMap R F q) ≠ 0 ↔
      q ∈ w.asIdeal

theorem AlgebraicCurve.isIntegral_adjoin_intermediateField_mk {L F} [Field L] [Field F]
    [Algebra L F] (E : IntermediateField L F) {j x : F} (hj : j ∈ E) (hx : x ∈ E)
    (h : IsIntegral (Algebra.adjoin L {j}) x) :
    IsIntegral (Algebra.adjoin L {(⟨j, hj⟩ : E)}) (⟨x, hx⟩ : E)

theorem AlgebraicCurve.isIntegral_adjoin_map_algHom {K F F'} [CommRing K] [CommRing F]
    [CommRing F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') {j x : F}
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin K {φ j}) (φ x)

theorem AlgebraicCurve.isIntegral_adjoin_of_isScalarTower {K L F} [CommRing K] [CommRing L]
    [CommRing F] [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F] {j x : F}
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin L {j}) x
```

## 3. Route notes, so none of this has to be rediscovered

- **Drop the pin's `private`/`rowMain`/`solution` device.** Every `S_` file wraps
  its content as `private theorem foo …` / `private theorem rowMain …` /
  `theorem solution … := …`, the last being what the checker's
  `p2m_exact_reverting` wrapper sees. In the port, write the public theorem
  **directly** with its proof. Keep genuinely reusable support `private` (e.g.
  `placeSubalgebra`, `valuationSubring_integers`, `le_exp_neg_one_of_lt_one`).
- **`ord_nonneg_of_mem` / `mem_of_ord_nonneg` / `mem_iff_ord_nonneg` already exist
  publicly in the pin's `Def_AlgebraicCurve_DivisorPushPull` 22–49.** AC0's
  `Defs/PushPull.lean` ports them as part of the ord/comap interface. **Do not
  write a second copy**: put them in `Defs/Place.lean` (or `Defs/PushPull.lean`) in
  AC0's keep set, and let T1 only add what AC0 left out. If AC0 already wrote both
  halves, T1's `mem_iff_ord_nonneg` is `⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩`.
- **`ord_algebraMap` needs `K` to be a field** (it divides by `c`); the pin proves
  `adicValuation (algebraMap K F c) = 1` for `c ≠ 0` through
  `adicValuation_coe_eq_one_iff` and `IsUnit.map`.
- **`mem_toValuationSubring_of_isIntegral_adjoin` is the one real proof in the
  topic.** The pin builds a `Subalgebra K F` (`placeSubalgebra`) from the
  valuation subring, shows `Algebra.adjoin K {j} ≤ placeSubalgebra`, and applies
  `IsIntegral.map_of_comp_eq` plus `Valuation.Integers.isIntegral_iff_v_le_one`.
  `ValuationSubring.valuation`, `Valuation.Integers` and
  `ValuationSubring.mem_of_valuation_le_one` are mathlib's.
- **`ord_eq_neg_log_of_valuationSubring_eq` needs one `ℤᵐ⁰` helper**
  (`le_exp_neg_one_of_lt_one`): for `x < 1` in `ℤᵐ⁰`, `x ≤ exp (-1)`. Prove it once
  (private), as the pin does. `WithZero.log_zpow`, `log_exp`, `exp_log` are
  mathlib's.
- **`isIntegral_adjoin_*` are generic algebra, not `Place` facts.** They are
  `CommRing` statements; state them exactly as the wrappers do (note
  `isIntegral_adjoin_map_algHom` takes `CommRing` where the other two take `Field`
  — that asymmetry is the pin's and the checker will see it). They will be imported
  by T5 and T9.
- **The pin's `mem_toValuationSubring_of_isIntegral_adjoin` solution body calls
  `ModularCurve.QexpN.mem_of_isIntegral_adjoin`** — a namespace-mangling artefact
  of `p2m_*`. Ignore the reference; the `private` `mem_of_isIntegral_adjoin` above
  it is the proof.
- **The four `Ideal` deprecations do not bite in T1** (they are T2's), but
  `mem_maximalIdeal_iff_adicValuation_lt_one` already touches
  `IsLocalRing.mem_maximalIdeal`; check for warnings.

## 4. What is different about this topic

- **It is mostly exposure of leaves.** Every proof is 6–41 content lines, and the
  pin's proof is written against the same mathlib API. If any of the nineteen turns
  out to need real work, that is a finding (§7): it distinguishes "the interface is
  small" from "the interface looked small".
- **Two of the nineteen are already implied by AC0's keep set** (see §3). The
  topic's measured size is therefore smaller than 399 lines; report the overlap.
- **The checker's last-name problem starts here.** `ord`, `ext`, `degree` are the
  collision-prone components; the four big leaves have distinctive names
  (`mem_iff_ord_nonneg`, `ord_algebraMap`, `mem_of_ord_nonneg`, `ord_nonneg_of_mem`).
  If a wrapper's last name already resolves to a `ModularCurve` declaration, put the
  AC wrapper earlier in `SOURCES` and say so in the log.
- **Consumer Zone B is the wire test.** It must be a cross-module composition: a
  concrete `ord`/degree computation that uses a `Place` lemma from `Defs/Place.lean`
  *and* a `Divisor` lemma from `Defs/Divisor.lean`, discharged for real (the FFG
  `Universal.lean` lesson).

## 5. Budget and stop-early

**2 goal rounds, checkpoint at 1.** Nineteen leaves, two of them already written,
against a build that catches each in seconds. Two is the threshold at which
something structural is wrong.

**Stop early, and report rather than restate, on**: a wrapper statement that will
not elaborate against AC0's `Place` (quote the divergence); a proof needing a
`Place` field or instance AC0 did not provide; or the checker ordering forcing a
choice between two AC declarations with the same last name.

## 6. Definition of done

- [ ] The 19 declarations public, statements verbatim from the wrappers, homes:
      `Defs/Place.lean` (14), `Defs/RatFuncPlaces.lean` (2),
      `Defs/IntegralAdjoin.lean` (3), with any overlap with AC0's keep set removed
      and reported.
- [ ] `WeilExchange/OrdInterface.lean` **not** created (deviation recorded in the
      log and in the report).
- [ ] The four `private` helpers that are genuinely reusable kept `private`
      (`placeSubalgebra`, `mem_placeSubalgebra`, `valuationSubring_integers`,
      `le_exp_neg_one_of_lt_one` — or their equivalents).
- [ ] Consumer **Zone B** at 0 errors, with the cross-module wire test proved.
- [ ] `spec/check_flt_statements.py`: the 19 AC wrappers in `SOURCES`; line
      `N identical, 0 mismatched, 0 missing`.
- [ ] `timeout 90 lake build` green, 0 warnings, no `sorry`.
- [ ] `logs/ac-port.md` T1 section: the **interface table**
      (declaration → external indegree → port module), the measured cost, and any
      overlap with AC0.
- [ ] `PORTING-AC.md` status line not touched; deviations reported.

## 7. Reporting back

Beyond the shared report (§6 of [SET-1.md](SET-1.md)):

1. **The interface table**, re-derived, with the claim checked that T1 now exposes
   most of the layer's outbound indegree mass (the four leaves sum to 536 of the
   189+143+107+108 external citers).
2. **Whether exposure was free.** Name any of the nineteen that took real work.
3. **The overlap with AC0**, exactly which declarations AC0 had already written.
4. **The `Defs/IntegralAdjoin.lean` call**: whether the three generic transport
   lemmas belonged there or were needed earlier by AC0's modules.
