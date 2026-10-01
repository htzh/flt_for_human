# Mathlib-first substitution audit — P3.6, the K ending (row 6)

**Method:** [`lean/porting-playbook.md`](../../porting-playbook.md) §2.2 (audit the
route, mathlib first), after the phase-1/2/3.1/3.2a–3.2g/3.3a–3.3d/3.4 templates
[`AUDIT-mathlib.md`](AUDIT-mathlib.md) … [`AUDIT-mathlib-p3-4.md`](AUDIT-mathlib-p3-4.md).
Pin: `anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Targets: the row-6 work order
[`WORKORDER-P3-6-kend.md`](WORKORDER-P3-6-kend.md) and
[`../PORTING-RR.md`](../../PORTING-RR.md) §3.

**Sources.** Two pin `S_` files and their `Thm_` wrappers, landing in three new
modules:

- [`P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean)
  (13,170 ln) — the ℙ¹ copy; its only genuinely-new declaration is the
  `solution` one-liner. Home: `FLTForHuman/AlgebraicCurve/ResidueTheorem/KRatFunc.lean`
  (32 ln).
- [`P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean)
  (8,121 ln) — the general-curve K ending. Homes:
  `FLTForHuman/AlgebraicCurve/ResidueTheorem/KCotrace.lean` (760 ln, the engine) and
  `FLTForHuman/AlgebraicCurve/ResidueTheorem/KFamily.lean` (897 ln, the assembly).

Wrappers: [`Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean)
and [`Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean).

**Baseline.** Checker **4071 identical / 0 mismatched / 0 missing / 30 own-proof**
(4101 checked) before this set. Measurement regenerated with
`tools/deps/port_advise.py` (`build/row6_kend_advise.{json,log}`,
`build/row6_ratfunc_advise.{json,log}`; `row6_new.tsv` re-derived).

## 1. Summary — class counts

| file | residual rows | SUBSTITUTE | GENERALISE | KEEP/NEW |
|---|---:|---:|---:|---:|
| `_ratFunc` (13,170 ln) | 1 public | 0 | 0 | 1 wrapper |
| `_of_isAlgClosed` (8,121 ln) | 205 public | 130 (102 importable + 28 pin-private) | 0 | 67 new + 13 private helpers + 4 `Prop` mints + 2 wrappers |
| **total** | | **130** | **0** | **86** |

**Headline.** The `_ratFunc` target is a statement-only wrapper; the `_of_isAlgClosed`
target is a genuine 67-declaration engine (none of the 67 names exist anywhere in the
port, verified by last name over `FLTForHuman/`). The engine's leaves are either
mathlib already (`KaehlerDifferential.map_D`, `range_mapBaseChange`) or port-public
substitutes (the ℙ¹ chain, `Tate/`, `LocalResidue/`); the genuinely new mathematics is
the `regularPoleSubmodule` family, the separator/polar-approximation block, the
cotrace-assembly chain, and the four named `Prop` rows.

## 2. Corrections to the work order and the measurement

**Correction 1 — the `def … : Prop` "substitution" trap list is ten names, not four.**
`port_advise` marks every `def … : Prop` whose *signature* (`: Prop`) is textually
equal to any other as a substitute; its attractor is
`EisensteinWeightOne.E1Chi3IsModular`
(`ModularForms/Defs/EisensteinChiNegThree.lean`). The false positives reported in the
`_of_isAlgClosed` substitution table are:

| pin row | pin ln | status |
|---|---:|---|
| `OrdDifferentialWellDefined` | 2468 | **real substitute** — port `P1/EnginePrelude.lean:102`, statement identical |
| `KaehlerRankOne` | 2955 | **real substitute** — port `P1/DXCoeff.lean:21` |
| `RamificationInertiaIdentity` | 1530 | **real substitute** — port `P1/DXCoeff.lean:55` |
| `IsSeparatingTranscendental` | 4672 | **NEW** — see Correction 2 |
| `FiberKaehlerCotraceResidueIdentity` | 4278 | **NEW** (`AlgebraicCurve` namespace absent) |
| `CotraceResidueIdentityOnFiberLocalized` | 5024 | **NEW** |
| `CotraceFiberLocalizedPolarApprox` | 5034 | **NEW** |
| `KwF4R1V384aCompletionSemilocalBij` | 269 | private in port; re-landed `private` in `Tate/CompletionTraceSum.lean` |
| `KwF4R1V384aDistinctKernels` | 282 | ditto |
| `KwF4R1V384aFinrankCompletionEF` | 288 | ditto |

The three "real substitutes" were confirmed byte-identical by extracting the pin and
port statements with the checker's own parser (the `def : Prop` signature is the whole
comparable text, so this is exactly the checker's relation), and `#check`-ed with

```bash
flock /tmp/flt_for_human.lock timeout 400 lake env lean \
  -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchRow6Audit.lean
```

(`ScratchRow6Audit.lean`, gitignored, deleted after use; exit 0 apart from the
`KaehlerDifferential.map_smul`/`FormallyUnramified.iff_…` probes recorded in §8.)

**Correction 2 — `IsSeparatingTranscendental` is a genuinely different definition,
not a rename of the port's `HasSeparatingTranscendental`.** The pin's row-6 predicate
(pin 4672) is the *differential* form
`KaehlerDifferential.D K F (algebraMap (RatFunc K) F RatFunc.X) ≠ 0`; the port's
`HasSeparatingTranscendental` (`Canonical/HasCanonicalDivisor.lean:918`) is the
*existential* form `∃ t, Transcendental K t ∧ …`. The port has **no** declaration
named `IsSeparatingTranscendental`; it is re-landed at the pin body (the port keeps
both names, since the ℙ¹ chain's own `HasSeparatingTranscendental` is untouched).

**Correction 3 — the 28 pin-`private` "substitutes" are already public in the port but
not importable under the pin's private prelude.** `port_advise`'s "only as a
port-private declaration" list (28 names) are helpers the pin repeats `private` and
the port happens to carry `private` too (`Tate/CompletionTraceSum.lean` `gapsw7_*`/
`kwF4R1V384a_*`, `P1/EnginePrelude.lean` `ord_add_eq_left`, …). The row-6 proof path
reaches only the *public* port analogues, so none is re-landed except the three
`KwF4R1V384a*` `Prop` mints (Correction 1). The port-public analogues used:
`Place.ord_add_eq_min` (`LocalResidue/Calculus.lean:69`, declared
`theorem _root_.AlgebraicCurve.Place.ord_add_eq_min`, public), `Place.exists_ord_pos`
and `Place.mem_of_ord_nonneg`/`mem_iff_ord_nonneg` (`Defs/PushPull.lean`),
`Place.ord_algebraMap`/`ord_eq_neg_log_of_valuationSubring_eq` (`Defs/Place.lean`),
`Place.canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj` and the whole
`poleSubmodule` family (`LocalResidue/Instance.lean`).

**Correction 4 — the port's `ResidueTheoremK` carries an extra auto-bound instance.**
The port's `def ResidueTheoremK` (`Defs/LocalResidue.lean:320`) has an auto-bound
`[∀ v : Place K F, v.DCoordGenerates]` in its elaborated signature (a consequence of
its `differentialCoeff_ne_zero` use), which the pin's `ResidueTheoremK` does not.
Every theorem here whose statement mentions `ResidueTheoremK K E` therefore carries
that instance as a section variable. This does not move any statement text (the
checker diffs source text), but it is the reason `CompositeRatFunc`/`FKCRIProduction`/
`Compose` list `[∀ v : Place K (RatFunc K), v.DCoordGenerates]` explicitly.

## 3. Mathlib ledger (all confirmed in `v4.34.0`)

| constant | role | file |
|---|---|---|
| `KaehlerDifferential.map_D` | `kaehlerCotrace_D` (pin 4364) | `Mathlib/RingTheory/Kaehler/Basic.lean` |
| `KaehlerDifferential.mapBaseChange`, `range_mapBaseChange`, `LinearMap.ker_eq_top` | `surjective_mapBaseChange_of_formallyUnramified` (pin 4791) | ditto |
| `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`, `Algebra.FormallyUnramified.of_isSeparable` | `IsSeparatingTranscendental` discharge (pins 4849/4857) | `Mathlib/RingTheory/Unramified/Basic.lean` |
| `LinearMap.map_smul`, `algebra_compatible_smul` | cotrace/pullback semilinearity (pins 4369/6540) | `Mathlib/Algebra/Algebra/…`, `Mathlib/LinearAlgebra/…` |
| `smul_left_injective` | `kaehlerCotrace_injective_iff_dCoord_ne_zero` (pin 4573) | `Mathlib/LinearAlgebra/…` |
| `ValuationSubring.ofPrime_idealOfLE`, `ofPrime_le_of_le`, `ofPrime_bot`, `ofPrime_top`, `IsLocalRing.eq_maximalIdeal`, `Ideal.IsPrime.isMaximal` | the DVR sandwich `cotpk43_t3_*` (pins 5723–5813) | `Mathlib/RingTheory/Valuation/ValuationSubring.lean`, `…/LocalRing/Basic.lean`, `…/Ideal/Maximal.lean` |
| `Submodule.comap_mono`, `Submodule.mem_iSup_of_directed`, `Submodule.mem_iSup_of_mem`, `Monotone.directed_le`, `Submodule.sum_mem`, `Submodule.sub_mem` | `regularPoleSubmodule` family + the uniform-layer induction | `Mathlib/LinearAlgebra/…`, `Mathlib/Order/…` |
| `SetLike.not_le_iff_exists` | `gf24a9r_exists_ord_pos_ord_neg` | `Mathlib/Order/SetLike.lean` |
| `Finset.sum_fiberwise_of_maps_to`, `sum_subset`, `add_sum_erase`, `sum_induction`, `single_le_sum`, `sum_attach`, `exists_ne_zero_of_sum_ne_zero` | `finsum_place_eq_finsum_fiber_sum` (pin 2693) and the assembly | `Mathlib/Algebra/BigOperators/…` |
| `Ideal.sum_ramification_inertia` | `sum_ramificationIndex_mul_inertiaDeg` (pin 1178) | `Mathlib/NumberTheory/RamificationInertia/Basic.lean` (deprecated; §7) |
| `IsAlgClosed.algebraMap_bijective_of_isIntegral`, `Algebra.IsIntegral.of_finite` | `surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue` (pin 6405) | `Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, `…/IntegralClosure/…` |
| `TensorProduct.induction_on`, `mapBaseChange_tmul` | `exists_kaehlerCotrace_ne_zero_of_formallyUnramified` (pin 4804) | `Mathlib/LinearAlgebra/TensorProduct/…`, Kähler/Basic |
| `Place.poleSubmodule`, `poleSubmodule_mono`, `iSup_poleSubmodule_eq_top`, `exists_mem_poleSubmodule`, `canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj`, `uniformizer_pow_ne_zero`, `ord_uniformizer_pow` | the `regularPoleSubmodule` carrier and the surjection criterion | port `LocalResidue/Instance.lean` |
| `Place.residueTraceCompletionCommute` | the pin's `kwTateRR3_RTCC_of_isSeparable` (byte-identical statement) → `kwTateRR3_residueTheoremK_of_isAlgClosed` | port `Tate/TraceCompletionCommute.lean:106` |
| `AlgebraicCurve.completionTraceSum_of_isSeparable` | the pin's `kwF4R1V386a_completionTraceSum_of_isSeparable` → the `hCTS` of `kw_es_*` | port `Tate/CompletionTraceSum.lean:693` |
| `Place.differentialCoeff_smul_dCoord`, `differentialCoeff_ne_zero`, `ord_mul`, `ord_inv`, `ord_one`, `ord_zpow` | the separation/order algebra | port `Defs/CanonicalDivisor.lean`, `Defs/LocalResidue.lean`, `Defs/PushPull.lean` |

No substitute needed a binder change; all `#check` outputs matched the pin's types.

## 4. Reuse wins and route options

**Route win 1.** `surjective_mapBaseChange_of_formallyUnramified` is **not** mathlib's
`KaehlerDifferential.mapBaseChange_surjective` (whose hypothesis is
`Surjective (algebraMap A B)`, which the pin does not have). It is two lines from
mathlib's `range_mapBaseChange` plus
`FormallyUnramified.subsingleton_kaehlerDifferential` — recorded so the next reader
does not try to force the surjectivity route.

**Route win 2.** The whole general-curve assembly is a *transport of the ℙ¹ theorem*:
the K-currency row (`residueTheoremK_of_cotraceResidueIdentityK`) pushes
`ResidueTheoremK K E` along the fiber identity `FiberKaehlerCotraceResidueIdentityK`,
the base case is the port's `p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main`,
and the top-level commutation is the already-ported
`AlgebraicCurve.residueTraceCompletionCommute`. The pin's `solution` is literally
`kwTateRR3_residueTheoremK_of_isAlgClosed`, so the headline proof is three calls.

**Route win 3.** `gf24a9r_cotraceFiberLocalizedPolarApprox` (152 pin lines) is the
one long new proof; it is the pin's own argument over the `gf24a9r_*` separator
toolkit, carried at the pin's text with the port's `Place` order API.

## 5. Re-landed `private` pieces and promotion debt

**Re-landed `private`: none — and the three `KwF4R1V384a*` `Prop` mints are *not on
the 67-name proof path.** Verified mechanically: for each of the 67 pin bodies
(scaffolding lines removed) none mentions
`KwF4R1V384aCompletionSemilocalBij`/`DistinctKernels`/`FinrankCompletionEF`; the only
occurrences are in the pin's `p2m_reactivate` scaffolding. The path reaches the
port's public `completionTraceSum_of_isSeparable` instead, so re-landing the three
would be dead code (`porting-playbook` §3.1: "no self-consumed lemmas"). They are
recorded as **promotion debt**, not copied:

| pin `S_` ln | row | port home | status |
|---:|---|---|---|
| 269 | `KwF4R1V384aCompletionSemilocalBij` (`private def : Prop`) | `Tate/CompletionTraceSum.lean:269` (private) | not re-landed |
| 282 | `KwF4R1V384aDistinctKernels` (`private def : Prop`) | `Tate/CompletionTraceSum.lean:282` (private) | not re-landed |
| 288 | `KwF4R1V384aFinrankCompletionEF` (`private def : Prop`) | `Tate/CompletionTraceSum.lean:288` (private) | not re-landed |

The port's own `Defs/TateResidueCurrency.lean` is the public home for
`FiberKaehlerCotraceResidueIdentityK`/`CotraceResidueIdentityOnFiberLocalizedK`; the
row-6 file's *no-`K`* `Prop` rows are the genuinely-new ones and are landed publicly
in `KCotrace.lean`. No frozen module was edited.

## 6. Checker delta

**4071 → 4144 identical** (4101 → 4174 checked), still **0 mismatched / 0 missing /
30 own-proof**. The `+73` is exactly the new comparable surface: the 67 row-6 engine
rows, the four named `Prop` mints (`FiberKaehlerCotraceResidueIdentity`,
`CotraceResidueIdentityOnFiberLocalized`, `CotraceFiberLocalizedPolarApprox`,
`IsSeparatingTranscendental`), and the two public headlines
(`residueTheoremK_ratFunc_of_isAlgClosed`, `residueTheoremK_of_isAlgClosed`). The
`promoted from pin-private` count rose 133 → 150 as the 17 public `Place`
`regularPoleSubmodule`/`surjection` rows resolve through the pin's `private`
originals.

## 7. API drift (`v4.34.0`) — what the worker changed

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `Ideal.sum_ramification_inertia` (pin 1182) | deprecated ("use results of `RingTheory.RamificationInertia.Basic`") | kept the pin's call under the existing file deprecation warning; the port's `P1/UnitFinite.lean` proves the same sum from `Ideal.sum_ramification_inertia_eq_finrank`, and a later cleanup can switch. |
| `TensorProduct.induction_on` (pin 4815) | deprecated → `TensorProduct.inductionOn` (different case names) | kept the pin's call (warning); the new name's alternative names do not match the pin's `zero`/`tmul`/`add` arms. |
| `haveI := hO` (pin 5740) | `linter.style.haveILetI` warns on `haveI` in a `Prop` goal | kept the pin's `haveI` (the instance is used by `Ideal.IsPrime.isMaximal inferInstance` and `IsLocalRing.eq_maximalIdeal`); warning only. |
| pin's `p2m_open`/`p2m_export` scaffolding | — | dropped; the required `open`s are spelled explicitly (`open KaehlerDifferential LinearMap Submodule WithZero IsDedekindDomain IsLocalRing ModularCurve.KwF4R1V391a`). |
| pin `set_option maxHeartbeats 6400000/12800000`, `synthInstance.maxHeartbeats …` | project cap `maxHeartbeats := 4_000_000` | dropped; no heartbeat override in any new module. |
| `residueFieldEquivCompletionResidueField`, `KwF4R1V384a*` prelude | port carries them `private` | not transcribed (Promotion debt, §5). |

## 8. Recorded negatives

1. **No mathlib lemma `KaehlerDifferential.map_smul`** (the probe is an unknown
   identifier); the pin uses `LinearMap.map_smul` plus `algebra_compatible_smul`, and
   so does the port.
2. **No `Algebra.FormallyUnramified.iff_subsingleton_kaehlerDifferential`**; the
   usable form is the class projection
   `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`.
3. **No mathlib `IsSeparatingTranscendental`, `FiberKaehlerCotraceResidueIdentity`,
   `CotraceResidueIdentityOnFiberLocalized`, `CotraceFiberLocalizedPolarApprox`,
   `regularPoleSubmodule`, `kwHgfV352_localResidueCompletion`** — all pin-local; the
   port's `Defs/`/`LocalResidue/` copies are the interface.
4. **The ten `def … : Prop` "substitutions" are false positives** (Correction 1); the
   `port_advise` `def`-body blind spot's attractor is
   `EisensteinWeightOne.E1Chi3IsModular`.
5. **No mathlib `KaehlerDifferential.mapBaseChange_surjective` with a
   `FormallyUnramified` hypothesis** — mathlib's version needs
   `Surjective (algebraMap A B)` (Correction/route win 1).

## 9. What this changes for the P3.6 review

**Scope.** `_ratFunc` is 1 statement-only wrapper (`KRatFunc.lean`, 32 ln); the real
set is `_of_isAlgClosed` (1,657 ln across `KCotrace.lean` + `KFamily.lean`) covering
the 67 new declarations, the 4 named `Prop` mints and the public headline. The pin's
8,121 lines are 130 port-public substitutes, 28 pin-private helpers the path does not
need, and the 67-row residual.

**Undischarged rows.** None: the checker is `0 missing / 0 mismatched`, both modules
build, and the two headlines `#print axioms` at
`[propext, Classical.choice, Quot.sound]`.

**Promotion debt.** §5's three `KwF4R1V384a*` `Prop` rows (already private in
`Tate/CompletionTraceSum.lean`, not re-landed). No duplicated public mathematics was
introduced: the four named `Prop` rows are the row-6 file's own canonical-currency
forms (the port's `…K` forms in `Defs/TateResidueCurrency.lean` are the explicit-`Rfam`
twins and stay the interface for the existing Tate theory).

**Residual.** The two `linter.overlappingInstances` warnings on the headline and
`kwTateRR3_*` (`IsCurveOver` already provides `HasPrincipalDivisors`) are inherent to
the wrapper's verbatim binder block and must stay.
