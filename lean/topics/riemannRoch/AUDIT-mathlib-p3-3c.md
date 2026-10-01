# Mathlib-first substitution audit — P3.3c, the Tate agreement

**Method:** [`lean/porting-playbook.md`](../porting-playbook.md) §2.2 (audit the route,
mathlib first), after the phase-1/2/3.1/3.2a–3.2f and 3.3a templates
[`AUDIT-mathlib.md`](AUDIT-mathlib.md) … [`AUDIT-mathlib-p3-3a.md`](AUDIT-mathlib-p3-3a.md).
Pin: `anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Work order target: [`PLAN-P3-3.md`](PLAN-P3-3.md) §1–§2.
Pre-port measurement: [`tools/deps/build/p33c_advise.log`](../../../tools/deps/build/p33c_advise.log)
and its `.json`.

**Sources.** One pin `S_` file and its `Thm_` wrapper, ported to the new
`FLTForHuman/AlgebraicCurve/Tate/Agreement.lean`:

- [`P2M/Sol/S_AlgebraicCurve_tateAgreement.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean)
  (4,816 ln, 173 checked declarations) — the agreement half: `isClosed_setOf_valued_le`,
  the `MazurTorsion` `IsAdicComplete` instance, the `kwHgfV352_localResidueCompletion`
  additivity/EPS block, the `KwF4R1V410a` forward/backward ring equivalence, the
  projector-independence trace algebra (`finrankTrace_*` cyclicity, `TateCohenKernelData`),
  the Cohen–Tate `alphaMap`/`mulOnRange`/`deltaQuotFactor` computation and the
  `KwTateRR3CohenLaurent{Spec,Compl}` construction ending in `solution`;
- [`Theorems/Thm_AlgebraicCurve_tateAgreement.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_tateAgreement.lean)
  — the public `AlgebraicCurve.tateAgreement` binders the port spells.

**Baseline.** Checker `3779 identical / 0 mismatched / 0 missing / 30 own-proof`
(3809 checked), i.e. the port after 3.3a (and the sibling 3.3b/3.3d modules, which are
already wired).

**Scratch evidence.** The port module was elaborated in the edit loop with

```bash
timeout 1500 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false \
  FLTForHuman/AlgebraicCurve/Tate/Agreement.lean
```

**final run clean, exit 0, zero warnings.** A separate `#check` probe of the mathlib
substitutes (`ScratchAuditP33c.lean`, gitignored, deleted after use) compiled clean
(0 errors, 34 `#check`s; log `tools/deps/build/p33c_probe.log`).

## 1. Summary

`port_advise` on the target reports **2 files / 174 declarations** and **46 declarations
already identical in the port (≈1,317 lines)**. That figure is an **over-count**: the
checker's `raw_declarations` returns a `def`'s signature without its body, so the 8
`def … : Prop` atoms of this file (`KwF4gRRTateCommFiniteGen`, `KwF4gRRTateProjectorIndep`,
`KwF4gRRTatePoleWindowImageFinite`, `KwF4gRRTateCohenTateAgreement`,
`KwF4gRRTateCohenKernelDataExists`, `KwTateRR3CohenLaurentSpecExists`,
`KwTateRR3CohenLaurentComplExists`) and the `def cohenB` are reported as substitutes for
`EisensteinWeightOne.E1Chi3IsModular` / `ModularCurve.KwF4gRRTate.adicIntegersKSubmod`
— the attractors for `def … : Prop` and `def … : Submodule`. Re-parsing the pin and the
port with the checker's own parsers gives the corrected split:

| class | count | disposition |
|---|---:|---|
| already identical in the port | **37** | import, do not re-prove |
| — of which `Tate/CommFinite.lean` | 35 | the shared `tateCommFinite` chain (incl. its three `KwF4gRRTate*` atoms) |
| — of which `P1/DivPow.lean` | 2 | `kwHgfV352_localResidueCompletion_{spec,algebraMap}` |
| pin-`private` `Place` helpers | 3 | public in `Defs/PushPull.lean` (generalise) |
| checker-invisible `scoped instance`s | 2 | imported from `Tate/CommFinite.lean` |
| **new (ported here)** | **~133 public + 16 private/scoped** | the agreement/Cohen block |

The `_v2` twin (`S_AlgebraicCurve_tateAgreement_v2.lean`) is **dropped**: one name per
piece, per [PORTING-RR.md](../PORTING-RR.md) §3. The pin's `p2m_*` scaffolding and its
local `maxHeartbeats` raises are dropped as usual.

## 2. Corrections to the measurement

**Correction 1 — the `def` substitutions are false positives.** Same defect as
`AUDIT-mathlib-p3-3a.md` Correction 1: `port_advise` reports 46 substitutes, of which
9 are the `def`-body blind spot. Three of the nine (`KwF4gRRTatePoleWindowFinite`,
`KwF4gRRTateDVRQuotPowKFinite`, `KwF4gRRTateDVRCotangentKFinite`) *are* genuinely in
`Tate/CommFinite.lean` and remain import-discharged; the other six Prop atoms and
`cohenB` are new and are landed here. The corrected substitute count is 37.

**Correction 2 — the shared `tateCommFinite` chain is import-discharged.** The pin's
Agreement file re-declares the whole finiteness chain (`maximalIdeal_le`, `tateProj*`,
the pole window, `kwF4R1V410a_*`, `DVRQuotPowKFinite`/`DVRCotangentKFinite` and their
discharges) that 3.3a already ported byte-for-byte into `Tate/CommFinite.lean`. The
port **imports** `Tate/CommFinite.lean` and does not re-declare those 35 rows; the
checker verifies them through the import. The two `scoped instance`s of the pin
(`kwF4R1V410a_subsingletonHeightOneSpectrumDVR`, `instIsScalarTower_K_toValuationSubring_adicCompletionIntegers`)
are likewise imported (`Tate/CommFinite.lean:469/804`), not re-landed.

**Correction 3 — the `kwHgfV352_localResidueCompletion_spec` subtlety.** The port has
**two** constants named `kwHgfV352_localResidueCompletion`: the public def in
`Defs/TateResidueCurrency.lean:159` and a `private` copy in `P1/DivPow.lean:683`. The
public `_spec`/`_algebraMap` in `P1/DivPow.lean` are stated about the **private** copy,
so they do not rewrite the public def's occurrences. The two new additivity/EPS lemmas
(`_eq_zero_of_mem_integers`, `_add`) therefore get private `_spec₀`/`_algebraMap₀`
re-proofs (the pin's spec proof applied to the public body). This is **friction debt**:
a future refactor should delete the `P1/DivPow.lean` private def and re-state the two
public facts about the `Defs` def.

**Correction 4 — the unported `InlineSpecific` uniformizer slice is reached again.**
`instIsAdicCompleteCompletionIdealAdicCompletionIntegers` (pin 580), its
`isClosed_setOf_valued_le` support (pin 567) and the `kwF4R1V410a` bridge need
`completionIdeal`, `mem_completionIdeal_pow`, `exists_ofAdd_natCast_lt` and the uniformizer
chain from `Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean`, which
mathlib `v4.34.0` does **not** have (`AUDIT-mathlib-p3-3a.md` probe N). As 3.3a did, the
reached rows are re-landed `private` at the pin's names — **promotion debt** to a shared
`Place/Completion.lean` (see §8).

**Correction 5 — `scoped` instances are checker-invisible.** The new file lands four
`scoped instance`s (`instIsAdicCompleteCompletionIdealAdicCompletionIntegers`,
`kw_ffgc_isAdicComplete_placeAdicCompletionIntegers`, and the three
`instFinDimRange*` instances). None begins a line with `instance`, so the checker never
diffs them; they are present for elaboration only.

## 3. SUBSTITUTE rows (import-discharged, with probe evidence)

### 3.1 The shared `tateCommFinite` chain → `Tate/CommFinite.lean`

35 pin declarations are byte-identical to the 3.3a port (the advice log lists them).
Do not re-declare. The two `scoped instance`s of that chain are also imported.

### 3.2 `kwHgfV352_localResidueCompletion_{spec,algebraMap}` → `P1/DivPow.lean`

The pin 968/986 facts match `P1/DivPow.lean:687/704` (about that module's `private`
def). Imported, not re-declared; see Correction 3 for the public-def re-proof needed by
the two new lemmas.

### 3.3 The pin-`private` `Place` helpers → `Defs/PushPull.lean`

`Place.ord_nonneg_of_mem` (pin 494) and `Place.mem_of_ord_nonneg` (pin 510) are public
in `Defs/PushPull.lean:43/60`; `Place.mem_iff_ord_nonneg` (pin 519) is the same-family
helper at `Defs/PushPull.lean:69`. Imported.

## 4. Reuse wins (mathlib terms with probe evidence)

All verified by `#check` in `ScratchAuditP33c.lean` (0 errors):

| pin call | `v4.34.0` substitute | note |
|---|---|---|
| `finrankTrace` cyclicity | `LinearMap.trace_comp_comm'`, `LinearMap.trace_conj'` | the trace of `g ∘ f` equals that of `f ∘ g`; used for `finrankTrace_comp_comm`/`_eq_trace_on_superspace`/`_sub_eq`/`_conj` |
| `finrankTrace (e.conj φ)` | `LinearEquiv.conj_apply`, `LinearMap.trace_conj'` | the conjugation computation |
| submodule finiteness | `Submodule.finiteDimensional_sup`, `Submodule.finiteDimensional_of_le`, `Module.Finite.of_submodule_quotient`, `Module.Finite.equiv` | all the `FiniteDimensional` discharges |
| quotient isomorphisms | `Submodule.quotientQuotientEquivQuotient`, `LinearMap.quotKerEquivRange`, `Submodule.Quotient.restrictScalarsEquiv`, `Submodule.quotEquivOfEq`, `Submodule.equivMapOfInjective` | `kwF4gRRTate_commFiniteGen`, `finiteDimensional_range_alphaMap`, `kwF4gRRTate_poleWindowImageFinite` |
| `LinearMap.mulLeft` | `LinearMap.mulLeft` | `range_mulLeft_…`; no mathlib `range (mulLeft a) = span {a}` (recorded negative) |
| `IsAdicComplete.liftRingHom`/`mk_liftRingHom` | `IsAdicComplete.liftRingHom`, `IsAdicComplete.mk_liftRingHom` | needs `import Mathlib.RingTheory.AdicCompletion.RingHom` (the port's closure has only the `AdicCompletion.*` variants) |
| `AdicCompletion` lift | `AdicCompletion.liftRingHom`, `AdicCompletion.evalₐ_liftRingHom`, `AdicCompletion.evalₐ_of`, `AdicCompletion.ext_evalₐ` | `kwF4R1V410a_{forward,backward,ringEquiv}` |
| Hausdorff uniqueness | `IsHausdorff.funext'` | `kwF4R1V410a_{forward_backward, backward_forward, ringEquiv_of}` |
| ideal quotient | `Ideal.Quotient.factorPow`, `Ideal.quotientMap_injective'`, `Ideal.Quotient.mk_eq_mk_iff_sub_mem`, `Ideal.Quotient.factor_mk`, `RingEquiv.ofRingHom` | the forward/backward family and `quotientEquivKAlg`-style maps |
| DVR | `Irreducible.maximalIdeal_eq`, `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`, `IsLocalRing.eq_maximalIdeal` | `span_irreducible…`, `kwF4gRRTate_clearPole`, `mem_completionIdeal_pow` |
| valued topology | `Valued.isClosed_closedBall`, `Valuation.restrict_le_iff`, `Valuation.map_sub_swap`, `Valuation.mem_maximalIdeal_iff` | `isClosed_setOf_valued_le`, the Cauchy/`haus'` arguments |
| `WithZero`/`Multiplicative` | `WithZero.exists_ne_zero_and_lt`, `Multiplicative.ofAdd`, `ofAdd_toAdd`, `ofAdd_lt`, `Int.le_natAbs`, `inv_mabs_le` | `exists_ofAdd_natCast_lt` re-proved (the pin's `norm_cast` step does not fire in `v4.34.0`; see §6) |

## 5. KEEP/NEW — the agreement and Cohen blocks

The genuinely new mathematics is ~133 public declarations:

- **Valued topology / adic completeness** (pin 567–745): `isClosed_setOf_valued_le`,
  `instIsAdicCompleteCompletionIdealAdicCompletionIntegers`,
  `kw_ffgc_isAdicComplete_placeAdicCompletionIntegers`.
- **Local-residue additivity / EPS** (pin 992–4330): `kwHgfV352_localResidueCompletion_{eq_zero_of_mem_integers,add}`,
  `kwF4R1V394a_localResidueCompletion_smul`, `cohenSectionHat*`, `cohenProjC*`,
  `cohenTateCommRestrict_single_term`, `KwTateRR3CohenLaurentSpec`,
  `aCoeff*`/`kwHgf_v277_*`/`kwHgf_v278_*`, `exists_approximant`,
  `localResidueCompletion_mul_cohenSectionHat`, `KwTateRR3CohenLaurentCompl`.
- **The `KwF4R1V410a` ring equivalence** (pin 1346–1528): `kwF4R1V410a_factorPow_evalₐ`,
  the forward/backward families, `kwF4R1V410a_ringEquiv`.
- **The trace algebra** (pin 1710–2908): `principalPart_mul_zero_of_mem_integers`,
  `tateCommRestrict_single_term`, the `finrankTrace` cyclicity block,
  `SameRangeIdemProjectors`, `deltaQuotFactor*`, `alphaMap`/`mulOnRange`,
  `K*FiniteGen` atoms, and the headline `kwF4gRRTate_projectorIndep`.
- **The Cohen–Tate kernel data** (pin 2972–3181, 4330–4809): `KwF4gRRTateCohenTateAgreement`,
  `TateCohenKernelData`, `sameRangeIdemProjectors_of_kernelData`,
  `tateCommTrace_of_kernelData`, `kwF4gRRTate_agreement_of_kernelData`,
  `cohenLaurentSpec_of_compl`, `kwTateRR3_cohenLaurent{Spec,Compl}Exists`, and the
  headline `AlgebraicCurve.tateAgreement` (pin's `solution`).

## 6. API drift (`v4.34.0`) actually hit

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `Set.mem_setOf_eq` | deprecated → `Set.mem_ofPred_eq` | replaced (2 sites) |
| `WithZero.zero_le _` | deprecated → `zero_le` | replaced (2 sites) |
| `norm_cast` closing `ofAdd (-↑y.natAbs) ≤ y` by `inv_mabs_le y` (pin 110) | **does not fire** | `exists_ofAdd_natCast_lt` re-proved directly by `lift` + `ofAdd_lt` + `Int.le_natAbs` + `omega` |
| `IsAdicComplete.liftRingHom`/`mk_liftRingHom` | present only under `Mathlib.RingTheory.AdicCompletion.RingHom`, not in the port's import closure | added the specific import |
| `IsAdicComplete (maximalMideal …)` instance | pin's `scoped instance` is active only under `open scoped MazurTorsion`; the pin activated it with `p2m_reactivate` | `open scoped MazurTorsion` placed just before its consumer (a top-of-file `open scoped` fails: the namespace is declared later in the file) |
| pin `p2m_open`/`p2m_export`/`p2m_reactivate` | not declarations | dropped; the corresponding `open`s are added by hand (and the file-local namespaces must be opened **after** their scaffolding declarations) |
| pin `maxHeartbeats 6400000/12800000`, `synthInstance.maxHeartbeats` | project cap 4,000,000 | dropped |
| unused-simp-args / `haveI` style warnings | pin's `set_option linter.* false` lines dropped | `set_option linter.style.haveILetI false` keeps the run at zero warnings |

## 7. Recorded negatives

1. **No mathlib declaration replaces any new pin row.** Every new name is a pin-specific
   `def`/`Prop`/`structure` or a statement over the pin's `Place`/`adicCompletion`
   vocabulary; the mathlib leaves above are proof ingredients only.
2. **No `exists_ofAdd_natCast_lt` in mathlib** (`grep -rn 'exists_ofAdd'` over
   `Mathlib/` is empty); it is pin-local (InlineSpecific pin 104).
3. **No mathlib lemma gives `range (LinearMap.mulLeft a) = (Ideal.span {a}).restrictScalars`**
   (pin 1055; recorded in `AUDIT-mathlib-p3-3a.md` §9.5).
4. **`completionIdeal` is not mathlib's**; it is the pin's
   `abbrev … := IsLocalRing.maximalIdeal (adicCompletionIntegers K v)` (InlineSpecific
   pin 299). `mem_completionIdeal_pow` (pin 525) is likewise pin-local.
5. **The `def … : Prop` / `def … : Submodule` "substitutions" are all false positives**
   (Correction 1); re-parse with the checker parsers or by last name before banking one.
6. **`scoped instance` is invisible to both `port_advise` and the checker** (DECL_RE
   requires the line to start with `private`/`noncomputable`/kind); the four new
   instances must be landed by hand.

## 8. Promotion debt / undischarged rows

Landed `private` here (do not edit existing modules), each a pin `file:line`:

- `Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean:104`
  `Multiplicative.exists_ofAdd_natCast_lt`;
- `…:299` `completionIdeal`; `…:430` `exists_uniformizer`; `…:438` `uniformizer_ne_zero`;
  `…:447` `uniformizer_not_isUnit`; `…:455` `eq_pow_uniformizer_mul_unit`;
  `…:474` `maximalIdeal_eq_span_uniformizer`; `…:525` `mem_completionIdeal_pow`;
  plus the port-only `isUnit_adicCompletionIntegers_of_valued_eq_one`.

The named future home is a shared `Place/Completion.lean` (same debt as 3.3a). The
`kwHgfV352_localResidueCompletion` public/`P1/DivPow.lean`-private split (Correction 3)
is a separate refactor item: drop the `DivPow` private def and re-state
`_spec`/`_algebraMap` about the `Defs` def.
