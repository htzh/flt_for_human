# The centre-cut fundamental-domain trio — automorphy transfer and the measurable cover twins

**Status: landed 2026-10-18.** Three of the four nodes the `--ready` shelf showed for the
centre-cut fundamental-domain subject are ported; the fourth is deferred because its definition
module is missing (below). The shared prelude is promoted once in `PeterssonSlabPairing.lean`.
Checker **10,263 identical**, 0 mismatched / 0 missing; the three wired headlines account for +3,
the other +21 is the newly public shared prelude that the checker can diff against existing
`SOURCES` copies. Register current: 198 registered-unwired declarations.

| node | module | lines | wire |
|---|---|---:|---|
| `AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre` | `AutomorphicForm/Adelic/DetNormSlab.lean` | 325 pin | headline +1 |
| `AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre` | `AutomorphicForm/Adelic/MeasurableFundamentalDomainCover.lean` | 267 pin | headline +1 |
| `AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre` | same module | 266 pin | headline +1 |
| `AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample` | **deferred** | 234 pin | needs `CuspidalSpectrumCarrier` |

## 1. What the three theorems say

**Automorphy transfer.** If `W = ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂` covers the
centre and `S` is a fundamental domain for the global-points subgroup inside a determinant slab
`α ≤ ‖det‖ ≤ β`, then an automorphic function at the production pins of `W` is automorphic at the
production pins of `S`. The proof takes the slab covering `N` of `W`
(`exists_finset_central_slab_covering_of_coversModCentre`), turns it into `CoveredBy`, and applies
`memLp_of_coveredBy`; the rest of `IsAutomorphicFnAt` is the inherited invariance.

**Measurable fundamental domain inside a cover.** Given the same cover and a determinant slab
`e₁ ≤ ‖det‖ ≤ e₂`, there is a measurable set `𝓕` that is a fundamental domain for the
global-points subgroup inside the slab and is contained in a finite union of translates of either
the integral-windowed Siegel set (the `integralWindowedSiegelSet` twin) or the centre-cut Siegel
set (the `centreCutSiegelSet` twin). The two proofs share the measure-theory engine
`exists_measurableSet_isFundamentalDomain_subset` — inside any measurable set meeting every orbit,
choose one representative per orbit with least `ℕ`-index, and check it is a fundamental domain.

**The deferred fourth.** `CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_…_ample`
is the slab integral bound `∫_{Φ₀} ‖φ‖² ≤ C * ∫_W ‖φ‖²` for an `IsSlabFundamentalDomain Φ₀`. It
is **not** ready: its wrapper imports `Definitions/Def_AutomorphicForm_CuspidalSpectrumCarrier.lean`
(288 lines / 31 declarations), which defines `IsSlabFundamentalDomain`, `fdPins`, `weightedMeasure`,
`memberSubmodule`, `cuspMemberSubmodule`, `pairing`, `toCarrier`, `IsLift`, … and is absent from the
port. The frontier's `--ready` test matched the *name* `IsSlabFundamentalDomain` to nothing and
priced the node as ported; this is the §4(a) import-only-definitions blindness. The module imports
only the already-ported `CuspidalConstituent` and `TateGlobalZeta`, so it is a cheap definition
wave when the node is scheduled. The three landed nodes do **not** need it.

## 2. The dedup

`port_advise` on the four-target slice reported **47 declarations / ≈350 lines already identical in
the port**, all `private` in `PeterssonSlabPairing.lean`; and **13 names / ≈216 lines** shared among
the four pin files. The block was promoted and completed in place, in the module that already owned
the generic `FundamentalDomainSlab` prelude:

* **23 declarations made public** — 20 promoted from `private`, plus the three new shared
  theorems below — each with a `-- pin:` marker:
  `setLIntegral_fd_le_of_cover`, `smulInvariantMeasure_restrict`,
  `aestronglyMeasurable_of_cover_translates`, `setLIntegral_biUnion_translates_le`,
  `memLp_two_of_lintegral`, `lintegral_lt_top_of_memLp_two`, `exists_measurableSet_isFundamentalDomain_subset`
  (107 lines, new), `setLIntegral_fd_le_sum_mul` (36 lines, new), `cover_of_forall` (23 lines, new),
  `dn`, `slab`, `μH`, `Γp`, `dn_mul`, `dn_globalPoints_mul`, `dn_subtype_mul`,
  `subtype_mul_mem_slab`, `measurableSet_slab`, `preimage_subtype_mul_slab`,
  `smulInvariantMeasure_slab`, `CoveredBy`, `coveredBy_of_forall`, `memLp_of_coveredBy`.
  The 20 existing declarations were already private there; the three new ones are the 107-line
  engine, `setLIntegral_fd_le_sum_mul` and `cover_of_forall`.
* The rest of the `PeterssonSlabPairing` prelude stays `private`; `build_ladder.py --edit` reports
  **0 dependent modules**, so the edit re-elaborates only the hub.
* The two twins are one module: they share the 107-line engine and differ only in the final set and
  parameter names, so `MeasurableFundamentalDomainCover.lean` holds two private `main`
  developments and two public headlines.
* `DetNormSlab.lean` holds only the automorphy-transfer headline.

## 3. Drift

* the 107-line engine needed the recorded `Set.mem_setOf_eq → Set.mem_ofPred_eq` rename;
* `setLIntegral_fd_le_sum_mul` carries one narrow `set_option linter.style.haveILetI false in`
  (the `haveI := smulInvariantMeasure_slab` is load-bearing);
* the two twin headlines carry narrow `set_option linter.unusedVariables false in` because their
  wrapper hypotheses `hc : 0 < c`, `hd₁ : 0 < d₁`, `he : e₁ < e₂` are used only to type the
  statement (the `main` theorems do not need them);
* `DetNormSlab` carries the same narrow `haveILetI` suppression for the two `letI` instance
  bindings in the transfer proof.

## 4. Verification

* edit loop: 0 errors / 0 warnings for all three modules and the promoted hub;
* `lake build`: hub 7.7 s, `DetNormSlab` 3.5 s, `MeasurableFundamentalDomainCover` 3.9 s;
* checker: **10,263 identical**, 0 mismatched / 0 missing, 10,503 checked; +3 headlines, +21
  promoted prelude declarations that the checker can diff against existing `SOURCES` copies;
* `#print axioms` on all three headlines: `[propext, Classical.choice, Quot.sound]`;
* `unwired_register.py --check`: current (the three new shared theorems are tier 3);
* `git status`: the two new modules, the promoted `PeterssonSlabPairing.lean`, the checker wiring,
  the regenerated register, and the records.

## 5. What it buys

The automorphy-transfer and measurable-cover nodes leave the `--include-leaves` demand. The
remaining ready-looking centre-cut node is the deferred 234-line slab-integral bound; it is blocked
on `Def_AutomorphicForm_CuspidalSpectrumCarrier.lean`, recorded in
[CARRY-FORWARD.md](../CARRY-FORWARD.md). The larger `coversModCentre` silo remains behind the
unit-factorizable chain.
