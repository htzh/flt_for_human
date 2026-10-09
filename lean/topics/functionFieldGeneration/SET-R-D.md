# SET-R-D — the three ready successors (one set, three orders)

**Status: done and verified (2026-10-08).** Fourth set of the qexp column, and
the first after the head landed. It authorizes **three new modules in dependency
order**. The scope is
[TOPIC-qexp-successors.md](TOPIC-qexp-successors.md) — read it in full, with the
head's record
[TOPIC-qexp-rationality-degree-head.md](TOPIC-qexp-rationality-degree-head.md) §10.
The three landed sets' conventions are
[SET-R-A.md](SET-R-A.md), [SET-R-B.md](SET-R-B.md), [SET-R-C.md](SET-R-C.md).

**Prerequisite already done — do not repeat it.** The `Gamma0Integral.lean` hub
promotion (sixteen `…X1DiamondRationalForms` rows) is landed, verified, and its
dependent wave is green; the pin's Atkin–Lehner `S_` file is already in `SOURCES`.
The checker baseline at dispatch is **6920 identical (313 promoted, 83 renamed),
0 mismatched, 0 missing, 36 own (6956 checked)**.

| order | module | headline (statement authority = the `Theorems/` wrapper) | `S_` file |
|---|---|---|---|
| 1 | `FLTForHuman/ModularCurve/Defs/QExpValuationReduction.lean` | `ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring` | `S_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring.lean` (557) |
| 2 | `FLTForHuman/ModularCurve/X1/FunctionFieldIsAlgClosed.lean` | `ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed` | `S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed.lean` (326) |
| 3 | `FLTForHuman/ModularCurve/X1/IsIntegralAtkinLehner.lean` | `ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even` | `S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean` (583) |

The orders share no premises; the order is a build-economy choice (cheapest
first). Verify each before starting the next. The module paths are the reviewer's
proposal; if the mathematics admits a leaf-side home, re-home and record it
(playbook host rule), but do not split one theory across modules.

## 0. What is already in the port

* **Order 1** has one premise, `AlgebraicCurve.finiteDimensional_adjoin_of_transcendental`,
  already ported. 26 declarations / 557 lines, **0 substitutions** — everything in
  the `S_` file is new. Big items: `main` (111), `card_le_finrank_of_linearIndependent`
  (89), `transcendental_upstairs` (64), `exists_reduced_relation` (61).
* **Order 2** has four premises — `exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField`
  (SET-R-C target 5, public), `ValuationSubring.exists_liesOverPrime_algebraicClosure_rat`,
  `ModularCurve.transcendental_jqModC`, `ModularCurve.jqModC_mem_intFormRatiosC`.
  15 declarations / 326 lines, **0 substitutions**. Big items: `transfer` (114),
  `isAlgebraic_residueField` (57), `map_mem_adjoin` (15).
* **Order 3**'s engine is the promoted `…X1DiamondRationalForms` block:
  `IsRat`, `IsRat.mul`, `IsRat.pow`, `IsRat.of_mul_eq`, `isRat_iff_exists_map`,
  `isRat_E4`, `isRat_E6`, `isRat_Eaux`, `levelOne_smul`, `Eaux`,
  `qExpansion_Eaux`, `constantCoeff_E4/E6/Eaux`, `exists_weights`,
  `conj_mem_Gamma1`. Import them. `RationalityDvd.conj_mem_Gamma1` is also public
  and is the copy SET-R-A uses — reuse, do not re-prove. 59 declarations / 583
  lines; 19 substitutions (3 importable: `qExpansion_coeff_unique'`,
  `periodic_mul`, `X1DiamondRational.disc_smul`; 16 now public in the hub).

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem`
(read-only; never modify). **Statement = the `Theorems/Thm_<stem>.lean` wrapper**,
binders verbatim; proof = the matching `P2M/Sol/S_<stem>.lean`. Adapt proofs, never
statements.

**Recorded risk for order 2.** Its pin `S_` file imports
`Definitions/Def_ModularCurve_X0ModL.lean`, the deliberately-unported definition
module. The head's §3 recorded that target 5 needs only two of that file's 20
declarations; hand-check this file's actual import list before writing, and if it
reaches a declaration that is genuinely absent, stop and report rather than
porting a definition module that is out of scope.

## 2. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` per module; **no
whole-tree build**. Bound everything:
`timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`,
`flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth`. On a timeout, quarantine and bisect; tell a blow-up
from contention with CPU time. Build serially. Do not commit.

## 3. The hub prohibition

**Do not edit any existing Lean module.** The `Gamma0Integral.lean` promotion is
already done; do not re-promote, do not rename, do not collapse the duplicate
block (that is a refactor-round item). If a needed helper is `private` in a hub,
re-derive it locally as `private` in your module and report it. If a promotion
seems genuinely required, **stop and report** with the declaration, host, reason
and `python3 tools/deps/build_ladder.py --edit <host>` — the manager decides.

## 4. Wiring

Per order, in `lean/spec/check_flt_statements.py`:

* order 1: append `Theorems/Thm_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring.lean`
  to `SOURCES` last; append `"FLTForHuman/ModularCurve/Defs/QExpValuationReduction.lean"`
  to `PORT_FILES` last.
* order 2: append the target's `S_` file **and** its `Theorems/` wrapper to
  `SOURCES` last; append the module to `PORT_FILES` last.
* order 3: the `S_` file is **already** in `SOURCES`; append only its
  `Theorems/` wrapper to `SOURCES` last; append the module to `PORT_FILES` last.

Target **0 mismatched, 0 missing**; mutation-test one headline per order and
revert.

## 5. Risks

* The usual `generalise` rows and suspect `def` substitutions
  (`tauPair`→`PeriodPair.ofTau`, `SField`→`modularFunctionField`, the
  `E4`/`E6`/`A12`/`D12` family, `fricke`→`WLight.WW`, `expandInt`→`expandPS`): read
  both copies before applying any of them. Order 3 in particular re-declares
  helpers that SET-R-A already has public — reuse those.
* Order 3's `IsRat` is a `def … : Prop` (the checker's prop-body class).
* The `Cos`/`Finset` reindexing shape has cost earlier topics; keep the pin's
  concrete function types.

## 6. Stop and report

As SET-R-A §6; plus the order-2 `Def_ModularCurve_X0ModL` import check; plus any
declaration whose proof reaches a definition module that is out of scope.

## 7. Completion report (per order)

Module path; public/`private` counts; every local `private` re-derivation with its
host; tier 0 / tier 1 wall and CPU times; checker before → after and the mutation
result; `#print axioms` for the headline; the substitutions you resolved and the
ones you declined; anything you could not match, quoted.

## 8. Outcome (2026-10-08, landed and manager-verified)

Checker **6920 → 6975 identical (313 promoted, 83 renamed), 0 mismatched,
0 missing, 36 own (7011 checked)**, +55 over the three orders; no existing Lean
module edited; nothing committed. Every order passed tier 0, tier 1 and a
one-token mutation (exactly one mismatch, reverted), and `#print axioms` is
`[propext, Classical.choice, Quot.sound]` on all three headlines.

| order | module | lines | public / private | tier 0 | tier 1 |
|---|---|---:|---:|---:|---:|
| 1 | `ModularCurve/Defs/QExpValuationReduction.lean` | 601 | 1 / 25 | 38.3 s | 40.0 s |
| 2 | `ModularCurve/X1/FunctionFieldIsAlgClosed.lean` | 405 | 15 / 4 | 27.3 s | 28.8 s |
| 3 | `ModularCurve/X1/IsIntegralAtkinLehner.lean` | 484 | 36 / 0 | 7.4 s | 9.8 s |

Order 3 reuses all sixteen promoted hub rows and declines every suspect `def`
substitution (none occurs in its file). Two rows (`conj_T_pow_mem`, `cardK`) are
re-hosted rather than aliased to `RationalityDvd`, whose copies bind `γ` inline
where the pin uses a section variable — a **correct note against this order's own
prose**, which had pointed at `RationalityDvd.conj_mem_Gamma1`; the statement that
file needs is the hub's promoted copy, not SET-R-A's. Order 1 transcribes one
`set_option synthInstance.maxHeartbeats 1600000 in` (the pin's own, not a
`maxHeartbeats` bump) and order 2 two file-scope ones; their proofs still fit the
4,000,000 cap.

**Order-2 import check.** Its pin `S_` file reaches exactly two declarations of
the unported `Def_ModularCurve_X0ModL.lean` — `coeffMap_ofPowerSeries` (already
public at `Frobenius/Defs.lean:57`) and `coeffMap_jqModC` (re-derived `private`,
as SET-R-C also did) — plus `ValuationSubring.charP_residueField_of_liesOverPrime_def`
from the equally unported `Def_WeierstrassCurve_ReductionMap.lean`, also
re-derived `private`. No definition module was ported.

The dependent wave is green at **9,234 jobs** (after the `Gamma0Integral.lean`
17-row duplicate collapse that followed the prerequisite; that edit is recorded in
[TOPIC-qexp-successors.md](TOPIC-qexp-successors.md) §3).

**Coverage.** The ready shelf is **86 again** — the three landed and three
successors took their place: `exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar`
and `exists_algEquiv_x1x0FunctionFieldC_atkinLehner` (both on order 3) and
`finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed` (on order 1).
The next cut re-scopes those.
