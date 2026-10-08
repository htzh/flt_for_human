# SET-R-C — the `JOneES` tail: the finrank/index bound and the residue-field model

**Status: done and verified (2026-10-08).** Third coding set of the qexp head.
Authorizes **two new modules, in this order**. Planning record:
[TOPIC-qexp-rationality-degree-head.md](TOPIC-qexp-rationality-degree-head.md)
§1 (targets 4–5), §3, §5, §7 items 1 and 5, §8.

| order | module | headline | wrapper | proof source |
|---|---|---|---|---|
| 1 | `FLTForHuman/ModularCurve/X1/FunctionFieldDegree.lean` | `ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index` | `Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean` | `P2M/Sol/S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean` (1,095) |
| 2 | `FLTForHuman/ModularCurve/X1/FunctionFieldResidue.lean` | `ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField` | `Theorems/Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField.lean` | `P2M/Sol/S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField.lean` (1,000) |

Order 2 is **independent** of order 1 (different pin files) but is the only
wholly new theory in the cluster, so write it second, when the promoted engine is
settled. Build order 1 and its checker delta before starting order 2.

## 0. What earlier work handed over (verified)

* **The `JOneES` promotion pass is landed.** `ModularCurve/X1/FunctionField.lean`
  now declares its whole block publicly: `JOneESAlg` (`linearIndependent_map`,
  `finiteDimensional_of_forall_aeval_eq_zero`, …), `JOneESLevelOne`
  (`monomialSpan`, `qExpansion_mem_monomialSpan`), `JOneESNorm` (`Cos`,
  `charPolyAt`, `card_cos`, `Nice` and its algebra, `coeffForm`,
  `sum_qExpansion_coeffForm_mul_pow_eq_zero`, …), `JOneESRat` (`xq`, `P6`,
  `isIntegralQExp_E6`, the `intFormRatiosC` closure,
  `mem_qExpFunctionFieldC_iff`, `coeffEmb_intSeriesC`, `coeffEmb_eq_map`,
  `sum_div_pow_eq`, `monomial_eq`, `exists_rat_relation`, …). **Import it; do not
  re-transcribe and do not re-privatise.**
* Two exceptions to carry: the anonymous `Fintype (Cos Γ)` instance is still
  `private` — declare the module's own `scoped instance` as the pin's
  `..._le_index.lean:235` does; and `coeff_one_eisenstein4` is still `private`
  (re-derive it locally if needed; it is not required).
* The target-4 `S_` file is **already in `SOURCES`** (appended by the promotion
  pass); its wrapper is not. Target 5's `S_` file and wrapper are both unwired.
* Checker baseline: **6602 identical (312 promoted, 83 renamed), 0/0**.

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3`; **statement = the wrapper**
(binders verbatim), proof = the `S_` file. Adapt proofs, never statements.

Recorded negatives (do not repeat the searches; topic §3):

* `Def_ModularCurve_X0ModL.lean` is not a missing module. Target 5 uses only
  `coeffMap_ofPowerSeries` (ported, `Frobenius/Defs.lean:57`) and
  `coeffMap_jqModC`, which is **not a named lemma in the port** — the same
  statement is proved inline at `Degree/PhiDegree.lean:103`. Budget ~3 lines.
* Mathlib has no statement of either conclusion and no `jqModC`/
  `qExpFunctionFieldC` vocabulary; those are the pin's and are ported.

Reuse homes for order 1 (`next5_advise` target 4): `X1/FunctionField.lean`
(46 of the 49 in-port declarations, now public), `JqIntegralRatios.lean`
(`intSeriesC`, `intFormRatiosC`, `qExpFunctionFieldC`, `mem_intFormRatiosC`,
`div_mem_qExpFunctionFieldC`, `isIntegralQExp_E4` — all public),
`ModularForms/WeightOne/Gamma0Integral.lean` (the `IsIntegralQExp` block).
The one unported premise under the literal reading is
`ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff`; under the
terminal reading the target is fully ready — check which the transcription needs
before porting it.

## 2. Build discipline

As SET-R-A §2. Bounds: `timeout 300 lake env lean -DmaxHeartbeats=4000000
-DautoImplicit=false <file>`; `flock .lake/flt_build.lock timeout 300 lake build
<module>` per module; no whole-tree build; no commits; serial builds only.

## 3. The hub prohibition

**Do not edit any existing module** — in particular not
`ModularCurve/X1/FunctionField.lean` (the promoted engine is frozen),
`JqIntegralRatios.lean`, `Gamma0Integral.lean`, or any other file in the tree.
If a helper you need is `private` there, re-derive it in your module and report.
If a promotion seems genuinely required, **stop and report** with the host and
`python3 tools/deps/build_ladder.py --edit <host>`.

## 4. Wiring

In `lean/spec/check_flt_statements.py`:

* order 1: append the wrapper
  (`Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean`)
  to `SOURCES` last; append the module to `PORT_FILES` last.
* order 2: append the target-5 `S_` file
  (`P2M/Sol/S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField.lean`)
  **and** its wrapper to `SOURCES` last; append the module to `PORT_FILES` last.
* Run the checker after each order; target **0 mismatched, 0 missing**;
  mutation-test one headline per order and revert.

## 5. Risks specific to this set

* **The `generalise` rows** (topic §7 item 3) and the **suspect `def`
  substitutions** (topic §7 item 4) — `tauPair`→`PeriodPair.ofTau`,
  `SField`→`modularFunctionField`, the `E4`/`E6`/`A12`/`D12` family,
  `fricke`→`WLight.WW`, `expandInt`→`expandPS`. Read both copies first.
* The `Cos`-indexed `Finset` sums are the `Finset`-sum reindexing shape that has
  cost earlier topics; keep the pin's concrete function types.

## 6. Stop and report

Same as SET-R-A §6, plus any reason to touch `X1/FunctionField.lean`.

## 7. Completion report

Per order: module path; public/`private` counts; local re-derivations with hosts;
tier 0/tier 1 wall and CPU times; checker before → after and mutation result;
`#print axioms` for the headline; the `coeffMap_jqModC` treatment.

## 8. Outcome (2026-10-08, landed and manager-verified)

**Order 1** `ModularCurve/X1/FunctionFieldDegree.lean`, 690 lines, 36 public /
0 private (plus a `scoped instance Fintype (Cos Γ)`, invisible to the checker).
The promoted JOneES engine is imported, not re-transcribed; the new work is the
pin's discriminant generator `wq = q(Δ)/q(E₄³)` (distinct from the promoted
`xq = q(E₆²)/q(E₄³)`), its monomial span, the `wq`-form relation, and the
`FIdxBC` base-change tail. `coeffMap_jqModC` is **not used** here. Checker
`6798 → 6834` (+36, one of them landing in `promoted`, 312 → 313); 0/0; mutation
in the headline `Γ'.index → Γ.index` gave exactly one mismatch, reverted. Tier 0
11.6 s, tier 1 13.8 s. The `hasSum_cosetPoly_coeff` premise occurs only in the
pin's attribute scaffolding — nothing was ported for it. The `A12 → e4cube`
parser substitution was **not** applied: the public `JOneES.JOneESRat.A12` is
byte-identical to target 4's, and `D12`/`PΔ` are transcribed at their pin names.

**Order 2** `ModularCurve/X1/FunctionFieldResidue.lean`, 1,027 lines, 70 public /
1 private. The private row is `coeffMap_jqModC {R S} (f : R →+* S)`, re-derived
(its pin host is the unported `Def_ModularCurve_X0ModL.lean`, and it is not a
declaration of target 5's `S_` file). Checker `6834 → 6904` (+70); 0/0; mutation
`≤ → <` gave exactly one mismatch, reverted. Tier 0 44.2 s, tier 1 45.8 s. The
pin's `maxHeartbeats` bumps were not transcribed; the one instance-search wall
(`Module.Free` of the residue-field extension) is discharged with
`Module.Free.of_divisionRing`. The pin's `IsInt (f : LaurentSeries L)` is
transcribed rather than reusing `DeligneSerre.Relevement.IsInt` (same last name,
different statement).

**Friction.** The pin's `attribute [-instance] DivisionRing.toRatAlgebra`
(`...le_index.lean:18`) is load-bearing under `v4.34.0` — without it
`Module.finrank`'s `Algebra ℚ` instance on `qExpFunctionFieldC ℚ Γ` resolves to
`DivisionRing.toRatAlgebra` while `FIdxAlg`'s generic lemma uses
`IntermediateField.algebra'`. The port's `X1/FunctionField.lean` transcription
dropped the attribute; order 1 re-supplied it locally. Follow up in the refactor
round if the promoted engine is ever used for another `finrank` goal.

Working tree: the two modules added, `spec/check_flt_statements.py` +46 wiring;
no hub edited, nothing committed.
