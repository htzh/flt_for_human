# WORKORDER-C2 — the `X₁`/`X_H` function field: q-expansion, integrality and structure

**Status: ready to dispatch.** The remaining half of subject C off the `ModularCurve` ready
shelf; the sibling C1 (the Frobenius headline) landed as a manager append into
`ModularCurve/Frobenius/QExpModL.lean`. **New files only**; no existing Lean module is edited.
Two phases: its definition layer, then the leaf rows.

| phase | modules | content |
|---|---|---|
| 1 | `ModularCurve/Defs/HeckeDifferential.lean`, `AlgebraicCurve/Differential/PushPull.lean`, `ModularCurve/Defs/SL2Elementary.lean`, `ModularCurve/X0/FunctionFieldFull.lean` | the pin's four unported definition modules, whole |
| 2 | `ModularCurve/X1/*.lean` (three suggested modules) | ten of the eleven ready rows; `exists_sum_smul_eq_of_isIntegralQExp_gamma1` is deferred to its own node (§2) |

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Checker baseline
**7431 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 37 own (7468 checked)**.

## 1. Phase 1 — the definition layer

Hand-checking the eleven `S_` files' `Definitions/` imports against the port leaves **four**
unported modules. Port them **whole** (every declaration with a consumer):

| pin module | lines | supplies | note |
|---|---:|---|---|
| `Definitions/Def_ModularCurve_HeckeDifferential.lean` | 186 | `qEulerFun`, `qEuler`, `qEulerOn`, `diffQExp`, `heckeDiffAlong`, `heckeDiffBar`, `diffQExpBar`, `regularDifferentialsBar` | `qEuler`/`diffQExp` occur nowhere in the port |
| `Definitions/Def_AlgebraicCurve_DifferentialPushPull.lean` | 79 | `AlgebraicCurve.Differential.{pullbackAlong, traceAlong, correspondence, …}` | **added at dispatch** — `HeckeDifferential`'s `heckeDiff*` block calls it, so porting that node whole needs it; home it in `AlgebraicCurve/Differential/PushPull.lean` |
| `Definitions/Def_ModularCurve_SL2Elementary.lean` | 74 | `upperElem`, `lowerElem`, `elemSet`, their closure lemmas | `elemSet` occurs nowhere in the port |
| `Definitions/Def_ModularCurve_X0ModL.lean` | 156 | `modularFunctionFieldFullC` and its theory | `Frobenius/Defs.lean` records it as *deliberately* left unported; C2 needs it |

The other imports are ported: `Def_ModularCurve_X1` (`ModularCurve/X1/Defs.lean`,
`x1FunctionFieldBar`), `Def_ModularCurve_XH` (`XH/FunctionField.lean`, `xHFunctionField`),
`Def_ModularCurve_JqCoeff` (`Defs/JqCoeff.lean`, `modularFunctionFieldC`),
`Def_ModularCurve_X0` (`Defs/Laurent.lean` has `qExpand`), `Def_FLTPrelim_Modularity`
(`ModularForms/Defs/Eigenform.lean` has `IsNormalizedEigenForm`), `Def_ModularCurve_PhiGen`, and
the `Def_AlgebraicCurve_*` modules. Keep the pin's namespaces; statements verbatim; adapt proof
bodies to `v4.34.0`; replace the pin's `import Mathlib` with specific imports.

## 2. Phase 2 — the eleven leaf rows

| node (`ModularCurve.` prefix) | `S_` lines | content |
|---|---:|---|
| `qExpansion_div_mem_laurentBaseChange_xHFunctionField` | 441 | the q-expansion quotient of two `Γ_H` modular forms lies in `laurentBaseChange ℂ (xHFunctionField N H)` |
| `isIntegral_jqNModC_of_modularPolynomialData` | 262 | `jqNModC K N` is integral over `K[jqModC]` for every `ModularPolynomialData N` |
| `exists_gamma0_qExpansion_div_eq_jqNModC` | 141 | `jqNModC ℂ ℓ` is a quotient of two level-`ℓ` `Γ₀` forms of weight 12 |
| `eisenstein4_cube_sub_mk_sq` | 121 | the power-series identity `eisenstein4 ^ 3 - (…) ^ 2 = 1728 * (X * dedekindEtaUnit)` |
| `diffQExp_x1FunctionFieldBar_injective` | 62 | `diffQExp (x1FunctionFieldBar M)` is injective |
| `modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero` | 46 | in characteristic zero the two function fields agree |
| `modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0` | 42 | `modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (Γ₀ M)` |
| `exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | every `Γ₁(N)` form is a `ℂ`-combination of integral-q-expansion forms — **DEFERRED** (see below) |
| `closure_elemSet_eq_top` | 35 | `Subgroup.closure (elemSet (ZMod N)) = ⊤` |
| `isCurveOver_x1FunctionFieldBar` | 20 | `IsCurveOver (AlgebraicClosure ℚ) (x1FunctionFieldBar M)` |
| `essFiniteType_x1FunctionFieldBar` | 16 | `Algebra.EssFiniteType (AlgebraicClosure ℚ) (x1FunctionFieldBar M)` |

Statements are the `Theorems/Thm_ModularCurve_<stem>.lean` wrappers, binders verbatim; proofs are
the matching `P2M/Sol/S_ModularCurve_<stem>.lean`. Suggested homes (re-home freely, recording it):
q-expansion/integrality (`qExpansion_div_mem…`, `isIntegral_jqNModC…`, `exists_gamma0…`,
`eisenstein4_cube_sub_mk_sq`, `exists_sum_smul_eq…`) in one `X1/` module;
structure (`isCurveOver…`, `essFiniteType…`, `diffQExp…`, `closure_elemSet_eq_top`) in another;
the two function-field inclusions in a third.

**Only the headlines are public**; the `S_`-local helpers stay `private`. Ten of the eleven land;
`exists_sum_smul_eq_of_isIntegralQExp_gamma1` is **deferred**:

**Deferral (found at implementation).** That row is not a leaf. Its one substantive proof step is
a premise node, `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (wrapper import
verbatim in the `S_` file), which is **not** in the port — only the `CuspForm` twin
`CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`
(`ModularForms/WeightOne/Gamma1IntegralBasis.lean`) is, and it cannot substitute: the headline's
`F` is a `ModularForm (CongruenceSubgroup.Gamma1 N) k` of arbitrary `k : ℤ`, and the cuspidal
subspace does not span the Eisenstein part. The `ModularForm`-side chain is ≈2k–5k `S_` lines
(`span_frickeRational_E4_pow_E6_pow_eq_top` 1,524, `exists_gamma1_frickeRational_sigmaTransport`
772, the four `…_mem_adjoin_exp`/`…_eq_algEquiv_apply`/`…_mem_range_ratCast` steps, and
`exists_mul_E4_pow_mul_E6_pow_eq_top` 424), i.e. a whole node, not a row; it needs its own work
order. **Tool finding:** `frontier.py` had marked this node `ready`, i.e. its readiness test
matched the `CuspForm` twin by last name, so the frontier understates that row's cost — register
it rather than trusting the `ready` flag for the `ModularForm`/`CuspForm` rename pairs.

## 3. Private dependencies to re-derive locally (no promotions)

`port_advise` reports three declarations C2 needs that exist in the port only `private` in a hub,
and none of those hubs shares C2's subject, so **re-derive each locally `private`** (report it):

* `swap_eq_of_evalSymm`, `ev_eq_aevalAeval` — `private` in
  `ModularCurve/ModularPolynomialIrreducible.lean`, needed by `isIntegral_jqNModC…`;
* `conj_mem_Gamma1` — `private` in `ModularForms/WeightOne/Gamma1IntegralBasis.lean`, needed by
  `qExpansion_div_mem_laurentBaseChange_xHFunctionField`.

There is **no shared prelude among the eleven** (`port_advise` finds none), and no suspect
`def`-`Prop` rows. (This is the C1 lesson applied in reverse: C1 was hosted in the module that
already held its privates *and* whose subject it concluded; here the subjects differ, so hosting
would be a mis-home and the cheaper correct move is a local re-derivation.)

## 4. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` when a file is done; **no whole-tree
build**. Bound everything: `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false
<file>`, `flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth`; on a timeout quarantine and bisect, and tell a blow-up from
contention by CPU time. Serial builds only. Do not commit.

## 5. The hub prohibition

**Do not edit any existing Lean module.** If a needed helper is `private` in a hub, re-derive it
locally as `private` and report it. If a promotion seems genuinely required, **stop and report**
with the declaration, host, reason and `python3 tools/deps/build_ladder.py --edit <host>` — the
manager decides.

## 6. Wiring

Append to `SOURCES` each phase-1 pin definition file and, for phase 2, each target's
`Theorems/Thm_ModularCurve_<stem>.lean` and `P2M/Sol/S_ModularCurve_<stem>.lean`; append each new
module to `PORT_FILES`; both last. Run the checker after each phase (text-only, no build) and
reconcile the `identical` delta to the new public surface before building; mutation-test each
headline and revert.

## 7. Stop and report

If a statement cannot be matched without moving the pin's text; if a phase-1 module's proof needs
an unported `Definitions/` module beyond the four listed (report the import verbatim); if a helper
is genuinely needed publicly and is `private` in a hub; or if a build exceeds its bound and
bisecting does not settle it.

## 8. Completion report

Module paths and line counts; public/`private` counts; tier-0 warnings (target **0**) and wall/CPU;
tier-1 result; every local `private` re-derivation with its host; the checker before → after with
the `identical` delta reconciled and a mutation result per headline; `#print axioms` for each
headline (`[propext, Classical.choice, Quot.sound]`); `git status --porcelain` showing only the
set's files; anything you could not match, quoted.

## 9. Outcome (2026-10-09; landed 10/11, one node deferred)

Eight new modules, **1,886 lines**, 70 public declarations; no existing Lean module edited;
nothing committed.

| module | lines | public | private |
|---|---:|---:|---:|
| `AlgebraicCurve/Differential/PushPull.lean` (the authorised fourth) | 106 | 8 | 0 |
| `ModularCurve/Defs/SL2Elementary.lean` | 87 | 13 | 0 |
| `ModularCurve/Defs/HeckeDifferential.lean` | 214 | 22 | 0 |
| `ModularCurve/X0/FunctionFieldFull.lean` | 171 | 17 | 4 |
| `ModularCurve/X1/QExpansionDiv.lean` | 527 | 1 | 45 |
| `ModularCurve/X1/IntegralityJqNModC.lean` | 461 | 3 | 31 |
| `ModularCurve/X1/Structure.lean` | 174 | 4 | 0 |
| `ModularCurve/X1/FunctionFieldInclusion.lean` | 146 | 2 | 0 |

All eight elaborate at tier 0 with **0 errors and 0 warnings**; all eight build at tier 1; no
`maxHeartbeats` raised, no `sorry`, no linter suppression needed (every pin `haveI` became
`have`). Ten mutations, one per landed headline, each caught and reverted (`md5sum -c` clean);
`#print axioms` on all ten `[propext, Classical.choice, Quot.sound]`. Milestone whole-tree build
green (**9,378 jobs**).

**Checker 7431 → 7502 identical, 0 mismatched, 0 missing, 36 own (7538 checked)** — the set's 70
new public declarations all verify. Getting there needed a manager fix: the `OWN_PROOFS` entry
`"correspondence"` was a bare *last name*, so it silently exempted C2's new
`AlgebraicCurve.Differential.correspondence` (and the pre-existing `Divisor.correspondence`, which
in fact verifies) alongside the genuine `Def_AlgebraicCurve_Correspondence.lean` collision. It is
now dotted, `"AlgebraicCurve.Pic0.correspondence"`: +2 verified, −2 exemptions.

**One row deferred.** `exists_sum_smul_eq_of_isIntegralQExp_gamma1` is not a leaf: its premise
node `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` is unported, the `CuspForm` twin
cannot substitute, and the chain is ≈4.8k raw / ≈2.1k `S_` lines. Deferred whole (see §2),
documented in `X1/IntegralityJqNModC.lean`'s docstring; it needs its own work order.

**Tool finding (verified).** `frontier.py --ready` lists that row as ready because the default
`union` frontier includes a names view keyed by the port's *last names*
(`frontier.py:473–474`), so the port's `CuspForm.…` twin marks the pin's distinct
`ModularForm.…` node as ported; `port_advise`'s drags share the blindness. The frontier therefore
understates that row by ~2k–5k lines — check the pin node, not just the imported names, before
trusting `ready` for a rename pair.

**Two §3 corrections for the record.** (i) `X0/FunctionFieldFull.lean` also needed four
`coeff_jqModC_*` helpers the pin imports from `Theorems/` wrappers (private in
`Degree/PhiDegree.lean`) — §3's "three declarations" undercounted. (ii) Of §3's two named
privates, only `ev_eq_aevalAeval` is on the `isIntegral_jqNModC` cone; `swap_eq_of_evalSymm` serves
the pin's separability branch, which C2 does not port. The lesson generalises: list the pin's
`Theorems/` imports, not just its `Definitions/` imports, when pricing a "leaf" row.
