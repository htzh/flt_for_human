# SET-R-E — the Atkin–Lehner exchange and the `isAlgClosed` finrank bound

**Status: ready to dispatch (2026-10-08).** Fifth set of the qexp column, and the
first whose **definition layer is already in place** (see §0). It authorizes
**two new modules, in this order**. Scope:
[TOPIC-qexp-successors-2.md](TOPIC-qexp-successors-2.md) — read it in full,
especially §1a-style characteristic-`p` note in §4 and the dedup in §3. Conventions
and the report format: [SET-R-D.md](SET-R-D.md) §0/§8.

**Prerequisite already done — do not repeat it.** The definition layer is landed:
the pin's `Def_WeierstrassCurve_ReductionMap` `ValuationSubring` block is now
public in `FLTForHuman/NumberTheory/ValuationAtPlace.lean`, the pin definition file
is in `SOURCES`, and the `private` re-derivation in `FunctionFieldIsAlgClosed.lean`
was removed in favour of the import. Checker **6975 → 6979 identical, 0 mismatched,
0 missing**; the wave is green (4,692 jobs). Checker baseline at dispatch:
**6979 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own
(7015 checked)**.

| order | module | headline | `S_` file |
|---|---|---|---|
| 1 | `FLTForHuman/ModularCurve/X1/FunctionFieldFinrankIsAlgClosed.lean` | `ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed` | `S_…_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean` (193) |
| 2 | `FLTForHuman/ModularCurve/X1/AtkinLehnerExchange.lean` | `ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar` **and** `ModularCurve.exists_algEquiv_x1x0FunctionFieldC_atkinLehner` | the two `S_…_atkinLehner…` files (1,195 and 1,237) |

The orders share no premises. Verify order 1 before starting order 2. The module
paths are the reviewer's proposal; if the mathematics admits a leaf-side home,
re-home and record it (playbook host rule), but do not split one theory across
modules.

## 0. What is already in the port

**The definition layer (done, 2026-10-08).** Every imported definition the three
targets use is public:

* `Definitions/Def_ModularCurve_XHOperators`, `Def_ModularCurve_X1HeckeOperator`,
  `Def_ModularCurve_X1Diamond`, `Def_ModularCurve_X1`, `Def_ModularCurve_JqCoeff`,
  `Def_FLTPrelim_Ramification` — the used declarations are all public
  (`ModularForms/Defs/HeckeOperator.lean` supplies `heckeDiagMatrix`,
  `heckeMatrix`, `slash_heckeDiagMatrix_apply`, … for both orders).
* `Definitions/Def_WeierstrassCurve_ReductionMap` — only its opening
  `ValuationSubring` block is needed and is now public in
  `NumberTheory/ValuationAtPlace.lean`:
  `ValuationSubring.liesOverPrime_iff`,
  `natCast_mem_maximalIdeal_of_liesOverPrime`,
  `charP_residueField_of_liesOverPrime_def` (and `natCast_mem'`). Import them; the
  rest of that pin module (the Weierstrass reduction map) is **unported** and not
  needed.
* Two `ModularForm` lemmas the parser flags (`heckeDiagMatrix_zero`,
  `heckeMatrix_zero`) occur **only** in the pin's `attribute [-simp] …` scaffolding
  lines, never in a statement or proof. Do not transcribe the attribute lines and
  do not re-derive the lemmas.

**Order 1** has six premises, all ported — the three SET-R-D/SET-R-C headlines plus
`JOneES.exists_transcendental_finiteDimensional_laurentBaseChange`,
`transcendental_jqModC`, `jqModC_mem_intFormRatiosC`. 3 substitution rows, all
importable; 0 port-`private`. Its block is 87 lines, 78 of which are the engine of
SET-R-D order 2 (`FunctionFieldIsAlgClosed.lean`), where `isAlgebraic_residueField`
(59) and `residueTopHom` (11) are **public** — import and reuse.

**Order 2's** two targets share a **472-line / 71-declaration block** (139 lines in
the port). Write it **once**, before either headline. Both also reuse SET-R-D
order 3 (`exists_isIntegralQExp_smul_atkinLehnerSlash_of_even`) and
`exists_algEquiv_laurentBaseChange_cover`. The `x1x0` target's second small block:
`conj_mem_Gamma1` **is** public in the hub (`…X1DiamondRationalForms`, promoted for
SET-R-D) — use it; **`T_mem_Gamma1` is not** (still `private` at
`Gamma0Integral.lean:1408`) — re-derive the four lines in place.

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem`
(read-only; never modify). **Statement = the `Theorems/Thm_<stem>.lean` wrapper**,
binders verbatim; proof = the matching `P2M/Sol/S_<stem>.lean`. Adapt proofs, never
statements. Note the two order-2 targets are **independent headlines over one
engine** — do not merge their statements, and do not weaken either.

## 2. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` per module; **no
whole-tree build**. Bound everything:
`timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`,
`flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth` (the pin's own `synthInstance.maxHeartbeats` scoped
options may be transcribed, as SET-R-D did); on a timeout quarantine and bisect,
and tell a blow-up from contention with CPU time. Serial builds only. Do not
commit.

## 3. The hub prohibition

**Do not edit any existing Lean module.** The definition layer and the
`Gamma0Integral.lean` promotions are done; do not re-promote, do not rename, do not
touch `FunctionFieldIsAlgClosed.lean`, `ValuationAtPlace.lean`,
`ModularForms/Defs/HeckeOperator.lean`, or anything else already in the tree. If a
needed helper is `private` in a hub, re-derive it locally as `private` in your
module and report it. If a promotion seems genuinely required, **stop and report**
with the declaration, host, reason and
`python3 tools/deps/build_ladder.py --edit <host>` — the manager decides.

## 4. Wiring

Per order, in `lean/spec/check_flt_statements.py`, appending **last** so no earlier
last-name match can flip:

* order 1: `P2M/Sol/S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean`
  and its `Theorems/` wrapper to `SOURCES`; `"FLTForHuman/ModularCurve/X1/FunctionFieldFinrankIsAlgClosed.lean"`
  to `PORT_FILES`.
* order 2: both `S_` files
  (`…_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar.lean`,
  `…_exists_algEquiv_x1x0FunctionFieldC_atkinLehner.lean`) and both wrappers to
  `SOURCES`; `"FLTForHuman/ModularCurve/X1/AtkinLehnerExchange.lean"` to
  `PORT_FILES`.

Target **0 mismatched, 0 missing**; mutation-test one headline per order and
revert.

## 5. Risks

* **The 8 suspect substitutions** (`port_plan`), all `def`-typed matches the parser
  cannot judge: `SFieldGen` → `modularFunctionField` (×2), `ALRational` → `PeriodPair.DiscriminantNeZero`
  (×2), `QuasiInv` → `PeriodPair.DiscriminantNeZero` (×2), `Γb` → `RelrankSol.GamGL`,
  `Γt` → `RelrankSol.Gam'GL`. Read both copies before applying any; the same class
  was wrong twice in the X_H topic. The remaining 38 substitutions are trusted but
  still worth a glance at the level-`N` spellings.
* **The `x1x0` target's hypotheses are inputs, not goals**: `HeckeBetaOneDefined`,
  `IsDiamondAut`, `IsBaseChangeAutOf`. Do not try to discharge them.
* Order 1's `Module.Free`/`synthInstance` instance-search walls were the previous
  module's known cost; if one appears, discharge it explicitly (as SET-R-D order 2
  did with `Module.Free.of_divisionRing`) rather than raising a bound.
* The `Cos`/`Finset` reindexing shape has cost earlier topics; keep the pin's
  concrete function types.

## 6. Stop and report

As SET-R-A §6; plus any reason to touch a module other than the two new ones and
the checker lists; plus a suspect substitution whose two copies disagree.

## 7. Completion report (per order)

Module path; public/`private` counts; every local `private` re-derivation with its
host; the shared-block dedup (how many lines were written once); tier 0 / tier 1
wall and CPU times; checker before → after and the mutation result; `#print axioms`
for each headline; the substitutions you resolved and the ones you declined;
anything you could not match, quoted.

## 8. Outcome (2026-10-08, landed and manager-verified)

Checker **6979 → 7218 identical (313 promoted, 83 renamed), 0 mismatched,
0 missing, 36 own (7254 checked)**, +239; no existing Lean module edited, nothing
committed; all three mutations (one in order 1, two in order 2) gave exactly one
`mismatched` and were reverted; axioms clean on all three headlines; tier 0/tier 1
green and the tree builds (4,348 jobs).

| order | module | lines | public / private | tier 0 | tier 1 |
|---|---|---:|---:|---:|---:|
| 1 | `ModularCurve/X1/FunctionFieldFinrankIsAlgClosed.lean` | 154 | 4 / 0 | 6.6 s | 8.2 s |
| 2 | `ModularCurve/X1/AtkinLehnerExchange.lean` | 2,110 | 235 / 0 | 24.9 s | 32.4 s |

Order 1's 78-line engine is imported from SET-R-D order 2's
`FunctionFieldIsAlgClosed.lean` rather than re-proved.

**The dedup deviates from the order, for a toolchain reason — recorded.** The
order said the 472-line shared block of the two Atkin–Lehner `S_` files is written
once. The implementer found that the genuinely generic engine — statements over an
abstract subgroup, with the closure facts in an `ALInputs` class — **does not
elaborate under this checkout's Lean `v4.34.0`**: section variables that occur only
in proofs are dropped from the local context (`variable (hγ : γ ∈ Γ₀ M)` is not
visible in a proof unless `hγ` occurs in the statement), and the pin's two `S_`
files rely on the v4.33.1 behaviour pervasively. Rewriting every proof to thread
its hypotheses explicitly was judged worse than the duplication. So the
**H-independent** half is shared once (58 declarations / ≈364 lines, plus imports
of the `A2ALInt` rows), and the **Γ-dependent** rows are written once per target
(86 declarations / 792 lines and 89 / 804) — because the two pin copies are
*different statements* under the same names (`Γt M H ℓ` vs `Γt M ℓ`,
`CohCarrier.GammaH M H` vs `Gamma1 M`), so they cannot be one declaration anyway.
This is the one place the set deviates from "write the block once"; the next
column that wants a *generic* Atkin–Lehner engine should budget for the explicit
hypothesis threading.

**All eight suspect substitutions were declined**, after reading both copies:
`SFieldGen` is `intFormRatiosC ℚ Γ`-as-a-field under `1 ∈ Γ.strictPeriods`, not the
level-`N` `modularFunctionField`; `ALRational`/`QuasiInv` are `Prop`s about the
Atkin–Lehner `alForm` and the `(ℓ+1)` exchange, not `PeriodPair.DiscriminantNeZero`;
`Γb`/`Γt` carry the level-`M` subgroup `H`, where `RelrankSol.GamGL`/`Gam'GL` are
the `H`-free groups. The rest were transcribed at the pin's own spelling.

**Correction to the scope (found here).** `TOPIC-qexp-successors-2.md` §5 had
claimed the hub's `…X1DiamondRationalForms.T_mem_Gamma1` was public; it is not
(still `private` at `Gamma0Integral.lean:1408` — the SET-R-D promotion took
sixteen rows and this was not one). The four-line pin copy is transcribed in
place; `conj_mem_Gamma1` **is** public and is reused. Both topics are corrected.

The dependent wave was not re-run for this set: neither module is imported by
anything yet, so nothing downstream is stale (the 4,348-job build above is the
modules plus their cone).
