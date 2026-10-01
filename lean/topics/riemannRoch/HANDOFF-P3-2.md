# Handoff — phase 3.2 after the R1 definitions round (2026-09-30)

**For the next session.** Row 2 (3.2) is **mathematically complete**. The
authoritative, tree-verified **residual-items checklist is
[PLAN-P3-2.md](PLAN-P3-2.md) §6**, not this file. Read
[WORKFLOW.md](WORKFLOW.md) first — this note assumes its loop, commands and review
checklist.

> **Update banner (2026-09-30, documentation pass).** An earlier revision of this
> handoff said the master ℙ¹ file was `Defs/P1ResidueCore.lean`, that the three
> sibling atom tails, the `Defs/` moves and the closeout refactor were still pending,
> and that the checker was **3642 / 0 / 0 / 30**. All of that is **stale**: the R1
> definitions round ([PLAN-RECTIFY-DEFS.md](PLAN-RECTIFY-DEFS.md) §5.1) moved/split
> the monolith into the `P1/` chain, and set 3.2g landed `P1/DivPowEnding.lean` +
> `P1/PerfectBase.lean`. This file now records only the corrected state; the debt
> lives in PLAN-P3-2.md §6. No code changed in the documentation pass.

## 1. State

- **Checker:** `python3 spec/check_flt_statements.py` → **4049 identical / 0
  mismatched / 0 missing / 30 own-proof** (4079 checked). Re-verified live in the
  documentation pass.
- **Builds:** whole-tree `lake build` green at the 3.2g closeout (4,900 jobs); no
  whole-tree build was re-run for the documentation pass (no code changed).
- Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

**Landed for row 2** (phase 3.1 was already complete):

| module | set | content |
|---|---|---|
| `Defs/PlaceEvaluation.lean` | 3.2a | the pin's `PlaceEvaluation` interface (defs) |
| `Defs/PlaceEvaluationAlgebra.lean` | 3.2a (gap B) | the `Divisor.evalFun_*` law layer |
| `P1/Dictionary.lean` | 3.2a (`Defs/` before R1) | the ℙ¹ place/ord dictionary + `placeOfPoint` block |
| `LocalResidue/Calculus.lean` | 3.2d′ (`Defs/` before R1) | the generic local-residue calculus (`p0n22_cpf_res_*`) |
| `LocalResidue/Instance.lean` | 3.1b-ii (`Defs/` before R1) | the `HasCanonicalLocalResidueKStar` producer |
| the 15-module `P1/` chain | 3.2b–e, split by R1 | the master ℙ¹ file (`EnginePrelude` … `Core`), incl. atom 1 and the shared K-base engine |
| `P1/TwoPlace.lean` | 3.2f | atom-2 two-place cancellation tail + headline |
| `P1/DivPow.lean` | 3.2f | atom-3 `P1Tower` tail |
| `P1/DivPowEnding.lean` | 3.2g | atom-3 headline `…finitePlace_div_pow_eq_zero` |
| `P1/PerfectBase.lean` | 3.2g | PF base `residueTheorem_ratFunc_of_perfectField` |
| `Tate/*`, `Defs/TateResidueCurrency.lean` | 3.3/3.4 | the Tate agreement + trace-completion commutation (rows 3.3/3.4) |

Audits: `AUDIT-mathlib-p3-2a/b/c/d/dprime/e/f/g.md`, `AUDIT-mathlib-p3-3{a,b,c,d}.md`,
`AUDIT-mathlib-p3-4.md`. Plans/work orders: `PLAN-P3-2.md`, `PLAN-P3-3.md`,
`PLAN-RECTIFY-DEFS.md`, `WORKORDER-P3-2a…`. Friction:
`../../logs/riemann-roch-friction.md` § Set 3.2a–3.2g.

## 2. What remains in row 2

Row 2 is **mathematically complete**. The remaining **row-2 debt** is the
promotion/duplication list in [PLAN-P3-2.md](PLAN-P3-2.md) §6.1 (**R1–R10**); items
already resolved are marked stale in §6.2.

**Not debt / out of scope** (PLAN-P3-2 §6.3): the six larger `evalAt_*` forward-cone
nodes; `Place_sum_ramificationIndex_mul_inertiaDeg` (already a substitute);
rows **3.5/3.6/3.7**; **row 6** (residual by human decision); the **R2 `Defs/`**
audit (deferred by PLAN-RECTIFY-DEFS §7.4).

*The earlier "three sibling atom tails" list is landed and no longer applies:* atom 2
is `P1/TwoPlace.lean`, atom 3 is `P1/DivPow.lean` + `P1/DivPowEnding.lean`, and the PF
base case is `P1/PerfectBase.lean`.

## 3. The `Defs/` home rule — executed by R1

**Rule (human, 2026-09-30): `Defs/` is for *definitions*; a proof-weighted theory
module must not live there**, because a consumer that only needs the definitions must
not import a large proof theory.

R1 executed the moves (PLAN-RECTIFY-DEFS.md §5.1): `P1Dictionary` →
`P1/Dictionary.lean`, `LocalResidueCalculus` → `LocalResidue/Calculus.lean`,
`CanonicalLocalResidueInstanceV2` → `LocalResidue/Instance.lean`, and
`Defs/P1ResidueCore.lean` → the 15-module `P1/` chain. `PlaceEvaluationAlgebra` stays
in `Defs/` by the adapter exception. Three cross-slice `private` helpers were promoted
in the same round.

The generic/mixed `Defs/` audit (the `Place/` + `Adeles/` homes) is **R2, deferred**
to its own bounded round (PLAN-RECTIFY-DEFS.md §7.4) — it is not a row-2 debt.

## 4. Refactor-round debt

**Superseded by [PLAN-P3-2.md](PLAN-P3-2.md) §6.1/§6.2** (tree-verified). The old §4
list, with current status:

1. five duplicated `private` helpers (`ord_add_eq_min` + the four `ag9b15u_*`) —
   **real**, still duplicated; R1 spread the copies, see PLAN-P3-2 **R1/R2**;
2. ten pin-private `_s12` rows — **real but relocated** (they survive without the
   `_s12` suffix in `P1/TraceEngine.lean`/`P1/FinitePlaceResidue.lean`), PLAN-P3-2
   **R4**;
3. the `F ≃ₐ[K] F` divisor-action layer — **real**, but the base `Place` action is
   already public in `Defs/SemilinearAut.lean`; only the `Divisor`-level copies remain
   in `P1/DXCoeff.lean`, PLAN-P3-2 **R3**;
4. `Place.differentialCoeff_add''` — **resolved by R1** (public at
   `LocalResidue/Calculus.lean:109`);
5. `P1Dictionary` transcriptions of `RatFuncDegree` private helpers — **real**,
   PLAN-P3-2 **R9**;
6. the seven `evalAt`/`IsRational` leaves in the wrong home — **real**, PLAN-P3-2
   **R10**;
7. scratch files — **gone** (no `Scratch*.lean`).

Plus the P3.2f/g debts not in the old list: `kwHgfV352_localResidueCompletion` (**R5**),
`P1Tower.gen` (**R6**), `surjective_algebraMap_residueField_of_deg_eq_one'` (**R7**),
the `InlineSpecific` completion chain (**R8**).

## 5. Reproduce / verify

```bash
cd lean
python3 spec/check_flt_statements.py                       # 4049 / 0 / 0 / 30
flock /tmp/flt_for_human.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.P1.Core
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/RiemannRochConsumer.lean
python3 ../tools/check_math_delimiters.py ../lean/topics/riemannRoch/*.md
```

Build economy: a per-module `lake build`, never a whole-tree build during a phase;
one whole-tree build at a refactor/definitions milestone (WORKFLOW §3). The debt
round's plan is PLAN-P3-2.md §6.4.

## 6. Open questions for the human

- Whether/when to take up the **P3.2 refactor round** (PLAN-P3-2.md §6.4) — the human
  elected a **documentation-only closeout** on 2026-09-30.
- **Rows 3.5–3.7** (PF ending, K ending, RR assembly) have **no plan file yet**;
  `PLAN-P3-3.md` covers only rows 3.3/3.4. The next phase needs a `PLAN-P3-4` (or an
  extension of `PLAN-P3-3`).
- The **R2 `Defs/` audit** stays deferred by decision.
