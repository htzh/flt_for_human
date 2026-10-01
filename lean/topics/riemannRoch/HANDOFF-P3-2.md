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

- **Checker:** `python3 spec/check_flt_statements.py` → **4182 identical / 0
  mismatched / 0 missing / 30 own-proof** (4212 checked) — 4144 before row 3.7, 4071
  before row 3.6, 4049 before the refactor round. Re-verified live.
- **Builds:** whole-tree `lake build` green (4,901 jobs) at the refactor round; rows
  3.6/3.7 and the K-side bridges landed six new modules with per-module builds and no
  cascade. `spec/RiemannRochConsumer.lean` exits 0 (Zone G added).
- Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.
- **The P3.2 refactor round (R1–R10) is done** ([PLAN-P3-2.md](PLAN-P3-2.md) §6). No
  row-2 debt is open except **R7**, kept as accepted duplication by human decision.
- **Rows 3.6 (K ending) and 3.7 (RR assembly) are done**, and the general
  `ResidueTheorem` over an algebraically closed field is produced:
  `ResidueTheorem/{KRatFunc,KCotrace,KFamily}.lean` (1,689 ln),
  `ResidueTheorem/RRAssembly.lean` (694 ln), `ResidueTheorem/GeneralFromK.lean`
  (~60 ln) — [WORKORDER-P3-6-kend.md](WORKORDER-P3-6-kend.md) §8,
  [WORKORDER-P3-7-rr-kend.md](WORKORDER-P3-7-rr-kend.md) §7.
  **Row 3.5 (the perfect-field ending, ≈7,050 written) is the last phase-3 port.**

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

Row 2 is **mathematically complete**, and its **debt is closed**: the R1–R10 round in
[PLAN-P3-2.md](PLAN-P3-2.md) §6 is executed, with R7 kept as accepted duplication
(§6.3) and R9 recorded as a miscategorised (non-)item.

**Not debt / out of scope** (PLAN-P3-2 §6.3): the six larger `evalAt_*` forward-cone
nodes; `Place_sum_ramificationIndex_mul_inertiaDeg` (already a substitute);
row **3.5** (the last phase-3 ending — the PF general-curve transport; the
algebraically-closed general `ResidueTheorem` is already produced via the K route); the
**R2 `Defs/`** audit (deferred by PLAN-RECTIFY-DEFS §7.4).

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

## 4. Refactor-round debt — EXECUTED (2026-09-30)

The P3.2 round is done; the authoritative dispositions are
[PLAN-P3-2.md](PLAN-P3-2.md) §6.1. Summary:

- **R1/R2** — the duplicated `private` `ord_add_eq_min` / `ag9b15u_*` were promoted
  public in `LocalResidue/Calculus.lean`; the `P1/EnginePrelude`/`P1/Differential`/
  `P1/DivPow` copies are deleted.
- **R3** — the `F ≃ₐ[K] F` action (`Place.ord_smul`/`deg_smul`, the `Divisor`
  `DistribMulAction` and its `smul_*`/`degree_smul` laws) is homed public in
  `Defs/SemilinearAut.lean`; the `P1/DXCoeff` copies are deleted.
- **R4** — deletion-only: the `P1/TraceEngine`/`P1/FinitePlaceResidue` copies of the
  ten helpers were dead, so they were removed and `Canonical/HasCanonicalDivisor` stays
  the single (private) home.
- **R5** — `P1/DivPow`'s public `kwHgfV352_localResidueCompletion_{spec,algebraMap}`
  are now about the public `Defs/TateResidueCurrency` def; the private def and the
  `_spec₀`/`_algebraMap₀` re-landings in `P1/DivPowEnding`, `Tate/Agreement`,
  `Tate/TraceCompletionCommute` are deleted.
- **R6** — `P1Tower.gen` is public in `P1/DivPow`; the `P1/DivPowEnding` re-landing is
  deleted.
- **R7** — kept: both `surjective_algebraMap_residueField_of_deg_eq_one` copies stay.
- **R8** — the `InlineSpecific` chain has the new public home
  `AlgebraicCurve/Place/Completion.lean`; the three `Tate/` private blocks are deleted.
- **R9** — no change: the `RatFuncDegree` helpers are *general* while the
  `P1/Dictionary` public statements are the pin's *specialised* dictionary nodes.
- **R10** — the seven `evalAt`/`IsRational` leaves moved to `Defs/PlaceEvaluation.lean`;
  `PlaceEvaluationAlgebra`'s duplicate private `evalAt_inv`/`evalAt_zpow` are deleted.

## 5. Reproduce / verify

```bash
cd lean
python3 spec/check_flt_statements.py                       # 4071 / 0 / 0 / 30
flock /tmp/flt_for_human.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.P1.Core
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/RiemannRochConsumer.lean
python3 ../tools/check_math_delimiters.py ../lean/topics/riemannRoch/*.md
```

Build economy: a per-module `lake build`, never a whole-tree build during a phase;
one whole-tree build at a refactor/definitions milestone (WORKFLOW §3). The executed
debt round's gate is PLAN-P3-2.md §6.4.

## 6. Open questions for the human

- The **P3.2 refactor round is done**; remaining row-2 duplication is only R7
  (accepted, human 2026-09-30).
- **Rows 3.6 (K ending) and 3.7 (RR assembly) are DONE**, plus the K-route general
  `ResidueTheorem` ([WORKORDER-P3-6-kend.md](WORKORDER-P3-6-kend.md) §8,
  [WORKORDER-P3-7-rr-kend.md](WORKORDER-P3-7-rr-kend.md) §7). **Row 3.5 (the
  perfect-field ending, ≈7,050 written) has no plan file yet** and is the last phase-3
  port; `PLAN-P3-3.md` covers rows 3.3/3.4. The next session needs a `PLAN-P3-4`/`-5`
  (or an extension of `PLAN-P3-3`).
- The **R2 `Defs/` audit** stays deferred by decision.
