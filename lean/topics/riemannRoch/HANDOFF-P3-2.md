# Handoff — phase 3.2 after chunk 4 (2026-09-30)

**For the next session.** This session finished porting the **master ℙ¹ file** of
row 2. It stops here by human instruction, with the remaining row-2 tails, the
`Defs/` home audit and the closeout refactor left to the new session. Read
[WORKFLOW.md](WORKFLOW.md) first — this note assumes its loop, commands and review
checklist.

## 1. State

- **Checker:** `python3 spec/check_flt_statements.py` → **3642 identical / 0
  mismatched / 0 missing / 30 own-proof** (3672 checked).
- **Builds:** all modules green; no whole-tree build has been run since phase 3.1's
  debt round (every 3.2 set landed in new files or appended to the then-unimported
  `P1ResidueCore`).
- Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

**Landed in this session** (phase 3.1 was already complete):

| module | ln | set | content |
|---|---:|---|---|
| `Defs/PlaceEvaluation.lean` | 104 | 3.2a | the pin's `PlaceEvaluation` interface (defs) |
| `Defs/PlaceEvaluationAlgebra.lean` | 185 | 3.2a (gap B) | the `Divisor.evalFun_*` law layer |
| `Defs/P1Dictionary.lean` | 1,344 | 3.2a | the ℙ¹ place/ord dictionary + `placeOfPoint` block |
| `Defs/LocalResidueCalculus.lean` | 1,229 | 3.2d′ | the generic local-residue calculus (`p0n22_cpf_res_*`) |
| `Defs/P1ResidueCore.lean` | **6,470** | 3.2b–e | the master ℙ¹ file (declarations #0–#579), including the atom-1 headline `RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero` and the shared K-base engine `residueTheoremK_ratFunc_of_isAlgClosed_*` |

Audits: `AUDIT-mathlib-p3-2a/b/c/d/dprime/e.md`. Plans and work orders:
`PLAN-P3-2.md`, `WORKORDER-P3-2a…`, `WORKORDER-P3-2b/c/d/dprime/e…`. Friction:
`../../logs/riemann-roch-friction.md` § Set 3.2a–3.2e.

## 2. What remains in row 2 (small)

The master file is done; its **three sibling atom files** still have unique tails
(the master shared 97% / 69% / 49% with them, so these are ≈1k written total):

1. `P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero.lean`
   (atom 2, two-place cancellation) — ~6 unique declarations;
2. `..._trace_localResidue_finitePlace_div_pow_eq_zero.lean` (atom 3) — ~61 unique;
3. `..._residueTheorem_ratFunc_of_perfectField.lean` (the PF base case) — ~38 unique.

Plus the small `Place.evalAt_*` extension nodes (§4 below) are **out of row 2**
(forward-cone), and `Place_sum_ramificationIndex_mul_inertiaDeg` is already a
substitute (`SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg`,
`Defs/PushPull.lean:678` + `WeilExchange/FiberOverCount.lean`).

**Also outstanding from the plan:** rows 3.3 (Tate agreement ≈8k), 3.4
(trace-completion commutation ≈525), 3.5 (PF ending ≈7k), 3.6 (K ending ≈2k), 3.7
(RR assembly ≈400) — see `../PORTING-RR.md` §3. Row 6 stays residual (human
decision: the rows-2/6 duplication is known; do not merge now).

## 3. The `Defs/` home rule and the files to audit/move (human directive)

**Rule (human, 2026-09-30): `Defs/` is for *definitions*. A theory file — a module
whose weight is proofs — must not live there, because a consumer that only needs
the definitions should not import a large proof theory.** This surfaced because the
ported pin files were large opaque theories with their own private defs and lemmas.

Measured disposition (lines / `def`-like / `theorem`-like declarations, regex count;
`THEORY` = theorems outnumber definitions):

| `Defs/` file | ln | defs | thms | verdict |
|---|---:|---:|---:|---|
| `P1ResidueCore.lean` | 6,470 | 46 | 306 | **MOVE** → `AlgebraicCurve/LocalResidue/P1Core.lean` |
| `CanonicalLocalResidueInstanceV2.lean` | 1,694 | 33 | 88 | **MOVE** (the `HasCanonicalLocalResidueKStar` construction) → `LocalResidue/Instance.lean` |
| `P1Dictionary.lean` | 1,344 | 4 | 75 | **MOVE** (dictionary *statements* are theory) → `LocalResidue/P1Dictionary.lean` or a `P1/` dir |
| `LocalResidueCalculus.lean` | 1,229 | 0 | 35 | **MOVE** → `LocalResidue/Calculus.lean` (already decided; the move was deferred to avoid racing the chunk-4 worker) |
| `PlaceEvaluationAlgebra.lean` | 185 | 0 | 16 | **MOVE** (pure law layer) → `LocalResidue/EvaluationAlgebra.lean` |
| `PushPull.lean` | 756 | 20 | 49 | audit: mixed; the `Place.restrict`/fibre *definitions* stay, the order theory may split |
| `PlacesOverDVR.lean` | 448 | 14 | 31 | audit |
| `Place.lean` | 392 | 13 | 36 | audit: the `Place` structure + API; likely split defs/theory |
| `AdelicIndex.lean` | 442 | 24 | 44 | audit |
| `Correspondence.lean` | 405 | 16 | 26 | audit |
| `PlaceDictionary.lean` | 398 | 5 | 12 | audit (mostly proofs) |
| `LocalResidue.lean` | 331 | 15 | 22 | audit: `LocalResidueData` defs stay; the API theory may split |
| `WeilOfKaehler.lean` | 359 | 5 | 19 | audit |
| `SemilinearAut.lean` | 221 | 11 | 20 | audit |
| `RatFuncPlaces.lean` | 272 | 7 | 15 | audit |
| `Repartitions.lean` | 157 | 6 | 13 | audit |
| `IsCurveOver.lean` | 86 | 4 | 6 | audit |
| `CanonicalDivisor.lean` | 152 | 10 | 12 | audit |
| `PlaceCompletion.lean` | 551 | 18 | 16 | **keep** (defs ≥ thms) but review |
| `Divisor.lean` | 90 | 9 | 6 | keep |
| `PoleDivisorPackage.lean` | 108 | 10 | 0 | keep |
| `RiemannRochRows.lean` | 73 | 6 | 2 | keep |
| `PlaceEvaluation.lean` | 104 | 5 | 9 | keep (the companion defs file) |
| the tiny leaves (`IntegralAdjoin`, `KaehlerTranscendental`, `RegularDifferentials`, `CanonicalDivisorUniformizer`, …) | ≤96 | ~0 | 1–3 | keep |

**Executing a move is a cascade** (module names change): rename the file, fix every
`import`, append the new module to `PORT_FILES`/`SOURCES` in
`spec/check_flt_statements.py`, and end with **one whole-tree `lake build`** — the
WORKFLOW §3 refactor-round pattern. A good first slice is the four clear MOVEs
(`P1ResidueCore`, `CanonicalLocalResidueInstanceV2`, `P1Dictionary`,
`LocalResidueCalculus`, `PlaceEvaluationAlgebra`) into a new
`AlgebraicCurve/LocalResidue/` directory, since nothing imports them yet except
`P1ResidueCore → LocalResidueCalculus`.

## 4. Refactor-round debt (recorded, do all in one bounded pass)

1. **Five duplicated private helpers**: `Place.ord_add_eq_min` and the four
   `ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_*` are `private`
   in **both** `LocalResidueCalculus.lean` and `P1ResidueCore.lean`. Fix: make them
   public in `LocalResidueCalculus` (the generic home), drop the core's copies.
   (A first attempt failed because making them public clashed with the core's
   `private` copies — the *core's* copies must be removed at the same time; and a
   scripted line-range removal crossed `section`/`end` and was reverted. **Do
   declaration surgery by hand with backups.**)
2. **Ten pin-private `_s12` rows** re-landed `private` in `P1ResidueCore` chunk 3
   (`ValuationSubring.ofPrime_congr`, `Place.inv_mem`/`div_mem_of_not_mem_centerIdeal`,
   `Place.toKSubalgebra`, `Transcendental.{isPrincipalIdealRing,isDedekindDomain,isIntegrallyClosed,isNoetherianRing}_adjoin`,
   `Algebra.FiniteType.adjoin_singleton`, `Transcendental.inv`) duplicate `private`
   copies in `Canonical/HasCanonicalDivisor.lean`. Promote there (public) and import.
3. **The `F ≃ₐ[K] F` divisor-action layer** transcribed `private` in chunk 2 for rows
   #240/#241/#243/#244 (`Place.ord_smul`, `Place.deg_smul`, the
   `MulAction`/`DistribMulAction` instances, `smul_*`, `degree_smul`) — the layer
   `Defs/SemilinearAut.lean` deliberately deferred. Promote or home it.
4. **`Place.differentialCoeff_add''`** re-landed `private` in chunk 4 (row #483
   consumes it; `LocalResidueCalculus`'s copy is private).
5. **`P1Dictionary` transcribes** public copies of `RatFuncDegree`'s private
   `exists_sub_algebraMap_intDegree_neg` / `single_add_single_apply_eq_ord` /
   `degree_single_add_single`; promote the `RatFuncDegree` copies and drop these.
6. **The seven `evalAt`/`IsRational` leaves** in `P1Dictionary` belong beside the
   `evalAt` definition (`PlaceEvaluation`).
7. **Scratch files left:** `lean/ScratchAuditP32b.lean`, `…P32bPort.lean`,
   `…P32c.lean`, `…P32d.lean`, `…P32dprime.lean`, `…P32e.lean` (audit probes, safe
   to delete). Worker tooling under `tools/deps/build/` (`gen_p32e.py`,
   `p32e_append.lean`) is gitignored.

## 5. Reproduce / verify

```bash
cd lean
python3 spec/check_flt_statements.py                       # 3642 / 0 / 0 / 30
flock /tmp/flt_for_human.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Defs.P1ResidueCore
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/RiemannRochConsumer.lean
python3 ../tools/check_math_delimiters.py ../lean/topics/riemannRoch/*.md
```

The row-2 measurement and the boundary rationale are in `PLAN-P3-2.md` §1–§3;
`AUDIT-mathlib-p3-2e.md` (634 ln; 28/111/6) has the chunk-4 per-row table. The
`gen_p32e.py` approach (generate an append from the inventory) is worth reusing for
the sibling atom files: it lets a worker omit the substituted rows mechanically, but
**check the omit list against the audit** — it silently kept one substituted row
(#459) and that would have broken the build.

## 6. Open questions for the human

- Confirm the `AlgebraicCurve/LocalResidue/` directory name and the five MOVEs in §3
  (and whether `P1Dictionary` belongs there or in its own `P1/` dir).
- Whether the sibling atom tails (§2) should be a final 3.2f set or folded into the
  new session's first dispatch.
- Rows 3.3–3.7 sequencing: the shared ℙ¹ engine is now landed, so 3.3 (Tate) is the
  next large block.
