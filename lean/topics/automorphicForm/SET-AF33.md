# SET-AF33 — the Weyl intertwining pair: the finite-slice integrability and its Euler product

**Status: LANDED 2026-11-07** — two orders on two new modules, run in parallel; §5 is the forecast
and §6 records the landing. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the final
read of the second round. It is the **thirty-third** `AutomorphicForm`-serving set — and the pair that
SET-AF27 §7 and the column's blueprint had recorded as *blocked*.

**2 rows / 2,640 silo / 1,072 net new math lines (`port_plan`) / 261 declaration groups**, of which
**1,499 declaration lines are already in the port** — the most composition-heavy pair on the shelf.

| row | silo | decls | what it says |
|---|---:|---:|---|
| `AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1,349 | 133 | for an induced-section vector at `etaFst`/`etaSnd` parameters with `Re s > 1/2`, the finite-adèle slice `t ↦ φ (adelicWeyl · n(0,t) · g)` is integrable |
| `AutomorphicForm.LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1,291 | 45 | the finite-adèle integral of a compactly-supported factor against the product of the unramified Weyl integrands off `S` equals the local integrals at `S` times the Euler product `∏' v ∉ S, (1 − χ v (ϖ v) N v ^ (-(2s+1)))` |

## 0. The read

The final read of the second round: `needed` **765 / 321,659**, frontier 1,651 / 805,717, ready
**62 / 16,628**, leaves 204 / 52,711, `AutomorphicForm` demand 275 / 121,503, `--selfcheck` PASS. Both
rows are on the ready block with complete closures.

## 1. The unblocking — FR-0151 was a scaffolder's mistake, not the port's

The pair was excluded from AF27 because two statements "could not be transcribed verbatim". Both were
re-diagnosed this pass, and **neither is a pin/port conflict**:

1. the 1,291 statement's qualified `NumberField.AdelicBox.integralFiniteAdeles` — the declaration
   **exists** in the port; it is simply declared in a module (`NumberTheory/NumberField/TateGlobal/IdeleNormValues.lean`)
   that the AF27 scaffold did not import. `#check @NumberField.AdelicBox.integralFiniteAdeles` succeeds
   once that module is imported, and the pin's qualified text needs no `open` at all.
2. the 1,349 statement's `(hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))` — the failure was `open scoped NNReal`
   missing: without it `ℝ≥0` in the `let α` block is not the type but an inequality, so the whole `let`
   collapsed into type-valued metavariables and the untyped binder reported `LE Type`. With
   `open scoped NNReal` the statement elaborates **verbatim**, untyped binder included.

So the pair is scaffoldable after all, and both scaffolds are checker-green (**1 ok each**). This is the
lesson the pass records (FR-0154): a scaffolding failure must be diagnosed as *environment* (a missing
import, a missing scoped open) or *conflict* (the port cannot state it) — and the first is the common
case. A "blocked" verdict written without that distinction can cost the shelf its largest subject for
weeks.

## 2. The price

| figure | value |
|---|---|
| raw `S_` lines | 2,640 |
| declaration lines | 2,574 |
| — duplicate copies | 3 |
| — boilerplate | 66 |
| distinct declaration groups | 261 |
| already in the port (vetted) | **1,499** (469 tier 1 + 1,030 tier 3) |
| **net new math lines** | **1,072** |

171 trusted substitutions, 8 suspect (`def`-typed matches — read the bodies). No definition gate:
`gate_scan` over the pair's `Def_` closure is 0 missing. `twin_scan`: `new` twice.

## 3. Homes — two modules, two orders, in parallel

The two rows are **different subjects** (an integrability statement over the finite adèles; an
Euler-product factorization), share no declaration, and each is a large file, so they are two modules
dispatched together on disjoint files:

| order | module | content |
|---|---|---|
| **AF33A** | `Adelic/WeylIntegrable/FiniteSlice.lean` | the 1,349 row, 133 declarations — the analytic core on the finite part |
| **AF33B** | `Adelic/LocalIntertwiningFinprod.lean` | the 1,291 row, 45 declarations — a **composition** row over the landed `LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion` (2,110) and `m_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top` (179) |

Both orders carry the surface gate as an explicit instruction (the pin's files are public
developments), and both are told the sibling file is off-limits.

## 4. The cut and the gates

Scaffolds: `1 ok / 0 mismatch / 0 missing` each, elaborating with the corrected environments (the
`DistribChar` import for `distribHaarChar`, `open scoped NNReal`, the `IdeleNormValues` import for the
qualified `integralFiniteAdeles`). Gates per order: checker 0/0 with the surface gate run, axioms on the
headline, silence and zero warnings, `dedup`/`move_dead`, and a consumer zone.

## 5. Forecast

| figure | before | after |
|---|---|---|
| `needed [F terminal]` | 765 / 321,659 | **763 / 320,587** |
| `needed [literal]` | 777 / 325,124 | **775 / 324,052** |
| frontier F | 1,651 / 805,717 | **1,653 / 807,357** |
| ready block | 62 / 16,628 | **60 / 13,988** (2 rows out; 0 in) |
| leaves block | 204 / 52,711 | **204 / 52,711** |
| `AutomorphicForm` demand | 275 / 121,503 | **273 / 118,863** |
| rows readied | — | see review |

## 6. The landing (2026-11-07)

Two orders, two new modules, both green.

| order | module | result |
|---|---|---|
| **A** | `Adelic/WeylIntegrable/FiniteSlice.lean` | **265 lines / 15 declarations** (headline + 14 helpers, nothing private); **15 ok / 0 / 0**; build 4.0 s; axioms clean; `dedup` 0; `move_dead` 0; consumer 0 errors |
| **B** | `Adelic/LocalIntertwiningFinprod.lean` | **1,315 lines / 87 declarations** (headline + the pin's whole 86-declaration ladder, **0 private**); **87 ok / 0 / 0**; build success; axioms clean; `dedup` 0; `move_dead` 0; consumer 0 errors |

**The pair was ~92 % already ported, and the measurement is the set's story.** A's pin file is 1,349
lines / 175 indexed declaration rows, and the worker verified by **recomputing statement hashes** that
**172 of the 175 were already byte-identical** in `WeylIntegrable/{Coset,Transfer,BoxBounds,LatticeEstimates,Assembly}.lean`;
the module therefore adds only five blocks (the slice identities, the finite-adèle measure algebra, the
`domGf` majorant, the continuity lemma and the kernel `integrable_weylIntegrand_finSlice`) in 170 lines
of Lean. Two pin names were deliberately not re-declared: `adelicWeyl_inv` (a byte-identical duplicate
of the pin's own `adelicWeyl_inv'`, landed at `Transfer:287`) and `tsum_idx_rpow_lt_top` (landed
unfolded at `LatticeEstimates:624`). B was a genuine transcription (none of its 87 declarations existed)
but a *composition* one: its two premises — the local unramified identity
(`integral_unramifiedWeylIntegrand_adicCompletion`, 2,110) and `m_prod`
(`tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top`, 179) — were both landed, and the worker's
closing judgement is worth keeping: **the local identity carries the mathematics** (it is the only step
that computes an integral into Euler factors, and its `(1 − χ(ϖ)N^{−(2s+1)})(1 − χ(ϖ)N^{−2s})⁻¹` pair is
where the statement's exponent bookkeeping comes from) while **`m_prod` carries the licence** to take the
`tprod` limit.

**Both modules dropped the pin's heartbeat overrides**: A has none to begin with, and B's pin file sets
`set_option maxHeartbeats 4000000` / `synthInstance.maxHeartbeats 400000` — the port's file elaborates
inside the 200,000 edit-loop budget with no per-declaration split.

**The re-read** (and one forecast slip of mine, recorded):

| figure | before | forecast | actual |
|---|---|---|---|
| `needed [F terminal]` | 765 / 321,659 | 763 / 320,587 | **763 / 319,019** |
| `needed [literal]` | 777 / 325,124 | 775 / 324,052 | **775 / 322,484** |
| frontier F | 1,651 / 805,717 | 1,653 / 807,357 | **1,653 / 808,357** |
| ready block | 62 / 16,628 | 60 / 13,988 | **60 / 13,988** ✓ |
| leaves block | 204 / 52,711 | 204 / 52,711 | **204 / 52,711** ✓ |
| `AutomorphicForm` demand | 275 / 121,503 | 273 / 118,863 | **273 / 118,863** ✓ |

The two wrong cells are an arithmetic slip of exactly the kind AF24 recorded: `needed` and the frontier
count **silo** lines (2,640), so they fall by the silo, not by the 1,072 *net*; the ready block and the
namespace demand were computed with the silo and came out right. Same rule, second miss — the brief's
forecast table should compute every line column from one number (the silo) and never mix in `port_plan`'s
net.

## 7. What this set does not do, and what the pair unblocks

- The **Euler-product consumer** `exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul`
  (995) needs this set *and* the meromorphic continuation beside it; it is the next block up.
- `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043) is a sibling of the 1,349 row
  (induced sections and the adelic height) and is the natural companion order.
- The **isCuspConstituent cluster** (94 nodes / 21,595 silo) is untouched, as are the Siegel/Petersson
  blocks; the `CuspidalSpectrum` carrier rows remain one premise short of their gateways.
