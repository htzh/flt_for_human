# SET-AF44 — the valuation approximation toolkit: normalization, partial fractions, strong approximation

**Status: LANDED 2026-11-12** — §1–3 the rows, price and manager's layer, §5 the forecast, §6 the landing record and the re-read. Read off the D–S shelf
with the recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md),
on the read SET-AF42/43's landing left, and cut from the **leaves block** — the `--include-leaves` half of
the canonical read, which is where the remaining cheap rows are. Forty-fourth set of the column, the first
whose rows are all `ValuationSubring.*`, and the best return-per-silo cut the column has measured.

**4 rows / 2,004 silo / 1,800 net (`port_plan`) in ≈1,700 written lines and 121 declaration groups**, none
in the port. **Return, measured by `af24-return.py`: 5 rows / 1,848 silo** — a ratio of 0.92, and two of
the readied rows (1,082 and 848 silo) become *one premise* away from two further large rows.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **1** | `ValuationSubring.exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul` | 705 | 1/1 | *normalization*: a sum `y = ∑ w i * z i` whose `z i` lie in every valuation subring containing `L` and `f`, and whose `w i` have `f`-cleared denominators with coefficients in `A`, can be rewritten with the scalars in `A` and the remainders small at every such valuation |
| **2** | `ValuationSubring.exists_aeval_div_eq_aeval_div_add_aeval_inv_div` | 672 | 1/1 | *partial fractions at infinity*: `p(f)/t(f) = p₁(f)/t₁(f) + q(f⁻¹)/s(f⁻¹)` with `p₁`, `q` coefficient-wise in `A` and both denominators units at `0` with small higher coefficients |
| **3** | `ValuationSubring.exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem` | 310 | 1/1 | *constancy*: if `x * aeval f t` lies in every valuation subring containing `L` and `f`, and `x * aeval f⁻¹ t'` in every one containing `f⁻¹`, then `x` is a constant of `L` |
| **4** | `ValuationSubring.exists_forall_mem_and_sub_mem_nonunits` | 317 | 1/1 | *strong approximation*: for a finite antichain of valuation subrings `R i` of `K` and `a i ∈ R i`, there is `z` with `z ∈ R i` and `z - a i ∈ (R i).nonunits` for every `i` |

## 0. The read

The read SET-AF42/43's landing left (corrected: the five `ModularCurve` phi markers unported):

| figure | value |
|---|---|
| `needed [F terminal]` | **726 / 305,262** |
| `needed [literal]` | 742 / 310,681 |
| frontier F | 1,685 / 819,266 |
| ready rows | 45 / 8,744 |
| leaves | 194 / 48,760 |
| `ValuationSubring` demand | 24 / 6,218 |
| `AlgebraicCurve` demand | 48 / 19,391 |
| withheld | 4 rows |

All four rows are on the **leaves** block. **The premise audit is empty** (`premises = 0` on all four: the
pin's `S_` files are premise-free) and so is the **definition gate** — the four wrappers import
`Mathlib`-level modules and `P2M.Util` only, not one `Definitions/Def_*` line (FR-0049's check by hand).

**The four pin files import `Mathlib` wholesale**, which is the set's one real risk: the port must not, so
each module's imports are a *union of specific mathlib modules* that the proofs actually use (the
scaffolds carry a first cut: `RingTheory.Valuation.{ValuationSubring,Extension}`,
`FieldTheory.IntermediateField.Adjoin.Basic`, `FieldTheory.IsAlgClosed.Basic`,
`LinearAlgebra.LinearIndependent.Basic`, `LinearAlgebra.Finsupp.LinearCombination`,
`Algebra.Polynomial.{Basic,Eval.Defs,Div}`, `RingTheory.LocalRing.Basic` and `Mathlib.Tactic`). A missing
specific module is a report, not a silent `import Mathlib` (82 port modules already import `Mathlib.Tactic`,
so that umbrella is available; `import Mathlib` is not).

## 1. The rows, and why these four

The four are one toolkit with one consumer block: they are the membership tests of the **valuation
spectrum** that the `AlgebraicCurve.RegularProlongation` residue computation uses. Rows 1 and 3 read "lies
in every valuation subring containing `L` and `f`" as a *coefficient condition in `A`*; row 2 is the
Laurent decomposition at infinity that makes the two-chart argument work; row 4 is the approximation
theorem the residue comparison needs (an antichain, not a chain, which is the sharp form here).

**Why this cut, on the leaves block.** The recipe's §1 measures leaves by return, and this block is the
shelf's leader by a wide margin: 4 rows / 2,004 silo ready **five** rows / 1,848 silo, among them
`ValuationSubring.exists_valuation_mul_eq_one_of_forall_sup_eq_top` (**870**) and
`AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le` (**427**), the latter being the single
premise of two further rows of 1,082 and 848 silo. No other leaf block comes close: the `NumberField.AdelicBox`
block (7 rows / 1,177) readies **0**, the `AutomorphicForm.CuspidalConstituent` block (6 rows / 1,288)
readies 637, the idèle/Haar-quotient block (5 rows / 1,610) readies 106.

The set is above the recipe's 1,300–1,600 silo band; it is taken whole because the return is 92% of its
silo — the AF21 precedent (2,352 silo) for a cut chosen on the return column rather than on the band.

## 2. The price

| figure | value |
|---|---:|
| raw `S_` lines | 2,004 |
| declaration lines | 1,963 |
| — duplicate copies | 163 |
| — boilerplate | 41 |
| distinct declaration groups | 121 |
| once-cost after dedup | 1,800 |
| already in the port | **0** |
| **net new math lines** | **1,800** |
| written (two orders) | ≈1,700 |

`port_advise` reports no trusted substitute. Four *binder-skeleton* pointers are refused after reading:
`valuation_algebraMap_eq_one` and `valuation_algebraMap_le_one` (the port's `AlgebraicCurve/DeuringNormResidue.lean`
has copies under different file-level binders — a candidate for a later promotion, not a substitution for
a public pin declaration), and `sum` twice (a type-only match to `ModularCurve.RelrankSol.An1.sum`).

## 3. The manager's layer, landed (do not redo it)

1. **Three modules exist, elaborate and are checker-green**, each in `FLTForHuman/FieldTheory/` — the
   mathlib-supplement home (the pin's namespaces are mathlib's `ValuationSubring`, and a later theory can
   state against them):

| module | scaffold | declarations | `check_port` | sorries |
|---|---|---:|---|---:|
| `ValuationSubringPolynomial.lean` | 400 lines | 69 | **69 ok / 0 mismatch / 0 missing** | 61 |
| `ValuationSubringPartialFraction.lean` | 316 | 62 | **62 ok / 0 / 0** | 58 |
| `ValuationSubringApproximation.lean` | 116 | 17 | **17 ok / 0 / 0** | 15 |

   All **148 public statements of the four pin files are verified verbatim**; the fourteen data definitions
   are transcribed; all three build.
2. **The pin's task-label namespaces (`ZfSol`, `P1aSol`, `E1Sol`, `W7XK3A`) are nested under
   `ValuationSubring`**, so the declarations are `ValuationSubring.<Label>.<name>` and the headlines are at
   the wrappers' names `ValuationSubring.<name>`. The checker matches the last name (it read 148 `ok`).
3. **No `own:` row, no marker, no `set_option` beyond `autoImplicit false`**; the pin's `Mathlib` import is
   **not** carried.
4. **No import, namespace or `spec-pin:` line is the worker's to change** — a missing mathlib module is a
   report (trap 1 of the orders).

## 4. Orders and gates

`tmp/af44/WORKORDER-AF44A-valuation-normalization.md` (row 1 + row 3, module A: 1,015 silo, 69
declarations) and `tmp/af44/WORKORDER-AF44B-partial-fractions.md` (rows 2 + 4, modules B and C: 989 silo,
79 declarations). Disjoint modules, no cross-import, so they run in parallel. Standard gates:
`check_port --force` at **69 / 62 / 17 ok, 0 mismatch / 0 missing**, axioms clean on the four headlines,
each module's own `lake build` under `flock`/`timeout` with no tree build, silence and zero warnings,
`dedup --within --module <Name>` / `move_dead` per module, and one `spec/` consumer zone per order.

## 5. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 726 / 305,262 | **722 / 303,258** |
| `needed [literal]` | 742 / 310,681 | **738 / 308,677** |
| frontier F | 1,685 / 819,266 | **1,689 / 821,270** |
| ready rows | 45 / 8,744 | **50 / 10,592** |
| leaves | 194 / 48,760 | **190 / 46,756** |
| `ValuationSubring` demand | 24 / 6,218 | **20 / 4,214** |
| `AlgebraicCurve` demand | 48 / 19,391 | 48 / 19,391 |

**Rows readied: five / 1,848 silo** — three `ValuationSubring.*` (870 + 337 + 138) and two
`AlgebraicCurve.RegularProlongation.*` (427 + 76), the 427 being the sole premise of the 1,082- and
848-silo rows that this set therefore moves to one premise each.

## 6. The landing (2026-11-12)

Two orders, three modules, all gates green; no blocker, nothing left undone.

| order | module | lines | proofs | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **44A** | `FieldTheory/ValuationSubringPolynomial.lean` | 400 → **1,058** | 61 | **69 ok / 0 / 0** | 6.5 s, silent | 2/2 clean |
| **44B** | `FieldTheory/ValuationSubringPartialFraction.lean` | 316 → **709** | 58 | **62 ok / 0 / 0** | 7.1 s, silent | 1/1 clean |
| **44B** | `FieldTheory/ValuationSubringApproximation.lean` | 116 → **339** | 15 | **17 ok / 0 / 0** | 4.4 s, silent | 1/1 clean |
| | **3 modules** | **2,106 lines** | 134 | **148 ok, 0 mismatch, 0 missing, 0 own** | | 4/4 |

**What the set consumed**: 4 rows / 2,004 silo in **1,273 written proof lines** over the three verified
scaffolds (832 lines) — 2,106 module lines for 2,004 silo. `move_dead` reports **0 dead** on all three;
`dedup` reports **0** clusters on the partial-fraction module, **1** on the approximation module (the pin's
own prime-version + public-alias pair, 8 lines) and **4** on the normalization module (54 lines: the pin's
`ZfSol`/`E1Sol` per-file preludes, see §6.1.3).

### 6.1 Deviations held for review

1. **One mathlib import added**, in the normalization module: `Mathlib.RingTheory.Valuation.LocalSubring`,
   the **sole** v4.34 home of `iInf_valuationSubring_superset` (the constancy criterion's key step). No
   other import changed; no module needed `import Mathlib`, which the pin files all carry.
2. **A namespace-shadowing trap, met twice and worth the record**: inside the port's
   `namespace ValuationSubring`, v4.34's own `ValuationSubring.add_mem`/`neg_mem`/`mul_mem` (declared with
   explicit `(x y : K)`) shadow `Subring`'s, so the pin's `add_mem (hp j) (hq j)` must be written with the
   binder or as `AddMemClass.add_mem` (7 sites in 44A, 3 in 44B). This is a *scoping* difference between the
   pin's `P2MW.S_…` wrapper namespace and the port's nested one — no mathematical change (FR-0170).
3. **Four intra-module `dedup` clusters are kept, and the reason is the pin's shape**: `ZfSol` and `E1Sol`
   each carry their own `IsGood`, `IsGood.valuation_le`, `IsGood.ne_zero` and
   `prod_X_sub_C_eq_C_mul_prod_one_sub`, because each pin file is self-contained under `import Mathlib`.
   They are distinct public declarations at distinct pin names in distinct namespaces, all 69 are
   `check_port`-verified, and folding one into the other would either drop a pin declaration or couple two
   namespaces whose whole point is that they are separate criteria. 27 of the 54 removable lines are the
   duplicated proofs; the rest is the duplicated *statements*, which the port keeps on purpose.
4. **The rest is v4.34 proof text**: `if_neg` → `ite_eq_right` (6 sites), `zero_le'` → `zero_le` (16),
   `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right`; `caseA`/`caseB` written bare inside `ZfSol.main`
   (a `ZfSol.`-prefixed self-reference does not resolve from inside the nested namespace — same constant);
   the pre-existing `omit [IsAlgClosed L] in` lines are the pin's.
5. **Both orders' consumer suggestions had to be replaced, and in both cases the suggestion was
   *untypeable mathematics*, not a mismatch**: `t = X` can never satisfy the constancy criterion's
   hypothesis (`X.coeff 0 = 0`, so `A.valuation (t.coeff 0) = 0 ≠ 1` for every valuation subring), and
   `t = 1 + X` can never satisfy the partial-fraction hypothesis (`(1 + X).coeff 1 = 1` has valuation `1`,
   and no valuation subring of a field makes `1` small). The zones were read at the pin's own good shape
   `t = 1 - C c * X` (`A.valuation c < 1`), which is what `IsGood.one_sub` provides; both substitutions are
   recorded in the consumer files and logged as FR-0171.

### 6.2 The re-read, exact on all eight cells

| figure | before | forecast | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 726 / 305,262 | 722 / 303,258 | **722 / 303,258** ✓ |
| `needed [literal]` | 742 / 310,681 | 738 / 308,677 | **738 / 308,677** ✓ |
| frontier F | 1,685 / 819,266 | 1,689 / 821,270 | **1,689 / 821,270** ✓ |
| ready rows | 45 / 8,744 | 50 / 10,592 | **50 / 10,592** ✓ |
| leaves | 194 / 48,760 | 190 / 46,756 | **190 / 46,756** ✓ |
| `ValuationSubring` demand | 24 / 6,218 | 20 / 4,214 | **20 / 4,214** ✓ |
| `AlgebraicCurve` demand | 48 / 19,391 | unchanged | **48 / 19,391** ✓ |

**Rows readied: the five the return column priced, to the line** — 870 + 427 + 337 + 138 + 76 = **1,848
silo**, with the 427 (`RegularProlongation.sum_finrank_adjoin_residue_le`) the sole premise of the 1,082-
and 848-silo rows, which this set therefore moves to one premise each. A set of 2,004 silo that readies
1,848 is the best return the column has recorded, and it is the recipe's own argument for reading the
leaves block before the ready block.

## 7. What this set does not do

- **The two rows the 427 unlocks** (`exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq`
  1,082 and `finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq` 848) stay: each needs the 427 *and* the
  1,848 of new ready work, so they are AF45's head.
- **The rest of the `ValuationSubring` block** — 20 rows / 4,214 silo after this set — is named for the next
  pass: `exists_valuation_mul_eq_one_of_forall_sup_eq_top` (870, readied here),
  `exists_sub_mem_nonunits_of_finrank_le_card` (337, readied), `exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv`
  (138, readied), `ringKrullDim_le_ringKrullDim_comap_add_trdeg` (269),
  `exists_smul_mem_of_transcendental_residue` (262), `isPrincipalIdealRing_of_finiteDimensional_adjoin`
  (259, **36 project consumers**), `natDegree_map_eq_card_roots_of_splits` (174),
  `exists_le_forall_mem_iff_apply_mem` (168), `mem_of_forall_mem_iff_of_subset` (126),
  `exists_mul_pow_inv_mem_of_finiteDimensional_adjoin` (112), `exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero`
  (57), `exists_root_mem_of_monic` (23), and the `charP_residueField_of_liesOverPrime` (37) /
  `IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` (83) pair.
- **`M4aTorus.completedRayL_fe`, 12,126 silo, is not cut**: it is the shelf's largest single node by a
  factor of three and would be a mechanical-transcription set of its own (the AF7 shape), not a story.
