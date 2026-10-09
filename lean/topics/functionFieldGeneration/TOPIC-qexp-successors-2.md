# The next qexp head — the Atkin–Lehner exchange and the `isAlgClosed` finrank bound

**Status: scoped 2026-10-08.** The three nodes that
[SET-R-D](SET-R-D.md) unblocked (its §8). Pin `aa2d8b3`, port checker at
**6975 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own
(7011 checked)** after SET-R-D. Predecessors:
[TOPIC-qexp-successors.md](TOPIC-qexp-successors.md) (the set that unblocked
these) and
[TOPIC-qexp-rationality-degree-head.md](TOPIC-qexp-rationality-degree-head.md)
(the original head).

## 1. Why these three

The ready shelf is **86** before and after SET-R-D: the three landed left it and
exactly three entered, all with a SET-R-D headline in their premise closure (same
method as the predecessor scope — intersect each ready node's premise closure with
the new headlines):

| node | unblocked by | `S_` lines |
|---|---|---:|
| `ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed` | SET-R-D order 1 | 193 |
| `ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar` | SET-R-D order 3 | 1,195 |
| `ModularCurve.exists_algEquiv_x1x0FunctionFieldC_atkinLehner` | SET-R-D order 3 | 1,237 |

## 1a. The definition layer (done, 2026-10-08)

Hand-checked against the three `S_` files' import lists (the head's §3 warns that
`--ready`/`--with-defs` do not see import-only definitions). Six pin definition
modules are imported; every declaration they use is public **except one block**:

* the opening `ValuationSubring` block of
  `Definitions/Def_WeierstrassCurve_ReductionMap.lean`
  (`liesOverPrime_iff`, `natCast_mem'`,
  `natCast_mem_maximalIdeal_of_liesOverPrime`,
  `charP_residueField_of_liesOverPrime_def`) was carried only as a `private`
  re-derivation inside `ModularCurve/X1/FunctionFieldIsAlgClosed.lean`. It is now
  **public in `NumberTheory/ValuationAtPlace.lean`** (its natural home: places of
  `ℚ̄` and integral elements, already importing
  `GaloisRep/Defs/Ramification.lean` for `LiesOverPrime`), `Def_WeierstrassCurve_ReductionMap.lean`
  is appended to `SOURCES`, and the `FunctionFieldIsAlgClosed.lean` copies were
  deleted in favour of the import. Checker **6975 → 6979, 0/0** (+4); wave green
  (4,692 jobs). The rest of that pin module — the Weierstrass reduction map
  (`reducePoint`, `equation_residue`, …) — stays unported and is not needed.
* `Def_ModularCurve_XHOperators`, `Def_ModularCurve_X1HeckeOperator`,
  `Def_ModularCurve_X1Diamond`, `Def_ModularCurve_X1`, `Def_ModularCurve_JqCoeff`,
  `Def_FLTPrelim_Ramification`: the used declarations are all public — no
  promotion needed.
* `ModularForm.heckeDiagMatrix_zero` / `heckeMatrix_zero` appear only in the pin's
  `attribute [-simp] …` scaffolding, never in a statement or proof — not needed.

So this head needs **no hub promotion and no hub edit**; the only hub node touched
was `ValuationAtPlace.lean` itself, above.

## 2. At a glance

| | `…heckeAlphaHBar_heckeBetaHBar` | `…x1x0FunctionFieldC_atkinLehner` | `…finrank_…_of_isAlgClosed` |
|---|---|---|---|
| role | Atkin–Lehner exchange on `xHTopFunctionFieldC` | the same exchange on `x1x0FunctionFieldC` | the `isAlgClosed` finrank/index bound |
| `S_` lines | 1,195 | 1,237 | 193 |
| premises | order 3 + `exists_algEquiv_laurentBaseChange_cover` + `qCoeff_comp_heckeDiagMatrix_smul` (all ported) | same three | order 1 + target 4 (`finrank_adjoin_jqModC_laurentBaseChange…`) + 4 public |
| substitution rows | 22 (all importable) | 21 (20 importable, **1 port-private**) | 3 (all importable) |
| hub touch | none | one avoidable row (§5) | none |

Union budget (`port_plan` on the three): raw **2,625** `S_` lines → **1,902 net new
math lines** after the once-only dedup, **250 distinct declaration groups**,
**38 trusted + 8 suspect** substitutions (`SFieldGen`→`modularFunctionField`,
`ALRational`/`QuasiInv`→`PeriodPair.DiscriminantNeZero`, `Γb`/`Γt`→
`RelrankSol.GamGL`/`Gam'GL` — read both copies before applying any).

## 3. The two Atkin–Lehner exchanges are one development

They share a **472-line / 71-declaration block** (139 lines already in the port).
Write it **once** and keep the two headlines as its consumers — this is the same
shape as the Γ₀-rationality pair in SET-R-A (`next5_plan`'s block detector, here
`port_plan`'s). Top shared rows: `ofPowerSeries_expandPS` (25),
`intSeriesC_expandPS` (17), `heckeDiag_mul_alGL_γ₁` (17), `algebraMap_mem_ratios`
(16), `conjSL_mem_Gamma0` (15), `heckeDiag_mul_mul_inv` (15).

`…x1x0FunctionFieldC_atkinLehner` also carries a second small block —
`conj_mem_Gamma1` (48) and `T_mem_Gamma1` (4). `conj_mem_Gamma1` **is** public: it is
one of the sixteen `Gamma0Integral.lean` rows promoted for SET-R-D (the
`X1DiamondRationalForms` block). **`T_mem_Gamma1` is not** — the promotion took
sixteen rows, and this was not among them (it is still `private` at
`Gamma0Integral.lean:1408`, and the `X1BoundedDenominators` copy was deleted in the
same pass's duplicate collapse). Re-derive the four lines in the consumer rather
than reopening the hub; SET-R-E did exactly that.

Statements (abridged; the `Theorems/` wrappers are the authority):
`…heckeAlphaHBar_heckeBetaHBar` produces a `w` in
`laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M*ℓ))` swapping
`heckeAlphaHBar` and `heckeBetaHBar` composed with `diamondAutHBar` — the Galois
exchange behind the `(ℓ+1)`-dimensional relrank of SET-R-B.
`…x1x0FunctionFieldC_atkinLehner` is its `x1x0FunctionFieldC` analogue, from the
`ℚ`-side diamond automorphism `IsDiamondAut` and its base change
`IsBaseChangeAutOf`.

## 4. The `isAlgClosed` finrank bound

`…finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed` (193 `S_`
lines) is the field-of-constants extension of SET-R-C order 1: for algebraically
closed `K` and `Γ ≤ Γ'` with the `±`-negation condition, the degree of
`qExpFunctionFieldC K Γ` over `K(jq)` is bounded by `Γ'.index`. Six premises, all
ported.

**This is the characteristic-`p` step of the index computation.** The earlier
finrank/index bounds — `finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index`
(SET-R-C order 1) and its γ₀/γ_H/γ₁ instances — are statements over `ℚ` and its
characteristic-0 base changes. This one holds over an **arbitrary algebraically
closed `K`**, `𝔽̄_p` included: it says the index bound is a statement about the
q-expansion model **in characteristic `p`**, not just over `ℚ`. Its proof is the
constant-extension step of SET-R-D order 2, and its numeric input is SET-R-D
order 1's Deuring reduction (which compares the two characteristics through a
shared integral series pair). Contrast with the ~166 generic `FiniteDimensional`
statements in `AlgebraicCurve/`, which *take* finiteness as a hypothesis: here the
finiteness **and the degree** are produced in characteristic `p`.

Its block is 87 lines (78 already in the port) and its top rows —
`isAlgebraic_residueField` (59), `residueTopHom` (11), `jqModC_eq_div` (9),
`coe_eq_zero_of_mem_maximalIdeal_top` (8) — are **the engine of SET-R-D order 2**
(`ModularCurve/X1/FunctionFieldIsAlgClosed.lean`), where `isAlgebraic_residueField`
and `residueTopHom` are public. Reuse them; the transcription is then short.

## 5. Hub contact: none required

The only port-`private` row in the union is **`T_mem_Gamma1`** — matched by the
`x1x0` target to `ModularCurve/X1/Inputs.lean`, and still `private` in the hub
`Gamma0Integral.lean:1408`. *Correction (2026-10-08, found during SET-R-E):* an
earlier draft of this section claimed the hub's `X1DiamondRationalForms` copy was
public; it is not — the SET-R-D promotion took sixteen rows and `T_mem_Gamma1` was
not one of them. The four-line pin copy is transcribed in place in the consumer.
**No promotion and no hub edit is proposed for this head.**

## 6. The cut — one set, SET-R-E, two orders

Written as [SET-R-E.md](SET-R-E.md).

* **Order 1** `FLTForHuman/ModularCurve/X1/FunctionFieldFinrankIsAlgClosed.lean`
  — the `isAlgClosed` finrank bound (193 lines, 3 substitutions all importable,
  reuses SET-R-D order 2's public engine). Small and clean; build it first.
* **Order 2** `FLTForHuman/ModularCurve/X1/AtkinLehnerExchange.lean` — the shared
  472-line engine written once plus the two Atkin–Lehner headlines (1,195 + 1,237
  raw lines; ≈1,900 written with the block deduped). Reuses SET-R-D order 3 and
  the promoted `conj_mem_Gamma1` (the `T_mem_Gamma1` copy is re-derived, §5).

Total ≈1,902 net new lines over 250 declaration groups — one set, one subagent,
after the module paths are confirmed. The implementer may re-home a node to a
leaf-side module where the mathematics admits it (playbook host rule) but must
record the deviation.

## 7. Risks

* The **8 suspect substitutions** of §2 — the `def`-typed matches the parser
  cannot judge (`SFieldGen`, `ALRational`, `QuasiInv`, `Γb`, `Γt`). Read both
  copies first, as SET-R-A/B/C did.
* The two Atkin–Lehner `S_` files each carry their own copy of the shared block;
  the dedup is the point of the set, so the engine must be written once **before**
  either headline.
* `…x1x0FunctionFieldC_atkinLehner` takes the Atkin–Lehner inputs
  (`HeckeBetaOneDefined`, `IsDiamondAut`, `IsBaseChangeAutOf`) as hypotheses —
  do not try to discharge them.
* The `Cos`/`Finset`-sum and `Finset`-reindexing shapes have cost earlier topics;
  keep the pin's concrete function types.
