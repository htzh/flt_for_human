# Topic m9 — the roof generation and the diagonal degree (M6)

**Status: work order drafted (pending the SET-M2/SET-M3 dispatch).** Second topic
of [SET-M3](SET-M3.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** One module, `FLTForHuman/ModularCurve/Degree/Roof.lean`, with:

- `ModularCurve.heckeRoof_adjoin_range_union_eq_top` (418 content);
- `ModularCurve.finrankAlong_towerSubstBar_comp_heckeAlphaBar` (441 content).

**Why this topic.** These are the **two field-theoretic hypotheses of
`heckeExchangeAt_of_WEX`**: `hgen` (the roof's two legs generate the top field)
and `hLD` (the diagonal degree is the product). With them, the capstone is pure
assembly over the ported `AlgebraicCurve` exchange. Both files' heads are the
now-familiar `TS`/slot prelude, which is fully ported.

## 1. `heckeRoof_adjoin_range_union_eq_top`

Wrapper (verbatim):

```lean
theorem ModularCurve.heckeRoof_adjoin_range_union_eq_top (L : Type*) [Field L] [Algebra ℚ L]
    (N ℓ ℓ' M : ℕ) [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M] (hM : M = N * ℓ * ℓ')
    (hgenQ : FunctionFieldGeneration M) (data' : ModularPolynomialData ℓ') :
    Algebra.adjoin L (Set.range (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2) ∪
      Set.range (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1)) = ⊤
```

After the ported prelude the pin's file has:

- `jqNModC_congr` (private);
- private `ModularCurve.mem_range_towerInclBar_iff`;
- private `ModularCurve.laurentBaseChange_adjoin_pair`;
- private `ModularCurve.heckeRoof_adjoin_range_union_eq_top` (≈128 lines), then
  the solution.

Inputs (ported or from earlier sets): `FunctionFieldGeneration M` (FFG capstone),
`modularFunctionField_eq_full`/`functionFieldGeneration_iff_full_eq` (ported),
`PhiGen_splits_prime_at_slot` (ported), m6's `isIntegral_jqNModC_mul`, m7's
`coeffEmb_jqN` and `laurentBaseChange_modularFunctionField`.

Note the wrapper takes `data'` and `hgenQ` as arguments; the pin's private proof
is the body. Scout `mem_range_towerInclBar_iff`/`laurentBaseChange_adjoin_pair`
first — they are the only new field-theoretic steps.

## 2. `finrankAlong_towerSubstBar_comp_heckeAlphaBar`

Wrapper (verbatim):

```lean
theorem ModularCurve.finrankAlong_towerSubstBar_comp_heckeAlphaBar (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] (ℓ ℓ' M : ℕ) [hl : Fact (Nat.Prime ℓ)] [hl' : Fact (Nat.Prime ℓ')]
    [NeZero M] (hM : M = N * ℓ * ℓ') (hne : ℓ ≠ ℓ') :
    AlgebraicCurve.finrankAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp
        (heckeAlphaBar L N ℓ'))
      = AlgebraicCurve.finrankAlong L (heckeAlphaBar L N ℓ') * AlgebraicCurve.finrankAlong L (heckeBetaBar L N ℓ)
```

After the ported prelude the pin's file has:

- the three generic AC helpers `AlgebraicCurve.finrankAlong_comp`,
  `finrankAlong_id`, `finrankAlong_eq_relfinrank_fieldRange` (the port has only
  `AlgebraicCurve.finrankAlong`; write them `private` here and record them as
  promotion candidates for AC's `Defs/Correspondence.lean`);
- private `full_congr`, `dedekindPsi_pos'`;
- private `fieldRange_heckeBetaBar`, `ModularCurve.finrankAlong_heckeBetaBar`
  (≈80 lines, the `if ℓ ∣ A then ℓ else ℓ+1` value);
- private `ModularCurve.finrankAlong_towerInclBar_of_eq` and
  `finrankAlong_towerSubstBar_roof` (≈26 lines);
- private `ModularCurve.finrankAlong_towerSubstBar_comp_heckeAlphaBar` (≈12 lines).

Inputs (m7 or ported): `relfinrank_qExpand_full`, `relfinrank_laurentBaseChange`,
`transcendental_jqN`, `laurentBaseChange_adjoin`, `laurentBaseChange_mono`,
`qExpand_mem_laurentBaseChange` (all m7/m1), and AC's along-API
(`algebraAlong`, `isScalarTower_along`).

## 3. Verification

- Append the two wrappers to `SOURCES`; `Degree/Roof.lean` to `PORT_FILES`.
- checker 0 mismatched / 0 missing.
- `#print axioms` on both headlines.
- Consumer **Zone F `[roof]`**: instantiate `heckeRoof_adjoin_range_union_eq_top`
  at the `N = 1`, `ℓ = 2`, `ℓ' = 3`, `M = 6` square (with `data'` from
  `exists_modularPolynomialData_evalSymm`), and
  `finrankAlong_towerSubstBar_comp_heckeAlphaBar` at the same square, composing
  it with the ported `AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_...`
  in the shape `heckeExchangeAt_of_WEX` consumes. This is the set's cross-module
  wire test.
- `grep -c` the prelude names to show none is re-declared.

## 4. Budget

**3 goal rounds.** Round 1: the three AC `finrankAlong` helpers +
`fieldRange_heckeBetaBar`/`finrankAlong_heckeBetaBar`. Round 2:
`mem_range_towerInclBar_iff`/`laurentBaseChange_adjoin_pair` + the roof. Round 3:
the diagonal degree, log/README/consumer.

**Stop early on**: `finrankAlong_eq_relfinrank_fieldRange` needing a mathlib
`fieldRange` statement the pin does not reach; the roof's generation argument
needing an FFG theorem the port lacks; or a statement mismatch.

## 5. Reporting back

1. Module/line/decl table and checker before/after.
2. The roof argument's structure and the two new field-theoretic steps.
3. The diagonal-degree argument: `finrankAlong_heckeBetaBar`'s route and the
   three AC `finrankAlong` helpers (with the promotion recommendation).
4. The prelude `grep -c` evidence.
5. The SET-M4 hand-off: the exact `HeckeExchangeAt`/`heckeOperatorsCommuteBar`
   binders the capstone consumes.
