# Topic m13 — the capstone: `heckeExchangeAt_of_WEX` and `heckeOperatorsCommuteBar` (**reserved for the human reviewer**)

**Status: reserved. Do not dispatch to the coding subagent.** This is the
effort's capstone, the analogue of the `AlgebraicCurve` T7
(`WeilExchange/DivisorExchange.lean`) that the reviewer wrote by hand. Writing it
is also the final review instrument: it consumes m9's roof, m10's integrality,
m11's principal divisors, m12's reduction and AC's exchange, so a binder or a
missing lemma anywhere upstream surfaces as a compile failure here.

**Goal.** One module, `FLTForHuman/ModularCurve/HeckeCommuteBar.lean`, porting the
pin's `S_ModularCurve_heckeOperatorsCommuteBar.lean` (112 raw / 63 content):

- the local `heckeExchangeAt_of_WEX` (the ported AC exchange applied to the
  Hecke roof square);
- `hfin_of_legR`, `heckeExchangeAt_of_rows`, `heckeOperatorsCommuteBar_of_rows`;
- the dischargers `hP_of_rows`, `dataAll_of_rows`, `hsepS_of_rows`;
- **the target** `ModularCurve.heckeOperatorsCommuteBar (N) [NeZero N] :
  HeckeOperatorsCommuteBar N`.

## 1. The pin's structure (to mirror)

```lean
section Discharge
variable (L) [Field L] [Algebra ℚ L] (N ℓ ℓ' M) [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M]
theorem heckeExchangeAt_of_WEX (hM : M = N * ℓ * ℓ')
    (hfin : FiniteAlong L ((towerSubstBar …).comp (heckeAlphaBar L N ℓ')))
    (hsep : SeparableAlong L (…)) (hgen : Algebra.adjoin L (range … ∪ range …) = ⊤)
    (hLD : finrankAlong L (…) = finrankAlong L (heckeAlphaBar …) * finrankAlong L (heckeBetaBar …)) :
    HeckeExchangeAt L N ℓ ℓ' M hM := by
  intro _ _ hβ hα' hu hu' D
  exact AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    (heckeAlphaBar L N ℓ') (heckeBetaBar L N ℓ)
    (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2)
    (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1)
    hα' hβ hu' hu (heckeSquareBar_commutes L ℓ ℓ' _ _) hfin hsep hgen hLD D
```

Then the roof section (`hfin_of_legR = finiteAlong_comp …`,
`heckeExchangeAt_of_rows` combining WEX with m9's `heckeRoof_adjoin_range_union_eq_top`
and `finrankAlong_towerSubstBar_comp_heckeAlphaBar`), the row combination
`heckeOperatorsCommuteBar_of_rows` (through m12's
`heckeOperatorsCommuteBar_of_heckeExchangeAt`), and the dischargers:
`hP_of_rows := hasPrincipalDivisors_modularFunctionFieldBar modularPolynomialFamily M`
(m11 + m6), `dataAll_of_rows := (modularPolynomialFamily p hp.out).choose`,
`hsepS_of_rows := separableAlong_of_charZero _ (…trans… (heckeAlphaBarIntegral_of_prime …)
(towerSubstBar_isIntegral …))` (AC + m10). The final `solution` composes them
with FFG's `functionFieldGeneration M`.

## 2. Verification

- Append `Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean` to `SOURCES`
  and `HeckeCommuteBar.lean` to `PORT_FILES`; checker 0 mismatched / 0 missing, and the
  identical count increases by 1.
- `#print axioms ModularCurve.heckeOperatorsCommuteBar` =
  `[propext, Classical.choice, Quot.sound]`.
- Consumer **Zone I `[capstone]`**: `#check ModularCurve.heckeOperatorsCommuteBar`
  and `example (N) [NeZero N] : ModularCurve.HeckeOperatorsCommuteBar N :=
  ModularCurve.heckeOperatorsCommuteBar N`.
- `timeout 180 lake build` green, 0 warnings, no `sorry`.

## 3. Reporting back

1. The module's line/decl count, the checker delta, and the axiom print.
2. Whether every upstream topic's interface composed without change; any
   binder that had to be adapted (quoted).
3. The final `#print axioms`, and the retrospective.
