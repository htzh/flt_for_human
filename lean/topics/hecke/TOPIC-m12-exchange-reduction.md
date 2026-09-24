# Topic m12 — the exchange reduction (M2)

**Status: work order drafted (pending the earlier sets).** Third topic of
[SET-M4](SET-M4.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** One module, `FLTForHuman/ModularCurve/HeckeExchange/Reduction.lean`,
with the four M2 nodes:

```lean
theorem ModularCurve.heckeDivBar_heckeDivBar_of_heckeExchangeAt
    (L : Type*) [Field L] [Algebra ℚ L] {N ℓ ℓ' M : ℕ} [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M]
    (hM : M = N * ℓ * ℓ') (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    (hα' : HeckeAlphaBarIntegral L N ℓ') (hβ' : HeckeBetaBarIntegral L N ℓ')
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ')))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull M))]
    (hu : …) (hu' : …) (h₁ : N * (ℓ * ℓ') ∣ M) (h₂ : N ∣ M) (hs : …) (hi : …)
    (hex : HeckeExchangeAt L N ℓ ℓ' M hM) (D : Divisor L …) :
    heckeDivBar hα hβ (heckeDivBar hα' hβ' D) = Divisor.correspondence (towerSubstBar L N (ℓ * ℓ') h₁) (towerInclBar L h₂) hs hi D

theorem ModularCurve.heckeDivBar_comm_of_heckeExchangeAt … :
    heckeDivBar hα hβ (heckeDivBar hα' hβ' D) = heckeDivBar hα' hβ' (heckeDivBar hα hβ D)

theorem ModularCurve.heckeOperatorBar_comm_of_heckeExchangeAt … :
    heckeOperatorBar N ⟨ℓ, Fact.out⟩ * heckeOperatorBar N ⟨ℓ', Fact.out⟩
      = heckeOperatorBar N ⟨ℓ', Fact.out⟩ * heckeOperatorBar N ⟨ℓ, Fact.out⟩

theorem ModularCurve.heckeOperatorsCommuteBar_of_heckeExchangeAt (N : ℕ) [NeZero N]
    (hP : ∀ (M : ℕ) [NeZero M], HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (hex : ∀ (ℓ ℓ' M : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M] (hM : M = N * ℓ * ℓ'), ℓ ≠ ℓ' →
      HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM) : HeckeOperatorsCommuteBar N
```

(Quote every binder from the `Theorems/` wrappers; the abridged ones above are
the survey's, not the authority.)

**Why this topic.** By the survey §5–§7, this is pure assembly over the ported
`AlgebraicCurve` `correspondence_correspondence_comm` and the ported
`PullbackPushforward` exchange; the mathematics is the two roofs collapsing to
the common level `Nℓℓ'`.

## 1. Routes

- **`heckeDivBar_heckeDivBar_of_heckeExchangeAt` (10).** Unfold
  `heckeDivBar = Divisor.correspondence (heckeBetaBar) (heckeAlphaBar)`, apply
  `hex` to move `β^* α_*` to `incl_* subst^*`, then the composites
  `towerSubstBar_comp_heckeBetaBar` (`qExpand_qExpand`) and
  `towerInclBar_comp_heckeAlphaBar` identify the single roof.
- **`heckeDivBar_comm_of_heckeExchangeAt` (17).** Run the previous with `(ℓ, ℓ')`
  and `(ℓ', ℓ)`, then `Divisor.correspondence_congr` identifies the two roofs
  (using `ℓ * ℓ' = ℓ' * ℓ` and `qExpand` composition congr). Needs the two
  `IsIntegral` hypotheses for the swapped legs too.
- **`heckeOperatorBar_comm_of_heckeExchangeAt` (29).** Split on `HeckeInputsAlong`
  (the junk branch is `0 = 0`); rewrite both operators through
  `heckeOperatorAlong_eq`; apply the ported
  `AlgebraicCurve.Pic0.correspondence_correspondence_comm`, whose divisor
  identity is the previous node. Needs the three `HasPrincipalDivisors`
  instances and the tower integrality of m9/m10.
- **`heckeOperatorsCommuteBar_of_heckeExchangeAt` (12).** The `ℓ = ℓ'` case is
  `rfl`; otherwise build `M = Nℓℓ'`, obtain `hP` at levels `Nℓ`, `Nℓ'`, `M`, and
  call the previous node twice. Pure `Nat.Primes` bookkeeping.

## 2. Imports

`Defs/{HeckeOperator,DegeneracyTower,HeckeTotal,HeckeModule}.lean`,
`HeckeInputs/Integrality.lean` (m10), `Degree/Roof.lean` (m9),
`AlgebraicCurve/WeilExchange/DivisorExchange.lean` (the ported exchange), and
`AlgebraicCurve/Defs/Correspondence.lean`.

## 3. Verification

- Append the four wrappers to `SOURCES`; the module to `PORT_FILES`.
- checker 0 mismatched / 0 missing.
- `#print axioms` on `heckeOperatorsCommuteBar_of_heckeExchangeAt`.
- Consumer **Zone H `[reduction]`**: state the three reductions at the
  `N = 1`/`ℓ = 2`/`ℓ' = 3`/`M = 6` square and compose them with m9's roof and
  m10's integrality; the wire test is that the composed term has the
  `HeckeOperatorsCommuteBar 1` type.

## 4. Budget

**2 goal rounds.** Round 1: the two `heckeDivBar` nodes. Round 2: the two
operator nodes + log/README/consumer.

**Stop early on**: a binder mismatch between the wrapper and `HeckeExchangeAt`
(the coverage's SET-2 recorded one such wrapper-vs-`S_` divergence in AC); the
junk-branch case split needing a `HasPrincipalDivisors` instance the pin obtains
differently; or `correspondence_congr` not matching the ported AC statement.

## 5. Reporting back

1. Module/line/decl table and checker before/after.
2. The `HeckeInputsAlong` split and the `Pic0` descent step.
3. The capstone hand-off: the exact `HeckeExchangeAt` binders the capstone's
   `heckeExchangeAt_of_WEX` must produce, and the `hP` shape.
