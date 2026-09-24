/-
  m13 — the capstone: `heckeExchangeAt_of_WEX` and
  `ModularCurve.heckeOperatorsCommuteBar`.

  Reserved for the human reviewer. This module is the port's analogue of the
  `AlgebraicCurve` T7 (`WeilExchange/DivisorExchange.lean`): every premise of the
  exchange is an explicit argument or a theorem delivered by SET-M1–SET-M4, so a
  wrong binder or a missing lemma anywhere upstream surfaces here as a compile
  failure.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean
-/
import FLTForHuman.ModularCurve.HeckeExchange.Reduction
import FLTForHuman.ModularCurve.Degree.Roof
import FLTForHuman.ModularCurve.HeckeInputs.Integrality
import FLTForHuman.ModularCurve.PrincipalDivisors.ModularCurveBar
import FLTForHuman.ModularCurve.Degree.PhiData
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.AlgebraicCurve.WeilExchange.DivisorExchange
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport

set_option autoImplicit false

noncomputable section

open AlgebraicCurve ModularCurve

namespace ModularCurve

section Discharge

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ) [NeZero N] [NeZero ℓ]
  [NeZero ℓ'] [NeZero M]

/-- The general exchange applied to the Hecke roof square: the ported
`AlgebraicCurve` exchange with the two legs of the square and the four
integrality hypotheses. This is `heckeExchangeAt_of_WEX` of the pin's `S_` file. -/
theorem heckeExchangeAt_of_WEX (hM : M = N * ℓ * ℓ')
    (hfin : FiniteAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp
      (heckeAlphaBar L N ℓ')))
    (hsep : SeparableAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp
      (heckeAlphaBar L N ℓ')))
    (hgen : Algebra.adjoin L
      (Set.range (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2) ∪
        Set.range (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1)) = ⊤)
    (hLD : finrankAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp
        (heckeAlphaBar L N ℓ')) =
      finrankAlong L (heckeAlphaBar L N ℓ') * finrankAlong L (heckeBetaBar L N ℓ)) :
    HeckeExchangeAt L N ℓ ℓ' M hM := by
  intro _ _ hβ hα' hu hu' D
  exact AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    (heckeAlphaBar L N ℓ') (heckeBetaBar L N ℓ)
    (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2)
    (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1)
    hα' hβ hu' hu (heckeSquareBar_commutes L ℓ ℓ' _ _) hfin hsep hgen hLD D

end Discharge

section Roof

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ) [NeZero N] [Fact (Nat.Prime ℓ)]
  [Fact (Nat.Prime ℓ')] [NeZero M]

/-- Finiteness of the diagonal leg, from the two tower finitenesses. -/
theorem hfin_of_legR (hM : M = N * ℓ * ℓ') :
    FiniteAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp
      (heckeAlphaBar L N ℓ')) :=
  finiteAlong_comp (heckeAlphaBar L N ℓ') (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2)
    (towerInclBar_finiteAlong L (dvd_mul_right N ℓ'))
    (towerSubstBar_finiteAlong L ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2)

/-- The roof rows: the exchange at `(N, ℓ, ℓ', M)` from the function-field
generation at `M`, a modular polynomial datum at `ℓ'`, and separability. -/
theorem heckeExchangeAt_of_rows (hM : M = N * ℓ * ℓ') (hne : ℓ ≠ ℓ')
    (hgenQ : FunctionFieldGeneration M) (data' : ModularPolynomialData ℓ')
    (hsep : SeparableAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp
      (heckeAlphaBar L N ℓ'))) :
    HeckeExchangeAt L N ℓ ℓ' M hM :=
  heckeExchangeAt_of_WEX L N ℓ ℓ' M hM (hfin_of_legR L N ℓ ℓ' M hM) hsep
    (heckeRoof_adjoin_range_union_eq_top L N ℓ ℓ' M hM hgenQ data')
    (finrankAlong_towerSubstBar_comp_heckeAlphaBar L N ℓ ℓ' M hM hne)

end Roof

/-- The all-pairs statement from the roof rows. -/
theorem heckeOperatorsCommuteBar_of_rows (N : ℕ) [NeZero N]
    (hP : ∀ (M : ℕ) [NeZero M], HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (hsepS : ∀ (ℓ ℓ' M : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M] (hM : M = N * ℓ * ℓ'), ℓ ≠ ℓ' →
      SeparableAlong (AlgebraicClosure ℚ)
        ((towerSubstBar (AlgebraicClosure ℚ) (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp
          (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ')))
    (hgenAll : ∀ (M : ℕ) [NeZero M], FunctionFieldGeneration M)
    (dataAll : ∀ (p : ℕ) [Fact p.Prime], ModularPolynomialData p) :
    HeckeOperatorsCommuteBar N :=
  heckeOperatorsCommuteBar_of_heckeExchangeAt N hP
    (fun ℓ ℓ' M _ _ _ hM hne =>
      heckeExchangeAt_of_rows (AlgebraicClosure ℚ) N ℓ ℓ' M hM hne (hgenAll M) (dataAll ℓ')
        (hsepS ℓ ℓ' M hM hne))

section Dischargers

/-- Principal divisors from m11 and the unconditional family (m6). -/
theorem hP_of_rows (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M) :=
  hasPrincipalDivisors_modularFunctionFieldBar modularPolynomialFamily M

/-- The datum at every prime, from the unconditional family (m6). -/
noncomputable def dataAll_of_rows (p : ℕ) [hp : Fact p.Prime] : ModularPolynomialData p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  exact (modularPolynomialFamily p hp.out).choose

/-- Separability of the diagonal leg, from the two integralities and
characteristic zero (AC). -/
theorem hsepS_of_rows (N ℓ ℓ' M : ℕ) [NeZero N] [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M]
    (hM : M = N * ℓ * ℓ') :
    SeparableAlong (AlgebraicClosure ℚ)
      ((towerSubstBar (AlgebraicClosure ℚ) (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp
        (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ')) :=
  separableAlong_of_charZero _
    (RingHom.IsIntegral.trans _ _
      (heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) N ℓ')
      (towerSubstBar_isIntegral (AlgebraicClosure ℚ) ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2))

end Dischargers

/-- **The target.** `ModularCurve.heckeOperatorsCommuteBar` — the ported
`math/009` theorem, unconditional. -/
theorem heckeOperatorsCommuteBar (N : ℕ) [NeZero N] : ModularCurve.HeckeOperatorsCommuteBar N :=
  heckeOperatorsCommuteBar_of_rows N (fun M _ => hP_of_rows M)
    (fun ℓ ℓ' M _ _ _ hM _ => hsepS_of_rows N ℓ ℓ' M hM)
    (fun M _ => functionFieldGeneration M) (fun p _ => dataAll_of_rows p)

end ModularCurve

end
