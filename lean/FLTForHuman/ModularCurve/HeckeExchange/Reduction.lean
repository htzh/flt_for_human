/-
  m12 — the divisor/`Pic0` exchange reduction (M2).

  The four nodes are pure assembly over the ported `AlgebraicCurve` correspondence
  API: `Divisor.correspondence_correspondence` moves the middle `β^* α_*` to
  `incl_* subst^*` through `HeckeExchangeAt`, the composites
  `towerSubstBar_comp_heckeBetaBar`/`towerInclBar_comp_heckeAlphaBar` identify the
  single roof, and `Divisor.correspondence_congr` closes the commutation with
  `ℓ * ℓ' = ℓ' * ℓ`. The operator nodes split on `HeckeInputsAlong` (the junk
  branch is `0 = 0`), rewrite through `heckeOperatorAlong_eq`, and descend to
  `Pic0.correspondence_correspondence_comm`; the last node is the `Nat.Primes`
  bookkeeping (`ℓ = ℓ'` is `rfl`). The tower integrality the operator nodes need
  is m10's `towerInclBar_isIntegral`/`towerSubstBar_isIntegral`.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean
-/
import FLTForHuman.ModularCurve.Defs.HeckeOperator
import FLTForHuman.ModularCurve.Defs.DegeneracyTower
import FLTForHuman.ModularCurve.Defs.HeckeTotal
import FLTForHuman.ModularCurve.Defs.HeckeModule
import FLTForHuman.ModularCurve.HeckeInputs.Integrality
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

theorem heckeDivBar_heckeDivBar_of_heckeExchangeAt (L : Type*) [Field L] [Algebra ℚ L]
    {N ℓ ℓ' M : ℕ} [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M] (hM : M = N * ℓ * ℓ')
    (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    (hα' : HeckeAlphaBarIntegral L N ℓ') (hβ' : HeckeBetaBarIntegral L N ℓ')
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ')))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull M))]
    (hu : (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1).toRingHom.IsIntegral)
    (hu' : (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).toRingHom.IsIntegral)
    (h₁ : N * (ℓ * ℓ') ∣ M) (h₂ : N ∣ M)
    (hs : (towerSubstBar L N (ℓ * ℓ') h₁).toRingHom.IsIntegral)
    (hi : (towerInclBar L h₂).toRingHom.IsIntegral)
    (hex : HeckeExchangeAt L N ℓ ℓ' M hM) (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :
    heckeDivBar hα hβ (heckeDivBar hα' hβ' D)
      = Divisor.correspondence (towerSubstBar L N (ℓ * ℓ') h₁) (towerInclBar L h₂) hs hi D := by
  rw [heckeDivBar, heckeDivBar,
    Divisor.correspondence_correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ)
      (heckeBetaBar L N ℓ') (heckeAlphaBar L N ℓ') (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1)
      (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2) hβ hα hβ' hα' hu hu'
      (RingHom.IsIntegral.trans _ _ hβ' hu') (RingHom.IsIntegral.trans _ _ hα hu)
      (fun D => hex hβ hα' hu hu' D) D]
  exact Divisor.correspondence_congr
    (towerSubstBar_comp_heckeBetaBar L ℓ ℓ' _ h₁) (towerInclBar_comp_heckeAlphaBar L ℓ _ h₂) _ _ _ _ D

theorem heckeDivBar_comm_of_heckeExchangeAt (L : Type*) [Field L] [Algebra ℚ L]
    {N ℓ ℓ' M : ℕ} [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M] (hM : M = N * ℓ * ℓ')
    (hM' : M = N * ℓ' * ℓ) (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    (hα' : HeckeAlphaBarIntegral L N ℓ') (hβ' : HeckeBetaBarIntegral L N ℓ')
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ')))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull M))]
    (hu : (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1).toRingHom.IsIntegral)
    (hu' : (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).toRingHom.IsIntegral)
    (hv : (towerInclBar L (dvd_of_eq_roof N ℓ' ℓ M hM').1).toRingHom.IsIntegral)
    (hv' : (towerSubstBar L (N * ℓ) ℓ' (dvd_of_eq_roof N ℓ' ℓ M hM').2).toRingHom.IsIntegral)
    (hex : HeckeExchangeAt L N ℓ ℓ' M hM) (hex' : HeckeExchangeAt L N ℓ' ℓ M hM')
    (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :
    heckeDivBar hα hβ (heckeDivBar hα' hβ' D)
      = heckeDivBar hα' hβ' (heckeDivBar hα hβ D) := by
  have h₁ : N * (ℓ * ℓ') ∣ M := ⟨1, by rw [hM]; ring⟩
  have h₁' : N * (ℓ' * ℓ) ∣ M := ⟨1, by rw [hM]; ring⟩
  have h₂ : N ∣ M := ⟨ℓ * ℓ', by rw [hM]; ring⟩
  have hs : (towerSubstBar L N (ℓ * ℓ') h₁).toRingHom.IsIntegral := by
    rw [← towerSubstBar_comp_heckeBetaBar L ℓ ℓ' (dvd_of_eq_roof N ℓ ℓ' M hM).2 h₁]
    exact RingHom.IsIntegral.trans _ _ hβ' hu'
  have hs' : (towerSubstBar L N (ℓ' * ℓ) h₁').toRingHom.IsIntegral := by
    rw [← towerSubstBar_comp_heckeBetaBar L ℓ' ℓ (dvd_of_eq_roof N ℓ' ℓ M hM').2 h₁']
    exact RingHom.IsIntegral.trans _ _ hβ hv'
  have hi : (towerInclBar L h₂).toRingHom.IsIntegral := by
    rw [← towerInclBar_comp_heckeAlphaBar L ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).1 h₂]
    exact RingHom.IsIntegral.trans _ _ hα hu
  rw [heckeDivBar_heckeDivBar_of_heckeExchangeAt L hM hα hβ hα' hβ' hu hu' h₁ h₂ hs hi hex D,
    heckeDivBar_heckeDivBar_of_heckeExchangeAt L hM' hα' hβ' hα hβ hv hv' h₁' h₂ hs' hi hex' D]
  exact Divisor.correspondence_congr (towerSubstBar_congr L (mul_comm ℓ ℓ') h₁ h₁') rfl _ _ _ _ D

theorem heckeOperatorBar_comm_of_heckeExchangeAt (N ℓ ℓ' M : ℕ) [NeZero N] [Fact ℓ.Prime]
    [Fact ℓ'.Prime] [NeZero M] (hM : M = N * ℓ * ℓ') (hM' : M = N * ℓ' * ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ'))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M)]
    (hex : HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM)
    (hex' : HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ' ℓ M hM') :
    heckeOperatorBar N ⟨ℓ, Fact.out⟩ * heckeOperatorBar N ⟨ℓ', Fact.out⟩
      = heckeOperatorBar N ⟨ℓ', Fact.out⟩ * heckeOperatorBar N ⟨ℓ, Fact.out⟩ := by
  by_cases h₁ : HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ
  swap
  · have z : heckeOperatorBar N ⟨ℓ, Fact.out⟩ = 0 := by
      show (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ).toIntLinearMap = 0
      rw [heckeOperatorAlong_of_not h₁]
      rfl
    rw [z, mul_zero, zero_mul]
  by_cases h₂ : HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ'
  swap
  · have z : heckeOperatorBar N ⟨ℓ', Fact.out⟩ = 0 := by
      show (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ').toIntLinearMap = 0
      rw [heckeOperatorAlong_of_not h₂]
      rfl
    rw [z, mul_zero, zero_mul]
  obtain ⟨hα, hβ, _, hfin, hFI, hN⟩ := h₁
  obtain ⟨hα', hβ', _, hfin', hFI', hN'⟩ := h₂
  apply LinearMap.ext; intro x
  show heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ' x)
    = heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ' (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ x)
  rw [heckeOperatorAlong_eq hα hβ hFI hfin hN, heckeOperatorAlong_eq hα' hβ' hFI' hfin' hN']
  refine Pic0.correspondence_correspondence_comm _ _ _ _ hβ hα hβ' hα' hFI hfin hN hFI' hfin' hN'
    (fun D => ?_) x
  exact heckeDivBar_comm_of_heckeExchangeAt (AlgebraicClosure ℚ) hM hM' hα hβ hα' hβ'
    (towerInclBar_isIntegral (AlgebraicClosure ℚ) _) (towerSubstBar_isIntegral (AlgebraicClosure ℚ) ℓ _)
    (towerInclBar_isIntegral (AlgebraicClosure ℚ) _) (towerSubstBar_isIntegral (AlgebraicClosure ℚ) ℓ' _)
    hex hex' D

theorem heckeOperatorsCommuteBar_of_heckeExchangeAt (N : ℕ) [NeZero N]
    (hP : ∀ (M : ℕ) [NeZero M], HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (hex : ∀ (ℓ ℓ' M : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M] (hM : M = N * ℓ * ℓ'),
      ℓ ≠ ℓ' → HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM) : HeckeOperatorsCommuteBar N := by
  rintro ⟨ℓ, hℓ⟩ ⟨ℓ', hℓ'⟩
  by_cases hne : ℓ = ℓ'
  · subst hne; rfl
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact ℓ'.Prime := ⟨hℓ'⟩
  have := hP (N * ℓ)
  have := hP (N * ℓ')
  have := hP (N * ℓ * ℓ')
  exact heckeOperatorBar_comm_of_heckeExchangeAt N ℓ ℓ' (N * ℓ * ℓ') rfl (by ring)
    (hex ℓ ℓ' _ rfl hne) (hex ℓ' ℓ (N * ℓ * ℓ') (by ring) (Ne.symm hne))

end ModularCurve

end
