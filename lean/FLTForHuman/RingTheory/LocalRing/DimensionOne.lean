/-
  The maximal ideal of a one-dimensional local domain is the radical of any nonzero principal
  ideal:

      `IsLocalRing.exists_dvd_pow_of_krullDimLE_one`:
      for `b ≠ 0` and `c` in the maximal ideal there is `n` with `b ∣ c ^ n`.

  The port of the pin leaf `IsLocalRing.exists_dvd_pow_of_krullDimLE_one` (33 pin lines),
  statement from its `Theorems/` wrapper and proof from the matching `P2M/Sol/S_…` file
  (pinned `aa2d8b3`). Split out of the former `RingTheory/LocalRingNilpotent` module
  (2026-10-20): the idempotent-lifting fact beside it is a different subject and lives in
  `RingTheory/LocalRing/IdempotentLift.lean`. The pin's block namespace `RankOneNilSol` is a
  proof label and is gone; the general statement keeps the pin's short name under the
  class's own namespace, `IsLocalRing.exists_dvd_pow`.

  The mathematics: `(b).radical` is the intersection of the primes over `(b)`; over a
  one-dimensional local ring the only prime over a nonzero proper ideal is the maximal
  ideal, so `c ∈ (b).radical`, i.e. `c ^ n ∈ (b)`.

  Assumes: mathlib `v4.34.0` only. Mathlib has no such statement (`rg -n
  "exists_dvd_pow_of_krullDimLE" Mathlib/` is empty, 2026-10-20). Ingredients imported
  rather than restated: `Ideal.radical_eq_sInf`, `IsLocalRing.le_maximalIdeal`,
  `IsLocalRing.eq_maximalIdeal`, `Ideal.IsPrime.isMaximal_of_ne_bot`,
  `Ideal.mem_span_singleton`.

  spec-pin: Theorems/Thm_IsLocalRing_exists_dvd_pow_of_krullDimLE_one.lean
  spec-pin: P2M/Sol/S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one.lean
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Operations

set_option autoImplicit false

open IsLocalRing

namespace IsLocalRing

theorem exists_dvd_pow {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by
  by_cases hu : IsUnit b
  · exact ⟨0, hu.dvd⟩
  · have hne : Ideal.span {b} ≠ ⊤ := by
      rwa [Ne, Ideal.span_singleton_eq_top]
    have hrad : (Ideal.span {b}).radical = maximalIdeal R := by
      rw [Ideal.radical_eq_sInf]
      refine le_antisymm (sInf_le ⟨IsLocalRing.le_maximalIdeal hne, inferInstance⟩) (le_sInf ?_)
      rintro J ⟨hJ, hJp⟩
      have hJ0 : J ≠ ⊥ := by
        intro h0
        rw [h0, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at hJ
        exact hb hJ
      exact (IsLocalRing.eq_maximalIdeal (hJp.isMaximal_of_ne_bot hJ0)).ge
    have hc' : c ∈ (Ideal.span {b}).radical := hrad ▸ hc
    obtain ⟨n, hn⟩ := hc'
    exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

end IsLocalRing

theorem IsLocalRing.exists_dvd_pow_of_krullDimLE_one
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by
  exact IsLocalRing.exists_dvd_pow hb hc
