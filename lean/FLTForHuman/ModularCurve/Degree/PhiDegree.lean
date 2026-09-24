/-
  m6 — the Φ degree tail: `transcendental_jqModC`, the finiteness of
  `jqNModC` over `K(jqModC)`, and the `dedekindPsi` degree bound.

  `transcendental_jqModC` is the `jqModC` analogue of the ported `Defs/Jq.lean`
  `transcendental_jq`; the `phiAt`/`phiOver` block of `finrank_adjoin_jqNModC_le`
  is written once here and the finiteness is its immediate corollary.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_transcendental_jqModC.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrank_adjoin_jqNModC_le.lean
-/
import FLTForHuman.ModularCurve.Degree.PhiData
import FLTForHuman.ModularCurve.Analytic.ModularUnitQExpansion
import FLTForHuman.ModularCurve.PhiGenDescendsStructure
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField HahnSeries PowerSeries

namespace ModularCurve

/-! ## `jqModC` is transcendental -/

section Transcendental

variable (K : Type*) [CommRing K]

private theorem jqModC_pow (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

private theorem constantCoeff_jNum_map : PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]

private theorem coeff_jqModC_pow_self (n : ℕ) : ((jqModC K) ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map, one_pow]

private theorem coeff_jqModC_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) :
    ((jqModC K) ^ n).coeff m = 0 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

private theorem coeff_jqModC_neg_one : (jqModC K).coeff (-1 : ℤ) = 1 := by
  simpa using coeff_jqModC_pow_self K 1

private theorem algebraMap_laurentSeries_eq_single_cr (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

private theorem aeval_jqModC_eq_zero {p : Polynomial K}
    (hp : Polynomial.aeval (jqModC K) p = 0) : p = 0 := by
  by_contra hp0
  set n := p.natDegree with hn
  have hcoeff : (Polynomial.aeval (jqModC K) p).coeff (-(n : ℤ)) = p.coeff n := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
      Finset.sum_eq_single n]
    · rw [algebraMap_laurentSeries_eq_single_cr, HahnSeries.coeff_single_zero_mul,
        coeff_jqModC_pow_self, mul_one]
    · intro i hi hin
      have hilt : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
      rw [algebraMap_laurentSeries_eq_single_cr, HahnSeries.coeff_single_zero_mul,
        coeff_jqModC_pow_of_lt, mul_zero]
      omega
    · intro hn'
      exact absurd (Finset.self_mem_range_succ n) hn'
  rw [hp] at hcoeff
  simp only [HahnSeries.coeff_zero] at hcoeff
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hcoeff.symm)

theorem transcendental_jqModC (K : Type*) [CommRing K] : Transcendental K (jqModC K) :=
  transcendental_iff.mpr fun _ hp => aeval_jqModC_eq_zero K hp

end Transcendental

/-! ## The degree of `K(jqModC)(jqNModC)` -/

section PhiAt

variable (R : Type*) [CommRing R] (N : ℕ) [NeZero N]

private def phiAt (Φ : Polynomial (Polynomial ℤ)) : LaurentSeries R :=
  Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries R)) (jqModC R)) (jqNModC R N)

private theorem coeffMap_eq_map {S : Type*} [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    coeffMap f x = x.map f := rfl

private theorem coeffMap_phiAt {S : Type*} [CommRing S] (f : R →+* S) (Φ : Polynomial (Polynomial ℤ)) :
    coeffMap f (phiAt R N Φ) = phiAt S N Φ := by
  unfold phiAt
  rw [Polynomial.hom_eval₂]
  have hj : coeffMap f (jqModC R) = jqModC S := by rw [coeffMap_eq_map, map_jqModC]
  have hjN : coeffMap f (jqNModC R N) = jqNModC S N := by
    rw [jqNModC, jqNModC, coeffMap_qExpand, hj]
  rw [hjN]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp
  · simp [hj]

section OverQ

variable (N : ℕ) [NeZero N]

private theorem phiAt_rat (Φ : Polynomial (Polynomial ℤ)) : phiAt ℚ N Φ = Φ.eval₂ evalAtJ (jqN N) := by
  unfold phiAt
  have hN : jqNModC ℚ N = jqN N := rfl
  rw [hN]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [evalAtJ]
  · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJ_X, jqModC_rat]

private theorem phiAt_eq_zero (K : Type*) [Field K] (data : ModularPolynomialData N) :
    phiAt K N data.Φ = 0 := by
  have hZ : phiAt ℤ N data.Φ = 0 := by
    apply coeffMap_injective (f := Int.castRingHom ℚ) (RingHom.injective_int (Int.castRingHom ℚ))
    rw [coeffMap_phiAt, map_zero, phiAt_rat, data.eval_eq_zero]
  rw [← coeffMap_phiAt ℤ N (Int.castRingHom K), hZ, map_zero]

end OverQ

section Degree

variable (K : Type*) [Field K] {N : ℕ} [NeZero N]

private def phiOver (Φ : Polynomial (Polynomial ℤ)) :
    Polynomial (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom _)
    (⟨jqModC K, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩ :
      IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))))

private theorem aeval_phiOver (Φ : Polynomial (Polynomial ℤ)) :
    Polynomial.aeval (jqNModC K N) (phiOver K Φ) = phiAt K N Φ := by
  rw [Polynomial.aeval_def, phiOver, Polynomial.eval₂_map]
  unfold phiAt
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp
  · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rfl

theorem finrank_adjoin_jqNModC_le (K : Type*) [Field K] {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) :
    Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) ≤ dedekindPsi N := by
  set E := IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))
  have hmonic : (phiOver K data.Φ).Monic := data.monic.map _
  have hroot : Polynomial.aeval (jqNModC K N) (phiOver K data.Φ) = 0 := by
    rw [aeval_phiOver, phiAt_eq_zero]
  have hint : IsIntegral E (jqNModC K N) :=
    ⟨phiOver K data.Φ, hmonic, by rwa [← Polynomial.aeval_def]⟩
  rw [IntermediateField.adjoin.finrank hint, ← data.natDegree_eq,
    ← (data.monic.natDegree_map _ : (phiOver K data.Φ).natDegree = _)]
  exact Polynomial.natDegree_le_of_dvd (minpoly.dvd E _ hroot) hmonic.ne_zero

theorem finiteDimensional_adjoin_jqNModC (K : Type*) [Field K] {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) :
    FiniteDimensional (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) := by
  have hmonic : (phiOver K data.Φ).Monic := data.monic.map _
  have hroot : Polynomial.aeval (jqNModC K N) (phiOver K data.Φ) = 0 := by
    rw [aeval_phiOver, phiAt_eq_zero]
  exact IntermediateField.adjoin.finiteDimensional
    ⟨phiOver K data.Φ, hmonic, by rwa [← Polynomial.aeval_def]⟩

end Degree

end PhiAt

end ModularCurve
