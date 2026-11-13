/-
  m6 — the Φ datum family: the `jqNModC` evaluation/integrality tail and the prime
  generation facts.

  Five of the M5 nodes are one-liners over the ported Φ_p effort
  (`exists_phiIrreducible_evalSymm` in `ModularPolynomialProperties.lean`, the
  `gen_prime`/`functionFieldGeneration_iff_full_eq` pair, and the
  `toAdjoin`/`aeval_jqN_toAdjoin` API); two more are ~30-line transcriptions over
  the ported `coeffMap_qExpand`/`coeffMap_injective`. The degree tail lives in
  `Degree/PhiDegree.lean`.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily.lean

  spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero.lean
  spec-pin: P2M/Sol/S_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily.lean

  spec-pin: Theorems/Thm_ModularCurve_exists_modularPolynomialData_evalSymm.lean
  spec-pin: Theorems/Thm_ModularCurve_modularPolynomialFamily.lean
  spec-pin: Theorems/Thm_ModularCurve_functionFieldGeneration_of_prime.lean
  spec-pin: Theorems/Thm_ModularCurve_full_eq_of_prime.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_isIntegral_jqN.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero.lean
  spec-pin: Theorems/Thm_ModularCurve_isIntegral_jqNModC_mul.lean

-/
import FLTForHuman.ModularCurve.Defs.FibrePoly
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.Defs.Invariants
import FLTForHuman.ModularCurve.ModularEquation.Existence
import FLTForHuman.ModularCurve.ModularEquation.Split
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Collapse
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField Finset Nat

namespace ModularCurve

/-! ## The one-liners over the ported Φ_p effort -/

theorem modularPolynomialFamily : ModularPolynomialFamily := fun ℓ _ hℓ => by
  have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  exact exists_modularPolynomialData_evalSymm ℓ

theorem functionFieldGeneration_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) :
    FunctionFieldGeneration ℓ := by
  have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  exact (functionFieldGeneration_iff_full_eq ℓ).mpr (gen_prime ℓ).symm

theorem full_eq_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) :
    modularFunctionFieldFull ℓ = modularFunctionField ℓ :=
  (functionFieldGeneration_iff_full_eq ℓ).mp (functionFieldGeneration_of_prime hℓ)

namespace ModularPolynomialData

theorem isIntegral_jqN {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral ℚ⟮jq⟯ (jqN N) :=
  ⟨data.toAdjoin, data.toAdjoin_monic, aeval_jqN_toAdjoin data⟩

end ModularPolynomialData

/-! ## The `jqNModC` evaluation tail -/

section EvalJqNModC

private theorem coeffMap_eval₂_jqNModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Φ : Polynomial (Polynomial ℤ)) (d e : ℕ) [NeZero d] [NeZero e] :
    coeffMap f (Φ.eval₂ (aeval (R := ℤ) (jqNModC R d)).toRingHom (jqNModC R e))
      = Φ.eval₂ (aeval (R := ℤ) (jqNModC S d)).toRingHom (jqNModC S e) := by
  rw [Polynomial.hom_eval₂, map_jqNModC]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [map_jqNModC]

private theorem eval₂_rat_of_data {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (d : ℕ)
    [NeZero d] : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℚ d)).toRingHom (jqNModC ℚ (d * ℓ)) = 0 := by
  have hcomp : (qExpand ℚ d).comp evalAtJ = (aeval (R := ℤ) (jqNModC ℚ d)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [evalAtJ]
    rfl
  have := congrArg (qExpand ℚ d) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂, hcomp, jqN, qExpand_qExpand] at this
  exact this

namespace ModularPolynomialData

theorem eval_jqNModC_mul_eq_zero {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (K : Type*)
    [CommRing K] (d : ℕ) [NeZero d] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K d)).toRingHom (jqNModC K (d * ℓ)) = 0 := by
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℤ d)).toRingHom (jqNModC ℤ (d * ℓ)) = 0 := by
    apply coeffMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
    rw [coeffMap_eval₂_jqNModC, map_zero]
    exact eval₂_rat_of_data data d
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [coeffMap_eval₂_jqNModC, map_zero] at this

theorem eval_jqNModC_of_mul_eq_zero {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ)
    (hsymm : EvalSymm data.Φ) (K : Type*) [CommRing K] (d : ℕ) [NeZero d] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K (d * ℓ))).toRingHom (jqNModC K d) = 0 := by
  have hQ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℚ (d * ℓ))).toRingHom (jqNModC ℚ d) = 0 := by
    rw [hsymm]
    exact eval₂_rat_of_data data d
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℤ (d * ℓ))).toRingHom (jqNModC ℤ d) = 0 := by
    apply coeffMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
    rw [coeffMap_eval₂_jqNModC, map_zero]
    exact hQ
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [coeffMap_eval₂_jqNModC, map_zero] at this

end ModularPolynomialData

end EvalJqNModC

/-! ## The integrality tail -/

section Integrality

private theorem isIntegral_of_eval₂_eq_zero {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic)
    {a b : LaurentSeries L} (ha : a ∈ F)
    (h : Φ.eval₂ (aeval (R := ℤ) a).toRingHom b = 0) : IsIntegral F b := by
  set ev : Polynomial ℤ →+* F := (aeval (R := ℤ) (⟨a, ha⟩ : F)).toRingHom with hev
  have hcomp : (algebraMap F (LaurentSeries L)).comp ev = (aeval (R := ℤ) a).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [hev]
  refine ⟨Φ.map ev, hΦ.map ev, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact h

theorem isIntegral_jqNModC_mul {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (d : ℕ) [NeZero d]
    (hd : jqNModC K d ∈ F) : IsIntegral F (jqNModC K (d * ℓ)) :=
  isIntegral_of_eval₂_eq_zero F data.monic hd (data.eval_jqNModC_mul_eq_zero K d)

end Integrality

section AllLevels

variable (K : Type*) [Field K]

local notation "L" => LaurentSeries K

local notation "F₀" => IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

private theorem step {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (d : ℕ) [NeZero d]
    (hd : IsIntegral F₀ (jqNModC K d)) : IsIntegral F₀ (jqNModC K (d * ℓ)) := by
  set E : IntermediateField F₀ L := IntermediateField.adjoin F₀ ({jqNModC K d} : Set L) with hE
  have : FiniteDimensional F₀ E := IntermediateField.adjoin.finiteDimensional hd
  have hmem : jqNModC K d ∈ E.restrictScalars K := by
    rw [IntermediateField.mem_restrictScalars]
    exact IntermediateField.mem_adjoin_simple_self _ _
  have h1 : IsIntegral (E.restrictScalars K) (jqNModC K (d * ℓ)) := isIntegral_jqNModC_mul _ data d hmem
  have h2 : IsIntegral E (jqNModC K (d * ℓ)) := h1
  have : Algebra.IsIntegral F₀ E := Algebra.IsIntegral.of_finite F₀ E
  exact isIntegral_trans _ h2

private theorem base : IsIntegral F₀ (jqModC K) :=
  isIntegral_algebraMap (x := (⟨jqModC K, mem_adjoin_simple_self K (jqModC K)⟩ : F₀))

private theorem jqNModC_congr {M N : ℕ} [NeZero M] [NeZero N] (h : M = N) :
    jqNModC K M = jqNModC K N := by
  subst h; rfl

private theorem isIntegral_jqNModC_all (hΦ : ModularPolynomialFamily) :
    ∀ (N : ℕ) [NeZero N], IsIntegral F₀ (jqNModC K N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    rcases le_or_gt N 1 with hle | hlt
    · obtain rfl : N = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
      rw [show jqNModC K 1 = jqModC K from qExpand_one_apply _]
      exact base K
    · have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨d, hd⟩ := Nat.minFac_dvd N
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hd
        exact absurd hd (by omega)
      have : NeZero d := ⟨hd0⟩
      have : NeZero N.minFac := ⟨hp.ne_zero⟩
      have hN' : N = d * N.minFac := hd.trans (mul_comm _ _)
      have hdlt : d < N := by
        have h2 : 2 ≤ N.minFac := hp.two_le
        have : d * 2 ≤ d * N.minFac := Nat.mul_le_mul_left d h2
        omega
      obtain ⟨data, -⟩ := hΦ N.minFac hp
      have hstepd : IsIntegral F₀ (jqNModC K (d * N.minFac)) := step K data d (ih d hdlt)
      rwa [jqNModC_congr K hN']

theorem isIntegral_jqNModC_all_of_modularPolynomialFamily (K : Type*) [Field K]
    (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) :=
  isIntegral_jqNModC_all K hΦ N

end AllLevels



end ModularCurve
