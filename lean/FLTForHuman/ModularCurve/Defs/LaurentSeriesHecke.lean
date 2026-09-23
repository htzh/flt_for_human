/-
  The formal Hecke operators on `LaurentSeries`.

  FLT carries these in two definition modules
  (`Definitions/Def_LaurentSeries_HeckeU.lean`, 50 lines, and
  `Def_LaurentSeries_HeckeV.lean`, 48); the port keeps them in one module because
  they are one mathematical role. The declarations are verbatim:

  - `heckeU R ℓ hℓ` keeps the coefficients on multiples of `ℓ` (`(U f).coeff n =
    f.coeff (ℓ * n)`), with `heckeU_ofPowerSeries` matching `PowerSeries.heckeU`;
  - `heckeV R ℓ hℓ` is the dilation `(V f).coeff n = if ℓ ∣ n then f.coeff (n/ℓ)
    else 0`;
  - `heckeT R ℓ hℓ k = heckeU + (ℓ : R) ^ (k - 1) • heckeV`.

  The pin builds the underlying Hahn series with
  `HahnSeries.ofSuppBddBelow`; mathlib `v4.34.0` names the coefficient lemma
  `HahnSeries.coeff_ofSuppBddBelow` (a function equality) rather than the pin's
  pointwise `ofSuppBddBelow_coeff`, so the two `coeff_*` proofs read the
  coefficient off that equality. Everything else is the pin's.

  Placement: the pin's two modules are `Definitions/` files; the port's
  `ModularCurve/Defs/` holds the `qExpand`/`qTwist` series vocabulary, so the
  formal Hecke operators live here. Nothing else in SET 3 needs them.

  FLT provenance, pinned `aa2d8b3`: `Definitions/Def_LaurentSeries_Hecke{U,V}.lean`.
-/
import Mathlib.RingTheory.LaurentSeries
import FLTForHuman.ModularForms.Defs.FormalHeckeOperators

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace LaurentSeries

/-- The support of `n ↦ f.coeff (ℓ * n)` is bounded below for `ℓ > 0`. -/
theorem bddBelow_support_coeff_mul {R : Type*} [Zero R] (f : LaurentSeries R) (ℓ : ℕ)
    (hℓ : 0 < ℓ) : BddBelow (Function.support fun n : ℤ => f.coeff (ℓ * n)) := by
  by_cases hS : (Function.support f.coeff).Nonempty
  · refine ⟨min (f.isWF_support.min hS) 0, fun n hn => ?_⟩
    have hmem : (ℓ : ℤ) * n ∈ Function.support f.coeff := hn
    have hmin : f.isWF_support.min hS ≤ (ℓ : ℤ) * n := f.isWF_support.min_le hS hmem
    by_cases hn0 : 0 ≤ n
    · exact le_trans (min_le_right _ _) hn0
    · have hℓ1 : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
      have hle : (ℓ : ℤ) * n ≤ n := by nlinarith
      exact le_trans (min_le_left _ _) (hmin.trans hle)
  · refine ⟨0, fun n hn => ?_⟩
    exact absurd ⟨(ℓ : ℤ) * n, hn⟩ hS

/-- The formal `U_ℓ` on Laurent series: `(U f).coeff n = f.coeff (ℓ * n)`. -/
def heckeU (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    LaurentSeries R →ₗ[R] LaurentSeries R where
  toFun f := HahnSeries.ofSuppBddBelow (fun n : ℤ => f.coeff (ℓ * n))
    (bddBelow_support_coeff_mul f ℓ hℓ)
  map_add' f g := by
    ext n
    simp [HahnSeries.coeff_ofSuppBddBelow]
  map_smul' c f := by
    ext n
    simp

@[simp]
theorem coeff_heckeU (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (f : LaurentSeries R) (n : ℤ) :
    (heckeU R ℓ hℓ f).coeff n = f.coeff (ℓ * n) :=
  congrFun (HahnSeries.coeff_ofSuppBddBelow (f := fun n : ℤ => f.coeff (ℓ * n))
    (hf := bddBelow_support_coeff_mul f ℓ hℓ)) n

/-- `U` commutes with the power-series inclusion. -/
theorem heckeU_ofPowerSeries (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (φ : PowerSeries R) :
    heckeU R ℓ hℓ (φ : LaurentSeries R) = ((PowerSeries.heckeU ℓ φ : PowerSeries R) : LaurentSeries R) := by
  ext n
  rw [coeff_heckeU, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h1 : ¬ (ℓ : ℤ) * (m : ℤ) < 0 := not_lt.mpr (by positivity)
    have h2 : ¬ (m : ℤ) < 0 := not_lt.mpr hn
    rw [ite_eq_right h1, ite_eq_right h2, PowerSeries.coeff_heckeU]
    congr 1
  · have h1 : (ℓ : ℤ) * n < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hℓ) hn
    rw [ite_eq_left h1, ite_eq_left hn]

/-- The support of `n ↦ if ℓ ∣ n then f.coeff (n / ℓ) else 0` is bounded below. -/
theorem bddBelow_support_coeff_div {R : Type*} [Zero R] (f : LaurentSeries R) (ℓ : ℕ)
    (hℓ : 0 < ℓ) :
    BddBelow (Function.support fun n : ℤ => if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0) := by
  by_cases hS : (Function.support f.coeff).Nonempty
  · refine ⟨(ℓ : ℤ) * f.isWF_support.min hS, fun n hn => ?_⟩
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    obtain ⟨⟨m, rfl⟩, hm⟩ := hn
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
    rw [Int.mul_ediv_cancel_left _ hℓ0] at hm
    have hmin : f.isWF_support.min hS ≤ m := f.isWF_support.min_le hS hm
    have hℓ1 : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
    nlinarith
  · refine ⟨0, fun n hn => ?_⟩
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    exact absurd ⟨_, hn.2⟩ hS

/-- The formal `V_ℓ` on Laurent series: the dilation. -/
def heckeV (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    LaurentSeries R →ₗ[R] LaurentSeries R where
  toFun f := HahnSeries.ofSuppBddBelow
    (fun n : ℤ => if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0)
    (bddBelow_support_coeff_div f ℓ hℓ)
  map_add' f g := by
    ext n
    by_cases h : (ℓ : ℤ) ∣ n <;> simp [HahnSeries.coeff_ofSuppBddBelow, h]
  map_smul' c f := by
    ext n
    by_cases h : (ℓ : ℤ) ∣ n <;> simp [h]

@[simp]
theorem coeff_heckeV (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (f : LaurentSeries R) (n : ℤ) :
    (heckeV R ℓ hℓ f).coeff n = if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0 :=
  congrFun (HahnSeries.coeff_ofSuppBddBelow
    (f := fun n : ℤ => if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0)
    (hf := bddBelow_support_coeff_div f ℓ hℓ)) n

/-- The formal `T_ℓ = U_ℓ + ℓ ^ (k - 1) • V_ℓ`. -/
def heckeT (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (k : ℕ) :
    LaurentSeries R →ₗ[R] LaurentSeries R :=
  heckeU R ℓ hℓ + ((ℓ : R) ^ (k - 1)) • heckeV R ℓ hℓ

theorem coeff_heckeT (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (k : ℕ)
    (f : LaurentSeries R) (n : ℤ) :
    (heckeT R ℓ hℓ k f).coeff n =
      f.coeff (ℓ * n) + (ℓ : R) ^ (k - 1) * (if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0) := by
  simp [heckeT, coeff_heckeU, coeff_heckeV]

end LaurentSeries

end
