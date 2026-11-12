/-
  The two range tests behind the descent of a conjugate product.

  A series fixed by the tame twist `q ↦ ζ q`, with `ζ` a primitive `ℓ`-th root of unity, has
  support on the multiples of `ℓ`, and is therefore the `q ↦ q ^ ℓ` substitution of its
  contraction. A series fixed by every `ℚ`-automorphism of a finite Galois extension is the
  coefficient extension of a rational series. A series with both properties is the level-`ℓ`
  image of a rational series, which is the shape a descended coefficient of `phiProd` has.

  These statements are about `qExpand`, `qTwist`, `coeffEmb` and the Galois action alone; they
  mention neither `jq` nor `conj`.
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.Twist

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

section Contract

variable {K : Type*} [Field K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

/-- The contraction of a level-`ℓ` support: the series `m ↦ f.coeff (ℓ * m)`. It is the inverse
of `qExpand K ℓ` on series whose support avoids the exponents not divisible by `ℓ`. -/
private def qContract (f : LaurentSeries K) : LaurentSeries K where
  coeff m := f.coeff ((ℓ : ℤ) * m)
  isPWO_support' := by
    have hsub : (Function.support fun m : ℤ => f.coeff ((ℓ : ℤ) * m)) ⊆
        (fun k : ℤ => k / (ℓ : ℤ)) '' f.support := by
      intro m hm
      refine ⟨(ℓ : ℤ) * m, hm, ?_⟩
      exact Int.mul_ediv_cancel_left m (Nat.cast_ne_zero.mpr hℓ.out.ne_zero)
    exact (f.isPWO_support'.image_of_monotone fun a b hab =>
      Int.ediv_le_ediv (Int.natCast_pos.mpr hℓ.out.pos) hab).mono hsub

@[simp]
private theorem qContract_coeff (f : LaurentSeries K) (m : ℤ) :
    (qContract ℓ f).coeff m = f.coeff ((ℓ : ℤ) * m) := rfl

variable {ℓ}

private theorem qExpand_qContract {f : LaurentSeries K}
    (hf : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → f.coeff m = 0) :
    qExpand K ℓ (qContract ℓ f) = f := by
  ext k
  by_cases hk : (ℓ : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qContract_coeff]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hk, hf k hk]

end Contract

section Twist

variable {K : Type*} [Field K]

/-- A coefficient of a series fixed by the twist `q ↦ ζ q` vanishes at every exponent not
divisible by the order of `ζ`. -/
private theorem coeff_eq_zero_of_qTwist_eq {ℓ : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {f : LaurentSeries K} (hf : qTwist ζ f = f) {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) :
    f.coeff m = 0 := by
  have h := congrArg (fun g => HahnSeries.coeff g m) hf
  simp only [qTwist_coeff] at h
  by_contra hc
  apply hm
  rw [← hζ.zpow_eq_one_iff_dvd]
  have hunit : ((ζ ^ m : Kˣ) : K) = (ζ : K) ^ m := Units.val_zpow_eq_zpow_val ζ m
  have hzero : (((ζ ^ m : Kˣ) : K) - 1) * f.coeff m = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.mp hzero with h1 | h1
  · rw [hunit] at h1
    linear_combination h1
  · exact absurd h1 hc

/-- A series fixed by the twist `q ↦ ζ q`, with `ζ` a primitive `ℓ`-th root of unity, is the
`q ↦ q ^ ℓ` substitution of its contraction. -/
theorem mem_range_qExpand_of_qTwist_eq (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) {f : LaurentSeries K}
    (hf : qTwist ζ f = f) : f ∈ Set.range (qExpand K ℓ) :=
  ⟨qContract ℓ f, qExpand_qContract fun _ hm => coeff_eq_zero_of_qTwist_eq hζ hf hm⟩

end Twist

section Galois

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- A series over a finite Galois extension fixed by every `ℚ`-automorphism is the coefficient
extension of a rational series. -/
theorem mem_range_coeffEmb_of_forall_coeffMap_eq [IsGalois ℚ K] [FiniteDimensional ℚ K]
    {f : LaurentSeries K} (hf : ∀ σ : K ≃ₐ[ℚ] K, coeffMap (σ : K →+* K) f = f) :
    f ∈ Set.range (coeffEmb K) := by
  have hcoeff : ∀ m : ℤ, ∃ r : ℚ, algebraMap ℚ K r = f.coeff m := fun m =>
    (IsGalois.mem_range_algebraMap_iff_fixed (f.coeff m)).mpr fun σ => by
      have hcongr := congrArg (fun g => HahnSeries.coeff g m) (hf σ)
      simpa using hcongr
  choose r hr using hcoeff
  refine ⟨⟨r, ?_⟩, ?_⟩
  · refine f.isPWO_support'.mono fun m hm => ?_
    simp only [Function.mem_support] at hm ⊢
    intro h
    exact hm (FaithfulSMul.algebraMap_injective ℚ K (by rw [hr m, h, map_zero]))
  · ext m
    exact hr m

end Galois

section Intersection

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- A series that is both a level-`ℓ` expansion and rational is the level-`ℓ` image of a
rational series. -/
theorem mem_range_coeffEmb_qExpand_of_mem_inter {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {f : LaurentSeries K} (h1 : f ∈ Set.range (qExpand K ℓ))
    (h2 : f ∈ Set.range (coeffEmb K)) :
    ∃ g : LaurentSeries ℚ, f = coeffEmb K (qExpand ℚ ℓ g) := by
  obtain ⟨h, hh⟩ := h2
  have hsupp : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → h.coeff m = 0 := by
    intro m hm
    obtain ⟨g, hg⟩ := h1
    refine FaithfulSMul.algebraMap_injective ℚ K ?_
    rw [map_zero, ← coeffEmb_coeff, hh, ← hg, qExpand_coeff_of_not_dvd ℓ g hm]
  refine ⟨qContract ℓ h, ?_⟩
  rw [qExpand_qContract hsupp]
  exact hh.symm

end Intersection

end ModularCurve
