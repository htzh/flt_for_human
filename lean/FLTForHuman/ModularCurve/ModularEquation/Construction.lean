/-
  The construction of the modular equation: the conjugate product descends to `ℚ((q))`, its
  coefficients are integers, and they assemble into a monic bivariate `Φ ∈ ℤ[X][Y]`.

  Three statements, in order:

  * `exists_phiGenDescends` — every coefficient of `∏ᵢ (Y - conjᵢ)` is the level-`ℓ` image of a
    rational series `c k`. The support of a coefficient collapses onto the multiples of `ℓ`
    (the tame twist fixes the product and permutes its factors), and the coefficient is fixed by
    `Gal(K/ℚ)` (which permutes the conjugates), so it lies in the image of the level embedding.
  * `PhiGenDescends.intCoeffs` — `c k` has integer `q`-coefficients: the product's coefficients lie
    in `ℤ[ζ]`, hence so do the descended ones, and a rational algebraic integer is an integer.
  * `exists_modularPolynomialData_coeff_eq` — the descended family assembles: integer polynomials
    `Q k` with `evalAtJ (Q k) = c k` and `Q (ℓ + 1) = 1` give the datum `Φ = ∑ Q k · X ^ k`, monic
    of degree `ℓ + 1`, vanishing at `(j(q), j(q ^ ℓ))`.

  The module stops at the datum: the two read-offs that turn the descended family into the datum's
  splitting and into the transpose's pole bounds are not generic in `c` or `Φ`, so they live with
  their only consumer (`Existence`).
-/

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.ModularEquation.Support.Permutation

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve
namespace PhiGen

/-! ## The contraction of a level-`ℓ` support

`qContract ℓ f` is the series `m ↦ f.coeff (ℓ * m)`. It is the inverse of `qExpand ℚ ℓ` on series
whose support avoids the exponents not divisible by `ℓ`, which is exactly what the twist produces.
-/

section Contract

variable {K : Type*} [Field K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

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

section Descent

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The coefficients of `phiProd ℓ (conj ℓ ζ)` descend to `ℚ((q))`.**

One coefficient at a time. The tame twist `qTwist ζ` fixes the infinite conjugate and cycles the
finite ones, so it permutes the conjugate family and fixes the product: a coefficient of the product
is therefore supported on the multiples of `ℓ`. A Galois automorphism fixes `coeffEmb K jq`, hence
also the infinite conjugate, and permutes the finite ones through its action `ζ ↦ ζ ^ a`, so it too
fixes the product: every `q`-coefficient of every `F_k` is fixed by `Gal(K/ℚ)`, hence rational. Both
together put each `F_k` in the image of `coeffEmb K ∘ qExpand ℚ ℓ`, and `c k` is the preimage. -/
theorem exists_phiGenDescends {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
    [IsGalois ℚ K] [FiniteDimensional ℚ K] (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    ∃ c : ℕ → LaurentSeries ℚ, PhiGenDescends ℓ ζ c := by
  -- The twist is the permutation `twistPerm` of the conjugates, and a product does not see a
  -- permutation of its factors.
  have twist_fixes : ∀ k, qTwist ζ ((phiProd ℓ (conj ℓ ζ)).coeff k)
      = (phiProd ℓ (conj ℓ ζ)).coeff k :=
    fun k => Polynomial.coeff_map_prod_of_perm (qTwist ζ)
      (fun i => Polynomial.X - Polynomial.C (conj ℓ ζ i)) (twistPerm ℓ)
      (qTwist_X_sub_C_conj ℓ hζ) k

  -- A coefficient fixed by the twist is supported on the multiples of `ℓ`.
  have hsupp : ∀ (k : ℕ) (m : ℤ),
      ¬ (ℓ : ℤ) ∣ m → ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff m = 0 := by
    intro k m hm
    have htwist := congrArg (fun g => HahnSeries.coeff g m) (twist_fixes k)
    simp only [qTwist_coeff] at htwist
    by_contra hc
    apply hm
    rw [← hζ.zpow_eq_one_iff_dvd]
    have hunit : ((ζ ^ m : Kˣ) : K) = (ζ : K) ^ m := Units.val_zpow_eq_zpow_val ζ m
    have hzero : (((ζ ^ m : Kˣ) : K) - 1) * ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff m = 0 := by
      rw [sub_mul, one_mul, htwist, sub_self]
    rcases mul_eq_zero.mp hzero with h1 | h1
    · rw [hunit] at h1
      linear_combination h1
    · exact absurd h1 hc

  -- A Galois automorphism is the permutation `galPerm σ` of the conjugates, through its value of the
  -- cyclotomic character; the product is unchanged by a permutation of its factors.
  have gal_fixes : ∀ (σ : K ≃ₐ[ℚ] K) (k : ℕ),
      coeffMap (σ : K →+* K) ((phiProd ℓ (conj ℓ ζ)).coeff k)
        = (phiProd ℓ (conj ℓ ζ)).coeff k :=
    fun σ k => Polynomial.coeff_map_prod_of_perm (coeffMap (σ : K →+* K))
      (fun i => Polynomial.X - Polynomial.C (conj ℓ ζ i)) (galPerm σ hζ)
      (coeffMap_X_sub_C_conj σ hζ) k


  -- A product fixed by the whole Galois group has rational coefficients.
  have rational : ∀ k, ∃ f : LaurentSeries ℚ,
      (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K f := by
    intro k
    have hcoeff : ∀ m : ℤ, ∃ r : ℚ,
        algebraMap ℚ K r = ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff m := by
      intro m
      exact (IsGalois.mem_range_algebraMap_iff_fixed _).mpr fun σ => by
        have hcongr := congrArg (fun g => HahnSeries.coeff g m) (gal_fixes σ k)
        simpa using hcongr
    choose r hr using hcoeff
    refine ⟨⟨r, ?_⟩, ?_⟩
    · refine ((phiProd ℓ (conj ℓ ζ)).coeff k).isPWO_support'.mono fun m hm => ?_
      simp only [Function.mem_support] at hm ⊢
      intro h
      exact hm (FaithfulSMul.algebraMap_injective ℚ K (by rw [hr m, h, map_zero]))
    · ext m
      rw [coeffEmb_coeff]
      exact (hr m).symm

  -- The support of the rational series is on the multiples of `ℓ`, so it contracts.
  have descend : ∀ k, ∃ g : LaurentSeries ℚ,
      (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (qExpand ℚ ℓ g) := by
    intro k
    obtain ⟨f, hf⟩ := rational k
    have hf_supp : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → f.coeff m = 0 := by
      intro m hm
      refine FaithfulSMul.algebraMap_injective ℚ K ?_
      rw [map_zero, ← coeffEmb_coeff, ← hf, hsupp k m hm]
    exact ⟨qContract ℓ f, by rw [qExpand_qContract hf_supp, hf]⟩

  choose c hc using descend
  exact ⟨c, hc⟩

end Descent

end PhiGen
end ModularCurve


namespace ModularCurve
namespace PhiGen

/-- The level substitution composed with the coefficient embedding is injective:
`coeffEmb` is (`coeffEmb_injective`) and `q ↦ q ^ ℓ` is (`qExpand_injective`). -/
private theorem coeffEmb_qExpand_injective {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] :
    Function.Injective (fun f : LaurentSeries ℚ => coeffEmb K (qExpand ℚ ℓ f)) :=
  (coeffEmb_injective K).comp (qExpand_injective (R := ℚ) ℓ)

/-- The descended family is monic: its top coefficient is `1`. -/
theorem PhiGenDescends.c_top {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) : c (ℓ + 1) = 1 := by
  refine coeffEmb_qExpand_injective (K := K) (ℓ := ℓ) ?_
  have h1 : (phiProd ℓ (conj ℓ ζ)).coeff (ℓ + 1) = 1 := by
    have h := (phiProd_monic ℓ (conj ℓ ζ)).coeff_natDegree
    rwa [phiProd_natDegree ℓ (conj ℓ ζ)] at h
  simp only [← hc (ℓ + 1), h1, map_one]

/-- The descended family vanishes above degree `ℓ + 1`. -/
theorem PhiGenDescends.c_eq_zero {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) {k : ℕ} (hk : ℓ + 1 < k) : c k = 0 := by
  refine coeffEmb_qExpand_injective (K := K) (ℓ := ℓ) ?_
  have h1 : (phiProd ℓ (conj ℓ ζ)).coeff k = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [phiProd_natDegree]; exact hk)
  simp only [← hc k, h1, map_zero]

/-- Every descended coefficient has pole order at most `ℓ + 1` at `q = 0`:
T10's bound `ℓ * ℓ + ℓ` in the expanded nome, divided by `ℓ` by
`tPoleOrderLE_of_qExpand`. -/
theorem PhiGenDescends.poleOrderLE {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (k : ℕ) : PoleOrderLE (c k) (ℓ + 1) := by
  have hW3 : TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ) :=
    tPoleOrderLE_phiProd_coeff ℓ ζ (coeffEmb K jq) (conj ℓ ζ) (conj_zero ℓ ζ) (conj_succ ℓ ζ)
      jSimplePole_jqK k
  rw [hc k, tPoleOrderLE_coeffEmb_iff] at hW3
  rw [← tPoleOrderLE_iff_poleOrderLE]
  exact tPoleOrderLE_of_qExpand (hW3.mono (le_of_eq (by ring)))

/-- The modular-equation relation in the descended family:
`∑_{k ≤ ℓ+1} c k * j(q^ℓ)^k = 0`. Applying the level substitution sends
`j(q^ℓ)` to the extra root `conj 0` and the product to its own root. -/
theorem PhiGenDescends.sum_mul_jqN_pow_eq_zero {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) :
    ∑ k ∈ Finset.range (ℓ + 2), c k * (jqN ℓ) ^ k = 0 := by

  set F : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ ℓ) with hF
  have hFapp : ∀ f : LaurentSeries ℚ, F f = coeffEmb K (qExpand ℚ ℓ f) := fun f => rfl
  have hFinj : Function.Injective F := coeffEmb_qExpand_injective

  have hconj0 : conj ℓ ζ (0 : Fin (ℓ + 1)) = F (jqN ℓ) := by
    show conj ℓ ζ 0 = coeffMap (algebraMap ℚ K) (qExpand ℚ ℓ (jqN ℓ))
    rw [conj_zero, jqN, qExpand_qExpand, coeffMap_qExpand]
    rfl

  have hterm : ∀ k ∈ Finset.range (ℓ + 2),
      F (c k * (jqN ℓ) ^ k)
        = (phiProd ℓ (conj ℓ ζ)).coeff k * (conj ℓ ζ 0) ^ k := by
    intro k _
    rw [map_mul, map_pow, ← hconj0, hFapp, hc k]
  refine hFinj ?_
  rw [map_zero, map_sum, Finset.sum_congr rfl hterm]
  rw [← Polynomial.eval_eq_sum_range' (n := ℓ + 2) (by rw [phiProd_natDegree]; omega)]
  exact phiProd_eval_conj ℓ _ 0

/-- Evaluation at `jq` from `ℤ[X]` is injective — `jq` is transcendental. This is
the public entry point T12's 895 block imports. -/
theorem evalAtJ_injective : Function.Injective evalAtJ := by
  intro P Q hPQ
  have h' : Polynomial.aeval jq (P.map (Int.castRingHom ℚ))
      = Polynomial.aeval jq (Q.map (Int.castRingHom ℚ)) := by
    rw [← evalAtJ_eq_aeval_map, ← evalAtJ_eq_aeval_map]
    exact hPQ
  exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    ((transcendental_iff_injective.mp transcendental_jq) h')

end PhiGen
end ModularCurve

namespace ModularCurve
namespace PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ## The source ring `ℤ[ζ]`

`ζ` is a root of `X ^ ℓ - 1`, so `ℤ[ζ]` sits inside `𝒪 = integralClosure ℤ K`;
and `ζ` is a unit of `ℤ[ζ]` (inverse `ζ ^ (ℓ - 1)`), so the `qExpand`/`qTwist`
formula that defines the conjugates runs over `ℤ[ζ]` with no further input. -/

omit [Algebra ℚ K] in
private theorem mem_integralClosure_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {x : K}
    (hx : x ^ n = 1) : x ∈ integralClosure ℤ K := by
  rw [mem_integralClosure_iff]
  exact ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [hx]⟩

variable {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]

/-- `ℤ[ζ]`: the subalgebra of `K` generated by `ζ`. -/
private def zetaRing (ζ : Kˣ) : Subalgebra ℤ K :=
  Algebra.adjoin ℤ {(ζ : K)}

omit [Algebra ℚ K] in
private theorem zetaRing_le (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) : zetaRing ζ ≤ integralClosure ℤ K := by
  rw [zetaRing, Algebra.adjoin_le_iff]
  rintro x (rfl : x = (ζ : K))
  exact mem_integralClosure_of_pow_eq_one hℓ.out.ne_zero (by
    rw [← Units.val_pow_eq_pow_val, hζ1, Units.val_one])

/-- `ζ` as a unit of `ℤ[ζ]`, with inverse `ζ ^ (ℓ - 1)`. -/
private def zetaUnitS (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) : (zetaRing ζ)ˣ :=
  have hζ : (ζ : K) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hζ1, Units.val_one]
  have hζmem : (ζ : K) ∈ zetaRing ζ := Algebra.subset_adjoin rfl
  have hinv : ((ζ : K) ^ (ℓ - 1)) ∈ zetaRing ζ := pow_mem hζmem (ℓ - 1)
  Units.mkOfMulEqOne ⟨(ζ : K), hζmem⟩ ⟨((ζ : K) ^ (ℓ - 1)), hinv⟩
    (Subtype.ext (by
      show (ζ : K) * (ζ : K) ^ (ℓ - 1) = 1
      rw [← pow_succ', Nat.sub_add_cancel hℓ.out.one_le]
      exact hζ))

omit [Algebra ℚ K] in
private theorem zetaUnitS_val (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) :
    ((zetaUnitS ζ hζ1 : ↥(zetaRing ζ)) : K) = (ζ : K) := rfl

private theorem intCoeffs_jq_pow (n : ℕ) : IntCoeffs (jq ^ n) := by
  intro m
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  by_cases hneg : (m - -(n : ℤ)) < 0
  · exact ⟨0, by rw [ofPowerSeries_coeff_of_neg _ hneg, Int.cast_zero]⟩
  · refine ⟨(PowerSeries.coeff (m - -(n : ℤ)).toNat (jNum ^ n) : ℤ), ?_⟩
    have hcast : (m - -(n : ℤ)) = (((m - -(n : ℤ)).toNat : ℕ) : ℤ) :=
      (Int.toNat_of_nonneg (not_lt.mp hneg)).symm
    rw [hcast, HahnSeries.ofPowerSeries_apply_coeff]
    show PowerSeries.coeff _ (jNumQ ^ n) = _
    rw [jNumQ, ← map_pow, PowerSeries.coeff_map]
    rfl

private theorem intCoeffs_jq : IntCoeffs jq := by
  have h := intCoeffs_jq_pow 1
  rwa [pow_one] at h

/-- The coefficients of `jq` lie in `ℤ[ζ]`. -/
private theorem jq_coeff_mem (ζ : Kˣ) (m : ℤ) : (coeffEmb K jq).coeff m ∈ zetaRing ζ := by
  obtain ⟨z, hz⟩ := intCoeffs_jq m
  have hcomp : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = algebraMap ℤ K :=
    Subsingleton.elim _ _
  have hval : (algebraMap ℚ K) ((z : ℚ)) = algebraMap ℤ K z := by
    rw [← hcomp]
    rfl
  rw [coeffEmb_coeff, hz, hval]
  exact Subalgebra.algebraMap_mem _ z

/-- `jq`, viewed over `ℤ[ζ]`. -/
private def jqS (ζ : Kˣ) : LaurentSeries ↥(zetaRing ζ) where
  coeff m := ⟨(coeffEmb K jq).coeff m, jq_coeff_mem ζ m⟩
  isPWO_support' := (coeffEmb K jq).isPWO_support'.mono fun m hm => by
    rw [Function.mem_support] at hm ⊢
    exact fun h0 => hm (Subtype.ext h0)

private theorem coeffMap_jqS (ζ : Kˣ) :
    coeffMap (algebraMap ↥(zetaRing ζ) K) (jqS ζ) = coeffEmb K jq := rfl

/-- `conj i`, viewed over `ℤ[ζ]`. -/
private def conjAdjoin (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) (i : Fin (ℓ + 1)) :
    LaurentSeries ↥(zetaRing ζ) :=
  qExpand ↥(zetaRing ζ) (cosetA ℓ i * cosetA ℓ i)
    (qTwist (zetaUnitS ζ hζ1 ^ (cosetA ℓ i * cosetB ℓ i)) (jqS ζ))

private theorem coeffMap_conjAdjoin (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) (i : Fin (ℓ + 1)) :
    coeffMap (algebraMap ↥(zetaRing ζ) K) (conjAdjoin ζ hζ1 i) = conj ℓ ζ i := by
  have hval : ∀ n : ℕ, Units.map (algebraMap ↥(zetaRing ζ) K).toMonoidHom
      ((zetaUnitS ζ hζ1) ^ n) = ζ ^ n := by
    intro n
    rw [map_pow]
    congr 1
    ext
    rw [Units.coe_map]
    exact zetaUnitS_val ζ hζ1
  rw [conjAdjoin, coeffMap_qExpand,
    coeffMap_qTwist (algebraMap ↥(zetaRing ζ) K)
      (zetaUnitS ζ hζ1 ^ (cosetA ℓ i * cosetB ℓ i)) (ζ ^ (cosetA ℓ i * cosetB ℓ i))
      (by rw [← hval (cosetA ℓ i * cosetB ℓ i)]; rfl),
    coeffMap_jqS]
  unfold conj cosetSubst
  rw [RingHom.comp_apply]

/-! `coeffMap_qTwist` was this module's `private` 3-argument transport copy; T16
promoted the canonical 5-argument form (with the explicit `v`/`huv`) to
`Defs/Twist.lean`, which this module imports transitively through `Defs/PhiGen`.
The one call site below now names the public lemma explicitly. -/

private theorem coeffMap_qExpand_qTwist {R S : Type*} [CommRing R] [CommRing S]
    (σ : R →+* S) (u : Rˣ) (v : Sˣ) (huv : (v : S) = σ (u : R)) (N : ℕ) [NeZero N]
    (f : LaurentSeries R) :
    coeffMap σ (qExpand R N (qTwist u f)) = qExpand S N (qTwist v (coeffMap σ f)) := by
  rw [coeffMap_qExpand, coeffMap_qTwist σ u v huv]

private theorem prod_eq_of_lift {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {n : ℕ} {y : Fin n → A} {z : Fin n → B} (h : ∀ i, f (y i) = z i) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (y i))).map f
      = ∏ i : Fin n, (Polynomial.X - Polynomial.C (z i)) := by
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, h]

/-- Every coefficient of the conjugate product lies in `𝒪`: the product is the
image of a product over `ℤ[ζ]`. -/
private theorem coeff_phiProd_mem (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) (k : ℕ) (m : ℤ) :
    ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff m ∈ integralClosure ℤ K := by
  have hmap : (∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conjAdjoin ζ hζ1 i))).map
        (coeffMap (algebraMap ↥(zetaRing ζ) K)) = phiProd ℓ (conj ℓ ζ) :=
    prod_eq_of_lift _ fun i => coeffMap_conjAdjoin ζ hζ1 i
  rw [← hmap, Polynomial.coeff_map, coeffMap_coeff]
  exact zetaRing_le ζ hζ1 (SetLike.coe_mem _)

/-! ## The integrality of the descended family -/

variable {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}

/-- The descended coefficients of `phiProd` have integer `q`-expansion coefficients. -/
theorem PhiGenDescends.intCoeffs {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (hζ1 : ζ ^ ℓ = 1) (k : ℕ) : IntCoeffs (c k) := by
  intro m
  have h1 : algebraMap ℚ K ((c k).coeff m)
      = ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m) := by
    rw [hc k, coeffEmb_coeff, qExpand_coeff_mul]
  have hmem : algebraMap ℚ K ((c k).coeff m) ∈ integralClosure ℤ K := by
    rw [h1]
    exact coeff_phiProd_mem ζ hζ1 k ((ℓ : ℤ) * m)
  have : IsScalarTower ℤ ℚ K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hint : IsIntegral ℤ ((c k).coeff m) := (isIntegral_algebraMap_iff (B := K)).mp hmem
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨z, by rw [← hz]; simp⟩


/-! ## The triangularity descent

`jq = q⁻¹ + ⋯`, so `P.coeff (natDegree P)` is the `q ^ (-natDegree)` coefficient
of `P(jq)` (`coeff_aeval_jq_neg`, promoted to `Defs/Jq.lean`); subtracting that
top term and inducting on the degree turns `IntCoeffs (P(jq))` into `P ∈ ℤ[X]`. -/

private theorem intCoeffs_algebraMap_int_mul_jq_pow (z : ℤ) (n : ℕ) :
    IntCoeffs (algebraMap ℚ (LaurentSeries ℚ) ((z : ℚ)) * jq ^ n) := by
  intro m
  obtain ⟨a, ha⟩ := intCoeffs_jq_pow n m
  refine ⟨z * a, ?_⟩
  rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, ha]
  push_cast
  ring

private theorem IntCoeffs.sub {f g : LaurentSeries ℚ} (hf : IntCoeffs f) (hg : IntCoeffs g) :
    IntCoeffs (f - g) := by
  intro m
  obtain ⟨a, ha⟩ := hf m
  obtain ⟨b, hb⟩ := hg m
  exact ⟨a - b, by rw [HahnSeries.coeff_sub, ha, hb]; push_cast; ring⟩

/-- The triangularity descent: a rational polynomial whose value at `jq` has integer
`q`-expansion coefficients is itself in `ℤ[X]`. -/
theorem aeval_jq_intCoeffs_descent (P : Polynomial ℚ)
    (hP : IntCoeffs (Polynomial.aeval jq P)) (k : ℕ) : ∃ z : ℤ, P.coeff k = (z : ℚ) := by
  suffices H : ∀ d : ℕ, ∀ P : Polynomial ℚ, P.natDegree = d →
      IntCoeffs (Polynomial.aeval jq P) → ∀ k : ℕ, ∃ z : ℤ, P.coeff k = (z : ℚ) by
    exact H P.natDegree P rfl hP k
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro P hd hP k
  obtain ⟨zd, hzd⟩ := hP (-(d : ℤ))
  have hlead : P.coeff d = (zd : ℚ) := by
    rw [← coeff_aeval_jq_neg P hd.le, hzd]
  rcases lt_trichotomy k d with hk | rfl | hk
  ·
    set Q : Polynomial ℚ := P - Polynomial.C (P.coeff d) * Polynomial.X ^ d with hQ
    have hQcoeff : Q.coeff k = P.coeff k := by
      rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        ite_eq_right (by omega), mul_zero, sub_zero]
    have hQdeg : Q.natDegree < d := by
      rcases eq_or_ne Q 0 with hQ0 | hQ0
      · rw [hQ0, Polynomial.natDegree_zero]; omega
      refine lt_of_le_of_ne ?_ ?_
      · refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        rw [hd]
        exact max_le le_rfl (Polynomial.natDegree_C_mul_X_pow_le _ _)
      · intro hcon
        apply hQ0
        rw [← Polynomial.leadingCoeff_eq_zero, Polynomial.leadingCoeff, hcon, hQ,
          Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          ite_eq_left rfl, mul_one, sub_self]
    have hQint : IntCoeffs (Polynomial.aeval jq Q) := by
      rw [hQ, map_sub, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hlead]
      exact hP.sub (intCoeffs_algebraMap_int_mul_jq_pow zd d)
    obtain ⟨z, hz⟩ := ih Q.natDegree hQdeg Q rfl hQint k
    exact ⟨z, by rw [← hQcoeff, hz]⟩
  · exact ⟨zd, hlead⟩
  · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Int.cast_zero]⟩

/-! ## The wire test

`P = X`: `aeval jq X = jq`, `hP` is `intCoeffs_jq`, and the conclusion is
`X.coeff 1 = 1 ∈ ℤ`. -/
private theorem aeval_jq_intCoeffs_descent_X :
    ∃ z : ℤ, (Polynomial.X : Polynomial ℚ).coeff 1 = (z : ℚ) :=
  aeval_jq_intCoeffs_descent Polynomial.X (by simpa using intCoeffs_jq) 1

end PhiGen
end ModularCurve

namespace ModularCurve
namespace PhiGen

/-- A polynomial in `jq` of pole order `≤ n` has degree `≤ n`: the `q ^ (-d)`
coefficient of `P(jq)` is `P`'s top coefficient (`coeff_aeval_jq_neg`). -/
private theorem natDegree_le_of_poleOrderLE_aeval (P : Polynomial ℚ) {n : ℕ}
    (hn : PoleOrderLE (Polynomial.aeval jq P) n) : P.natDegree ≤ n := by
  by_contra h
  push Not at h
  have hP : P ≠ 0 := by
    rintro rfl
    simp at h
  have h0 := hn (-(P.natDegree : ℤ)) (by omega)
  rw [coeff_aeval_jq_neg P le_rfl] at h0
  exact (Polynomial.leadingCoeff_ne_zero.mpr hP) h0

/-- A series in `ℚ[jq]` of pole order `≤ n` is `P(jq)` for a `P` of degree
`≤ n`. -/
private theorem exists_aeval_jq_eq_of_mem_adjoin {f : LaurentSeries ℚ}
    (hf : f ∈ Algebra.adjoin ℚ {jq}) {n : ℕ}
    (hn : PoleOrderLE f n) : ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ f = Polynomial.aeval jq P := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hf
  obtain ⟨P, rfl⟩ := hf
  exact ⟨P, natDegree_le_of_poleOrderLE_aeval P hn, rfl⟩

section Exits

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
variable {c : ℕ → LaurentSeries ℚ}

/-- The integer polynomial `Q` with `evalAtJ Q = c k`, of degree `≤ ℓ + 1`. -/
private theorem PhiGenDescends.exists_intPoly (hc : PhiGenDescends ℓ ζ c)
    (hint : ∀ k, IntCoeffs (c k)) (hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq}) (k : ℕ) :
    ∃ Q : Polynomial ℤ, Q.natDegree ≤ ℓ + 1 ∧ evalAtJ Q = c k := by

  obtain ⟨P, hPdeg, hP⟩ := exists_aeval_jq_eq_of_mem_adjoin (hmem k) (hc.poleOrderLE k)

  have hPint : ∀ n : ℕ, ∃ z : ℤ, P.coeff n = (z : ℚ) :=
    aeval_jq_intCoeffs_descent P (by rw [← hP]; exact hint k)

  have hlift : P ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨z, hz⟩ := hPint n
    exact ⟨z, by rw [eq_intCast]; exact hz.symm⟩
  obtain ⟨Q, hQ⟩ := hlift
  have hQmap : Q.map (Int.castRingHom ℚ) = P := hQ
  refine ⟨Q, ?_, ?_⟩
  · rw [← Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℚ)
      Int.cast_injective Q, hQmap]
    exact hPdeg
  · rw [evalAtJ_eq_aeval_map, hQmap, hP]

end Exits

section StrongExistence

/-- The `m`-th coefficient of `∑_{k < n} C (Q k) * X ^ k` is `Q m` for `m < n`. -/
private theorem coeff_sum_C_mul_X_pow (Q : ℕ → Polynomial ℤ) (n m : ℕ) (hm : m < n) :
    (∑ k ∈ Finset.range n, Polynomial.C (Q k) * Polynomial.X ^ k).coeff m = Q m := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]
  · intro k _ hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (Ne.symm hk), mul_zero]
  · intro hm'
    exact absurd (Finset.mem_range.mpr hm) hm'

end StrongExistence

/-- The assembled datum: `Φ = ∑_{k ≤ ℓ+1} Q k (X) Y^k`, monic of degree `ℓ+1` and
vanishing at `j(q^ℓ)`, with `evalAtJ (Φ.coeff k) = c k`. -/
theorem exists_modularPolynomialData_coeff_eq {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (hint : ∀ k, IntCoeffs (c k))
    (hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq}) :
    ∃ data : ModularPolynomialData ℓ, ∀ k, evalAtJ (data.Φ.coeff k) = c k := by

  choose Q hQdeg hQeval using hc.exists_intPoly hint hmem

  have hQtop : Q (ℓ + 1) = 1 := by
    refine evalAtJ_injective ?_
    rw [hQeval (ℓ + 1), hc.c_top, map_one]

  set Φ : Polynomial (Polynomial ℤ) :=
    ∑ k ∈ Finset.range (ℓ + 2), Polynomial.C (Q k) * Polynomial.X ^ k with hΦ

  have hΦtop : Φ.coeff (ℓ + 1) = 1 := by
    rw [hΦ, coeff_sum_C_mul_X_pow Q (ℓ + 2) (ℓ + 1) (by omega), hQtop]

  have hΦdeg_le : Φ.natDegree ≤ ℓ + 1 := by
    rw [hΦ]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hΦdeg : Φ.natDegree = ℓ + 1 :=
    le_antisymm hΦdeg_le
      (Polynomial.le_natDegree_of_ne_zero (by rw [hΦtop]; exact one_ne_zero))

  have hΦcoeff : ∀ k, evalAtJ (Φ.coeff k) = c k := by
    intro k
    by_cases hk : k < ℓ + 2
    · rw [hΦ, coeff_sum_C_mul_X_pow Q (ℓ + 2) k hk, hQeval k]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Φ.natDegree < k), map_zero,
        hc.c_eq_zero (by omega : ℓ + 1 < k)]

  refine ⟨⟨Φ, ?_, ?_, ?_⟩, hΦcoeff⟩
  ·
    show Φ.coeff Φ.natDegree = 1
    rw [hΦdeg]
    exact hΦtop
  ·
    rw [hΦdeg, dedekindPsi_prime hℓ.out]
  ·
    rw [Polynomial.eval₂_eq_sum_range' evalAtJ (n := ℓ + 2) (by rw [hΦdeg]; omega) (jqN ℓ)]
    have hterm : ∀ k ∈ Finset.range (ℓ + 2),
        evalAtJ (Φ.coeff k) * (jqN ℓ) ^ k = c k * (jqN ℓ) ^ k := by
      intro k _
      rw [hΦcoeff k]
    rw [Finset.sum_congr rfl hterm]
    exact hc.sum_mul_jqN_pow_eq_zero

end PhiGen
end ModularCurve


end
