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

  The q-expansion dictionary of a descent closes the module: `splits_of_descends` states the
  splitting in the `evalAtJK` spelling, and the pole bounds of the product read as the three
  coefficient bounds the transpose needs.
-/

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.DedekindPsi
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.ModularEquation.Support.LevelEmbedding
import FLTForHuman.ModularCurve.ModularEquation.Support.PoleBounds

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve
namespace PhiGen

section PermLemma

variable {K : Type*} [Field K] {ℓ : ℕ} {conj : Fin (ℓ + 1) → LaurentSeries K}

private theorem map_phiProd_of_perm (F : LaurentSeries K →+* LaurentSeries K)
    (e : Fin ℓ ≃ Fin ℓ) (h0 : F (conj 0) = conj 0)
    (hS : ∀ b : Fin ℓ, F (conj b.succ) = conj (e b).succ) :
    (phiProd ℓ conj).map F = phiProd ℓ conj := by
  rw [phiProd, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, h0]
  congr 1
  calc ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (conj b.succ)))
      = ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj (e b).succ)) := by
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [hS b]
    _ = ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj b.succ)) :=
        e.prod_comp fun b => Polynomial.X - Polynomial.C (conj b.succ)

private theorem map_phiProd_coeff_of_perm (F : LaurentSeries K →+* LaurentSeries K)
    (e : Fin ℓ ≃ Fin ℓ) (h0 : F (conj 0) = conj 0)
    (hS : ∀ b : Fin ℓ, F (conj b.succ) = conj (e b).succ) (k : ℕ) :
    F ((phiProd ℓ conj).coeff k) = (phiProd ℓ conj).coeff k := by
  conv_rhs => rw [← map_phiProd_of_perm F e h0 hS]
  rw [Polynomial.coeff_map]

end PermLemma

section TwistRoot

variable {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}

private theorem zeta_pow_mod (hζ : IsPrimitiveRoot (ζ : K) ℓ) (n : ℕ) :
    ζ ^ (n % ℓ) = ζ ^ n :=
  (pow_eq_pow_mod n (units_pow_eq_one_of_isPrimitiveRoot hζ)).symm

end TwistRoot

section TwistConj

variable {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
  {conj : Fin (ℓ + 1) → LaurentSeries K} {ζ : Kˣ} {J : LaurentSeries K}

private theorem qTwist_conj_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J) : qTwist ζ (conj 0) = conj 0 := by
  rw [hconj0, qTwist_qExpand]
  congr 1
  rw [zpow_natCast, pow_mul, units_pow_eq_one_of_isPrimitiveRoot hζ, one_pow,
    qTwist_one_apply]

private theorem qTwist_conj_succ (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J) (b : Fin ℓ) :
    qTwist ζ (conj b.succ) = conj ((Equiv.addRight (1 : Fin ℓ)) b).succ := by
  rw [hconjS b, hconjS ((Equiv.addRight (1 : Fin ℓ)) b), qTwist_qTwist]
  congr 1
  simp only [Equiv.coe_addRight]
  have h1 : ((1 : Fin ℓ) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt hℓ.out.one_lt
  rw [Fin.val_add, h1, zeta_pow_mod hζ ((b : ℕ) + 1), pow_succ, mul_comm ζ (ζ ^ (b : ℕ))]

end TwistConj

section SupportCollapse

variable {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}

private theorem coeff_eq_zero_of_qTwist_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
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

end SupportCollapse

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

private theorem mem_range_qExpand_of_qTwist_eq {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {f : LaurentSeries K} (hf : qTwist ζ f = f) : f ∈ Set.range (qExpand K ℓ) :=
  ⟨qContract ℓ f, qExpand_qContract fun _ hm => coeff_eq_zero_of_qTwist_eq hζ hf hm⟩

end Contract

section GaloisPerm

variable {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}

private theorem exists_galoisPerm (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* K) :
    ∃ e : Fin ℓ ≃ Fin ℓ,
      ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ) := by

  have hσζ : (σ (ζ : K)) ^ ℓ = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζ

  set e₀ : Fin ℓ → Fin ℓ := fun b => ⟨(a * (b : ℕ)) % ℓ, Nat.mod_lt _ hℓ.out.pos⟩

  have hkey : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e₀ b : Fin ℓ) : ℕ) := by
    intro b
    show σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((a * (b : ℕ)) % ℓ)
    rw [map_pow, ← ha, ← pow_mul]
    exact pow_eq_pow_mod _ hζ.pow_eq_one

  have hinj : Function.Injective e₀ := by
    intro b b' hbb'
    have h1 : σ ((ζ : K) ^ (b : ℕ)) = σ ((ζ : K) ^ ((b' : Fin ℓ) : ℕ)) := by
      rw [hkey b, hkey b', hbb']
    exact Fin.ext (hζ.pow_inj b.isLt b'.isLt (σ.injective h1))
  exact ⟨Equiv.ofBijective e₀ (Finite.injective_iff_bijective.mp hinj), hkey⟩

end GaloisPerm

section GaloisConj

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **A Galois automorphism fixes the conjugate at infinity**: `conj 0` is a plain `q`-expansion of
the coefficient field (`conj_zero`), so any `σ` that fixes `coeffEmb K jq` and commutes with
`qExpand` fixes it. No permutation of the finite cusps enters — this is the `h0` hypothesis of
`map_phiProd_coeff_of_perm`, and it holds for every `σ` and every `ℓ`, `ζ` alike. -/
private theorem coeffMap_conj_zero (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (σ : K ≃ₐ[ℚ] K) :
    coeffMap (σ : K →+* K) (conj ℓ ζ 0) = conj ℓ ζ 0 := by
  calc coeffMap (σ : K →+* K) (conj ℓ ζ 0)
      = coeffMap (σ : K →+* K) (qExpand K (ℓ * ℓ) (coeffEmb K jq)) := by
        rw [conj_zero ℓ ζ]
    _ = qExpand K (ℓ * ℓ) (coeffMap (σ : K →+* K) (coeffEmb K jq)) := by
        rw [coeffMap_qExpand]
    _ = qExpand K (ℓ * ℓ) (coeffEmb K jq) := by
        rw [coeffMap_coeffEmb σ jq]
    _ = conj ℓ ζ 0 := by
        rw [← conj_zero ℓ ζ]

end GaloisConj

section FixedField

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem mem_range_coeffEmb_of_forall_coeffMap_eq [IsGalois ℚ K] [FiniteDimensional ℚ K]
    {f : LaurentSeries K} (hf : ∀ σ : K ≃ₐ[ℚ] K, coeffMap (σ : K →+* K) f = f) :
    f ∈ Set.range (coeffEmb K) := by
  have hfix : ∀ c : K, (∀ σ : K ≃ₐ[ℚ] K, σ c = c) → ∃ r : ℚ, algebraMap ℚ K r = c :=
    fun c hc => (IsGalois.mem_range_algebraMap_iff_fixed c).mpr hc
  have hcoeff : ∀ m : ℤ, ∃ r : ℚ, algebraMap ℚ K r = f.coeff m := fun m =>
    hfix (f.coeff m) fun σ => by
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

end FixedField

section Descent

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem mem_range_coeffEmb_qExpand_of_mem_inter {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {f : LaurentSeries K} (h1 : f ∈ Set.range (ModularCurve.qExpand K ℓ))
    (h2 : f ∈ Set.range (coeffEmb K)) :
    ∃ g : LaurentSeries ℚ, f = coeffEmb K (ModularCurve.qExpand ℚ ℓ g) := by
  obtain ⟨h, hh⟩ := h2

  have hsupp : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → h.coeff m = 0 := by
    intro m hm
    obtain ⟨g, hg⟩ := h1
    refine FaithfulSMul.algebraMap_injective ℚ K ?_
    rw [map_zero, ← coeffEmb_coeff, hh, ← hg, qExpand_coeff_of_not_dvd ℓ g hm]
  refine ⟨qContract ℓ h, ?_⟩
  rw [qExpand_qContract hsupp]
  exact hh.symm

end Descent

/-- **The coefficients of `phiProd ℓ (conj ℓ ζ)` descend to `ℚ((q))`**: each one is a `q ^ ℓ`
expansion (its support collapses onto multiples of `ℓ`) **and** rational (it is Galois-fixed), so it
lies in the intersection of those two ranges, which is the image of `coeffEmb K ∘ qExpand ℚ ℓ`
(`mem_range_coeffEmb_qExpand_of_mem_inter`); the descent is the choice of the preimage per
coefficient. The statement is the pin wrapper's
`Theorems/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean`. -/
theorem exists_phiGenDescends {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
    [IsGalois ℚ K] [FiniteDimensional ℚ K] (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    ∃ c : ℕ → LaurentSeries ℚ, PhiGenDescends ℓ ζ c := by
  have hmem : ∀ k : ℕ, ∃ g : LaurentSeries ℚ,
      (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (qExpand ℚ ℓ g) := by
    intro k
    refine mem_range_coeffEmb_qExpand_of_mem_inter ?_ ?_
    · refine mem_range_qExpand_of_qTwist_eq hζ ?_
      exact map_phiProd_coeff_of_perm (qTwist ζ) (Equiv.addRight (1 : Fin ℓ))
        (qTwist_conj_zero hζ (conj_zero ℓ ζ)) (qTwist_conj_succ hζ (conj_succ ℓ ζ)) k
    · refine mem_range_coeffEmb_of_forall_coeffMap_eq fun σ => ?_
      obtain ⟨e, he⟩ := exists_galoisPerm hζ (σ : K →+* K)
      refine map_phiProd_coeff_of_perm (coeffMap (σ : K →+* K)) e
        (coeffMap_conj_zero ℓ ζ σ) ?_ k
      intro b
      calc coeffMap (σ : K →+* K) (conj ℓ ζ b.succ)
          = coeffMap (σ : K →+* K) (qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq)) := by
            rw [conj_succ ℓ ζ b]
        _ = qTwist (ζ ^ ((e b : Fin ℓ) : ℕ)) (coeffMap (σ : K →+* K) (coeffEmb K jq)) := by
            rw [coeffMap_qTwist (σ : K →+* K) (ζ ^ (b : ℕ)) (ζ ^ ((e b : Fin ℓ) : ℕ))
                (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he b])]
        _ = qTwist (ζ ^ ((e b : Fin ℓ) : ℕ)) (coeffEmb K jq) := by
            rw [coeffMap_coeffEmb σ jq]
        _ = conj ℓ ζ (e b).succ := by
            rw [← conj_succ ℓ ζ (e b)]
  choose c hc using hmem
  exact ⟨c, hc⟩

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

namespace ModularCurve

/-! ## The q-expansion dictionary of a descent -/

namespace PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
  {c : ℕ → LaurentSeries ℚ}

/-- The level embedding creates and loses no coefficients: the coefficient of `q ^ (ℓ * m)` in
`qEmbedT`'s image is the embedding of the `q ^ m` coefficient. -/
private theorem coeff_qEmbedT (f : LaurentSeries ℚ) (m : ℤ) :
    (qEmbedT K ℓ f).coeff ((ℓ : ℤ) * m) = algebraMap ℚ K (f.coeff m) := by
  rw [qEmbedT_eq_coeffEmb_qExpand, coeffEmb_coeff, qExpand_coeff_mul]

/-- **A descent is a splitting**: a polynomial whose `X`-coefficients are the descended family's
is annihilated by the conjugates of `j(q)`. -/
theorem splits_of_descends (hdescend : PhiGenDescends ℓ ζ c) {Φ : Polynomial (Polynomial ℤ)}
    (hΦ : ∀ k, evalAtJ (Φ.coeff k) = c k) :
    Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ) := by
  refine Polynomial.ext fun k => ?_
  rw [Polynomial.coeff_map, evalAtJK_def, RingHom.comp_apply, hΦ k,
    qEmbedT_eq_coeffEmb_qExpand, ← hdescend k]

/-- The coefficient dictionary of a level substitution: a `q ↦ q ^ ℓ` substitution moves the
index by `ℓ` and nothing else, so the `m`-th coefficient of `Φ`'s `k`-th coefficient is the
`ℓ * m`-th coefficient of the conjugate product's. -/
private theorem coeff_eq_coeff_phiProd_of_splits {Φ : Polynomial (Polynomial ℤ)}
    (hsplit : Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ)) (k : ℕ) (m : ℤ) :
    algebraMap ℚ K ((evalAtJ (Φ.coeff k)).coeff m)
      = ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m) := by
  have hk : evalAtJK K ℓ (Φ.coeff k) = (phiProd ℓ (conj ℓ ζ)).coeff k := by
    rw [← Polynomial.coeff_map, ← hsplit]
  rw [← hk, evalAtJK_def, RingHom.comp_apply, coeff_qEmbedT]

/-- **The pole bounds of a splitting**: `Φ`'s coefficients have, coefficient by coefficient, the
`q`-expansion of a monic degree-`ψ(ℓ)` polynomial read through the transpose — `q ^ (-ψ(ℓ))`
carries a `1`, nothing sits below it, and every other coefficient vanishes at and below it.
T10's leading term `phiProd_conj_coeff_zero_lead` and vanishing bound
`phiProd_conj_coeff_eq_zero_of_le` are read at their `ℓ`-scaled index, and the constant
coefficient's tail from T10's uniform bound `ℓ * ℓ + ℓ`. -/
theorem coeff_poleBounds_of_splits (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {Φ : Polynomial (Polynomial ℤ)} (hsplit : Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ)) :
    (evalAtJ (Φ.coeff 0)).coeff (-(dedekindPsi ℓ : ℤ)) = 1 ∧
      (∀ m : ℕ, dedekindPsi ℓ < m → (evalAtJ (Φ.coeff 0)).coeff (-(m : ℤ)) = 0) ∧
      (∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi ℓ ≤ m →
        (evalAtJ (Φ.coeff k)).coeff (-(m : ℤ)) = 0) := by
  have hψ := dedekindPsi_prime hℓ.out
  have hW : ∀ k, TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ) := fun k =>
    tPoleOrderLE_phiProd_coeff ℓ ζ (coeffEmb K jq) (conj ℓ ζ) (conj_zero ℓ ζ)
      (conj_succ ℓ ζ) jSimplePole_jqK k
  have hidx : ∀ m : ℕ, (ℓ : ℤ) * (-(m : ℤ)) = -((ℓ * m : ℕ) : ℤ) := by
    intro m; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · have h1 : algebraMap ℚ K (1 : ℚ) = 1 := map_one _
    refine (algebraMap ℚ K).injective ?_
    rw [h1, coeff_eq_coeff_phiProd_of_splits hsplit 0, hψ]
    have hidx' : (ℓ : ℤ) * (-((ℓ + 1 : ℕ) : ℤ)) = -((ℓ * ℓ + ℓ : ℕ) : ℤ) := by push_cast; ring
    rw [hidx']
    exact phiProd_conj_coeff_zero_lead ℓ ζ hζ
  · intro m hm
    have h0 : algebraMap ℚ K (0 : ℚ) = 0 := map_zero _
    refine (algebraMap ℚ K).injective ?_
    rw [h0, coeff_eq_coeff_phiProd_of_splits hsplit 0, hidx]
    exact hW 0 _ (by
      rw [hψ] at hm
      have hm' : (ℓ : ℤ) + 1 < (m : ℤ) := by exact_mod_cast hm
      have h2 : (2 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ.out.two_le
      push_cast
      nlinarith)
  · intro k hk0 m hm
    have h0 : algebraMap ℚ K (0 : ℚ) = 0 := map_zero _
    refine (algebraMap ℚ K).injective ?_
    rw [h0, coeff_eq_coeff_phiProd_of_splits hsplit k, hidx]
    exact phiProd_conj_coeff_eq_zero_of_le ℓ ζ k hk0 (ℓ * m)
      (by rw [hψ] at hm; nlinarith [hℓ.out.two_le])

end PhiGen

end ModularCurve

end
