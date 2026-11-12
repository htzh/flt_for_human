/-
  The permutation of the conjugates induced by the tame twist.

  `conj : Fin (ℓ + 1) → K((q))` indexes the conjugates of `j(q)`: index `0` is the cusp at infinity
  (the extra conjugate `j(q ^ (ℓ * ℓ))`), the index `b.succ` is the finite cusp with coset label `b`.
  The tame twist `q ↦ ζ q` fixes the cusp at infinity and advances the finite labels by one, so it is
  a single `ℓ`-cycle on the finite cusps. This module computes that permutation, its arithmetic and
  cycle structure, and the equivariance `qTwist ζ (conj i) = conj (twistPerm i)`.

  The permutation is an object in its own right: `b ↦ b + n` on the labels, order `ℓ`, the cusp at
  infinity as its only fixed point, and transitivity on the finite cusps.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.Defs.Twist

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

/-! ## Products under a permutation

A product does not see a permutation of its factors. This is the generic statement: any finite index
set, any family of polynomials, any permutation of the family, and any endomorphism of the
coefficient ring that permutes the family. The only mathematical inputs are mathlib's `map_prod` and
`Equiv.prod_comp`. -/

namespace Polynomial

variable {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι]

/-- A product is fixed by a coefficient endomorphism that permutes the family of its factors. -/
theorem map_prod_of_perm (F : R →+* R) (f : ι → Polynomial R) (e : ι ≃ ι)
    (h : ∀ i, (f i).map F = f (e i)) :
    (∏ i, f i).map F = ∏ i, f i := by
  rw [Polynomial.map_prod]
  calc ∏ i, (f i).map F = ∏ i, f (e i) := Finset.prod_congr rfl fun i _ => h i
    _ = ∏ i, f i := e.prod_comp f

/-- Every coefficient of the product inherits the invariance. -/
theorem coeff_map_prod_of_perm (F : R →+* R) (f : ι → Polynomial R) (e : ι ≃ ι)
    (h : ∀ i, (f i).map F = f (e i)) (k : ℕ) :
    F ((∏ i, f i).coeff k) = (∏ i, f i).coeff k := by
  conv_rhs => rw [← map_prod_of_perm F f e h]
  rw [Polynomial.coeff_map]

end Polynomial

/-! ## The permutation of the conjugates induced by the tame twist -/

namespace Fin

variable {n : ℕ}

/-- A permutation of `Fin n`, extended to `Fin (n + 1)` by fixing `0`. -/
def succEquivOfEquiv (e : Fin n ≃ Fin n) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.cases 0 fun b => (e b).succ
  invFun := Fin.cases 0 fun b => (e.symm b).succ
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun b => ?_) i <;> simp
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun b => ?_) i <;> simp

@[simp]
theorem succEquivOfEquiv_zero (e : Fin n ≃ Fin n) : succEquivOfEquiv e 0 = 0 := rfl

@[simp]
theorem succEquivOfEquiv_succ (e : Fin n ≃ Fin n) (b : Fin n) :
    succEquivOfEquiv e b.succ = (e b).succ := rfl

end Fin

namespace ModularCurve

namespace PhiGen

section Twist

variable (ℓ : ℕ) [NeZero ℓ] [hℓ : Fact (Nat.Prime ℓ)]

/-- The permutation of the conjugate index set induced by the tame twist `q ↦ ζ q`: the cusp at
infinity is fixed and the `ℓ` finite cusps are rotated. -/
def twistPerm : Fin (ℓ + 1) ≃ Fin (ℓ + 1) :=
  Fin.succEquivOfEquiv (Equiv.addRight (1 : Fin ℓ))

omit hℓ in
@[simp]
theorem twistPerm_zero : twistPerm ℓ 0 = 0 := rfl

omit hℓ in
@[simp]
theorem twistPerm_succ (b : Fin ℓ) :
    twistPerm ℓ b.succ = ((Equiv.addRight (1 : Fin ℓ)) b).succ := rfl

/-- The label formula: the twist advances the coset label by one. -/
theorem twistPerm_succ_val (b : Fin ℓ) :
    ((twistPerm ℓ b.succ : Fin (ℓ + 1)) : ℕ) = ((b : ℕ) + 1) % ℓ + 1 := by
  rw [twistPerm_succ]
  simp only [Fin.val_succ, Equiv.coe_addRight]
  congr 1
  simp [Fin.val_add, Nat.mod_eq_of_lt hℓ.out.one_lt]

/-- The cusp at infinity is the only fixed point of the twist. -/
theorem twistPerm_eq_self_iff {i : Fin (ℓ + 1)} : twistPerm ℓ i = i ↔ i = 0 := by
  refine Fin.cases ?_ (fun b => ?_) i
  · simp
  · constructor
    · intro h
      have hv := congrArg (fun k : Fin (ℓ + 1) => (k : ℕ)) h
      rw [twistPerm_succ_val, Fin.val_succ] at hv
      have h2 := hℓ.out.two_le
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt b.isLt) with hlt | heq
      · rw [Nat.mod_eq_of_lt hlt] at hv
        omega
      · have heq' : (b : ℕ) + 1 = ℓ := heq
        rw [heq', Nat.mod_self] at hv
        omega
    · intro h
      exact absurd h (Fin.succ_ne_zero b)

/-- The twist acts on the conjugates through `twistPerm`. -/
theorem qTwist_conj {K : Type*} [Field K] [Algebra ℚ K] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) (i : Fin (ℓ + 1)) :
    qTwist ζ (conj ℓ ζ i) = conj ℓ ζ (twistPerm ℓ i) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [twistPerm_zero, conj_zero, qTwist_qExpand]
    congr 1
    rw [zpow_natCast, pow_mul, units_pow_eq_one_of_isPrimitiveRoot hζ, one_pow, qTwist_one_apply]
  · rw [twistPerm_succ, conj_succ ℓ ζ b, conj_succ ℓ ζ ((Equiv.addRight (1 : Fin ℓ)) b),
      qTwist_qTwist]
    congr 1
    simp only [Equiv.coe_addRight]
    have h1 : ((1 : Fin ℓ) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt hℓ.out.one_lt
    rw [Fin.val_add, h1,
      (pow_eq_pow_mod ((b : ℕ) + 1) (units_pow_eq_one_of_isPrimitiveRoot hζ)).symm, pow_succ,
      mul_comm ζ (ζ ^ (b : ℕ))]

/-- The same equivariance factor by factor, the shape the product lemma consumes. -/
theorem qTwist_X_sub_C_conj {K : Type*} [Field K] [Algebra ℚ K] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) (i : Fin (ℓ + 1)) :
    (Polynomial.X - Polynomial.C (conj ℓ ζ i)).map (qTwist ζ)
      = Polynomial.X - Polynomial.C (conj ℓ ζ (twistPerm ℓ i)) := by
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, qTwist_conj ℓ hζ i]


end Twist

/-! ## The permutation of the conjugates induced by a Galois automorphism

A Galois automorphism `σ` sends `ζ` to `ζ ^ a` for a value `a` of the cyclotomic character. It fixes
the cusp at infinity and multiplies the finite labels by `a`, so it too acts on the conjugates
through a permutation of `Fin (ℓ + 1)`. -/

section Galois

variable {ℓ : ℕ} [NeZero ℓ] [hℓ : Fact (Nat.Prime ℓ)]
  {K : Type*} [Field K] [Algebra ℚ K]

omit [NeZero ℓ] hℓ in
private theorem galPow_one (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    (σ (ζ : K)) ^ ℓ = 1 := by
  rw [← map_pow, hζ.pow_eq_one, map_one]

/-- The value of the cyclotomic character at `σ`: the exponent with `ζ ^ a = σ ζ`. -/
noncomputable def galExp (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) : ℕ :=
  Classical.choose (hζ.eq_pow_of_pow_eq_one (galPow_one σ hζ))

omit hℓ in
theorem galExp_lt (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    galExp σ hζ < ℓ :=
  (Classical.choose_spec (hζ.eq_pow_of_pow_eq_one (galPow_one σ hζ))).1

omit hℓ in
theorem galExp_spec (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    (ζ : K) ^ galExp σ hζ = σ (ζ : K) :=
  (Classical.choose_spec (hζ.eq_pow_of_pow_eq_one (galPow_one σ hζ))).2

/-- Multiplication of the finite labels by the value of the cyclotomic character. -/
noncomputable def galLabelPerm (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    Fin ℓ ≃ Fin ℓ :=
  Equiv.ofBijective
    (fun b : Fin ℓ => ⟨(galExp σ hζ * (b : ℕ)) % ℓ, Nat.mod_lt _ hℓ.out.pos⟩)
    (Finite.injective_iff_bijective.mp fun b b' hbb' => by
      have hb : (galExp σ hζ * (b : ℕ)) % ℓ = (galExp σ hζ * (b' : ℕ)) % ℓ :=
        congrArg Fin.val hbb'
      have h1 : σ ((ζ : K) ^ (b : ℕ)) = σ ((ζ : K) ^ ((b' : Fin ℓ) : ℕ)) := by
        rw [map_pow, map_pow, ← galExp_spec σ hζ, ← pow_mul, ← pow_mul,
          pow_eq_pow_mod (galExp σ hζ * (b : ℕ)) hζ.pow_eq_one,
          pow_eq_pow_mod (galExp σ hζ * (b' : ℕ)) hζ.pow_eq_one, hb]
      exact Fin.ext (hζ.pow_inj b.isLt b'.isLt (σ.injective h1)))

@[simp]
theorem galLabelPerm_val (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : Fin ℓ) :
    ((galLabelPerm σ hζ b : Fin ℓ) : ℕ) = (galExp σ hζ * (b : ℕ)) % ℓ := rfl

/-- The permutation of the conjugate index set induced by `σ`. -/
noncomputable def galPerm (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    Fin (ℓ + 1) ≃ Fin (ℓ + 1) :=
  Fin.succEquivOfEquiv (galLabelPerm σ hζ)

@[simp]
theorem galPerm_zero (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    galPerm σ hζ 0 = 0 := rfl

@[simp]
theorem galPerm_succ (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : Fin ℓ) :
    galPerm σ hζ b.succ = (galLabelPerm σ hζ b).succ := rfl

/-- `σ` acts on the conjugates through `galPerm`. -/
theorem coeffMap_conj (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (i : Fin (ℓ + 1)) :
    coeffMap (σ : K →+* K) (conj ℓ ζ i) = conj ℓ ζ (galPerm σ hζ i) := by
  have he : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ))
      = (ζ : K) ^ ((galLabelPerm σ hζ b : Fin ℓ) : ℕ) := fun b => by
    rw [map_pow, ← galExp_spec σ hζ, ← pow_mul, pow_eq_pow_mod _ hζ.pow_eq_one]
    rfl
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [galPerm_zero]
    calc coeffMap (σ : K →+* K) (conj ℓ ζ 0)
        = coeffMap (σ : K →+* K) (qExpand K (ℓ * ℓ) (coeffEmb K jq)) := by
          rw [conj_zero ℓ ζ]
      _ = qExpand K (ℓ * ℓ) (coeffMap (σ : K →+* K) (coeffEmb K jq)) := by
          rw [coeffMap_qExpand]
      _ = qExpand K (ℓ * ℓ) (coeffEmb K jq) := by
          rw [coeffMap_coeffEmb σ jq]
      _ = conj ℓ ζ 0 := by
          rw [← conj_zero ℓ ζ]
  · rw [galPerm_succ]
    calc coeffMap (σ : K →+* K) (conj ℓ ζ b.succ)
        = coeffMap (σ : K →+* K) (qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq)) := by
          rw [conj_succ ℓ ζ b]
      _ = qTwist (ζ ^ ((galLabelPerm σ hζ b : Fin ℓ) : ℕ))
            (coeffMap (σ : K →+* K) (coeffEmb K jq)) := by
          rw [coeffMap_qTwist (σ : K →+* K) (ζ ^ (b : ℕ))
            (ζ ^ ((galLabelPerm σ hζ b : Fin ℓ) : ℕ))
            (by
              rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
              exact (he b).symm)]
      _ = qTwist (ζ ^ ((galLabelPerm σ hζ b : Fin ℓ) : ℕ)) (coeffEmb K jq) := by
          rw [coeffMap_coeffEmb σ jq]
      _ = conj ℓ ζ (galLabelPerm σ hζ b).succ := by
          rw [← conj_succ ℓ ζ (galLabelPerm σ hζ b)]
      _ = conj ℓ ζ (galPerm σ hζ b.succ) := by
          rw [galPerm_succ]

/-- The same equivariance factor by factor. -/
theorem coeffMap_X_sub_C_conj (σ : K ≃ₐ[ℚ] K) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (i : Fin (ℓ + 1)) :
    (Polynomial.X - Polynomial.C (conj ℓ ζ i)).map (coeffMap (σ : K →+* K))
      = Polynomial.X - Polynomial.C (conj ℓ ζ (galPerm σ hζ i)) := by
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, coeffMap_conj σ hζ i]

end Galois

end PhiGen

end ModularCurve
