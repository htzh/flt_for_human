/-
The cleared-polynomial degree engine (cluster E) and the generic point,
translation and function-field layer (cluster F) of the explicit-Vélu port.

Statements are transcribed verbatim from the pinned FLT `aa2d8b3` files

* `P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean`
  (the canonical statement copy), and
* `P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq.lean`
  (the proof bodies, whose declaration order this module follows);

only proof bodies are adapted to mathlib `v4.34.0`. Cluster E and cluster F live
in one module because they interleave in the pin (F's `translationAlgEquivOf*`
family is declared after most of E and uses it).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Formula
import FLTForHuman.WeierstrassCurve.Place.Dictionary
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import Mathlib.Tactic.ComputeDegree
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Polynomial Finset
open scoped Polynomial.Bivariate

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace WeierstrassCurve

open WeierstrassCurve.Affine

section PowHelpers

variable {k : Type*} [Field k] {V : WeierstrassCurve k} {q : ℕ} {φ : k →+* k}

private lemma some_congr {R : Type*} [CommRing R] {V' : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V'.Nonsingular x₁ y₁) (h₂ : V'.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

end PowHelpers

section RationalPoints

variable {F : Type*} [Field F] {k : Type*} [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

def ratPointMap : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

@[scoped simp]
lemma ratPointMap_zero : ratPointMap f (0 : W₀.toAffine.Point) = 0 :=
  rfl

lemma ratPointMap_some {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    ratPointMap f (.some x y h)
      = .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

lemma ratPointMap_injective : Function.Injective (ratPointMap f (W₀ := W₀)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [ratPointMap_some, ratPointMap_some, Affine.Point.some.injEq] at h
    exact some_congr (f.injective h.1) (f.injective h.2) _ _

theorem ratPointMap_add [DecidableEq F] [DecidableEq k] (P Q : W₀.toAffine.Point) :
    ratPointMap f (P + Q) = ratPointMap f P + ratPointMap f Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, ratPointMap_zero, ratPointMap_some,
      ratPointMap_some,
      Affine.Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, Affine.map_negY])]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy, ratPointMap_some, ratPointMap_some, ratPointMap_some,
      Affine.Point.add_some hxy']
    exact some_congr (by rw [Affine.map_slope, Affine.map_addX])
      (by rw [Affine.map_slope, Affine.map_addY]) _ _

@[simps]
def ratPointHom [DecidableEq F] [DecidableEq k] :
    W₀.toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := ratPointMap f
  map_zero' := rfl
  map_add' := ratPointMap_add f

end RationalPoints

section ClearedPoly

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluKernelDenom (S : Finset (F × F)) : F[X] := ∏ A ∈ S, (X - C A.1)

lemma veluKernelDenom_monic (S : Finset (F × F)) :
    (veluKernelDenom (F := F) S).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma veluKernelDenom_natDegree (S : Finset (F × F)) :
    (veluKernelDenom (F := F) S).natDegree = S.card := by
  unfold veluKernelDenom
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

lemma eval_veluKernelDenom (S : Finset (F × F)) (r : F) :
    (veluKernelDenom (F := F) S).eval r = ∏ A ∈ S, (r - A.1) := by
  simp [veluKernelDenom, eval_prod]

def veluDeficitSingletonSumClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, C ((W.Ψ₃).eval A.1) * W.veluDeficitPsiCofactorReducedPoly A.1
    * (∏ B ∈ S.erase A, (X - C B.1)) ^ 4

theorem veluDeficit_sum_singleton_mul_prodPow_eq {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2)
    (hav : ∀ A ∈ S, r ≠ A.1) :
    (∑ A ∈ S, W.veluDeficit {A} r s) * (∏ A ∈ S, (r - A.1)) ^ 4
      = (W.veluDeficitSingletonSumClearedPoly S).eval r := by
  rw [veluDeficitSingletonSumClearedPoly, eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hsplit : (∏ B ∈ S, (r - B.1)) ^ 4
      = (r - A.1) ^ 4 * (∏ B ∈ S.erase A, (r - B.1)) ^ 4 := by
    rw [← mul_pow, ← Finset.prod_erase_mul S _ hA, mul_comm]
  rw [hsplit, ← mul_assoc,
    show ({A} : Finset (F × F)) = {(A.1, A.2)} by simp,
    W.veluDeficit_singleton_mul_pow_four_eq hP (hSeq A hA) (hav A hA)]
  simp only [eval_mul, eval_C, eval_pow, eval_prod, eval_sub, eval_X,
    eval_veluDeficitPsiCofactorReducedPoly]
  ring

theorem veluDeficitSingletonSumClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitSingletonSumClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1)
    (natDegree_le_iff_degree_le.mpr ?_) (by omega)
  refine (degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_)
  refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
  have hcard : (S.erase A).card = S.card - 1 := Finset.card_erase_of_mem hA
  calc (C ((W.Ψ₃).eval A.1) * W.veluDeficitPsiCofactorReducedPoly A.1
          * (∏ B ∈ S.erase A, (X - C B.1)) ^ 4).natDegree
      ≤ (C ((W.Ψ₃).eval A.1) * W.veluDeficitPsiCofactorReducedPoly A.1).natDegree
          + ((∏ B ∈ S.erase A, ((X : F[X]) - C B.1)) ^ 4).natDegree := natDegree_mul_le
    _ ≤ 3 + 4 * (S.card - 1) := by
        refine add_le_add ((natDegree_C_mul_le _ _).trans
            (W.veluDeficitPsiCofactorReducedPoly_natDegree_le A.1)) ?_
        rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
        simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, hcard, le_refl]
    _ ≤ 4 * S.card - 1 := by omega

theorem veluDeficit_mul_prodPow_eq_clearedPoly_add_crossQuad {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2)
    (hav : ∀ A ∈ S, r ≠ A.1) :
    W.veluDeficit S r s * (∏ A ∈ S, (r - A.1)) ^ 4
      = (W.veluDeficitSingletonSumClearedPoly S).eval r
        + W.veluDeficitCrossQuad S r s * (∏ A ∈ S, (r - A.1)) ^ 4 := by
  rw [W.veluDeficit_eq_sum_singleton_add_crossQuad hP, add_mul,
    W.veluDeficit_sum_singleton_mul_prodPow_eq hP hSeq hav]

end ClearedPoly

section ArchetypeGeneralD

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem veluDeficit_isConstant_constant_eq_zero_of_crossQuadProdDegLt [Infinite F]
    {S : Finset (F × F)} (hS : S.Nonempty) {c : F}
    (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2)
    (habs : ∀ r : F, ∃ s, W.toAffine.Equation r s)
    (hc : ∀ ⦃r s : F⦄, W.toAffine.Equation r s → (∀ A ∈ S, r ≠ A.1) →
      W.veluDeficit S r s = c)
    {M : F[X]} (hMdeg : M.natDegree < 4 * S.card)
    (hM : ∀ ⦃r s : F⦄, W.toAffine.Equation r s → (∀ A ∈ S, r ≠ A.1) →
      W.veluDeficitCrossQuad S r s * (∏ A ∈ S, (r - A.1)) ^ 4 = M.eval r) :
    c = 0 := by
  set D : F[X] := veluKernelDenom S with hD_def
  set P : F[X] := C c * D ^ 4 - W.veluDeficitSingletonSumClearedPoly S - M with hP_def
  have hroot : ∀ r ∈ ((S.image Prod.fst : Finset F) : Set F)ᶜ, P.IsRoot r := by
    intro r hr
    have hav : ∀ A ∈ S, r ≠ A.1 := by
      intro A hA hrA; apply hr
      exact Finset.mem_coe.mpr (hrA ▸ Finset.mem_image_of_mem Prod.fst hA)
    obtain ⟨s, hrs⟩ := habs r
    have key := W.veluDeficit_mul_prodPow_eq_clearedPoly_add_crossQuad hrs hSeq hav
    rw [hc hrs hav, hM hrs hav] at key
    simp only [IsRoot, hP_def, hD_def, eval_sub, eval_mul, eval_C, eval_pow,
      eval_veluKernelDenom]
    linear_combination key
  have hinf : (((S.image Prod.fst : Finset F) : Set F)ᶜ).Infinite :=
    (Set.Finite.infinite_compl (Finset.finite_toSet _))
  have hP0 : P = 0 := eq_zero_of_infinite_isRoot P (hinf.mono fun r hr => hroot r hr)
  have hDmon : (D ^ 4).Monic := (veluKernelDenom_monic S).pow 4
  have hDdeg : (D ^ 4).natDegree = 4 * S.card := by
    rw [natDegree_pow, hD_def, veluKernelDenom_natDegree]
  have hcoeff : P.coeff (4 * S.card) = c := by
    rw [hP_def, coeff_sub, coeff_sub, coeff_C_mul]
    have h1 : (D ^ 4).coeff (4 * S.card) = 1 := by
      have := hDmon.coeff_natDegree; rwa [hDdeg] at this
    have h2 : (W.veluDeficitSingletonSumClearedPoly S).coeff (4 * S.card) = 0 :=
      coeff_eq_zero_of_natDegree_lt (W.veluDeficitSingletonSumClearedPoly_natDegree_lt hS)
    have h3 : M.coeff (4 * S.card) = 0 := coeff_eq_zero_of_natDegree_lt hMdeg
    rw [h1, h2, h3, mul_one, sub_zero, sub_zero]
  rw [hP0, coeff_zero] at hcoeff
  exact hcoeff.symm

end ArchetypeGeneralD

section CrossQuadCarrier

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitCrossQuadProdDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuad
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r

variable {F}

namespace Affine

theorem exists_equation_of_isAlgClosed [IsAlgClosed F] (W : WeierstrassCurve F)
    (r : F) : ∃ s, W.toAffine.Equation r s := by
  set q : F[X] := X ^ 2 + C (W.a₁ * r + W.a₃) * X
    - C (r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆) with hq
  have hqdeg : q.degree = 2 := by rw [hq]; compute_degree!
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_root q (by rw [hqdeg]; exact two_ne_zero)
  refine ⟨s, (Affine.equation_iff ..).mpr ?_⟩
  have hs' : q.eval s = 0 := hs
  simp only [hq, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hs'
  linear_combination hs'

end Affine

end CrossQuadCarrier

section AlphaPoly

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluXCorrNumPoly (A : F × F) : F[X] :=
  C (W.veluT A.1 A.2) * (X - C A.1) + C (W.veluU A.1 A.2)

lemma veluXCorrNumPoly_natDegree_le (A : F × F) :
    (W.veluXCorrNumPoly A).natDegree ≤ 1 := by
  unfold veluXCorrNumPoly; compute_degree

def veluXCorrPadPoly (S : Finset (F × F)) (A : F × F) : F[X] :=
  W.veluXCorrNumPoly A * (∏ B ∈ S.erase A, (X - C B.1)) ^ 2

theorem eval_veluXCorrPadPoly {S : Finset (F × F)} {A : F × F} (hA : A ∈ S) {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluX {A} r - r) * (∏ B ∈ S, (r - B.1)) ^ 2
      = (W.veluXCorrPadPoly S A).eval r := by
  have hd : r - A.1 ≠ 0 := sub_ne_zero.mpr (hav A hA)
  have hsplit : (∏ B ∈ S, (r - B.1)) ^ 2
      = (r - A.1) ^ 2 * (∏ B ∈ S.erase A, (r - B.1)) ^ 2 := by
    rw [← mul_pow, ← Finset.prod_erase_mul S _ hA, mul_comm]
  rw [hsplit, ← mul_assoc, veluXCorrPadPoly, veluXCorrNumPoly]
  simp only [veluX, Finset.sum_singleton, eval_mul, eval_add, eval_C, eval_sub, eval_X,
    eval_pow, eval_prod]
  field_simp
  ring

def veluXCorrSumPadPoly (S : Finset (F × F)) : F[X] := ∑ A ∈ S, W.veluXCorrPadPoly S A

lemma veluX_sub_self_eq_sum_singleton (S : Finset (F × F)) (r : F) :
    W.veluX S r - r = ∑ A ∈ S, (W.veluX {A} r - r) := by
  simp only [veluX, Finset.sum_singleton, add_sub_cancel_left]

theorem eval_veluXCorrSumPadPoly {S : Finset (F × F)} {r : F} (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluX S r - r) * (∏ B ∈ S, (r - B.1)) ^ 2
      = (W.veluXCorrSumPadPoly S).eval r := by
  rw [veluXCorrSumPadPoly, eval_finsetSum, W.veluX_sub_self_eq_sum_singleton, Finset.sum_mul]
  exact Finset.sum_congr rfl fun A hA => W.eval_veluXCorrPadPoly hA hav

theorem veluXCorrPadPoly_natDegree_le {S : Finset (F × F)} {A : F × F} (hA : A ∈ S) :
    (W.veluXCorrPadPoly S A).natDegree ≤ 2 * S.card - 1 := by
  have hScard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨A, hA⟩
  unfold veluXCorrPadPoly
  calc (W.veluXCorrNumPoly A * (∏ B ∈ S.erase A, ((X : F[X]) - C B.1)) ^ 2).natDegree
      ≤ 1 + 2 * (S.card - 1) := by
        refine natDegree_mul_le.trans (add_le_add (W.veluXCorrNumPoly_natDegree_le A) ?_)
        rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
        simp [Finset.card_erase_of_mem hA]
    _ ≤ 2 * S.card - 1 := by omega

theorem veluXCorrSumPadPoly_natDegree_le (S : Finset (F × F)) :
    (W.veluXCorrSumPadPoly S).natDegree ≤ 2 * S.card - 1 := by
  refine natDegree_le_iff_degree_le.mpr ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
  exact degree_le_natDegree.trans (Nat.cast_le.mpr (W.veluXCorrPadPoly_natDegree_le hA))

end AlphaPoly

section AlphaSqCrossCleared

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadAlphaSqClearedPoly (S : Finset (F × F)) : F[X] :=
  -(C 3 * X + C W.a₂)
      * ((W.veluXCorrSumPadPoly S) ^ 2 - ∑ A ∈ S, (W.veluXCorrPadPoly S A) ^ 2)
    + C 5 * (C (W.veluTSum S) * W.veluXCorrSumPadPoly S
        - ∑ A ∈ S, C (W.veluT A.1 A.2) * W.veluXCorrPadPoly S A)
      * (veluKernelDenom S) ^ 2

theorem veluDeficitCrossQuadAlphaSq_mul_prodPow_eq {S : Finset (F × F)} {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadAlphaSq S r * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadAlphaSqClearedPoly S).eval r := by
  set D : F := ∏ B ∈ S, (r - B.1)
  have hD4 : D ^ 4 = D ^ 2 * D ^ 2 := by ring
  have hαS : (W.veluX S r - r) * D ^ 2 = (W.veluXCorrSumPadPoly S).eval r :=
    W.eval_veluXCorrSumPadPoly hav
  have hαA : ∀ A ∈ S, (W.veluX {A} r - r) * D ^ 2 = (W.veluXCorrPadPoly S A).eval r :=
    fun A hA => W.eval_veluXCorrPadPoly hA hav
  unfold veluDeficitCrossQuadAlphaSq veluDeficitCrossQuadAlphaSqClearedPoly
  simp only [eval_add, eval_neg, eval_mul, eval_C, eval_X, eval_sub, eval_pow,
    eval_finsetSum, eval_veluKernelDenom]
  rw [sub_mul, Finset.sum_mul, hD4]
  have key1 : (-(3 * r + W.a₂) * (W.veluX S r - r) ^ 2
      + 5 * W.veluTSum S * (W.veluX S r - r)) * (D ^ 2 * D ^ 2)
      = -(3 * r + W.a₂) * ((W.veluXCorrSumPadPoly S).eval r) ^ 2
        + 5 * (W.veluTSum S * (W.veluXCorrSumPadPoly S).eval r) * D ^ 2 := by
    rw [← hαS]; ring
  have key2 : ∀ A ∈ S,
      (-(3 * r + W.a₂) * (W.veluX {A} r - r) ^ 2
        + 5 * W.veluTSum {A} * (W.veluX {A} r - r)) * (D ^ 2 * D ^ 2)
      = -(3 * r + W.a₂) * ((W.veluXCorrPadPoly S A).eval r) ^ 2
        + 5 * (W.veluT A.1 A.2 * (W.veluXCorrPadPoly S A).eval r) * D ^ 2 := by
    intro A hA
    rw [← hαA A hA, veluTSum, Finset.sum_singleton]; ring
  rw [key1, Finset.sum_congr rfl key2, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem veluDeficitCrossQuadAlphaSqClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitCrossQuadAlphaSqClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1)
    (natDegree_le_iff_degree_le.mpr ?_) (by omega)
  unfold veluDeficitCrossQuadAlphaSqClearedPoly
  refine (degree_add_le _ _).trans (max_le ?_ ?_)
  ·
    rw [neg_mul, degree_neg]
    refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
    refine natDegree_mul_le.trans ?_
    have h1 : (C (3 : F) * X + C W.a₂).natDegree ≤ 1 := by compute_degree
    have h2 : ((W.veluXCorrSumPadPoly S) ^ 2
        - ∑ A ∈ S, (W.veluXCorrPadPoly S A) ^ 2).natDegree ≤ 2 * (2 * S.card - 1) := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_pow_le).trans
          (Nat.mul_le_mul_left 2 (W.veluXCorrSumPadPoly_natDegree_le S))
      · refine natDegree_le_iff_degree_le.mpr
          ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
        refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
        exact (natDegree_pow_le).trans
          (Nat.mul_le_mul_left 2 (W.veluXCorrPadPoly_natDegree_le hA))
    omega
  ·
    refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
    refine natDegree_mul_le.trans ?_
    have hD : ((veluKernelDenom (F := F) S) ^ 2).natDegree = 2 * S.card := by
      rw [natDegree_pow, veluKernelDenom_natDegree]
    rw [hD]
    have hαbound : (C (5 : F) * (C (W.veluTSum S) * W.veluXCorrSumPadPoly S
        - ∑ A ∈ S, C (W.veluT A.1 A.2) * W.veluXCorrPadPoly S A)).natDegree
        ≤ 2 * S.card - 1 := by
      refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le ?_ ?_))
      · exact (natDegree_C_mul_le _ _).trans (W.veluXCorrSumPadPoly_natDegree_le S)
      · refine natDegree_le_iff_degree_le.mpr
          ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
        exact degree_le_natDegree.trans (Nat.cast_le.mpr
          ((natDegree_C_mul_le _ _).trans (W.veluXCorrPadPoly_natDegree_le hA)))
    omega

end AlphaSqCrossCleared

section ReductionCubeBeta

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitCrossQuadCubeBetaDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadCubeBeta
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r

end ReductionCubeBeta

section MapVelu'

variable {F F' : Type*} [Field F] [Field F'] (W : WeierstrassCurve F) (f : F →+* F')

lemma map_veluX' (S : Finset (F × F)) (hf : Function.Injective f) (x : F) :
    (W.map f).veluX (S.map ⟨Prod.map f f, hf.prodMap hf⟩) (f x) = f (W.veluX S x) := by
  simp only [veluX, Finset.sum_map, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
    map_veluT, map_veluU, map_add, map_sum, map_div₀, map_sub, map_pow]

lemma map_veluY' (S : Finset (F × F)) (hf : Function.Injective f) (x y : F) :
    (W.map f).veluY (S.map ⟨Prod.map f f, hf.prodMap hf⟩) (f x) (f y) = f (W.veluY S x y) := by
  simp only [veluY, Finset.sum_map, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
    map_veluT, map_veluU, map_veluGx, map_veluGy, map_a₁, map_a₃,
    map_add, map_sub, map_mul, map_div₀, map_pow, map_sum, map_ofNat]

theorem map_veluDeficit (S : Finset (F × F)) (hf : Function.Injective f) (r s : F) :
    (W.map f).veluDeficit (S.map ⟨Prod.map f f, hf.prodMap hf⟩) (f r) (f s)
      = f (W.veluDeficit S r s) := by
  simp only [veluDeficit, W.map_veluX' f S hf, W.map_veluY' f S hf,
    W.map_veluQuotient f S hf, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    map_add, map_sub, map_mul, map_pow]

end MapVelu'

section FunctionFieldLift

variable {F : Type*} [Field F] (W : Affine F)

def liftSummingSet (S : Finset (F × F)) : Finset (W.FunctionField × W.FunctionField) :=
  S.map ⟨Prod.map (algebraMap F W.FunctionField) (algebraMap F W.FunctionField),
    (algebraMap F W.FunctionField).injective.prodMap (algebraMap F W.FunctionField).injective⟩

def veluDeficitFun (S : Finset (F × F)) : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).veluDeficit (W.liftSummingSet S)
    (polyToFunctionField W X) (yGen W)

end FunctionFieldLift

section HelperCube

lemma cube_sum_sub_sum_cube_eq {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → R) :
    (∑ A ∈ s, f A) ^ 3 - ∑ A ∈ s, f A ^ 3
      = ∑ A ∈ s, ∑ B ∈ s.erase A, ((∑ E ∈ s, f E) + f A) * (f A * f B) := by
  have key : ∀ A ∈ s, ∑ B ∈ s.erase A, ((∑ E ∈ s, f E) + f A) * (f A * f B)
      = (∑ E ∈ s, f E) ^ 2 * f A - f A ^ 3 := by
    intro A hA
    have hsum : (∑ B ∈ s.erase A, f B) = (∑ E ∈ s, f E) - f A := by
      linear_combination Finset.add_sum_erase s f hA
    calc ∑ B ∈ s.erase A, ((∑ E ∈ s, f E) + f A) * (f A * f B)
        = ((∑ E ∈ s, f E) + f A) * f A * ∑ B ∈ s.erase A, f B := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun B _ => by ring
      _ = ((∑ E ∈ s, f E) + f A) * f A * ((∑ E ∈ s, f E) - f A) := by rw [hsum]
      _ = (∑ E ∈ s, f E) ^ 2 * f A - f A ^ 3 := by ring
  calc (∑ A ∈ s, f A) ^ 3 - ∑ A ∈ s, f A ^ 3
      = (∑ E ∈ s, f E) ^ 2 * (∑ A ∈ s, f A) - ∑ A ∈ s, f A ^ 3 := by ring
    _ = (∑ A ∈ s, (∑ E ∈ s, f E) ^ 2 * f A) - ∑ A ∈ s, f A ^ 3 := by rw [Finset.mul_sum]
    _ = ∑ A ∈ s, ((∑ E ∈ s, f E) ^ 2 * f A - f A ^ 3) := by rw [Finset.sum_sub_distrib]
    _ = _ := Eq.symm (Finset.sum_congr rfl key)

end HelperCube

section Decomp

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadAlphaCube (S : Finset (F × F)) (r : F) : F :=
  (W.veluX S r - r) ^ 3 - ∑ A ∈ S, (W.veluX {A} r - r) ^ 3

def veluDeficitCrossQuadBetaOnly [DecidableEq F] (S : Finset (F × F)) (r s : F) : F :=
  W.veluDeficitCrossQuadCubeBeta S r s + W.veluDeficitCrossQuadAlphaCube S r

lemma veluDeficitCrossQuadCubeBeta_eq_betaOnly_sub_alphaCube [DecidableEq F]
    (S : Finset (F × F)) (r s : F) :
    W.veluDeficitCrossQuadCubeBeta S r s
      = W.veluDeficitCrossQuadBetaOnly S r s - W.veluDeficitCrossQuadAlphaCube S r := by
  unfold veluDeficitCrossQuadBetaOnly; ring

theorem veluDeficitCrossQuadBetaOnly_eq [DecidableEq F] (S : Finset (F × F)) (r s : F) :
    W.veluDeficitCrossQuadBetaOnly S r s
      = ((W.veluY S r s - s) ^ 2 + W.a₁ * (W.veluX S r - r) * (W.veluY S r s - s))
        - ∑ A ∈ S, ((W.veluY {A} r s - s) ^ 2
            + W.a₁ * (W.veluX {A} r - r) * (W.veluY {A} r s - s)) := by
  unfold veluDeficitCrossQuadBetaOnly veluDeficitCrossQuadCubeBeta veluDeficitCrossQuadAlphaCube
    veluDeficitCrossQuad veluDeficitCrossQuadAlphaSq veluDeficitQuad
  have hsum : (∑ A ∈ S, ((W.veluY {A} r s - s) ^ 2
        + W.a₁ * (W.veluX {A} r - r) * (W.veluY {A} r s - s)
        - (3 * r + W.a₂) * (W.veluX {A} r - r) ^ 2 - (W.veluX {A} r - r) ^ 3
        + 5 * W.veluTSum {A} * (W.veluX {A} r - r)))
      - (∑ A ∈ S, (-(3 * r + W.a₂) * (W.veluX {A} r - r) ^ 2
          + 5 * W.veluTSum {A} * (W.veluX {A} r - r)))
      + (∑ A ∈ S, (W.veluX {A} r - r) ^ 3)
      = ∑ A ∈ S, ((W.veluY {A} r s - s) ^ 2
          + W.a₁ * (W.veluX {A} r - r) * (W.veluY {A} r s - s)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun A _ => by ring
  linear_combination -hsum

end Decomp

section PairPad

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluXCorrPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluXCorrNumPoly A * W.veluXCorrNumPoly B
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 2

theorem veluXCorrPadPoly_mul_eq_kernelDenom_sq_mul {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluXCorrPadPoly S A * W.veluXCorrPadPoly S B
      = (veluKernelDenom S) ^ 2 * W.veluXCorrPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluXCorrPadPoly veluXCorrPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

theorem veluXCorrPairPadQuot_natDegree_le {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (W.veluXCorrPairPadQuot S A B).natDegree ≤ 2 * S.card - 2 := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  unfold veluXCorrPairPadQuot
  calc (W.veluXCorrNumPoly A * W.veluXCorrNumPoly B
          * (∏ E ∈ (S.erase A).erase B, ((X : F[X]) - C E.1)) ^ 2).natDegree
      ≤ (1 + 1) + 2 * (S.card - 2) := by
        refine natDegree_mul_le.trans (add_le_add ?_ ?_)
        · exact natDegree_mul_le.trans
            (add_le_add (W.veluXCorrNumPoly_natDegree_le A) (W.veluXCorrNumPoly_natDegree_le B))
        · rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
          simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem hBA, Finset.card_erase_of_mem hA]
          omega
    _ ≤ 2 * S.card - 2 := by
        have : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨A, hA, B, hB, hAB⟩
        omega

end PairPad

section AlphaCubeCross

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadAlphaCubeClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A,
    (W.veluXCorrSumPadPoly S + W.veluXCorrPadPoly S A) * W.veluXCorrPairPadQuot S A B

theorem veluXCorrSumPadPoly_cube_sub_sum_cube_eq (S : Finset (F × F)) :
    (W.veluXCorrSumPadPoly S) ^ 3 - ∑ A ∈ S, (W.veluXCorrPadPoly S A) ^ 3
      = (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadAlphaCubeClearedPoly S := by
  have hRHS : (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadAlphaCubeClearedPoly S
      = ∑ A ∈ S, ∑ B ∈ S.erase A,
          (W.veluXCorrSumPadPoly S + W.veluXCorrPadPoly S A)
            * (W.veluXCorrPadPoly S A * W.veluXCorrPadPoly S B) := by
    rw [veluDeficitCrossQuadAlphaCubeClearedPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
    rw [W.veluXCorrPadPoly_mul_eq_kernelDenom_sq_mul hA hBS hBA.symm]; ring
  rw [hRHS, veluXCorrSumPadPoly]
  exact cube_sum_sub_sum_cube_eq S _

theorem veluDeficitCrossQuadAlphaCube_mul_prodPow_eq {S : Finset (F × F)} {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadAlphaCube S r * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadAlphaCubeClearedPoly S).eval r := by
  set D : F := ∏ B ∈ S, (r - B.1) with hD_def
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun B hB => sub_ne_zero.mpr (hav B hB)
  have hmul : W.veluDeficitCrossQuadAlphaCube S r * D ^ 6
      = D ^ 2 * (W.veluDeficitCrossQuadAlphaCubeClearedPoly S).eval r := by
    have hαS := W.eval_veluXCorrSumPadPoly hav
    have hLHS : W.veluDeficitCrossQuadAlphaCube S r * D ^ 6
        = (W.veluXCorrSumPadPoly S).eval r ^ 3
          - ∑ A ∈ S, ((W.veluXCorrPadPoly S A).eval r) ^ 3 := by
      unfold veluDeficitCrossQuadAlphaCube
      rw [sub_mul, Finset.sum_mul,
        show (D : F) ^ 6 = (D ^ 2) ^ 3 from by ring, ← mul_pow, hαS]
      congr 1
      exact Finset.sum_congr rfl fun A hA => by
        rw [← mul_pow, W.eval_veluXCorrPadPoly hA hav]
    rw [hLHS]
    have hRHS := congrArg (Polynomial.eval r) (W.veluXCorrSumPadPoly_cube_sub_sum_cube_eq S)
    simpa only [eval_sub, eval_pow, eval_finsetSum, eval_mul, eval_veluKernelDenom,
      ← hD_def] using hRHS
  have h64 : D ^ 2 * (W.veluDeficitCrossQuadAlphaCube S r * D ^ 4)
      = D ^ 2 * (W.veluDeficitCrossQuadAlphaCubeClearedPoly S).eval r := by
    rw [← hmul]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hD) h64

theorem veluDeficitCrossQuadAlphaCubeClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitCrossQuadAlphaCubeClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1)
    (natDegree_le_iff_degree_le.mpr ?_) (by omega)
  refine (degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_)
  refine ((degree_sum_le _ _).trans (Finset.sup_le fun B hB => ?_))
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
  have h1 : (W.veluXCorrSumPadPoly S + W.veluXCorrPadPoly S A).natDegree ≤ 2 * S.card - 1 :=
    (natDegree_add_le _ _).trans
      (max_le (W.veluXCorrSumPadPoly_natDegree_le S) (W.veluXCorrPadPoly_natDegree_le hA))
  have h2 := W.veluXCorrPairPadQuot_natDegree_le hA hBS hBA.symm
  calc ((W.veluXCorrSumPadPoly S + W.veluXCorrPadPoly S A)
          * W.veluXCorrPairPadQuot S A B).natDegree
      ≤ (2 * S.card - 1) + (2 * S.card - 2) := natDegree_mul_le.trans (add_le_add h1 h2)
    _ ≤ 4 * S.card - 1 := by omega

end AlphaCubeCross

section ReductionBetaOnly

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitCrossQuadBetaOnlyDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadBetaOnly
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r

end ReductionBetaOnly

namespace Affine

universe u

variable {F : Type u} [Field F] {W : Affine F}

theorem polyToFunctionField_X_ne_algebraMap (c : F) :
    polyToFunctionField W X ≠ algebraMap F W.FunctionField c := by
  intro hcon
  refine polyToFunctionField_ne_zero (W := W) (X_sub_C_ne_zero c) ?_
  rw [map_sub, polyToFunctionField_C, hcon, sub_self]

section TranslationCoords

variable (W : Affine F) (a b : F)

local notation "ι" => algebraMap F W.FunctionField

def addXFun : W.FunctionField :=
  (W.map ι).addX (polyToFunctionField W X) (ι a)
    ((W.map ι).slope (polyToFunctionField W X) (ι a) (yGen W) (ι b))

def addYFun : W.FunctionField :=
  (W.map ι).addY (polyToFunctionField W X) (ι a) (yGen W)
    ((W.map ι).slope (polyToFunctionField W X) (ι a) (yGen W) (ι b))

variable {a b} in
theorem equation_map_addFun (hA : W.Equation a b) :
    (W.map ι).Equation (W.addXFun a b) (W.addYFun a b) :=
  Affine.equation_add (W := (W.map ι).toAffine)
    equation_map_polyToFunctionField_yGen (hA.map ι)
    (fun h => polyToFunctionField_X_ne_algebraMap a h.1)

variable {a b} in
theorem eval₂_polynomial_addFun (hA : W.Equation a b) :
    W.polynomial.eval₂
      (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom (W.addYFun a b) = 0 := by
  have heq := equation_map_addFun W hA
  rw [equation_iff'] at heq
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X]
  linear_combination heq

end TranslationCoords

section GenericPointGroup

variable {W : Affine F}

local notation "ι" => algebraMap F W.FunctionField

theorem map_functionField_Δ_ne_zero (hΔ : W.Δ ≠ 0) : (W.map ι).Δ ≠ 0 := by
  rw [map_Δ]
  exact fun h => hΔ ((algebraMap F W.FunctionField).injective (by simpa using h))

theorem nonsingular_map_polyToFunctionField_yGen (hΔ : W.Δ ≠ 0) :
    (W.map ι).Nonsingular (polyToFunctionField W X) (yGen W) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (map_functionField_Δ_ne_zero hΔ)).mp
    equation_map_polyToFunctionField_yGen

def genericPoint (hΔ : W.Δ ≠ 0) : (W.map ι).toAffine.Point :=
  Affine.Point.some (polyToFunctionField W X) (yGen W)
    (nonsingular_map_polyToFunctionField_yGen hΔ)

theorem nonsingular_map_algebraMap (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).Nonsingular (ι a) (ι b) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (map_functionField_Δ_ne_zero hΔ)).mp (hA.map ι)

def mapPoint (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) : (W.map ι).toAffine.Point :=
  Affine.Point.some (ι a) (ι b) (nonsingular_map_algebraMap hΔ hA)

theorem nonsingular_map_addFun (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).Nonsingular (W.addXFun a b) (W.addYFun a b) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (map_functionField_Δ_ne_zero hΔ)).mp
    (equation_map_addFun W hA)

theorem genericPoint_add_map (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    genericPoint hΔ + mapPoint hΔ hA
      = Affine.Point.some (W.addXFun a b) (W.addYFun a b) (nonsingular_map_addFun hΔ hA) :=
  Affine.Point.add_of_X_ne (polyToFunctionField_X_ne_algebraMap a)

theorem equation_neg_mapPoint {a b : F} (hA : W.Equation a b) : W.Equation a (W.negY a b) :=
  (Affine.equation_neg a b).mpr hA

theorem addFun_ne_mapPoint (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    ¬ (W.addXFun a b = ι a ∧ W.addYFun a b = ι b) := by
  intro ⟨hX, hY⟩
  have heq : Affine.Point.some _ _ (nonsingular_map_addFun hΔ hA) = mapPoint hΔ hA := by
    show Affine.Point.some _ _ _ = Affine.Point.some _ _ _
    simp only [Affine.Point.some.injEq]; exact ⟨hX, hY⟩
  have h0 : genericPoint hΔ + mapPoint hΔ hA = 0 + mapPoint hΔ hA := by
    rw [zero_add]; exact (genericPoint_add_map hΔ hA).trans heq
  exact Affine.Point.some_ne_zero _ (add_right_cancel h0)

theorem neg_mapPoint_eq (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    -(mapPoint hΔ hA) = Affine.Point.some (ι a) (ι (W.negY a b))
      (nonsingular_map_algebraMap hΔ (equation_neg_mapPoint hA)) := by
  show Affine.Point.some (ι a) ((W.map ι).negY (ι a) (ι b)) _ = _
  congr 1
  exact map_negY ι a b

theorem addFun_neg_mapPoint_hxy (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    ¬ (W.addXFun a b = ι a
        ∧ W.addYFun a b = (W.map ι).negY (ι a) (ι (W.negY a b))) := by
  rw [map_negY ι a (W.negY a b), Affine.negY_negY]
  exact addFun_ne_mapPoint hΔ hA

theorem addFun_neg_cancel (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).addX (W.addXFun a b) (ι a)
        ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b)))
      = polyToFunctionField W X
    ∧ (W.map ι).addY (W.addXFun a b) (ι a) (W.addYFun a b)
        ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b)))
      = yGen W := by
  have hns₂ := Affine.nonsingular_add (nonsingular_map_addFun hΔ hA)
      (nonsingular_map_algebraMap hΔ (equation_neg_mapPoint hA))
      (addFun_neg_mapPoint_hxy hΔ hA)
  have hsum : (Affine.Point.some _ _ (nonsingular_map_addFun hΔ hA))
        + (-(mapPoint hΔ hA))
      = Affine.Point.some _ _ hns₂ := by
    rw [neg_mapPoint_eq hΔ hA]
    exact Affine.Point.add_some (addFun_neg_mapPoint_hxy hΔ hA)
  have hcancel : Affine.Point.some _ _ hns₂ = genericPoint hΔ := by
    rw [← hsum, ← genericPoint_add_map hΔ hA, add_neg_cancel_right]
  exact Affine.Point.some.inj hcancel

theorem addFun_neg_cancel_X (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).addX (W.addXFun a b) (ι a)
        ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b)))
      = polyToFunctionField W X :=
  (addFun_neg_cancel hΔ hA).1

theorem addFun_neg_cancel_Y (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).addY (W.addXFun a b) (ι a) (W.addYFun a b)
        ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b)))
      = yGen W :=
  (addFun_neg_cancel hΔ hA).2

end GenericPointGroup

section CoordHom

variable {W : Affine F} {a b : F} (hA : W.Equation a b)

def translationCoordHom : W.CoordinateRing →ₐ[F] W.FunctionField where
  __ := AdjoinRoot.lift
    (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom
    (W.addYFun a b) (eval₂_polynomial_addFun W hA)
  commutes' c := by
    show AdjoinRoot.lift _ _ (eval₂_polynomial_addFun W hA) (algebraMap F _ c)
      = algebraMap F W.FunctionField c
    rw [CoordinateRing.algebraMap_eq_mk_C_C, AdjoinRoot.lift_mk, eval₂_C]
    exact Polynomial.aeval_C _ c

theorem translationCoordHom_mk (g : F[X][Y]) :
    translationCoordHom hA (CoordinateRing.mk W g)
      = g.eval₂ (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom (W.addYFun a b) :=
  AdjoinRoot.lift_mk (eval₂_polynomial_addFun W hA) g

theorem translationCoordHom_comp_algebraMap :
    (translationCoordHom hA).toRingHom.comp (algebraMap F[X] W.CoordinateRing)
      = (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom := by
  refine RingHom.ext fun p => ?_
  show translationCoordHom hA (algebraMap F[X] _ p) = _
  rw [algebraMap_polynomial_eq_mk_C, translationCoordHom_mk, eval₂_C]

@[scoped simp] theorem translationCoordHom_XClass :
    translationCoordHom hA (algebraMap F[X] W.CoordinateRing X) = W.addXFun a b := by
  rw [algebraMap_polynomial_eq_mk_C, translationCoordHom_mk, eval₂_C]
  exact Polynomial.aeval_X _

@[scoped simp] theorem translationCoordHom_YClass :
    translationCoordHom hA (CoordinateRing.mk W Y) = W.addYFun a b := by
  rw [translationCoordHom_mk]
  exact eval₂_X _ _

end CoordHom

section AdjoinSurjective

variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

theorem slope_mem_intermediateField {K : IntermediateField F W.FunctionField}
    {x₁ x₂ y₁ y₂ : W.FunctionField}
    (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K) (hy₁ : y₁ ∈ K) (hy₂ : y₂ ∈ K) :
    (W.map ι).slope x₁ x₂ y₁ y₂ ∈ K := by
  have hF : ∀ c : F, ι c ∈ K := fun c => (algebraMap F K c).2
  have hN : ∀ n : ℕ, (n : W.FunctionField) ∈ K := fun n => natCast_mem K n
  unfold Affine.slope
  split
  · split
    · exact zero_mem K
    · simp only [map_a₁, map_a₂, map_a₄]
      refine div_mem (sub_mem (add_mem (add_mem (mul_mem (hN 3) (pow_mem hx₁ 2))
        (mul_mem (mul_mem (hN 2) (hF _)) hx₁)) (hF _)) (mul_mem (hF _) hy₁)) (sub_mem hy₁ ?_)
      unfold Affine.negY
      simp only [map_a₁, map_a₃]
      exact sub_mem (sub_mem (neg_mem hy₁) (mul_mem (hF _) hx₁)) (hF _)
  · exact div_mem (sub_mem hy₁ hy₂) (sub_mem hx₁ hx₂)

include hΔ hA in
theorem polyToFunctionField_X_mem_adjoin_addFun :
    polyToFunctionField W X
      ∈ IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) := by
  set K := IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)
  rw [← addFun_neg_cancel_X hΔ hA]
  have hX' : W.addXFun a b ∈ K := IntermediateField.subset_adjoin F _ (Or.inl rfl)
  have hY' : W.addYFun a b ∈ K := IntermediateField.subset_adjoin F _ (Or.inr rfl)
  have hF : ∀ c : F, ι c ∈ K := fun c => (algebraMap F K c).2
  have hslope := slope_mem_intermediateField (W := W) hX' (hF a) hY' (hF (W.negY a b))
  show (W.map ι).addX (W.addXFun a b) (ι a) _ ∈ K
  rw [Affine.addX]
  simp only [map_a₁, map_a₂]
  exact sub_mem (sub_mem (sub_mem (add_mem (pow_mem hslope 2) (mul_mem (hF _) hslope))
    (hF _)) hX') (hF _)

include hΔ hA in
theorem yGen_mem_adjoin_addFun :
    yGen W
      ∈ IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) := by
  set K := IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)
  rw [← addFun_neg_cancel_Y hΔ hA]
  have hX' : W.addXFun a b ∈ K := IntermediateField.subset_adjoin F _ (Or.inl rfl)
  have hY' : W.addYFun a b ∈ K := IntermediateField.subset_adjoin F _ (Or.inr rfl)
  have hF : ∀ c : F, ι c ∈ K := fun c => (algebraMap F K c).2
  have hslope := slope_mem_intermediateField (W := W) hX' (hF a) hY' (hF (W.negY a b))
  have haddX : (W.map ι).addX (W.addXFun a b) (ι a)
      ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b))) ∈ K := by
    rw [Affine.addX]
    simp only [map_a₁, map_a₂]
    exact sub_mem (sub_mem (sub_mem (add_mem (pow_mem hslope 2) (mul_mem (hF _) hslope))
      (hF _)) hX') (hF _)
  show (W.map ι).addY (W.addXFun a b) (ι a) (W.addYFun a b) _ ∈ K
  rw [Affine.addY, Affine.negY, Affine.negAddY]
  simp only [map_a₁, map_a₃]
  exact sub_mem (sub_mem (neg_mem (add_mem (mul_mem hslope (sub_mem haddX hX')) hY'))
    (mul_mem (hF _) haddX)) (hF _)

include hΔ hA in
theorem adjoin_addFun_eq_top :
    IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  set K := IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)
  have hX : polyToFunctionField W X ∈ K := polyToFunctionField_X_mem_adjoin_addFun hΔ hA
  have hY : yGen W ∈ K := yGen_mem_adjoin_addFun hΔ hA
  have hpoly : ∀ p : F[X], polyToFunctionField W p ∈ K := by
    intro p
    induction p using Polynomial.induction_on' with
    | add g h hg hh => rw [map_add]; exact add_mem hg hh
    | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, polyToFunctionField_C]
        exact mul_mem (algebraMap F K c).2 (pow_mem hX n)
  have hcr : ∀ r : W.CoordinateRing,
      algebraMap W.CoordinateRing W.FunctionField r ∈ K := by
    intro r
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq (W' := W) r
    rw [algebraMap_smul_basis]
    exact add_mem (hpoly p) (mul_mem (hpoly q) hY)
  rw [← hrs]
  exact div_mem (hcr r) (hcr s)

end AdjoinSurjective

section TranslationHom

variable {W : Affine F} {a b : F} (hA : W.Equation a b)

def AddXFunTranscendental (W : Affine F) (a b : F) : Prop :=
  Transcendental F (W.addXFun a b)

variable (htr : AddXFunTranscendental W a b)

include htr in
theorem translationCoordHom_injective : Function.Injective (translationCoordHom hA) := by
  have hker : RingHom.ker (translationCoordHom hA).toRingHom = ⊥ := by
    haveI : Module.Finite F[X] W.CoordinateRing :=
      Module.Finite.of_basis (CoordinateRing.basis W)
    refine Ideal.eq_bot_of_under_eq_bot (R := F[X]) ?_
    rw [Ideal.under_def, RingHom.comap_ker, translationCoordHom_comp_algebraMap,
      ← RingHom.injective_iff_ker_eq_bot]
    exact (injective_iff_map_eq_zero _).mpr fun p hp => transcendental_iff.mp htr p hp
  exact (RingHom.injective_iff_ker_eq_bot (translationCoordHom hA).toRingHom).mpr hker

def translationHom : W.FunctionField →ₐ[F] W.FunctionField :=
  IsFractionRing.liftAlgHom (translationCoordHom_injective hA htr)

theorem translationHom_algebraMap (r : W.CoordinateRing) :
    translationHom hA htr (algebraMap W.CoordinateRing W.FunctionField r)
      = translationCoordHom hA r :=
  IsFractionRing.lift_algebraMap (translationCoordHom_injective hA htr) r

@[scoped simp] theorem translationHom_polyToFunctionField_X :
    translationHom hA htr (polyToFunctionField W X) = W.addXFun a b := by
  rw [polyToFunctionField_apply, translationHom_algebraMap, ← translationCoordHom_XClass hA]

@[scoped simp] theorem translationHom_yGen :
    translationHom hA htr (yGen W) = W.addYFun a b := by
  show translationHom hA htr (algebraMap _ _ (CoordinateRing.mk W Y)) = _
  rw [translationHom_algebraMap, translationCoordHom_YClass]

variable (hΔ : W.Δ ≠ 0)

include hΔ in
theorem translationHom_surjective : Function.Surjective (translationHom hA htr) := by
  intro z
  have hz : z ∈ IntermediateField.adjoin F
      ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) := by
    rw [adjoin_addFun_eq_top hΔ hA]; trivial
  have hle : IntermediateField.adjoin F
      ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)
      ≤ (translationHom hA htr).fieldRange := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ (rfl | rfl)
    · exact ⟨polyToFunctionField W X, translationHom_polyToFunctionField_X hA htr⟩
    · exact ⟨yGen W, translationHom_yGen hA htr⟩
  exact hle hz

def translationAlgEquiv : W.FunctionField ≃ₐ[F] W.FunctionField :=
  AlgEquiv.ofBijective (translationHom hA htr)
    ⟨(translationHom hA htr).injective, translationHom_surjective hA htr hΔ⟩

end TranslationHom

end Affine

section BetaSCoeffPoly

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluYCorrSCoeffNumPoly (A : F × F) : F[X] :=
  -(C (2 * W.veluU A.1 A.2) + C (W.veluT A.1 A.2) * (X - C A.1))

lemma veluYCorrSCoeffNumPoly_natDegree_le (A : F × F) :
    (W.veluYCorrSCoeffNumPoly A).natDegree ≤ 1 := by
  unfold veluYCorrSCoeffNumPoly; compute_degree

def veluYCorrSCoeffPadPoly (S : Finset (F × F)) (A : F × F) : F[X] :=
  W.veluYCorrSCoeffNumPoly A * (∏ B ∈ S.erase A, (X - C B.1)) ^ 3

theorem eval_veluYCorrSCoeffPadPoly {S : Finset (F × F)} {A : F × F} (hA : A ∈ S) {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3 + W.veluT A.1 A.2 / (r - A.1) ^ 2)
        * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrSCoeffPadPoly S A).eval r := by
  have hd : r - A.1 ≠ 0 := sub_ne_zero.mpr (hav A hA)
  have hsplit : (∏ B ∈ S, (r - B.1)) ^ 3
      = (r - A.1) ^ 3 * (∏ B ∈ S.erase A, (r - B.1)) ^ 3 := by
    rw [← mul_pow, ← Finset.prod_erase_mul S _ hA, mul_comm]
  rw [hsplit, veluYCorrSCoeffPadPoly, veluYCorrSCoeffNumPoly]
  simp only [eval_mul, eval_neg, eval_add, eval_C, eval_sub, eval_X, eval_pow, eval_prod]
  field_simp

def veluYCorrSCoeffSumPadPoly (S : Finset (F × F)) : F[X] := ∑ A ∈ S, W.veluYCorrSCoeffPadPoly S A

lemma veluY_sub_self_sLinear (S : Finset (F × F)) (r s : F) :
    (W.veluY S r s - s) - (W.veluY S r 0 - 0)
      = (∑ A ∈ S, -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3
          + W.veluT A.1 A.2 / (r - A.1) ^ 2)) * s := by
  simp only [veluY, sub_zero, sub_sub_cancel_left, zero_sub, sub_neg_eq_add, neg_add_eq_sub,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun A _ => by ring

theorem veluY_singleton_sub_sLinear (A : F × F) (r s : F) :
    (W.veluY {A} r s - s) - (W.veluY {A} r 0 - 0)
      = -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3 + W.veluT A.1 A.2 / (r - A.1) ^ 2) * s := by
  have key := W.veluY_sub_self_sLinear {A} r s
  simpa using key

theorem veluY_sub_self_sCoeff_mul_prodPow_eq {S : Finset (F × F)} {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    (∑ A ∈ S, -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3
          + W.veluT A.1 A.2 / (r - A.1) ^ 2)) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrSCoeffSumPadPoly S).eval r := by
  rw [veluYCorrSCoeffSumPadPoly, eval_finsetSum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun A hA => W.eval_veluYCorrSCoeffPadPoly hA hav

end BetaSCoeffPoly

section BetaConstPoly

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

lemma veluY_sub_self_eq_sum_singleton (S : Finset (F × F)) (r s : F) :
    W.veluY S r s - s = ∑ A ∈ S, (W.veluY {A} r s - s) := by
  simp only [veluY, Finset.sum_singleton, sub_sub_cancel_left, ← Finset.sum_neg_distrib]

def veluYCorrConstNumPoly (A : F × F) : F[X] :=
  -(C (W.veluU A.1 A.2) * (C W.a₁ * X + C W.a₃))
    - (C (W.veluT A.1 A.2) * (C W.a₁ * (X - C A.1) - C A.2)
        + C (W.a₁ * W.veluU A.1 A.2 - W.veluGx A.1 A.2 * W.veluGy A.1 A.2)) * (X - C A.1)

lemma veluYCorrConstNumPoly_natDegree_le (A : F × F) :
    (W.veluYCorrConstNumPoly A).natDegree ≤ 2 := by
  unfold veluYCorrConstNumPoly; compute_degree

def veluYCorrConstPadPoly (S : Finset (F × F)) (A : F × F) : F[X] :=
  W.veluYCorrConstNumPoly A * (∏ B ∈ S.erase A, (X - C B.1)) ^ 3

theorem eval_veluYCorrConstPadPoly {S : Finset (F × F)} {A : F × F} (hA : A ∈ S) {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluY {A} r 0 - 0) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrConstPadPoly S A).eval r := by
  have hd : r - A.1 ≠ 0 := sub_ne_zero.mpr (hav A hA)
  have hsplit : (∏ B ∈ S, (r - B.1)) ^ 3
      = (r - A.1) ^ 3 * (∏ B ∈ S.erase A, (r - B.1)) ^ 3 := by
    rw [← mul_pow, ← Finset.prod_erase_mul S _ hA, mul_comm]
  rw [hsplit, veluYCorrConstPadPoly, veluYCorrConstNumPoly]
  simp only [veluY, Finset.sum_singleton, eval_mul, eval_neg, eval_add, eval_C, eval_sub, eval_X,
    eval_pow, eval_prod]
  field_simp
  ring

def veluYCorrConstSumPadPoly (S : Finset (F × F)) : F[X] := ∑ A ∈ S, W.veluYCorrConstPadPoly S A

theorem eval_veluYCorrConstSumPadPoly {S : Finset (F × F)} {r : F} (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluY S r 0 - 0) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrConstSumPadPoly S).eval r := by
  rw [veluYCorrConstSumPadPoly, eval_finsetSum, W.veluY_sub_self_eq_sum_singleton, Finset.sum_mul]
  exact Finset.sum_congr rfl fun A hA => W.eval_veluYCorrConstPadPoly hA hav

end BetaConstPoly

section BetaSDecomp

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem veluY_sub_self_mul_prodCube_sDecomp {S : Finset (F × F)} {r : F} (s : F)
    (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluY S r s - s) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrConstSumPadPoly S).eval r + (W.veluYCorrSCoeffSumPadPoly S).eval r * s := by
  have hlin := W.veluY_sub_self_sLinear S r s
  have hconst := W.eval_veluYCorrConstSumPadPoly (S := S) hav
  have hcoeff := W.veluY_sub_self_sCoeff_mul_prodPow_eq (S := S) hav
  have key : (W.veluY S r s - s)
      = (W.veluY S r 0 - 0) + (∑ A ∈ S, -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3
          + W.veluT A.1 A.2 / (r - A.1) ^ 2)) * s := by
    linear_combination hlin
  rw [key, add_mul, hconst, mul_right_comm, hcoeff]

theorem veluY_singleton_sub_self_mul_prodCube_sDecomp {S : Finset (F × F)} {A : F × F}
    (hA : A ∈ S) {r : F} (s : F) (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluY {A} r s - s) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrConstPadPoly S A).eval r + (W.veluYCorrSCoeffPadPoly S A).eval r * s := by
  have hlin := W.veluY_singleton_sub_sLinear A r s
  have hconst := W.eval_veluYCorrConstPadPoly hA hav
  have hcoeff := W.eval_veluYCorrSCoeffPadPoly hA (r := r) hav
  have key : (W.veluY {A} r s - s)
      = (W.veluY {A} r 0 - 0) + (-(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3
          + W.veluT A.1 A.2 / (r - A.1) ^ 2)) * s := by
    linear_combination hlin
  rw [key, add_mul, hconst, mul_right_comm, hcoeff]

end BetaSDecomp

section TwoCrossTypes

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadBetaSq (S : Finset (F × F)) (r s : F) : F :=
  (W.veluY S r s - s) ^ 2 - ∑ A ∈ S, (W.veluY {A} r s - s) ^ 2

def veluDeficitCrossQuadAlphaBeta (S : Finset (F × F)) (r s : F) : F :=
  (W.veluX S r - r) * (W.veluY S r s - s)
    - ∑ A ∈ S, (W.veluX {A} r - r) * (W.veluY {A} r s - s)

theorem veluDeficitCrossQuadBetaOnly_eq_betaSq_add_alphaBeta [DecidableEq F]
    (S : Finset (F × F)) (r s : F) :
    W.veluDeficitCrossQuadBetaOnly S r s
      = W.veluDeficitCrossQuadBetaSq S r s + W.a₁ * W.veluDeficitCrossQuadAlphaBeta S r s := by
  rw [W.veluDeficitCrossQuadBetaOnly_eq, veluDeficitCrossQuadBetaSq,
    veluDeficitCrossQuadAlphaBeta]
  have hper : ∀ A ∈ S, ((W.veluY {A} r s - s) ^ 2
        + W.a₁ * (W.veluX {A} r - r) * (W.veluY {A} r s - s))
      = (W.veluY {A} r s - s) ^ 2
        + W.a₁ * ((W.veluX {A} r - r) * (W.veluY {A} r s - s)) := fun A _ => by ring
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end TwoCrossTypes

section ReductionTwoDecomp

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitCrossQuadBetaSDecompDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M N : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadBetaOnly
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r + N.eval r * s

def VeluDeficitCrossQuadBetaSqDecompDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M N : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadBetaSq
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r + N.eval r * s

def VeluDeficitCrossQuadAlphaBetaDecompDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M N : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadAlphaBeta
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r + N.eval r * s

variable {F}

theorem veluDeficitCrossQuadBetaSDecompDegLtAt_of_betaSq_of_alphaBeta
    {p : ℕ} (hBSq : VeluDeficitCrossQuadBetaSqDecompDegLtAt F p)
    (hαβ : VeluDeficitCrossQuadAlphaBetaDecompDegLtAt F p) :
    VeluDeficitCrossQuadBetaSDecompDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  obtain ⟨M₁, N₁, hM₁deg, hMN₁⟩ := hBSq W hΔ x₀ y₀ h₀ hord
  obtain ⟨M₂, N₂, hM₂deg, hMN₂⟩ := hαβ W hΔ x₀ y₀ h₀ hord
  refine ⟨M₁ + C W.a₁ * M₂, N₁ + C W.a₁ * N₂, ?_, ?_⟩
  ·
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hM₁deg ?_)
    exact lt_of_le_of_lt (natDegree_mul_le.trans (by simp)) hM₂deg
  · intro r s hrs hav
    rw [W.veluDeficitCrossQuadBetaOnly_eq_betaSq_add_alphaBeta, add_mul, mul_assoc,
      hMN₁ hrs hav, hMN₂ hrs hav]
    simp only [eval_add, eval_mul, eval_C]; ring

end ReductionTwoDecomp

section MixedPairPad

lemma prod_sum_sub_sum_diag_eq {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (f g : α → R) :
    (∑ A ∈ s, f A) * (∑ B ∈ s, g B) - ∑ A ∈ s, f A * g A
      = ∑ A ∈ s, ∑ B ∈ s.erase A, f A * g B := by
  have key : ∀ A ∈ s, f A * (∑ B ∈ s, g B)
      = f A * g A + ∑ B ∈ s.erase A, f A * g B := by
    intro A hA
    rw [← Finset.mul_sum, ← Finset.add_sum_erase s g hA, mul_add]
  rw [Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_add_distrib, add_sub_cancel_left]

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluXYCorrConstPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluXCorrNumPoly A * W.veluYCorrConstNumPoly B * (X - C A.1) ^ 2 * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

def veluXYCorrSCoeffPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluXCorrNumPoly A * W.veluYCorrSCoeffNumPoly B * (X - C A.1) ^ 2 * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

theorem veluXCorrPadPoly_mul_veluYCorrConstPadPoly_eq_kernelDenom_mul {S : Finset (F × F)}
    {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluXCorrPadPoly S A * W.veluYCorrConstPadPoly S B
      = veluKernelDenom S * W.veluXYCorrConstPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluXCorrPadPoly veluYCorrConstPadPoly veluXYCorrConstPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

theorem veluXCorrPadPoly_mul_veluYCorrSCoeffPadPoly_eq_kernelDenom_mul {S : Finset (F × F)}
    {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluXCorrPadPoly S A * W.veluYCorrSCoeffPadPoly S B
      = veluKernelDenom S * W.veluXYCorrSCoeffPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluXCorrPadPoly veluYCorrSCoeffPadPoly veluXYCorrSCoeffPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

end MixedPairPad

section AlphaBetaCleared

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadAlphaBetaConstClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluXYCorrConstPairPadQuot S A B

def veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluXYCorrSCoeffPairPadQuot S A B

theorem veluXCorrSumPadPoly_mul_veluYCorrConstSumPadPoly_sub_sum_eq (S : Finset (F × F)) :
    W.veluXCorrSumPadPoly S * W.veluYCorrConstSumPadPoly S
        - ∑ A ∈ S, W.veluXCorrPadPoly S A * W.veluYCorrConstPadPoly S A
      = veluKernelDenom S * W.veluDeficitCrossQuadAlphaBetaConstClearedPoly S := by
  rw [veluXCorrSumPadPoly, veluYCorrConstSumPadPoly,
    prod_sum_sub_sum_diag_eq S _ _, veluDeficitCrossQuadAlphaBetaConstClearedPoly,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluXCorrPadPoly_mul_veluYCorrConstPadPoly_eq_kernelDenom_mul hA hBS hBA.symm

theorem veluXCorrSumPadPoly_mul_veluYCorrSCoeffSumPadPoly_sub_sum_eq (S : Finset (F × F)) :
    W.veluXCorrSumPadPoly S * W.veluYCorrSCoeffSumPadPoly S
        - ∑ A ∈ S, W.veluXCorrPadPoly S A * W.veluYCorrSCoeffPadPoly S A
      = veluKernelDenom S * W.veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly S := by
  rw [veluXCorrSumPadPoly, veluYCorrSCoeffSumPadPoly,
    prod_sum_sub_sum_diag_eq S _ _, veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluXCorrPadPoly_mul_veluYCorrSCoeffPadPoly_eq_kernelDenom_mul hA hBS hBA.symm

theorem veluDeficitCrossQuadAlphaBeta_mul_prodPow_sDecomp {S : Finset (F × F)} {r : F} (s : F)
    (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadAlphaBeta S r s * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadAlphaBetaConstClearedPoly S).eval r
        + (W.veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly S).eval r * s := by
  set D : F := ∏ B ∈ S, (r - B.1) with hD_def
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun B hB => sub_ne_zero.mpr (hav B hB)
  have hαS : (W.veluX S r - r) * D ^ 2 = (W.veluXCorrSumPadPoly S).eval r :=
    hD_def ▸ W.eval_veluXCorrSumPadPoly hav
  have hβS : (W.veluY S r s - s) * D ^ 3
      = (W.veluYCorrConstSumPadPoly S).eval r + (W.veluYCorrSCoeffSumPadPoly S).eval r * s :=
    hD_def ▸ W.veluY_sub_self_mul_prodCube_sDecomp s hav
  have hαA : ∀ A ∈ S, (W.veluX {A} r - r) * D ^ 2 = (W.veluXCorrPadPoly S A).eval r :=
    fun A hA => hD_def ▸ W.eval_veluXCorrPadPoly hA hav
  have hβA : ∀ A ∈ S, (W.veluY {A} r s - s) * D ^ 3
      = (W.veluYCorrConstPadPoly S A).eval r + (W.veluYCorrSCoeffPadPoly S A).eval r * s :=
    fun A hA => hD_def ▸ W.veluY_singleton_sub_self_mul_prodCube_sDecomp hA s hav
  refine mul_left_cancel₀ hD ?_
  have hLHS : D * (W.veluDeficitCrossQuadAlphaBeta S r s * D ^ 4)
      = ((W.veluXCorrSumPadPoly S).eval r * (W.veluYCorrConstSumPadPoly S).eval r
            - ∑ A ∈ S, (W.veluXCorrPadPoly S A).eval r * (W.veluYCorrConstPadPoly S A).eval r)
        + ((W.veluXCorrSumPadPoly S).eval r * (W.veluYCorrSCoeffSumPadPoly S).eval r
            - ∑ A ∈ S, (W.veluXCorrPadPoly S A).eval r
                * (W.veluYCorrSCoeffPadPoly S A).eval r) * s := by
    have htop : ((W.veluX S r - r) * (W.veluY S r s - s)) * (D ^ 2 * D ^ 3)
        = (W.veluXCorrSumPadPoly S).eval r * (W.veluYCorrConstSumPadPoly S).eval r
          + ((W.veluXCorrSumPadPoly S).eval r * (W.veluYCorrSCoeffSumPadPoly S).eval r) * s := by
      rw [show (W.veluX S r - r) * (W.veluY S r s - s) * (D ^ 2 * D ^ 3)
          = ((W.veluX S r - r) * D ^ 2) * ((W.veluY S r s - s) * D ^ 3) from by ring,
        hαS, hβS]; ring
    have hsum : (∑ A ∈ S, (W.veluX {A} r - r) * (W.veluY {A} r s - s)) * (D ^ 2 * D ^ 3)
        = (∑ A ∈ S, (W.veluXCorrPadPoly S A).eval r * (W.veluYCorrConstPadPoly S A).eval r)
          + (∑ A ∈ S, (W.veluXCorrPadPoly S A).eval r
              * (W.veluYCorrSCoeffPadPoly S A).eval r) * s := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun A hA => ?_
      rw [show (W.veluX {A} r - r) * (W.veluY {A} r s - s) * (D ^ 2 * D ^ 3)
          = ((W.veluX {A} r - r) * D ^ 2) * ((W.veluY {A} r s - s) * D ^ 3) from by ring,
        hαA A hA, hβA A hA]; ring
    unfold veluDeficitCrossQuadAlphaBeta
    rw [show D * (((W.veluX S r - r) * (W.veluY S r s - s)
            - ∑ A ∈ S, (W.veluX {A} r - r) * (W.veluY {A} r s - s)) * D ^ 4)
        = ((W.veluX S r - r) * (W.veluY S r s - s)) * (D ^ 2 * D ^ 3)
          - (∑ A ∈ S, (W.veluX {A} r - r) * (W.veluY {A} r s - s)) * (D ^ 2 * D ^ 3) from by ring,
      htop, hsum]; ring
  rw [hLHS]
  have hM := congrArg (Polynomial.eval r)
    (W.veluXCorrSumPadPoly_mul_veluYCorrConstSumPadPoly_sub_sum_eq S)
  have hN := congrArg (Polynomial.eval r)
    (W.veluXCorrSumPadPoly_mul_veluYCorrSCoeffSumPadPoly_sub_sum_eq S)
  simp only [eval_sub, eval_mul, eval_finsetSum, eval_veluKernelDenom, ← hD_def] at hM hN
  rw [hM, hN]; ring

theorem veluXYCorrConstPairPadQuot_natDegree_le {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (W.veluXYCorrConstPairPadQuot S A B).natDegree ≤ 4 * S.card - 2 := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hScard : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨A, hA, B, hB, hAB⟩
  unfold veluXYCorrConstPairPadQuot
  calc (W.veluXCorrNumPoly A * W.veluYCorrConstNumPoly B * (X - C A.1) ^ 2 * (X - C B.1)
          * (∏ E ∈ (S.erase A).erase B, ((X : F[X]) - C E.1)) ^ 4).natDegree
      ≤ ((1 + 2) + 2 + 1) + 4 * (S.card - 2) := by
        refine natDegree_mul_le.trans (add_le_add ?_ ?_)
        · refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          refine natDegree_mul_le.trans (add_le_add ?_ ?_)
          · exact natDegree_mul_le.trans (add_le_add (W.veluXCorrNumPoly_natDegree_le A)
              (W.veluYCorrConstNumPoly_natDegree_le B))
          · simp [natDegree_pow]
        · rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
          simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem hBA, Finset.card_erase_of_mem hA]
          omega
    _ ≤ 4 * S.card - 2 := by omega

theorem veluDeficitCrossQuadAlphaBetaConstClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitCrossQuadAlphaBetaConstClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1)
    (natDegree_le_iff_degree_le.mpr ?_) (by omega)
  refine (degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_)
  refine ((degree_sum_le _ _).trans (Finset.sup_le fun B hB => ?_))
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
  exact (W.veluXYCorrConstPairPadQuot_natDegree_le hA hBS hBA.symm).trans (by omega)

end AlphaBetaCleared

section BetaSqPairPad

lemma sq_sum_sub_sum_sq_eq {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → R) :
    (∑ A ∈ s, f A) ^ 2 - ∑ A ∈ s, f A ^ 2
      = ∑ A ∈ s, ∑ B ∈ s.erase A, f A * f B := by
  have key : ∀ A ∈ s, f A * (∑ B ∈ s, f B)
      = f A ^ 2 + ∑ B ∈ s.erase A, f A * f B := by
    intro A hA
    rw [← Finset.mul_sum, ← Finset.add_sum_erase s f hA, mul_add, sq]
  rw [sq, Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_add_distrib, add_sub_cancel_left]

lemma prod_sum_sub_sum_diag_eq' {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (f g : α → R) :
    (∑ A ∈ s, f A) * (∑ B ∈ s, g B) - ∑ A ∈ s, f A * g A
      = ∑ A ∈ s, ∑ B ∈ s.erase A, f A * g B := by
  have key : ∀ A ∈ s, f A * (∑ B ∈ s, g B)
      = f A * g A + ∑ B ∈ s.erase A, f A * g B := by
    intro A hA
    rw [← Finset.mul_sum, ← Finset.add_sum_erase s g hA, mul_add]
  rw [Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_add_distrib, add_sub_cancel_left]

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluYYCorrConstPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluYCorrConstNumPoly A * W.veluYCorrConstNumPoly B * (X - C A.1) * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

def veluYYCorrCrossPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluYCorrConstNumPoly A * W.veluYCorrSCoeffNumPoly B * (X - C A.1) * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

def veluYYCorrSCoeffPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluYCorrSCoeffNumPoly A * W.veluYCorrSCoeffNumPoly B * (X - C A.1) * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

theorem veluYCorrConstPadPoly_mul_eq_kernelDenom_sq_mul {S : Finset (F × F)}
    {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluYCorrConstPadPoly S A * W.veluYCorrConstPadPoly S B
      = (veluKernelDenom S) ^ 2 * W.veluYYCorrConstPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluYCorrConstPadPoly veluYYCorrConstPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

theorem veluYCorrConstPadPoly_mul_veluYCorrSCoeffPadPoly_eq_kernelDenom_sq_mul
    {S : Finset (F × F)} {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluYCorrConstPadPoly S A * W.veluYCorrSCoeffPadPoly S B
      = (veluKernelDenom S) ^ 2 * W.veluYYCorrCrossPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluYCorrConstPadPoly veluYCorrSCoeffPadPoly veluYYCorrCrossPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

theorem veluYCorrSCoeffPadPoly_mul_eq_kernelDenom_sq_mul {S : Finset (F × F)}
    {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluYCorrSCoeffPadPoly S A * W.veluYCorrSCoeffPadPoly S B
      = (veluKernelDenom S) ^ 2 * W.veluYYCorrSCoeffPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluYCorrSCoeffPadPoly veluYYCorrSCoeffPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

end BetaSqPairPad

section BetaSqCleared

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadBetaSqConstClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluYYCorrConstPairPadQuot S A B

def veluDeficitCrossQuadBetaSqCrossClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluYYCorrCrossPairPadQuot S A B

def veluDeficitCrossQuadBetaSqSqClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluYYCorrSCoeffPairPadQuot S A B

theorem veluYCorrConstSumPadPoly_sq_sub_sum_sq_eq (S : Finset (F × F)) :
    (W.veluYCorrConstSumPadPoly S) ^ 2 - ∑ A ∈ S, (W.veluYCorrConstPadPoly S A) ^ 2
      = (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadBetaSqConstClearedPoly S := by
  rw [veluYCorrConstSumPadPoly, veluDeficitCrossQuadBetaSqConstClearedPoly,
    sq_sum_sub_sum_sq_eq S _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluYCorrConstPadPoly_mul_eq_kernelDenom_sq_mul hA hBS hBA.symm

theorem veluYCorrConstSumPadPoly_mul_SCoeffSumPadPoly_sub_sum_eq (S : Finset (F × F)) :
    W.veluYCorrConstSumPadPoly S * W.veluYCorrSCoeffSumPadPoly S
        - ∑ A ∈ S, W.veluYCorrConstPadPoly S A * W.veluYCorrSCoeffPadPoly S A
      = (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadBetaSqCrossClearedPoly S := by
  rw [veluYCorrConstSumPadPoly, veluYCorrSCoeffSumPadPoly,
    veluDeficitCrossQuadBetaSqCrossClearedPoly, prod_sum_sub_sum_diag_eq' S _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluYCorrConstPadPoly_mul_veluYCorrSCoeffPadPoly_eq_kernelDenom_sq_mul hA hBS hBA.symm

theorem veluYCorrSCoeffSumPadPoly_sq_sub_sum_sq_eq (S : Finset (F × F)) :
    (W.veluYCorrSCoeffSumPadPoly S) ^ 2 - ∑ A ∈ S, (W.veluYCorrSCoeffPadPoly S A) ^ 2
      = (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadBetaSqSqClearedPoly S := by
  rw [veluYCorrSCoeffSumPadPoly, veluDeficitCrossQuadBetaSqSqClearedPoly,
    sq_sum_sub_sum_sq_eq S _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluYCorrSCoeffPadPoly_mul_eq_kernelDenom_sq_mul hA hBS hBA.symm

theorem veluDeficitCrossQuadBetaSq_mul_prodPow_sQuadDecomp {S : Finset (F × F)} {r : F} (s : F)
    (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadBetaSq S r s * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadBetaSqConstClearedPoly S).eval r
        + 2 * (W.veluDeficitCrossQuadBetaSqCrossClearedPoly S).eval r * s
        + (W.veluDeficitCrossQuadBetaSqSqClearedPoly S).eval r * s ^ 2 := by
  set D : F := ∏ B ∈ S, (r - B.1) with hD_def
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun B hB => sub_ne_zero.mpr (hav B hB)
  have hβS : (W.veluY S r s - s) * D ^ 3
      = (W.veluYCorrConstSumPadPoly S).eval r + (W.veluYCorrSCoeffSumPadPoly S).eval r * s :=
    hD_def ▸ W.veluY_sub_self_mul_prodCube_sDecomp s hav
  have hβA : ∀ A ∈ S, (W.veluY {A} r s - s) * D ^ 3
      = (W.veluYCorrConstPadPoly S A).eval r + (W.veluYCorrSCoeffPadPoly S A).eval r * s :=
    fun A hA => hD_def ▸ W.veluY_singleton_sub_self_mul_prodCube_sDecomp hA s hav
  refine mul_left_cancel₀ (pow_ne_zero 2 hD) ?_
  have hLHS : D ^ 2 * (W.veluDeficitCrossQuadBetaSq S r s * D ^ 4)
      = ((W.veluYCorrConstSumPadPoly S).eval r ^ 2
            - ∑ A ∈ S, (W.veluYCorrConstPadPoly S A).eval r ^ 2)
        + 2 * ((W.veluYCorrConstSumPadPoly S).eval r * (W.veluYCorrSCoeffSumPadPoly S).eval r
            - ∑ A ∈ S, (W.veluYCorrConstPadPoly S A).eval r
                * (W.veluYCorrSCoeffPadPoly S A).eval r) * s
        + ((W.veluYCorrSCoeffSumPadPoly S).eval r ^ 2
            - ∑ A ∈ S, (W.veluYCorrSCoeffPadPoly S A).eval r ^ 2) * s ^ 2 := by
    have htop : ((W.veluY S r s - s) * D ^ 3) ^ 2
        = (W.veluYCorrConstSumPadPoly S).eval r ^ 2
          + 2 * ((W.veluYCorrConstSumPadPoly S).eval r
              * (W.veluYCorrSCoeffSumPadPoly S).eval r) * s
          + (W.veluYCorrSCoeffSumPadPoly S).eval r ^ 2 * s ^ 2 := by
      rw [hβS]; ring
    have hsum : ∑ A ∈ S, ((W.veluY {A} r s - s) * D ^ 3) ^ 2
        = (∑ A ∈ S, (W.veluYCorrConstPadPoly S A).eval r ^ 2)
          + 2 * (∑ A ∈ S, (W.veluYCorrConstPadPoly S A).eval r
              * (W.veluYCorrSCoeffPadPoly S A).eval r) * s
          + (∑ A ∈ S, (W.veluYCorrSCoeffPadPoly S A).eval r ^ 2) * s ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun A hA => by rw [hβA A hA]; ring
    unfold veluDeficitCrossQuadBetaSq
    have hreorg : D ^ 2 * (((W.veluY S r s - s) ^ 2
            - ∑ A ∈ S, (W.veluY {A} r s - s) ^ 2) * D ^ 4)
        = ((W.veluY S r s - s) * D ^ 3) ^ 2
          - ∑ A ∈ S, ((W.veluY {A} r s - s) * D ^ 3) ^ 2 := by
      simp only [mul_pow, ← Finset.sum_mul]; ring
    rw [hreorg, htop, hsum]; ring
  rw [hLHS]
  have hM00 := congrArg (Polynomial.eval r) (W.veluYCorrConstSumPadPoly_sq_sub_sum_sq_eq S)
  have hM01 := congrArg (Polynomial.eval r)
    (W.veluYCorrConstSumPadPoly_mul_SCoeffSumPadPoly_sub_sum_eq S)
  have hM11 := congrArg (Polynomial.eval r) (W.veluYCorrSCoeffSumPadPoly_sq_sub_sum_sq_eq S)
  simp only [eval_sub, eval_mul, eval_pow, eval_finsetSum, eval_veluKernelDenom,
    ← hD_def] at hM00 hM01 hM11
  rw [hM00, hM01, hM11]; ring

end BetaSqCleared

section S2Reduction

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluWeierstrassCubicPoly : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

lemma veluWeierstrassCubicPoly_natDegree_le : W.veluWeierstrassCubicPoly.natDegree ≤ 3 := by
  unfold veluWeierstrassCubicPoly; compute_degree

theorem sq_eq_veluWeierstrassCubicPoly_sub_of_equation {r s : F} (hrs : W.toAffine.Equation r s) :
    s ^ 2 = W.veluWeierstrassCubicPoly.eval r - (W.a₁ * r + W.a₃) * s := by
  have heq := (Affine.equation_iff r s).mp hrs
  simp only [veluWeierstrassCubicPoly, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination heq

def veluDeficitCrossQuadBetaSqConstS2ClearedPoly (S : Finset (F × F)) : F[X] :=
  W.veluDeficitCrossQuadBetaSqConstClearedPoly S
    + W.veluWeierstrassCubicPoly * W.veluDeficitCrossQuadBetaSqSqClearedPoly S

def veluDeficitCrossQuadBetaSqSCoeffS2ClearedPoly (S : Finset (F × F)) : F[X] :=
  2 * W.veluDeficitCrossQuadBetaSqCrossClearedPoly S
    - (C W.a₁ * X + C W.a₃) * W.veluDeficitCrossQuadBetaSqSqClearedPoly S

theorem veluDeficitCrossQuadBetaSq_mul_prodPow_sDecomp {S : Finset (F × F)} {r s : F}
    (hrs : W.toAffine.Equation r s) (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadBetaSq S r s * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly S).eval r
        + (W.veluDeficitCrossQuadBetaSqSCoeffS2ClearedPoly S).eval r * s := by
  rw [W.veluDeficitCrossQuadBetaSq_mul_prodPow_sQuadDecomp s hav,
    W.sq_eq_veluWeierstrassCubicPoly_sub_of_equation hrs,
    veluDeficitCrossQuadBetaSqConstS2ClearedPoly, veluDeficitCrossQuadBetaSqSCoeffS2ClearedPoly]
  simp only [eval_add, eval_mul, eval_sub, eval_ofNat, eval_C, eval_X]
  ring

end S2Reduction

section DegBoundBetaSq

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem veluYYCorrConstPairPadQuot_natDegree_le {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (W.veluYYCorrConstPairPadQuot S A B).natDegree ≤ 4 * S.card - 2 := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hScard : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨A, hA, B, hB, hAB⟩
  unfold veluYYCorrConstPairPadQuot
  calc (W.veluYCorrConstNumPoly A * W.veluYCorrConstNumPoly B * (X - C A.1) * (X - C B.1)
          * (∏ E ∈ (S.erase A).erase B, ((X : F[X]) - C E.1)) ^ 4).natDegree
      ≤ ((2 + 2) + 1 + 1) + 4 * (S.card - 2) := by
        refine natDegree_mul_le.trans (add_le_add ?_ ?_)
        · refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          exact natDegree_mul_le.trans (add_le_add (W.veluYCorrConstNumPoly_natDegree_le A)
            (W.veluYCorrConstNumPoly_natDegree_le B))
        · rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
          simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem hBA, Finset.card_erase_of_mem hA]
          omega
    _ ≤ 4 * S.card - 2 := by omega

theorem veluYYCorrSCoeffPairPadQuot_natDegree_le {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (W.veluYYCorrSCoeffPairPadQuot S A B).natDegree ≤ 4 * S.card - 4 := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hScard : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨A, hA, B, hB, hAB⟩
  unfold veluYYCorrSCoeffPairPadQuot
  calc (W.veluYCorrSCoeffNumPoly A * W.veluYCorrSCoeffNumPoly B * (X - C A.1) * (X - C B.1)
          * (∏ E ∈ (S.erase A).erase B, ((X : F[X]) - C E.1)) ^ 4).natDegree
      ≤ ((1 + 1) + 1 + 1) + 4 * (S.card - 2) := by
        refine natDegree_mul_le.trans (add_le_add ?_ ?_)
        · refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          exact natDegree_mul_le.trans (add_le_add (W.veluYCorrSCoeffNumPoly_natDegree_le A)
            (W.veluYCorrSCoeffNumPoly_natDegree_le B))
        · rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
          simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem hBA, Finset.card_erase_of_mem hA]
          omega
    _ ≤ 4 * S.card - 4 := by omega

theorem veluDeficitCrossQuadBetaSqConstClearedPoly_natDegree_le (S : Finset (F × F)) :
    (W.veluDeficitCrossQuadBetaSqConstClearedPoly S).natDegree ≤ 4 * S.card - 2 := by
  refine natDegree_le_iff_degree_le.mpr ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
  refine ((degree_sum_le _ _).trans (Finset.sup_le fun B hB => ?_))
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact degree_le_natDegree.trans
    (Nat.cast_le.mpr (W.veluYYCorrConstPairPadQuot_natDegree_le hA hBS hBA.symm))

theorem veluDeficitCrossQuadBetaSqSqClearedPoly_natDegree_le (S : Finset (F × F)) :
    (W.veluDeficitCrossQuadBetaSqSqClearedPoly S).natDegree ≤ 4 * S.card - 4 := by
  refine natDegree_le_iff_degree_le.mpr ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
  refine ((degree_sum_le _ _).trans (Finset.sup_le fun B hB => ?_))
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact degree_le_natDegree.trans
    (Nat.cast_le.mpr (W.veluYYCorrSCoeffPairPadQuot_natDegree_le hA hBS hBA.symm))

theorem veluDeficitCrossQuadBetaSqConstS2ClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1) ?_ (by omega)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (W.veluDeficitCrossQuadBetaSqConstClearedPoly_natDegree_le S).trans (by omega)
  · refine natDegree_mul_le.trans ?_
    have h₁ := W.veluWeierstrassCubicPoly_natDegree_le
    have h₂ := W.veluDeficitCrossQuadBetaSqSqClearedPoly_natDegree_le S
    omega

end DegBoundBetaSq

namespace Affine

universe u

variable {F : Type u} [Field F]

section NonDegeneracy

variable {W : Affine F} [DecidableEq F] (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

include hΔ hA in
theorem addXFun_ne_algebraMap : W.addXFun a b ≠ ι a := by
  classical
  intro hX
  have hY : W.addYFun a b = ι (W.negY a b) := by
    have heq := equation_map_addFun W hA
    rw [hX] at heq
    rcases Affine.Y_eq_of_X_eq heq (hA.map ι) rfl with hY | hY
    · exact absurd ⟨hX, hY⟩ (addFun_ne_mapPoint hΔ hA)
    · rw [hY, map_negY]
  have hcancel := addFun_neg_cancel_X hΔ hA
  rw [hX, hY] at hcancel
  rw [Affine.map_slope ι a a (W.negY a b) (W.negY a b),
    Affine.map_addX (W' := W) ι a a (W.slope a a (W.negY a b) (W.negY a b))] at hcancel
  exact polyToFunctionField_X_ne_algebraMap _ hcancel.symm

end NonDegeneracy

section Transcendence

variable {W : Affine F} {a b : F}

theorem isIntegral_addYFun_adjoin_addXFun (hA : W.Equation a b) :
    _root_.IsIntegral (Algebra.adjoin F ({W.addXFun a b} : Set W.FunctionField)) (W.addYFun a b) := by
  set R := Algebra.adjoin F ({W.addXFun a b} : Set W.FunctionField)
  have hmem : ∀ p : F[X], (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom p ∈ R := by
    intro p
    show Polynomial.aeval (R := F) (W.addXFun a b) p ∈ R
    rw [show R = Algebra.adjoin F ({W.addXFun a b} : Set W.FunctionField) from rfl,
      Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  let φ : F[X] →+* R :=
    (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom.codRestrict R.toSubring hmem
  refine ⟨W.polynomial.map φ, monic_polynomial.map φ, ?_⟩
  show Polynomial.eval₂ (algebraMap R W.FunctionField) (W.addYFun a b) (W.polynomial.map φ) = 0
  rw [Polynomial.eval₂_map]
  exact eval₂_polynomial_addFun W hA

theorem addXFunTranscendental (hΔ : W.Δ ≠ 0) (hA : W.Equation a b) :
    AddXFunTranscendental W a b := by
  intro hX'alg
  have hX'int : _root_.IsIntegral F (W.addXFun a b) := isAlgebraic_iff_isIntegral.mp hX'alg
  haveI hRint : Algebra.IsIntegral F
      (Algebra.adjoin F ({W.addXFun a b} : Set W.FunctionField)) :=
    Algebra.IsIntegral.adjoin (fun x hx => by
      obtain rfl := Set.mem_singleton_iff.mp hx; exact hX'int)
  have hY'int : _root_.IsIntegral F (W.addYFun a b) :=
    isIntegral_trans (W.addYFun a b) (isIntegral_addYFun_adjoin_addXFun hA)
  have hKalg : Algebra.IsAlgebraic F
      (IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)) :=
    IntermediateField.isAlgebraic_adjoin (fun x hx => by
      rcases hx with rfl | rfl
      · exact hX'int
      · exact hY'int)
  have hXmem : polyToFunctionField W X
      ∈ IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) :=
    polyToFunctionField_X_mem_adjoin_addFun hΔ hA
  have hXalg : IsAlgebraic F (polyToFunctionField W X) :=
    IntermediateField.isAlgebraic_iff.mp
      (Algebra.IsAlgebraic.isAlgebraic (⟨polyToFunctionField W X, hXmem⟩ :
        IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)))
  exact transcendental_polyToFunctionField_X hXalg

end Transcendence

section UnconditionalAut

variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

def translationAlgEquivOf : W.FunctionField ≃ₐ[F] W.FunctionField :=
  translationAlgEquiv hA (addXFunTranscendental hΔ hA) hΔ

@[scoped simp] theorem translationAlgEquivOf_apply (z : W.FunctionField) :
    translationAlgEquivOf hΔ hA z = translationHom hA (addXFunTranscendental hΔ hA) z := rfl

@[scoped simp] theorem translationAlgEquivOf_polyToFunctionField_X :
    translationAlgEquivOf hΔ hA (polyToFunctionField W X) = W.addXFun a b :=
  translationHom_polyToFunctionField_X hA (addXFunTranscendental hΔ hA)

@[scoped simp] theorem translationAlgEquivOf_yGen :
    translationAlgEquivOf hΔ hA (yGen W) = W.addYFun a b :=
  translationHom_yGen hA (addXFunTranscendental hΔ hA)

end UnconditionalAut

end Affine

universe u

variable {F : Type u} [Field F]

section CoordsAPI

variable {W : Affine F} (hΔ : W.Δ ≠ 0)

local notation "ι" => algebraMap F W.FunctionField

theorem genericPoint_add_mapPoint_coordsOrZero {a b : F} (hA : W.Equation a b) :
    (Affine.genericPoint hΔ + Affine.mapPoint hΔ hA).coordsOrZero
      = (W.addXFun a b, W.addYFun a b) := by
  rw [Affine.genericPoint_add_map hΔ hA, Point.coordsOrZero_some]

end CoordsAPI

section AlgHomFixes

variable {K : Type*} [Field K] [Algebra F K]

theorem algHom_toRingHom_comp_algebraMap (τ : K →ₐ[F] K) :
    τ.toRingHom.comp (algebraMap F K) = algebraMap F K :=
  RingHom.ext fun c => τ.commutes c

theorem map_map_algHom_toRingHom_eq_self (W : WeierstrassCurve F) (τ : K →ₐ[F] K) :
    (W.map (algebraMap F K)).map τ.toRingHom = W.map (algebraMap F K) := by
  rw [WeierstrassCurve.map_map, algHom_toRingHom_comp_algebraMap]

variable (W : Affine F)

theorem liftSummingSet_map_algHom (τ : W.FunctionField →ₐ[F] W.FunctionField)
    (hτ : Function.Injective τ.toRingHom) (S : Finset (F × F)) :
    (W.liftSummingSet S).map ⟨Prod.map τ.toRingHom τ.toRingHom, hτ.prodMap hτ⟩
      = W.liftSummingSet S := by
  unfold liftSummingSet
  rw [Finset.map_map]
  congr 1
  refine Function.Embedding.ext fun ⟨c, d⟩ => ?_
  show (τ.toRingHom (algebraMap F W.FunctionField c), τ.toRingHom (algebraMap F W.FunctionField d))
    = (algebraMap F W.FunctionField c, algebraMap F W.FunctionField d)
  rw [show τ.toRingHom (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c from
        τ.commutes c,
      show τ.toRingHom (algebraMap F W.FunctionField d) = algebraMap F W.FunctionField d from
        τ.commutes d]

end AlgHomFixes

section AlgHomNaturality

variable (W : Affine F)

local notation "ι" => algebraMap F W.FunctionField

theorem algHom_veluDeficit_liftSummingSet (τ : W.FunctionField →ₐ[F] W.FunctionField)
    (S : Finset (F × F)) (r s : W.FunctionField) :
    τ ((W.map ι).veluDeficit (W.liftSummingSet S) r s)
      = (W.map ι).veluDeficit (W.liftSummingSet S) (τ r) (τ s) := by
  have hτinj : Function.Injective τ.toRingHom := τ.toRingHom.injective
  have hkey := (W.map ι).map_veluDeficit τ.toRingHom (W.liftSummingSet S) hτinj r s
  rw [W.map_map_algHom_toRingHom_eq_self τ, W.liftSummingSet_map_algHom τ hτinj S] at hkey
  exact hkey.symm

theorem algHom_veluDeficitFun (τ : W.FunctionField →ₐ[F] W.FunctionField)
    (S : Finset (F × F)) :
    τ (W.veluDeficitFun S)
      = (W.map ι).veluDeficit (W.liftSummingSet S)
          (τ (polyToFunctionField W X)) (τ (yGen W)) :=
  W.algHom_veluDeficit_liftSummingSet τ S (polyToFunctionField W X) (yGen W)

end AlgHomNaturality

section TranslationAction

variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

theorem translationAlgEquivOf_veluDeficitFun (S : Finset (F × F)) :
    Affine.translationAlgEquivOf hΔ hA (W.veluDeficitFun S)
      = (W.map ι).veluDeficit (W.liftSummingSet S) (W.addXFun a b) (W.addYFun a b) := by
  rw [Affine.translationAlgEquivOf_apply,
    W.algHom_veluDeficitFun (Affine.translationHom hA (Affine.addXFunTranscendental hΔ hA)) S,
    Affine.translationHom_polyToFunctionField_X, Affine.translationHom_yGen]

theorem translationAlgEquivOf_veluDeficitFun_eq_coordsOrZero (S : Finset (F × F)) :
    Affine.translationAlgEquivOf hΔ hA (W.veluDeficitFun S)
      = (W.map ι).veluDeficit (W.liftSummingSet S)
          (Affine.genericPoint hΔ + Affine.mapPoint hΔ hA).coordsOrZero.1
          (Affine.genericPoint hΔ + Affine.mapPoint hΔ hA).coordsOrZero.2 := by
  rw [translationAlgEquivOf_veluDeficitFun hΔ hA S,
    genericPoint_add_mapPoint_coordsOrZero hΔ hA]

theorem veluDeficitFun_eq_coordsOrZero_genericPoint (S : Finset (F × F)) :
    W.veluDeficitFun S
      = (W.map ι).veluDeficit (W.liftSummingSet S)
          (Affine.genericPoint hΔ).coordsOrZero.1
          (Affine.genericPoint hΔ).coordsOrZero.2 :=
  rfl

theorem translationAlgEquivOf_veluDeficitFun_eq_iff (S : Finset (F × F)) :
    Affine.translationAlgEquivOf hΔ hA (W.veluDeficitFun S) = W.veluDeficitFun S
      ↔ (W.map ι).veluDeficit (W.liftSummingSet S)
            (Affine.genericPoint hΔ + Affine.mapPoint hΔ hA).coordsOrZero.1
            (Affine.genericPoint hΔ + Affine.mapPoint hΔ hA).coordsOrZero.2
          = (W.map ι).veluDeficit (W.liftSummingSet S)
            (Affine.genericPoint hΔ).coordsOrZero.1
            (Affine.genericPoint hΔ).coordsOrZero.2 := by
  rw [translationAlgEquivOf_veluDeficitFun_eq_coordsOrZero hΔ hA S,
    veluDeficitFun_eq_coordsOrZero_genericPoint hΔ S]

end TranslationAction

section GenericNotConstant

variable {W : Affine F} (hΔ : W.Δ ≠ 0)

local notation "ι" => algebraMap F W.FunctionField

theorem genericPoint_ne_some_algebraMap (c d : F)
    (hns : (W.map ι).Nonsingular (ι c) (ι d)) :
    Affine.genericPoint hΔ ≠ Affine.Point.some (ι c) (ι d) hns := by
  intro h
  exact polyToFunctionField_X_ne_algebraMap c (Affine.Point.some.inj h).1

theorem genericPoint_ne_zero : Affine.genericPoint hΔ ≠ 0 :=
  Affine.Point.some_ne_zero _

end GenericNotConstant

section CoordsAPIRat

variable {k : Type*} [Field k] (f : F →+* k) {W : WeierstrassCurve F}

theorem coordsOrZero_ratPointMap (P : W.toAffine.Point) :
    (ratPointMap f P).coordsOrZero = (f P.coordsOrZero.1, f P.coordsOrZero.2) := by
  rcases P with _ | ⟨x, y, h⟩
  · show ((0, 0) : k × k) = (f 0, f 0); rw [_root_.map_zero]
  · rfl

end CoordsAPIRat

section SummingSetCompat

variable [DecidableEq F] (W : Affine F)

local notation "ι" => algebraMap F W.FunctionField

variable [DecidableEq W.FunctionField]

theorem liftSummingSet_oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ) :
    W.liftSummingSet (W.oddOrderSummingSet Q n)
      = (W.map ι).oddOrderSummingSet (ratPointHom (W₀ := W) ι Q) n := by
  refine Finset.ext fun A => ?_
  simp only [liftSummingSet, oddOrderSummingSet, Finset.mem_map, Finset.mem_image,
    Finset.mem_Icc, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, by
      rw [← map_nsmul, ratPointHom_apply, coordsOrZero_ratPointMap]; rfl⟩
  · rintro ⟨k, hk, hkA⟩
    exact ⟨(k • Q).coordsOrZero, ⟨k, hk, rfl⟩, by
      rw [← hkA, ← map_nsmul, ratPointHom_apply, coordsOrZero_ratPointMap]; rfl⟩

end SummingSetCompat

section GenericNotInRange

variable [DecidableEq F] {W : Affine F} (hΔ : W.Δ ≠ 0)

local notation "ι" => algebraMap F W.FunctionField

variable [DecidableEq W.FunctionField]

theorem genericPoint_notMem_range_ratPointHom :
    Affine.genericPoint hΔ ∉ (ratPointHom (W₀ := W) ι).range := by
  rintro ⟨P, hP⟩
  rcases P with _ | ⟨c, d, h⟩
  · exact genericPoint_ne_zero hΔ hP.symm
  · exact genericPoint_ne_some_algebraMap hΔ c d _ hP.symm

theorem genericPoint_notMem_zmultiples_ratPointHom (Q : W.toAffine.Point) :
    Affine.genericPoint hΔ ∉ AddSubgroup.zmultiples (ratPointHom (W₀ := W) ι Q) := by
  intro hmem
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine genericPoint_notMem_range_ratPointHom hΔ ⟨n • Q, ?_⟩
  rw [map_zsmul, hn]

end GenericNotInRange

namespace Affine

section InverseOnX

variable {W : Affine F} [DecidableEq F] (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

include hΔ hA in
theorem translationAlgEquivOf_addXFun_negY :
    translationAlgEquivOf hΔ hA (W.addXFun a (W.negY a b)) = polyToFunctionField W X := by
  have key := addFun_neg_cancel_X hΔ hA
  rw [Affine.slope_of_X_ne (addXFun_ne_algebraMap hΔ hA)] at key
  rw [addXFun, Affine.slope_of_X_ne (polyToFunctionField_X_ne_algebraMap a)]
  set τ := translationAlgEquivOf hΔ hA
  have hτX : τ (polyToFunctionField W X) = W.addXFun a b :=
    translationAlgEquivOf_polyToFunctionField_X hΔ hA
  have hτY : τ (yGen W) = W.addYFun a b := translationAlgEquivOf_yGen hΔ hA
  have hτι : ∀ c : F, τ (ι c) = ι c := fun c => τ.commutes c
  simp only [Affine.addX, map_a₁, map_a₂] at key ⊢
  simp only [map_sub, map_add, map_mul, map_pow, map_div₀, hτX, hτY, hτι]
  exact key

include hΔ hA in
theorem translationAlgEquivOf_symm_polyToFunctionField_X :
    (translationAlgEquivOf hΔ hA).symm (polyToFunctionField W X)
      = W.addXFun a (W.negY a b) :=
  (AlgEquiv.symm_apply_eq _).mpr (translationAlgEquivOf_addXFun_negY hΔ hA).symm

end InverseOnX

section OrdAtInftyValues

variable {W : Affine F}
variable (v : AlgebraicCurve.Place F W.FunctionField)

theorem ord_X_eq_neg_two_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) :
    v.ord (polyToFunctionField W X) = -2 := by
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have hYord := two_mul_ord_Y_eq_three_mul_ord_X v hv
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπord : v.ord (π : W.FunctionField) = 1 := v.ord_coe_irreducible hπ
  have hπ0 : (π : W.FunctionField) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing)
    (π : W.FunctionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, _root_.map_zero, zero_div] at hab
    exact hπ0 hab.symm
  have ha' : algebraMap W.CoordinateRing W.FunctionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr ha0
  have hb' : algebraMap W.CoordinateRing W.FunctionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hb0
  have h1 := two_mul_ord_eq_of_not_isFinitePlace v hv ha0
  have h2 := two_mul_ord_eq_of_not_isFinitePlace v hv hb0
  have h3 : v.ord (π : W.FunctionField)
      = v.ord (algebraMap W.CoordinateRing W.FunctionField a)
        - v.ord (algebraMap W.CoordinateRing W.FunctionField b) := by
    rw [← hab, div_eq_mul_inv, v.ord_mul ha' (inv_ne_zero hb'), v.ord_inv]
    ring
  rw [hπord] at h3
  have h4 : (2 : ℤ) = v.ord (polyToFunctionField W X) * (((Algebra.norm F[X] a).natDegree : ℤ)
      - ((Algebra.norm F[X] b).natDegree : ℤ)) := by
    linear_combination 2 * h3 + h1 - h2
  have h5 : v.ord (polyToFunctionField W X) ∣ 2 := ⟨_, h4⟩
  have h6 : (2 : ℤ) ∣ v.ord (polyToFunctionField W X) := by
    have h7 : (2 : ℤ) ∣ 3 * v.ord (polyToFunctionField W X) := ⟨_, hYord.symm⟩
    omega
  have h8 : (v.ord (polyToFunctionField W X)).natAbs ∣ (2 : ℤ).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h5
  have h9 : (2 : ℤ).natAbs ∣ (v.ord (polyToFunctionField W X)).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h6
  have h10 : (v.ord (polyToFunctionField W X)).natAbs = 2 :=
    Nat.dvd_antisymm (by simpa using h8) (by simpa using h9)
  omega

theorem ord_Y_eq_neg_three_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) :
    v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) = -3 := by
  have h1 := two_mul_ord_Y_eq_three_mul_ord_X v hv
  rw [ord_X_eq_neg_two_of_not_isFinitePlace v hv] at h1
  omega

end OrdAtInftyValues

section OrdPins

variable {W : Affine F}
variable (v : AlgebraicCurve.Place F W.FunctionField)

theorem ord_X_sub_algebraMap_of_not_isFinitePlace
    (hv : ¬ IsFinitePlace v) (c : F) :
    v.ord (polyToFunctionField W X - algebraMap F W.FunctionField c) = -2 := by
  have key : polyToFunctionField W X - algebraMap F W.FunctionField c
      = polyToFunctionField W (X - C c) := by
    rw [map_sub, polyToFunctionField_C]
  rw [key, v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C
    (ord_X_neg_of_not_isFinitePlace v hv) (X_sub_C_ne_zero c), natDegree_X_sub_C,
    ord_X_eq_neg_two_of_not_isFinitePlace v hv]
  norm_num

theorem X_sub_algebraMap_ne_zero (c : F) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c : W.FunctionField) ≠ 0 :=
  sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap c)

theorem inv_X_sub_algebraMap_mem_of_not_isFinitePlace
    (hv : ¬ IsFinitePlace v) (c : F) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹ ∈ v.toValuationSubring := by
  refine v.mem_of_ord_nonneg (inv_ne_zero (X_sub_algebraMap_ne_zero c)) ?_
  rw [v.ord_inv, ord_X_sub_algebraMap_of_not_isFinitePlace v hv]
  omega

theorem X_mul_inv_X_sub_algebraMap_mem_of_not_isFinitePlace
    (hv : ¬ IsFinitePlace v) (c : F) :
    polyToFunctionField W X * (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹
      ∈ v.toValuationSubring := by
  refine v.mem_of_ord_nonneg
    (mul_ne_zero (polyToFunctionField_ne_zero X_ne_zero)
      (inv_ne_zero (X_sub_algebraMap_ne_zero c))) ?_
  rw [v.ord_mul (polyToFunctionField_ne_zero X_ne_zero)
    (inv_ne_zero (X_sub_algebraMap_ne_zero c)), v.ord_inv,
    ord_X_eq_neg_two_of_not_isFinitePlace v hv,
    ord_X_sub_algebraMap_of_not_isFinitePlace v hv]
  omega

theorem ord_yGen_of_not_isFinitePlace
    (hv : ¬ IsFinitePlace v) :
    v.ord (yGen W) = -3 :=
  ord_Y_eq_neg_three_of_not_isFinitePlace v hv

theorem yGen_mul_inv_X_sub_algebraMap_sq_mem_of_not_isFinitePlace
    (hv : ¬ IsFinitePlace v) (c : F) :
    yGen W * ((polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹) ^ 2
      ∈ v.toValuationSubring := by
  have hY : yGen W ≠ (0 : W.FunctionField) := Y_image_ne_zero
  have hinv : (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹
      ≠ (0 : W.FunctionField) := inv_ne_zero (X_sub_algebraMap_ne_zero c)
  refine v.mem_of_ord_nonneg (mul_ne_zero hY (pow_ne_zero 2 hinv)) ?_
  rw [v.ord_mul hY (pow_ne_zero 2 hinv), v.ord_pow, v.ord_inv,
    ord_X_sub_algebraMap_of_not_isFinitePlace v hv, ord_yGen_of_not_isFinitePlace v hv]
  omega

theorem natCast_mem (n : ℕ) :
    (n : W.FunctionField) ∈ v.toValuationSubring := by
  rw [show (n : W.FunctionField) = algebraMap F W.FunctionField n from (map_natCast _ n).symm]
  exact v.algebraMap_mem' (n : F)

end OrdPins

section Corrections

variable {W : Affine F}
variable {v : AlgebraicCurve.Place F W.FunctionField}

local notation "W'" => W.map (algebraMap F W.FunctionField)
local notation "ι" => algebraMap F W.FunctionField
local notation "𝕏" => polyToFunctionField W X
local notation "𝕐" => yGen W

theorem veluXCorr_genericPoint_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) (c d : F) :
    (W').veluXCorr (ι c) (ι d) 𝕏 ∈ v.toValuationSubring := by
  have hδ := inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv c
  unfold WeierstrassCurve.veluXCorr
  rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, map_veluT, map_veluU]
  exact add_mem (mul_mem (v.algebraMap_mem' _) hδ)
    (mul_mem (v.algebraMap_mem' _) (pow_mem hδ 2))

theorem veluYCorr_genericPoint_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) (c d : F) :
    (W').veluYCorr (ι c) (ι d) 𝕏 𝕐 ∈ v.toValuationSubring := by
  have hδ := inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv c
  have hXδ := X_mul_inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv c
  have hYδ := yGen_mul_inv_X_sub_algebraMap_sq_mem_of_not_isFinitePlace v hv c
  set δ : W.FunctionField := (𝕏 - ι c)⁻¹ with hδdef
  have key : (W').veluYCorr (ι c) (ι d) 𝕏 𝕐
      = -((2 * ι (W.veluU c d)) * (𝕐 * δ ^ 2) * δ
          + (ι (W.a₁ * W.veluU c d)) * (𝕏 * δ) * δ ^ 2
          + (ι (W.a₃ * W.veluU c d)) * δ ^ 3
          + (ι (W.a₁ * W.veluT c d)) * δ
          + (ι (W.veluT c d)) * (𝕐 * δ ^ 2)
          + (-ι (d * W.veluT c d)) * δ ^ 2
          + (ι (W.a₁ * W.veluU c d - W.veluGx c d * W.veluGy c d)) * δ ^ 2) := by
    have hδne : (𝕏 - ι c : W.FunctionField) ≠ 0 := X_sub_algebraMap_ne_zero c
    unfold WeierstrassCurve.veluYCorr
    simp only [map_veluU, map_veluT, map_veluGx, map_veluGy, map_a₁, map_a₃, map_mul, map_sub]
    rw [hδdef]
    field_simp
    ring
  rw [key]
  have h2 : (2 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 2; push_cast at this; exact this
  refine neg_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_)
  · exact mul_mem (mul_mem (mul_mem h2 (v.algebraMap_mem' _)) hYδ) hδ
  · exact mul_mem (mul_mem (v.algebraMap_mem' _) hXδ) (pow_mem hδ 2)
  · exact mul_mem (v.algebraMap_mem' _) (pow_mem hδ 3)
  · exact mul_mem (v.algebraMap_mem' _) hδ
  · exact mul_mem (v.algebraMap_mem' _) hYδ
  · exact mul_mem (neg_mem (v.algebraMap_mem' _)) (pow_mem hδ 2)
  · exact mul_mem (v.algebraMap_mem' _) (pow_mem hδ 2)

theorem veluY_sub_self_genericPoint_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    (S : Finset (F × F)) :
    (W').veluY (W.liftSummingSet S) 𝕏 𝕐 - 𝕐 ∈ v.toValuationSubring := by
  rw [(W').veluY_sub_self_eq_sum_veluYCorr]
  refine sum_mem fun Q hQ => ?_
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
  obtain ⟨B, -, rfl⟩ := hQ
  exact veluYCorr_genericPoint_mem_of_not_isFinitePlace hv B.1 B.2

end Corrections

end Affine

end WeierstrassCurve

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

private theorem eq_algebraMap_of_forall_ord_nonneg_aux (v₀ : Place K F) (hrat : v₀.IsRational)
    (hdeg : v₀.deg ≠ 0) {g : F} (hg : g ≠ 0) (hord : ∀ v : Place K F, 0 ≤ v.ord g) :
    ∃ c : K, g = algebraMap K F c := by
  have hg₀ : g ∈ v₀.toValuationSubring := v₀.mem_of_ord_nonneg hg (hord v₀)
  refine ⟨v₀.evalAt g, ?_⟩
  by_contra hne
  set t : F := g - algebraMap K F (v₀.evalAt g) with ht
  have htne : t ≠ 0 := sub_ne_zero.mpr hne
  have hzero : 0 < v₀.ord t := v₀.ord_sub_evalAt_pos hrat hg₀ htne
  have hpole : ∀ v : Place K F, 0 ≤ v.ord t := fun v =>
    v.ord_nonneg_of_mem (sub_mem (v.mem_of_ord_nonneg hg (hord v)) (v.algebraMap_mem' _))
  obtain ⟨D, hD, hdeg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) t htne
  have hDpos : 0 < D v₀ := by rw [hD v₀]; exact hzero
  have hDnonneg : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact hpole v
  have hmem : v₀ ∈ D.support := Finsupp.mem_support_iff.mpr hDpos.ne'
  have hpos : 0 < Divisor.degree D := by
    rw [Divisor.degree_eq_sum]
    calc (0 : ℤ) < D v₀ * (v₀.deg : ℤ) :=
          mul_pos hDpos (by exact_mod_cast Nat.pos_of_ne_zero hdeg)
      _ ≤ ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
          Finset.single_le_sum
            (fun v _ => mul_nonneg (hDnonneg v) (Int.natCast_nonneg _)) hmem
  omega

theorem exists_eq_algebraMap_of_forall_ord_nonneg₀ (v₀ : Place K F) (hdeg : v₀.deg = 1)
    {g : F} (hord : ∀ v : Place K F, 0 ≤ v.ord g) :
    ∃ c : K, g = algebraMap K F c := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact ⟨0, (algebraMap K F).map_zero.symm⟩
  · exact eq_algebraMap_of_forall_ord_nonneg_aux v₀ ((isRational_iff_deg_eq_one v₀).2 hdeg)
      (hdeg ▸ one_ne_zero) hg hord

end Place

end AlgebraicCurve

namespace WeierstrassCurve

namespace Affine

universe u

variable {F : Type u} [Field F]

section LiouvilleBridge

variable {W : Affine F}

theorem functionField_liouville_of_equation [AlgebraicCurve.HasPrincipalDivisors F W.FunctionField]
    [IsDedekindDomain W.CoordinateRing] {x₀ y₀ : F} (h₀ : W.Equation x₀ y₀)
    {f : W.FunctionField}
    (hord : ∀ v : AlgebraicCurve.Place F W.FunctionField, 0 ≤ v.ord f) :
    ∃ c : F, f = algebraMap F W.FunctionField c :=
  AlgebraicCurve.Place.exists_eq_algebraMap_of_forall_ord_nonneg₀
    (placeOfEquation h₀) (deg_placeOfEquation h₀) hord

end LiouvilleBridge

end Affine

section Constancy

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

theorem kw_infinite_of_isAlgClosed : Infinite F := by
  rw [← not_finite_iff_infinite]
  intro hfin
  haveI := Fintype.ofFinite F
  have hdeg : (∏ a : F, (X - C a) : F[X]).degree = (Fintype.card F : ℕ) := by
    simp [Polynomial.degree_prod, Polynomial.degree_X_sub_C]
  have hlt : (1 : F[X]).degree < (∏ a : F, (X - C a) : F[X]).degree := by
    rw [Polynomial.degree_one, hdeg]; exact_mod_cast Fintype.card_pos
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (1 + ∏ a : F, (X - C a) : F[X])
    (by rw [Polynomial.degree_add_eq_right_of_degree_lt hlt, hdeg]
        exact_mod_cast Fintype.card_pos.ne')
  have heval : (1 + ∏ a : F, (X - C a) : F[X]).eval x = 1 := by
    simp only [eval_add, eval_one, eval_prod, eval_sub, eval_X, eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_univ x) (sub_self x), add_zero]
  rw [Polynomial.IsRoot, heval] at hx
  exact one_ne_zero hx

theorem kw_hDDTerm :
    ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing :=
  fun _W hΔ => Affine.CoordinateRing.isDedekindDomain_of_Δ_ne_zero hΔ

end Constancy

namespace Affine

universe u

variable {F : Type u} [Field F]

section TransportEngine

variable {W : Affine F}

theorem not_isFinitePlace_smul_of_symm_X_notMem
    (σ : W.FunctionField ≃ₐ[F] W.FunctionField) (v : AlgebraicCurve.Place F W.FunctionField)
    (h : σ.symm (polyToFunctionField W X) ∉ v.toValuationSubring) :
    ¬ IsFinitePlace (σ • v) := by
  rw [isFinitePlace_smul_iff_forall_symm_mem]
  intro hall
  apply h
  have := hall (algebraMap F[X] W.CoordinateRing X)
  rwa [← polyToFunctionField_apply] at this

end TransportEngine

section Pole

variable {W : Affine F} [DecidableEq F]

local notation "ι" => algebraMap F W.FunctionField

open CoordinateRing

private lemma algebraMap_XClass_eq (c : F) :
    algebraMap W.CoordinateRing W.FunctionField (XClass W c)
      = polyToFunctionField W X - ι c := by
  rw [show (XClass W c : W.CoordinateRing) = algebraMap F[X] W.CoordinateRing (X - C c) from rfl,
    ← polyToFunctionField_apply, map_sub, polyToFunctionField_C]

private lemma algebraMap_YClass_eq (c : F) :
    algebraMap W.CoordinateRing W.FunctionField (YClass W (C c)) = yGen W - ι c := by
  have h1 : (YClass W (C c) : W.CoordinateRing)
      = CoordinateRing.mk W Y - algebraMap F[X] W.CoordinateRing (C c) := by
    show CoordinateRing.mk W (Y - C (C c)) = _
    rw [map_sub]; rfl
  rw [h1, map_sub, ← polyToFunctionField_apply, polyToFunctionField_C]; rfl

theorem addXFun_negY_notMem_of_XClass_mem_centre {a b : F}
    {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v)
    (hX : XClass W a ∈ hv.centre) (hY : YClass W (C (W.negY a b)) ∉ hv.centre) :
    W.addXFun a (W.negY a b) ∉ v.toValuationSubring := by
  set δX : W.FunctionField := polyToFunctionField W X - ι a with hδX
  set δY : W.FunctionField := yGen W - ι (W.negY a b) with hδY
  have hδX0 : δX ≠ 0 := X_sub_algebraMap_ne_zero (W := W) a
  have hδY0 : δY ≠ 0 := hδY ▸ algebraMap_YClass_eq (W.negY a b) ▸
    algebraMap_coordinateRing_ne_zero (YClass_ne_zero (W' := W) (C (W.negY a b)))
  have hδXord : 1 ≤ v.ord δX := by
    have h1 : v.ord δX ≠ 0 := by
      have := (hv.mem_centre_iff_ord_ne_zero (XClass_ne_zero (W' := W) a)).mp hX
      rwa [algebraMap_XClass_eq] at this
    have h2 : 0 ≤ v.ord δX := by
      rw [hδX, ← algebraMap_XClass_eq]; exact v.ord_nonneg_of_mem (hv (XClass W a))
    omega
  have hδYord : v.ord δY = 0 := by
    have h1 : ¬ v.ord δY ≠ 0 := by
      rw [hδY, ← algebraMap_YClass_eq]
      exact fun hne => hY ((hv.mem_centre_iff_ord_ne_zero
        (YClass_ne_zero (W' := W) (C (W.negY a b)))).mpr hne)
    omega
  set ℓ : W.FunctionField := δY / δX with hℓ
  have hℓ0 : ℓ ≠ 0 := div_ne_zero hδY0 hδX0
  have hℓord : v.ord ℓ ≤ -1 := by rw [hℓ, v.ord_div hδY0 hδX0, hδYord]; omega
  have hℓnotmem : ℓ ∉ v.toValuationSubring := by
    rw [v.mem_iff_ord_nonneg hℓ0]; omega
  have hℓa₁notmem : ℓ + ι W.a₁ ∉ v.toValuationSubring := by
    intro hmem
    exact hℓnotmem (by simpa using sub_mem hmem (v.algebraMap_mem' W.a₁))
  have hprod_notmem : ℓ * (ℓ + ι W.a₁) ∉ v.toValuationSubring := by
    have hℓa₁0 : ℓ + ι W.a₁ ≠ 0 := by
      intro h0; exact hℓa₁notmem (h0 ▸ zero_mem v.toValuationSubring)
    rw [v.mem_iff_ord_nonneg (mul_ne_zero hℓ0 hℓa₁0), v.ord_mul hℓ0 hℓa₁0]
    have h1 : v.ord (ℓ + ι W.a₁) < 0 := by
      rw [← not_le, ← v.mem_iff_ord_nonneg hℓa₁0]; exact hℓa₁notmem
    omega
  have hkey : W.addXFun a (W.negY a b)
      = ℓ * (ℓ + ι W.a₁) - (ι W.a₂ + polyToFunctionField W X + ι a) := by
    rw [addXFun, Affine.slope_of_X_ne (polyToFunctionField_X_ne_algebraMap a)]
    simp only [Affine.addX, map_a₁, map_a₂, hℓ, hδX, hδY]
    ring
  intro hmem
  apply hprod_notmem
  have htail : (ι W.a₂ + polyToFunctionField W X + ι a : W.FunctionField)
      ∈ v.toValuationSubring :=
    add_mem (add_mem (v.algebraMap_mem' W.a₂)
      (polyToFunctionField_apply (W := W) X ▸ hv (algebraMap F[X] W.CoordinateRing X)))
      (v.algebraMap_mem' a)
  have := add_mem hmem htail
  rwa [hkey, sub_add_cancel] at this

end Pole

section CombinedDischarge

variable {W : Affine F} [DecidableEq F]
variable (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

open CoordinateRing

theorem not_isFinitePlace_translationAlgEquivOf_smul_of_centre
    {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v)
    (hX : XClass W a ∈ hv.centre) (hY : YClass W (C (W.negY a b)) ∉ hv.centre) :
    ¬ IsFinitePlace (translationAlgEquivOf hΔ hA • v) := by
  apply not_isFinitePlace_smul_of_symm_X_notMem (translationAlgEquivOf hΔ hA) v
  rw [translationAlgEquivOf_symm_polyToFunctionField_X hΔ hA]
  exact addXFun_negY_notMem_of_XClass_mem_centre hv hX hY

end CombinedDischarge

end Affine

end WeierstrassCurve
