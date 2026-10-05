/-
The explicit-Vélu `restrictAlong` isomorphism: the H4 capstone of the Vélu port.

This module holds the restrictAlong-only engine, and is where the two headline
theorems

* `WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed`
  (the general statement), and
* `WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq`
  (the plain statement, derived as a corollary),

are to be stated.

Statements are transcribed from the pinned FLT `aa2d8b3` `Theorems/` wrappers
(the statement authority):

* `Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean`
* `Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq.lean`

and proof bodies from the canonical pin solution file

* `P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean`

only adapted to mathlib `v4.34.0`.

## Status: complete (H5a + H5b landed; the column is closed)

H5a's `GenusOnePlaceGate`/`IsCentred`/`AbelTheorem` vocabulary and H5b's
`natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong` are now in
the tree, so the three previously blocked engine declarations and the two
headlines are appended below.  The two headlines' statements are the pin
`Theorems/` wrappers' verbatim; the plain one is the general one plus
`[CharZero F]`, proved as a direct corollary (no transcribed proof body).

**Fidelity note (the section-instance re-spelling).**  The 65 engine
declarations already in the module had their section instances routed through the
port's older `InfinitePlace` *class*; that class is not part of the pin's
vocabulary.  They now carry the pin's `[GenusOnePlaceGate W.toAffine]`,
`[GenusOnePlaceGate.IsCentred W.toAffine]`, `[AbelTheorem W.toAffine]` (and the
corresponding instances on the Vélu quotient), exactly as the pin's `S_` sections
do.  The pin's statement text spells the infinite place `InfinitePlace.place`
(its `S_`-local namespace definition `placeOfPoint 0`); to keep the checker's
textual match the module recovers the port's class by an *anonymous* instance
from the gate vocabulary (`section InfinitePlaceBridge`), so no `[InfinitePlace]`
binder survives in any elaborated signature (verified with `#check`; the
checker cannot see section variables).

**Off-list prerequisites discovered by the wire test** (absent from the port,
transcribed here because only this module may be edited; all are `private`):

* `AlgebraicCurve.F10d.relNorm_eq_pow_of_isMaximal_of_isSeparable` (the pin's
  155-line `S_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable.lean`);
* the port's `PrincipalDivisors/Transcendence.lean` fibre-centre norm argument
  re-run without `[CharZero F]`, giving
  `Divisor.pushforwardNormFormula_of_finiteDimensional` char-free and then
  `normFormulaAlong_of_elliptic` / `s2c_key`;
* the char-free separability chain
  `kw_isSeparable_of_aeval_derivative_ne_zero`,
  `kw_derivative_mul_sq_sub_mul_derivative_sq_ne_zero`,
  `kw_isSeparable_yGen_of_algebraMap_eq`,
  `kw_isSeparable_polyToFunctionField_X_oddOrderSummingSet_odd`,
  `kw_oddOrderSummingSetFunctionFieldHom_odd_separableAlong`, and
  `two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero'`.

The `WeierstrassCurve/Place/Dictionary.lean` `ord`-at-a-point dictionary
(`eq_placeOfEquation_of_le_centre`, `ord_polyToFunctionField_{pos,eq_zero}_iff`)
was relocated to the dictionary by the H5r refactor round; the pin's
`InfinitePlace` namespace lemmas are recovered privately.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.OddOrder
import FLTForHuman.WeierstrassCurve.Velu.MapEquation
import FLTForHuman.WeierstrassCurve.GenusOnePlaceGate
import FLTForHuman.WeierstrassCurve.Isogeny.ConditionalCurrency
import FLTForHuman.WeierstrassCurve.Isogeny.NatCard
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.Defs.RestrictAlongAPI
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open Polynomial Finset
open scoped Polynomial.Bivariate Classical
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing
open AlgebraicCurve

/-! ### The `restrictAlong` place calculus

`Place.mem_restrictAlong_iff`, `Place.ramificationIndexAlong_pos` and
`Place.ord_restrictAlong_ne_zero_iff` were extracted to the leaf module
`AlgebraicCurve/Defs/RestrictAlongAPI.lean` (H5 SET-1), imported above, so that
the H5 `IsogenyEndDatum` column can use them without importing Vélu. -/

namespace WeierstrassCurve

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

/-! ### Private bridge: the pin's `InfinitePlace` namespace from the gate

The pin defines its infinite place as `placeOfPoint 0` inside the
`GenusOnePlaceGate` section (`S_` lines 267--288).  The port's older
`InfinitePlace` *class* is not part of the pin's vocabulary, so the sections below
route through `[GenusOnePlaceGate W.toAffine]` /
`[GenusOnePlaceGate.IsCentred W.toAffine]` / `[AbelTheorem W.toAffine]` and use
these private recombinations in place of the pin's namespace lemmas. -/

section InfinitePlaceBridge

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

private theorem placeOfPoint_some' [IsDedekindDomain W.toAffine.CoordinateRing]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine]
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    placeOfPoint (Point.some x y h) = placeOfEquation h.left :=
  placeOfPoint_some_eq_ofHeightOneSpectrum h (heightOneSpectrumOfEquation h.left) rfl

private theorem not_isFinitePlace_placeOfPoint_zero [IsAlgClosed F] [W.toAffine.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine] :
    ¬ IsFinitePlace (placeOfPoint (0 : W.toAffine.Point)) := fun h =>
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero (W := W.toAffine) (h _)

private theorem eq_placeOfPoint_zero_of_not_isFinitePlace [IsAlgClosed F]
    [IsDedekindDomain W.toAffine.CoordinateRing] [GenusOnePlaceGate W.toAffine]
    [GenusOnePlaceGate.IsCentred W.toAffine]
    (v : Place F W.toAffine.FunctionField) (hv : ¬ IsFinitePlace v) :
    v = placeOfPoint (0 : W.toAffine.Point) := by
  obtain ⟨P, rfl⟩ : ∃ P : W.toAffine.Point, placeOfPoint P = v :=
    ⟨(pointEquivPlace (W := W.toAffine)).symm v,
      (pointEquivPlace (W := W.toAffine)).apply_symm_apply v⟩
  cases P with
  | zero => rfl
  | some x y h =>
      exact absurd (placeOfPoint_some' h ▸ isFinitePlace_placeOfEquation h.left) hv

/-- The port's older `InfinitePlace` carrier, recovered from the pin's gate
vocabulary: the seam lemmas below keep the pin's `S_` statement text (which
spells the infinite place `InfinitePlace.place`) while their sections carry the
pin's `GenusOnePlaceGate`/`IsCentred`/`AbelTheorem` instances.  The instance is
anonymous, so it is invisible to the statement checker; the elaborated
signatures carry the gate classes, not this class. -/
instance [IsAlgClosed F] [W.toAffine.IsElliptic] [GenusOnePlaceGate W.toAffine]
    [GenusOnePlaceGate.IsCentred W.toAffine] : InfinitePlace W.toAffine where
  place := placeOfPoint (0 : W.toAffine.Point)
  not_isFinitePlace := not_isFinitePlace_placeOfPoint_zero
  deg_eq_one := deg_placeOfPoint (W := W.toAffine) 0
  eq_of_not_isFinitePlace := fun v hv => eq_placeOfPoint_zero_of_not_isFinitePlace v hv

end InfinitePlaceBridge

section TwoNeZeroOrA1OrA3

variable {F : Type*} [Field F]

/-- Pin `WeierstrassCurve.two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero'`
(res `S_` line 945), needed by the char-free separability of `yGen`. -/
theorem two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero' (W : WeierstrassCurve F)
    (hΔ : W.Δ ≠ 0) : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h2, h1, h3⟩ := h
  apply hΔ
  have hb2 : W.b₂ = 0 := by
    rw [WeierstrassCurve.b₂, h1]; linear_combination (2 * W.a₂) * h2
  have hb4 : W.b₄ = 0 := by
    rw [WeierstrassCurve.b₄, h1]; linear_combination W.a₄ * h2
  have hb6 : W.b₆ = 0 := by
    rw [WeierstrassCurve.b₆, h3]; linear_combination (2 * W.a₆) * h2
  rw [WeierstrassCurve.Δ, hb2, hb4, hb6]; ring

end TwoNeZeroOrA1OrA3

/-- Pin `WeierstrassCurve.kw_isSeparable_of_aeval_derivative_ne_zero`
(res `S_` line 8751). -/
theorem kw_isSeparable_of_aeval_derivative_ne_zero {L K : Type*} [Field L] [Field K]
    [Algebra L K] {x : K} {f : L[X]} (hroot : aeval x f = 0)
    (hder : aeval x (derivative f) ≠ 0) : IsSeparable L x := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hder (by rw [derivative_zero, _root_.map_zero])
  have hint : _root_.IsIntegral L x := _root_.IsAlgebraic.isIntegral ⟨f, hf0, hroot⟩
  obtain ⟨h, hfgh⟩ := minpoly.dvd L x hroot
  have hg' : aeval x (derivative (minpoly L x)) ≠ 0 := by
    intro h0
    apply hder
    rw [hfgh, derivative_mul, map_add, map_mul, map_mul, h0, minpoly.aeval, zero_mul, zero_mul,
      add_zero]
  have hg'0 : derivative (minpoly L x) ≠ 0 := by
    intro h0
    exact hg' (by rw [h0, _root_.map_zero])
  exact (separable_iff_derivative_ne_zero (minpoly.irreducible hint)).mpr hg'0

/-- Pin `WeierstrassCurve.kw_derivative_mul_sq_sub_mul_derivative_sq_ne_zero`
(res `S_` line 8769). -/
theorem kw_derivative_mul_sq_sub_mul_derivative_sq_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {N D : R[X]} {m : ℕ} (hN : N.Monic) (hNdeg : N.natDegree = 2 * m + 1) (hD : D.Monic)
    (hDdeg : D.natDegree = m) :
    derivative N * D ^ 2 - N * derivative (D ^ 2) ≠ 0 := by
  have hE : (D ^ 2).Monic := hD.pow 2
  have hEdeg : (D ^ 2).natDegree = 2 * m := by rw [hD.natDegree_pow, hDdeg]
  have hN'deg : (derivative N).natDegree ≤ 2 * m :=
    (natDegree_derivative_le N).trans (by rw [hNdeg]; omega)
  have h1 : (derivative N * D ^ 2).coeff (4 * m) = ((2 * m : ℕ) : R) + 1 := by
    rw [show 4 * m = 2 * m + 2 * m by ring, coeff_mul_add_eq_of_natDegree_le hN'deg hEdeg.le,
      coeff_derivative, show N.coeff (2 * m + 1) = 1 from hNdeg ▸ hN.coeff_natDegree,
      show (D ^ 2).coeff (2 * m) = 1 from hEdeg ▸ hE.coeff_natDegree, one_mul, mul_one]
  have h2 : (N * derivative (D ^ 2)).coeff (4 * m) = ((2 * m : ℕ) : R) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hD1 : D = 1 := eq_one_of_monic_natDegree_zero hD hDdeg
      simp [hD1]
    · have hE'deg : (derivative (D ^ 2)).natDegree ≤ 2 * m - 1 :=
        (natDegree_derivative_le _).trans (by rw [hEdeg])
      rw [show 4 * m = (2 * m + 1) + (2 * m - 1) by omega,
        coeff_mul_add_eq_of_natDegree_le hNdeg.le hE'deg, coeff_derivative,
        show N.coeff (2 * m + 1) = 1 from hNdeg ▸ hN.coeff_natDegree,
        show 2 * m - 1 + 1 = 2 * m by omega,
        show (D ^ 2).coeff (2 * m) = 1 from hEdeg ▸ hE.coeff_natDegree, one_mul, one_mul]
      have : ((2 * m - 1 : ℕ) : R) + 1 = ((2 * m : ℕ) : R) := by
        rw [← Nat.cast_succ]; congr 1; omega
      exact this
  intro h
  have hc := congrArg (fun q => q.coeff (4 * m)) h
  simp only [coeff_sub, coeff_zero, h1, h2, add_sub_cancel_left] at hc
  exact one_ne_zero hc

section SeparabilityYGen

variable {F : Type*} [Field F] {W : Affine F}

/-- Pin `WeierstrassCurve.Affine.kw_isSeparable_yGen_of_algebraMap_eq`
(res `S_` line 8809). -/
theorem kw_isSeparable_yGen_of_algebraMap_eq (h2or : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0)
    {M : Type*} [Field M]
    [Algebra M W.FunctionField] (b c : M)
    (hb : algebraMap M W.FunctionField b
      = algebraMap F W.FunctionField W.a₁ * polyToFunctionField W X
          + algebraMap F W.FunctionField W.a₃)
    (hc : algebraMap M W.FunctionField c
      = polyToFunctionField W X ^ 3 + algebraMap F W.FunctionField W.a₂ * polyToFunctionField W X ^ 2
          + algebraMap F W.FunctionField W.a₄ * polyToFunctionField W X
          + algebraMap F W.FunctionField W.a₆) :
    IsSeparable M (yGen W) := by
  have heq := equation_map_polyToFunctionField_yGen (W := W)
  rw [equation_iff] at heq
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  refine kw_isSeparable_of_aeval_derivative_ne_zero (f := X ^ 2 + C b * X - C c) ?_ ?_
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, hb, hc]
    linear_combination heq
  · have hd : derivative (X ^ 2 + C b * X - C c) = C (2 : M) * X + C b := by
      rw [derivative_sub, derivative_add, derivative_X_sq, derivative_mul, derivative_C,
        derivative_C, derivative_X, zero_mul, zero_add, mul_one, sub_zero]
    rw [hd]
    simp only [map_add, map_mul, aeval_X, aeval_C, hb, map_ofNat]
    intro h0
    have hrepr : (2 : W.FunctionField) * yGen W
        + (algebraMap F W.FunctionField W.a₁ * polyToFunctionField W X
            + algebraMap F W.FunctionField W.a₃)
        = algebraMap W.CoordinateRing W.FunctionField
            ((C W.a₁ * X + C W.a₃) • (1 : W.CoordinateRing) + (C (2 : F)) • CoordinateRing.mk W Y) := by
      rw [algebraMap_smul_basis, map_add, map_mul, polyToFunctionField_C, polyToFunctionField_C,
        polyToFunctionField_C, map_ofNat, yGen, yCoord]
      ring
    rw [hrepr, map_eq_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)] at h0
    have hlin : (C W.a₁ * X + C W.a₃ : F[X]) = 0 := (smul_basis_eq_zero h0).1
    have h2 : (C (2 : F) : F[X]) = 0 := (smul_basis_eq_zero h0).2
    rcases h2or with h | h | h
    · exact h (by simpa using h2)
    · exact h (by simpa using congrArg (·.coeff 1) hlin)
    · exact h (by simpa using congrArg (·.coeff 0) hlin)

end SeparabilityYGen

/-! ### The point map attached to a summing-set map equation -/

section PointMap

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

variable (W) in
private abbrev KwVeluMapEquationAt (S : Finset (F × F)) : Prop :=
  ∀ ⦃r s : F⦄, W.toAffine.Equation r s → (∀ Q ∈ S, r ≠ Q.1) →
    (W.veluQuotient S).toAffine.Equation (W.veluX S r) (W.veluY S r s)

variable {S : Finset (F × F)}

theorem kw_velu_map_nonsingular (hmapeq : W.KwVeluMapEquationAt S)
    (hΔ : (W.veluQuotient S).Δ ≠ 0) {x y : F} (hP : W.toAffine.Equation x y)
    (hx : ∀ Q ∈ S, x ≠ Q.1) :
    (W.veluQuotient S).toAffine.Nonsingular (W.veluX S x) (W.veluY S x y) :=
  ((W.veluQuotient S).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (hmapeq hP hx)

noncomputable def kwVeluPointMap (hmapeq : W.KwVeluMapEquationAt S)
    (hΔ : (W.veluQuotient S).Δ ≠ 0) :
    W.toAffine.Point → (W.veluQuotient S).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : ∀ Q ∈ S, x ≠ Q.1 then
      .some _ _ (kw_velu_map_nonsingular hmapeq hΔ h.1 hx)
    else .zero

variable (hmapeq : W.KwVeluMapEquationAt S) (hΔ : (W.veluQuotient S).Δ ≠ 0)

@[simp] lemma kwVeluPointMap_zero : kwVeluPointMap hmapeq hΔ .zero = .zero := rfl

set_option linter.unusedVariables false in
lemma kwVeluPointMap_some_of_mem {x y : F} (h : W.toAffine.Nonsingular x y)
    {Q : F × F} (hQ : Q ∈ S) (hx : x = Q.1) :
    kwVeluPointMap hmapeq hΔ (.some x y h) = 0 := by
  classical
  simp only [kwVeluPointMap]
  exact dif_neg (fun hall => hall Q hQ hx)

lemma kwVeluPointMap_some_of_ne {x y : F} (h : W.toAffine.Nonsingular x y)
    (hx : ∀ Q ∈ S, x ≠ Q.1) :
    kwVeluPointMap hmapeq hΔ (.some x y h)
      = .some _ _ (kw_velu_map_nonsingular hmapeq hΔ h.1 hx) := by
  classical
  simp only [kwVeluPointMap]
  exact dif_pos hx

end PointMap

/-! ### The level polynomial `veluXClearedPoly` -/

section LevelPoly

variable {F : Type*} [Field F] [DecidableEq F]

def veluXDenomPoly (S : Finset (F × F)) : F[X] := ∏ P ∈ S, (X - C P.1)

theorem veluXDenomPoly_monic (S : Finset (F × F)) : (veluXDenomPoly S).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_veluXDenomPoly (S : Finset (F × F)) :
    (veluXDenomPoly S).natDegree = S.card := by
  unfold veluXDenomPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

private lemma cleared_summand_aux {a t u E : F} (ha : a ≠ 0) :
    (t * a + u) * E ^ 2 = (a * E) ^ 2 * (t / a + u / a ^ 2) := by
  have h2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  field_simp

variable (W : WeierstrassCurve F)

def veluXClearedPoly (S : Finset (F × F)) : F[X] :=
  X * (veluXDenomPoly S) ^ 2
    + ∑ P ∈ S, (C (W.veluT P.1 P.2) * (X - C P.1) + C (W.veluU P.1 P.2))
        * (∏ A ∈ S.erase P, (X - C A.1)) ^ 2

theorem eval_veluXClearedPoly (S : Finset (F × F)) {x : F} (hx : ∀ P ∈ S, x ≠ P.1) :
    (veluXClearedPoly W S).eval x = (veluXDenomPoly S).eval x ^ 2 * W.veluX S x := by
  unfold veluXClearedPoly veluXDenomPoly veluX
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_finsetSum, eval_prod, eval_sub, eval_C]
  rw [mul_add, mul_comm _ x, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun P hP => ?_
  have hxP : x - P.1 ≠ 0 := sub_ne_zero.mpr (hx P hP)
  have hprod : ∏ A ∈ S, (x - A.1) = (x - P.1) * ∏ A ∈ S.erase P, (x - A.1) :=
    (Finset.prod_erase_mul S _ hP).symm.trans (mul_comm _ _)
  rw [hprod]
  exact cleared_summand_aux hxP

theorem veluXClearedPoly_monic (S : Finset (F × F)) :
    (veluXClearedPoly W S).Monic ∧ (veluXClearedPoly W S).natDegree = 2 * S.card + 1 := by
  have hD : (veluXDenomPoly (F := F) S).Monic := veluXDenomPoly_monic S
  have hDdeg : (veluXDenomPoly (F := F) S).natDegree = S.card := natDegree_veluXDenomPoly S
  have hlead : (X * (veluXDenomPoly (F := F) S) ^ 2).Monic := monic_X.mul (hD.pow 2)
  have hleaddeg : (X * (veluXDenomPoly (F := F) S) ^ 2).natDegree = 2 * S.card + 1 := by
    rw [natDegree_mul monic_X.ne_zero (hD.pow 2).ne_zero, natDegree_X,
      natDegree_pow, hDdeg]; ring
  have htraildeg : ∀ P ∈ S, ((C (W.veluT P.1 P.2) * (X - C P.1) + C (W.veluU P.1 P.2))
      * (∏ A ∈ S.erase P, (X - C A.1)) ^ 2).natDegree ≤ 2 * S.card - 1 := by
    intro P hP
    have hcard : (S.erase P).card = S.card - 1 := Finset.card_erase_of_mem hP
    have h1 : ((∏ A ∈ S.erase P, ((X : F[X]) - C A.1)) ^ 2).natDegree = 2 * (S.card - 1) := by
      rw [natDegree_pow,
        Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
      simp [hcard]
    have h2 : (C (W.veluT P.1 P.2) * (X - C P.1) + C (W.veluU P.1 P.2)).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans ?_
      refine max_le ?_ (by rw [natDegree_C]; omega)
      exact (natDegree_C_mul_le _ _).trans (le_of_eq (natDegree_X_sub_C (R := F) P.1))
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨P, hP⟩
    calc _ ≤ _ + _ := natDegree_mul_le
      _ ≤ 1 + 2 * (S.card - 1) := add_le_add h2 (le_of_eq h1)
      _ ≤ 2 * S.card - 1 := by omega
  have hlt : (∑ P ∈ S, (C (W.veluT P.1 P.2) * (X - C P.1) + C (W.veluU P.1 P.2))
      * (∏ A ∈ S.erase P, (X - C A.1)) ^ 2).degree < (X * (veluXDenomPoly (F := F) S) ^ 2).degree := by
    rw [Polynomial.degree_eq_natDegree hlead.ne_zero, hleaddeg]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    have hbot : (⊥ : WithBot ℕ) < (2 * S.card + 1 : ℕ) := WithBot.bot_lt_coe _
    refine (Finset.sup_lt_iff hbot).mpr fun P hP => ?_
    refine lt_of_le_of_lt (Polynomial.degree_le_natDegree) ?_
    exact_mod_cast lt_of_le_of_lt (htraildeg P hP) (by omega)
  refine ⟨hlead.add_of_left hlt, ?_⟩
  have hdegeq : (veluXClearedPoly W S).natDegree = (X * (veluXDenomPoly (F := F) S) ^ 2).natDegree :=
    natDegree_add_eq_left_of_degree_lt hlt
  rw [hdegeq, hleaddeg]

end LevelPoly

/-! ### The numerator polynomials of the singleton Vélu functions -/

namespace Affine

variable {F : Type*} [Field F] (W : Affine F)

private def veluXNumPoly (x₀ y₀ : F) : F[X] :=
  X * (X - C x₀) ^ 2 + C (W.veluT x₀ y₀) * (X - C x₀) + C (W.veluU x₀ y₀)

private def veluYNumQ (x₀ y₀ : F) : F[X] :=
  (X - C x₀) ^ 3 - C (2 * W.veluU x₀ y₀) - C (W.veluT x₀ y₀) * (X - C x₀)

private def veluYNumP (x₀ y₀ : F) : F[X] :=
  -(C (W.veluU x₀ y₀) * (C W.a₁ * X + C W.a₃)
    + C (W.veluT x₀ y₀) * (C W.a₁ * (X - C x₀) - C y₀) * (X - C x₀)
    + C (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (X - C x₀))

def veluXFun (x₀ y₀ : F) : W.FunctionField :=
  polyToFunctionField W (W.veluXNumPoly x₀ y₀) / polyToFunctionField W ((X - C x₀) ^ 2)

def veluYNumCR (x₀ y₀ : F) : W.CoordinateRing :=
  W.veluYNumP x₀ y₀ • (1 : W.CoordinateRing) + W.veluYNumQ x₀ y₀ • CoordinateRing.mk W Y

def veluYFun (x₀ y₀ : F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (veluYNumCR W x₀ y₀)
    / polyToFunctionField W ((X - C x₀) ^ 3)

theorem polyToFunctionField_eq_eval_map (p : F[X]) :
    polyToFunctionField W p
      = (p.map (algebraMap F W.FunctionField)).eval (polyToFunctionField W X) := by
  rw [polyToFunctionField_eq_aeval, Polynomial.aeval_def, Polynomial.eval_map]

end Affine

/-! ### The function-field lift of the deficit function -/

section FunctionFieldLift

variable {F : Type*} [Field F] (W : Affine F)

theorem veluDeficitFun_eq_zero_iff_equation (S : Finset (F × F)) :
    W.veluDeficitFun S = 0
      ↔ ((W.map (algebraMap F W.FunctionField)).veluQuotient (W.liftSummingSet S)).toAffine.Equation
          ((W.map (algebraMap F W.FunctionField)).veluX (W.liftSummingSet S)
            (polyToFunctionField W X))
          ((W.map (algebraMap F W.FunctionField)).veluY (W.liftSummingSet S)
            (polyToFunctionField W X) (yGen W)) :=
  ((W.map (algebraMap F W.FunctionField)).veluQuotient_equation_iff_veluDeficit_eq_zero
    (W.liftSummingSet S) (polyToFunctionField W X) (yGen W)).symm

theorem map_veluQuotient_liftSummingSet (S : Finset (F × F)) :
    (W.map (algebraMap F W.FunctionField)).veluQuotient (W.liftSummingSet S)
      = (W.veluQuotient S).map (algebraMap F W.FunctionField) :=
  W.map_veluQuotient (algebraMap F W.FunctionField) S (algebraMap F W.FunctionField).injective

end FunctionFieldLift

/-! ### The generic Vélu functions -/

section GenericVeluFun

variable {F : Type*} [Field F] (W : Affine F) (S : Finset (F × F))

def kwVeluXGenFun : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).veluX (W.liftSummingSet S) (polyToFunctionField W X)

def kwVeluYGenFun : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).veluY (W.liftSummingSet S)
    (polyToFunctionField W X) (yGen W)

variable {W S}

theorem kw_kwVeluXGenFun_notMem_of_not_isFinitePlace
    (v : Place F W.FunctionField) (hv : ¬ IsFinitePlace v) :
    kwVeluXGenFun W S ∉ v.toValuationSubring := by
  intro hmem
  have hdiff : kwVeluXGenFun W S - polyToFunctionField W X ∈ v.toValuationSubring :=
    veluX_sub_self_genericPoint_mem_of_not_isFinitePlace (W := W) (v := v) hv S
  have hx : polyToFunctionField W X ∈ v.toValuationSubring := by
    have h := sub_mem hmem hdiff
    simp only [sub_sub_cancel] at h
    exact h
  have hxneg := ord_X_neg_of_not_isFinitePlace (W := W) (v := v) hv
  exact absurd
    ((v.mem_iff_ord_nonneg (polyToFunctionField_ne_zero Polynomial.X_ne_zero)).mp hx)
    (not_le.mpr hxneg)

end GenericVeluFun

section ExistsEquationAvoids

variable {F : Type*} [Field F] [IsAlgClosed F]

theorem kw_exists_equation_avoids (W : WeierstrassCurve F) (T : Finset F) :
    ∃ r s : F, W.toAffine.Equation r s ∧ ∀ a ∈ T, r ≠ a := by
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset T
  obtain ⟨s, hs⟩ := W.toAffine.exists_equation r
  exact ⟨r, s, hs, fun a ha hra => hr (hra ▸ ha)⟩

end ExistsEquationAvoids

section TranscendentalGenFun

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
variable [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine]
  [AbelTheorem W.toAffine]

theorem kw_transcendental_kwVeluXGenFun (S : Finset (F × F)) :
    Transcendental F (kwVeluXGenFun W.toAffine S) := by
  rw [transcendental_iff]
  intro q hq
  by_contra hq0
  have hint : _root_.IsIntegral F (kwVeluXGenFun W.toAffine S) :=
    isAlgebraic_iff_isIntegral.mp ⟨q, hq0, hq⟩
  have hdeg : (minpoly F (kwVeluXGenFun W.toAffine S)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.degree_eq_one_iff.mp hdeg
  refine kw_kwVeluXGenFun_notMem_of_not_isFinitePlace (S := S)
    (InfinitePlace.place : Place F W.toAffine.FunctionField) InfinitePlace.not_isFinitePlace ?_
  rw [← hc]
  exact (InfinitePlace.place : Place F W.toAffine.FunctionField).algebraMap_mem' c

theorem kw_aeval_kwVeluXGenFun_injective (S : Finset (F × F)) :
    Function.Injective (Polynomial.aeval (R := F) (kwVeluXGenFun W.toAffine S)) :=
  (injective_iff_map_eq_zero _).mpr fun q hq =>
    transcendental_iff.mp (kw_transcendental_kwVeluXGenFun (W := W) S) q hq

end TranscendentalGenFun

/-! ### The cleared identity and the denominator non-vanishing -/

section MapPoly

variable {F : Type*} [Field F] [DecidableEq F] {F' : Type*} [Field F'] [DecidableEq F']

theorem kw_map_veluXDenomPoly (f : F →+* F') (hf : Function.Injective f)
    (S : Finset (F × F)) :
    (veluXDenomPoly S).map f
      = veluXDenomPoly (S.map ⟨Prod.map f f, hf.prodMap hf⟩) := by
  unfold veluXDenomPoly
  rw [Polynomial.map_prod, Finset.prod_map]
  simp only [Polynomial.map_sub, map_X, map_C, Function.Embedding.coeFn_mk, Prod.map_fst]

theorem kw_map_veluXClearedPoly (f : F →+* F') (hf : Function.Injective f)
    (W : WeierstrassCurve F) (S : Finset (F × F)) :
    (veluXClearedPoly W S).map f
      = veluXClearedPoly (W.map f) (S.map ⟨Prod.map f f, hf.prodMap hf⟩) := by
  unfold veluXClearedPoly
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X,
    kw_map_veluXDenomPoly f hf, Polynomial.map_sum, Finset.sum_map]
  congr 1
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [← Finset.map_erase]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub,
    map_X, map_C, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
    map_veluT, map_veluU, Polynomial.map_prod, Finset.prod_map]

end MapPoly

section ClearedIdentity

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) (S : Finset (F × F))

theorem kw_kwVeluXGenFun_mul_denom_sq_eq_cleared :
    kwVeluXGenFun W S * polyToFunctionField W (veluXDenomPoly S) ^ 2
      = polyToFunctionField W (veluXClearedPoly W S) := by
  have hinj := (algebraMap F W.FunctionField).injective
  have hav : ∀ P ∈ W.liftSummingSet S, polyToFunctionField W X ≠ P.1 :=
    polyToFunctionField_X_ne_of_mem_liftSummingSet W
  have heval := eval_veluXClearedPoly (W.map (algebraMap F W.FunctionField))
    (W.liftSummingSet S) (x := polyToFunctionField W X) hav
  rw [show W.liftSummingSet S
        = S.map ⟨Prod.map (algebraMap F W.FunctionField) (algebraMap F W.FunctionField),
            hinj.prodMap hinj⟩ from rfl,
    ← kw_map_veluXClearedPoly _ hinj, ← kw_map_veluXDenomPoly _ hinj,
    ← polyToFunctionField_eq_eval_map, ← polyToFunctionField_eq_eval_map] at heval
  rw [heval]
  exact mul_comm _ _

theorem kw_eval_veluXClearedPoly_ne_zero_of_mem (hset : W.IsOddVeluSet S)
    {A : F × F} (hA : A ∈ S) : (veluXClearedPoly W S).eval A.1 ≠ 0 := by
  unfold veluXClearedPoly
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_finsetSum, eval_sub, eval_C, eval_prod]
  have hD : (veluXDenomPoly S).eval A.1 = 0 := by
    unfold veluXDenomPoly
    rw [eval_prod]
    exact Finset.prod_eq_zero hA (by simp)
  rw [hD, zero_pow two_ne_zero, mul_zero, zero_add]
  rw [Finset.sum_eq_single A (fun B hB hBA => ?_) (fun h => absurd hA h)]
  · simp only [sub_self, mul_zero, zero_add]
    refine mul_ne_zero ?_ (pow_ne_zero 2 ?_)
    · rw [veluU]; exact pow_ne_zero 2 (hset.gy_ne_zero A hA)
    · exact Finset.prod_ne_zero_iff.mpr fun C hC =>
        sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hC).1
          (hset.x_injOn C (Finset.mem_of_mem_erase hC) A hA h.symm)
  ·
    have hAerase : A ∈ S.erase B := Finset.mem_erase.mpr ⟨fun h => hBA h.symm, hA⟩
    exact mul_eq_zero_of_right _
      (pow_eq_zero_iff two_ne_zero |>.mpr (Finset.prod_eq_zero hAerase (by simp)))

end ClearedIdentity

/-! ### The deficit-fun specialisation and the odd-order discharge -/

section SpecializesConst

variable {F : Type*} [Field F] [DecidableEq F]

theorem veluDeficitFunSpecializesConstAt_of_dedekind
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    (p : ℕ) : VeluDeficitFunSpecializesConstAt F p :=
  veluDeficitFunSpecializesConstAt_of_evalAtPlace hDD
    (fun W hΔ x₀ y₀ h₀ _hord r s hrs hav => by
      haveI := hDD W hΔ
      exact Affine.evalAt_veluDeficitFun_placeOfEquation hrs hav)

end SpecializesConst

section UnconditionalSpecializes

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

private theorem hDDTerm :
    ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing :=
  fun _W hΔ => Affine.CoordinateRing.isDedekindDomain_of_Δ_ne_zero hΔ

variable (F) in
theorem veluDeficitFunSpecializesConstAt_unconditional' (p : ℕ) :
    VeluDeficitFunSpecializesConstAt F p :=
  veluDeficitFunSpecializesConstAt_of_dedekind (F := F)
    (fun _W hΔ => Affine.CoordinateRing.isDedekindDomain_of_Δ_ne_zero hΔ) p

end UnconditionalSpecializes

section OddConstancy

variable (F : Type*) [Field F] [DecidableEq F] [IsAlgClosed F] in
theorem kw_veluDeficitIsConstantAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitIsConstantAt F p :=
  veluDeficitIsConstantAt_of_ordNonneg_of_dedekind (kw_veluHPDSupplier (F := F)) kw_hDDTerm
    (kw_veluDeficitFunOrdNonnegAt_odd F kw_hDDTerm hp3 hpodd)

variable (F : Type*) [Field F] [DecidableEq F] [IsAlgClosed F] in
theorem kw_veluDeficitConstancyAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitConstancyAt F p := by
  haveI : Infinite F := kw_infinite_of_isAlgClosed
  refine veluDeficitConstancyAt_of_isConstant_of_constantZero F
    (kw_veluDeficitIsConstantAt_odd F hp3 hpodd)
    (kw_veluDeficitConstantIsZeroAt_odd hp3 hpodd ?_)
  refine kw_veluDeficitCrossQuadProdDegLtAt_odd hp3 hpodd
    (kw_veluDeficitCrossQuadCubeBetaDegLtAt_odd hp3 hpodd
      (kw_veluDeficitCrossQuadBetaOnlyDegLtAt_odd
        (veluDeficitCrossQuadBetaSDecompDegLtAt_of_betaSq_of_alphaBeta
          (kw_veluDeficitCrossQuadBetaSqDecompDegLtAt_odd hp3 hpodd)
          (kw_veluDeficitCrossQuadAlphaBetaDecompDegLtAt_odd hp3 hpodd))))

end OddConstancy

/-! ### The odd-order summing-set map equation -/

section MapEquationOdd

theorem kw_kwVeluMapEquationAt_oddOrderSummingSet_odd
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W : WeierstrassCurve F} {Q : W.toAffine.Point} {p : ℕ}
    (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p) (hΔW : W.Δ ≠ 0) :
    W.KwVeluMapEquationAt (W.oddOrderSummingSet Q ((p - 1) / 2)) := by
  haveI : W.IsElliptic := ⟨(Ne.isUnit hΔW)⟩
  intro r s hrs hav
  have hQ : addOrderOf Q = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨k, hk⟩ := hpodd
    rw [hord, hk]; omega
  exact velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed W ((p - 1) / 2) Q hQ hrs hav

end MapEquationOdd

/-! ### The `vgffhso` anchor and the vanishing of the deficit function -/

theorem kw_vgffhso_axiomAnchor : True :=
  have _h₁ : True = True := propext Iff.rfl
  have _h₂ : ℕ := Classical.choice ⟨0⟩
  have _h₃ : Quot.mk (fun (_ _ : ℕ) => True) 0 = Quot.mk (fun (_ _ : ℕ) => True) 1 :=
    Quot.sound trivial
  trivial

section DeficitZeroOdd

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {W : WeierstrassCurve F} {Q : W.toAffine.Point} {p : ℕ}

theorem kw_veluDeficitFun_oddOrderSummingSet_eq_zero_odd
    (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p) (hΔW : W.Δ ≠ 0) :
    W.toAffine.veluDeficitFun (W.oddOrderSummingSet Q ((p - 1) / 2)) = 0 := by
  have _ := kw_vgffhso_axiomAnchor
  have hQ0 : Q ≠ 0 := by intro h; rw [h, addOrderOf_zero] at hord; omega
  obtain ⟨x₀, y₀, h₀, rfl, -⟩ := exists_some_of_ne_zero hQ0
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2) with hS
  haveI : HasPrincipalDivisors F W.toAffine.FunctionField := kw_veluHPDSupplier (F := F) W hΔW
  haveI : IsDedekindDomain W.toAffine.CoordinateRing :=
    Affine.CoordinateRing.isDedekindDomain_of_Δ_ne_zero hΔW
  have hreg := kw_veluDeficitFunOrdNonnegAt_odd (F := F)
    (fun V hΔV => Affine.CoordinateRing.isDedekindDomain_of_Δ_ne_zero hΔV)
    hp3 hpodd W hΔW x₀ y₀ h₀ hord
  obtain ⟨c, hc⟩ := Affine.functionField_liouville_of_equation (W := W.toAffine) h₀.1 hreg
  obtain ⟨r, s, hrs, hrav⟩ := kw_exists_equation_avoids W (S.image Prod.fst)
  have hav : ∀ A ∈ S, r ≠ A.1 := fun A hA =>
    hrav A.1 (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
  have hspec := veluDeficitFunSpecializesConstAt_unconditional' F p W hΔW x₀ y₀ h₀ hord c hc
    hrs hav
  have hcst := kw_veluDeficitConstancyAt_odd (F := F) hp3 hpodd W hΔW x₀ y₀ h₀ hord hrs hav
  rw [hc, show c = 0 from hspec.symm.trans hcst]
  exact (algebraMap F W.toAffine.FunctionField).map_zero

theorem kw_equation_map_veluQuotient_kwVeluGenFun_odd
    (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p) (hΔW : W.Δ ≠ 0) :
    ((W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).map
        (algebraMap F W.toAffine.FunctionField)).toAffine.Equation
      (kwVeluXGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2)))
      (kwVeluYGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2))) := by
  set S := W.oddOrderSummingSet Q ((p - 1) / 2)
  have key := (W.toAffine.veluDeficitFun_eq_zero_iff_equation S).mp
    (kw_veluDeficitFun_oddOrderSummingSet_eq_zero_odd hp3 hpodd hord hΔW)
  rwa [W.toAffine.map_veluQuotient_liftSummingSet S] at key

end DeficitZeroOdd

/-! ### The coordinate-ring and function-field homomorphisms -/

section CoordHomOdd

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
variable [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine]
  [AbelTheorem W.toAffine]
variable {Q : W.toAffine.Point} {p : ℕ}
variable (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p)

local notation "S_Q" => W.oddOrderSummingSet Q ((p - 1) / 2)
set_option quotPrecheck false in
local notation "V'" => (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine

include hp3 hpodd hord in
theorem kw_eval₂_polynomial_kwVeluGenFun_odd :
    ((W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.polynomial).eval₂
        (Polynomial.aeval
            (kwVeluXGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2))) :
          F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom
        (kwVeluYGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2))) = 0 := by
  have heq := kw_equation_map_veluQuotient_kwVeluGenFun_odd hp3 hpodd hord
    W.toAffine.isUnit_Δ.ne_zero
  rw [equation_iff'] at heq
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X]
  linear_combination heq

include hp3 hpodd hord in
noncomputable def kw_oddOrderSummingSetCoordHom_odd :
    (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.CoordinateRing
      →ₐ[F] W.toAffine.FunctionField where
  __ := AdjoinRoot.lift
    (Polynomial.aeval (kwVeluXGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2))) :
      F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom
    (kwVeluYGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2)))
    (kw_eval₂_polynomial_kwVeluGenFun_odd hp3 hpodd hord)
  commutes' c := by
    show AdjoinRoot.lift _ _ (kw_eval₂_polynomial_kwVeluGenFun_odd hp3 hpodd hord)
      (algebraMap F _ c) = algebraMap F W.toAffine.FunctionField c
    rw [CoordinateRing.algebraMap_eq_mk_C_C, AdjoinRoot.lift_mk, eval₂_C]
    exact Polynomial.aeval_C _ c

include hp3 hpodd hord in
theorem kw_oddOrderSummingSetCoordHom_odd_mk (g : F[X][Y]) :
    kw_oddOrderSummingSetCoordHom_odd hp3 hpodd hord
        (CoordinateRing.mk
          (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine g)
      = g.eval₂
          (Polynomial.aeval
              (kwVeluXGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2))) :
            F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom
          (kwVeluYGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2))) :=
  AdjoinRoot.lift_mk (kw_eval₂_polynomial_kwVeluGenFun_odd hp3 hpodd hord) g

include hp3 hpodd hord in
theorem kw_oddOrderSummingSetCoordHom_odd_comp_algebraMap :
    (kw_oddOrderSummingSetCoordHom_odd hp3 hpodd hord).toRingHom.comp
        (algebraMap F[X]
          (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.CoordinateRing)
      = (Polynomial.aeval
            (kwVeluXGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2))) :
          F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom := by
  refine RingHom.ext fun q => ?_
  show kw_oddOrderSummingSetCoordHom_odd hp3 hpodd hord (algebraMap F[X] _ q) = _
  rw [algebraMap_polynomial_eq_mk_C, kw_oddOrderSummingSetCoordHom_odd_mk, eval₂_C]

include hp3 hpodd hord in
theorem kw_oddOrderSummingSetCoordHom_odd_injective :
    Function.Injective (kw_oddOrderSummingSetCoordHom_odd (W := W) hp3 hpodd hord) := by
  have hker : RingHom.ker (kw_oddOrderSummingSetCoordHom_odd (W := W) hp3 hpodd hord).toRingHom
      = ⊥ := by
    haveI : Module.Finite F[X]
        (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.CoordinateRing :=
      Module.Finite.of_basis (CoordinateRing.basis
        (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine)
    refine Ideal.eq_bot_of_under_eq_bot (R := F[X]) ?_
    rw [Ideal.under_def, RingHom.comap_ker, kw_oddOrderSummingSetCoordHom_odd_comp_algebraMap,
      ← RingHom.injective_iff_ker_eq_bot]
    exact kw_aeval_kwVeluXGenFun_injective (W := W) _
  exact (RingHom.injective_iff_ker_eq_bot
    (kw_oddOrderSummingSetCoordHom_odd (W := W) hp3 hpodd hord).toRingHom).mpr hker

include hp3 hpodd hord in
noncomputable def kw_oddOrderSummingSetFunctionFieldHom_odd :
    (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.FunctionField
      →ₐ[F] W.toAffine.FunctionField :=
  IsFractionRing.liftAlgHom (kw_oddOrderSummingSetCoordHom_odd_injective hp3 hpodd hord)

include hp3 hpodd hord in
theorem kw_oddOrderSummingSetFunctionFieldHom_odd_algebraMap
    (r : (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.CoordinateRing) :
    kw_oddOrderSummingSetFunctionFieldHom_odd hp3 hpodd hord
        (algebraMap
          (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.CoordinateRing
          (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.FunctionField r)
      = kw_oddOrderSummingSetCoordHom_odd hp3 hpodd hord r :=
  IsFractionRing.lift_algebraMap (kw_oddOrderSummingSetCoordHom_odd_injective hp3 hpodd hord) r

include hp3 hpodd hord in
theorem kw_oddOrderSummingSetFunctionFieldHom_odd_polyToFunctionField_X :
    kw_oddOrderSummingSetFunctionFieldHom_odd (W := W) hp3 hpodd hord
        (polyToFunctionField
          (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine X)
      = kwVeluXGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2)) := by
  rw [polyToFunctionField_apply, kw_oddOrderSummingSetFunctionFieldHom_odd_algebraMap,
    algebraMap_polynomial_eq_mk_C, kw_oddOrderSummingSetCoordHom_odd_mk, eval₂_C]
  exact Polynomial.aeval_X _

include hp3 hpodd hord in
theorem kw_oddOrderSummingSetFunctionFieldHom_odd_yGen :
    kw_oddOrderSummingSetFunctionFieldHom_odd (W := W) hp3 hpodd hord
        (yGen (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine)
      = kwVeluYGenFun W.toAffine (W.oddOrderSummingSet Q ((p - 1) / 2)) := by
  show kw_oddOrderSummingSetFunctionFieldHom_odd hp3 hpodd hord
      (algebraMap _ _ (CoordinateRing.mk _ Y)) = _
  rw [kw_oddOrderSummingSetFunctionFieldHom_odd_algebraMap,
    kw_oddOrderSummingSetCoordHom_odd_mk]
  exact eval₂_X _ _

end CoordHomOdd

/-! ### Integrality and finiteness of the odd-order function-field hom -/

section IntegralityOdd

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
variable [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine]
  [AbelTheorem W.toAffine]
variable {Q : W.toAffine.Point} {p : ℕ}
variable (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p)

local notation "S_Q" => W.oddOrderSummingSet Q ((p - 1) / 2)
set_option quotPrecheck false in
local notation "V'" => (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine
local notation "ι" => kw_oddOrderSummingSetFunctionFieldHom_odd (W := W) hp3 hpodd hord

include hp3 hpodd hord in
theorem kw_isIntegral_polyToFunctionField_X_oddOrderSummingSet_odd :
    letI : Algebra (V').FunctionField W.toAffine.FunctionField := (ι).toRingHom.toAlgebra
    _root_.IsIntegral (V').FunctionField (polyToFunctionField W.toAffine X) := by
  letI : Algebra (V').FunctionField W.toAffine.FunctionField := (ι).toRingHom.toAlgebra
  refine ⟨(veluXClearedPoly W S_Q).map (algebraMap F (V').FunctionField)
      - C (polyToFunctionField V' X)
          * ((veluXDenomPoly S_Q).map (algebraMap F (V').FunctionField)) ^ 2,
    ?_, ?_⟩
  · rw [sub_eq_add_neg]
    refine (((veluXClearedPoly_monic W S_Q).1).map _).add_of_left ?_
    rw [Polynomial.degree_neg]
    calc (C (polyToFunctionField V' X)
            * ((veluXDenomPoly S_Q).map (algebraMap F (V').FunctionField)) ^ 2).degree
        ≤ _ := Polynomial.degree_le_natDegree
      _ ≤ ((2 * (S_Q).card : ℕ) : WithBot ℕ) := by
          refine Nat.cast_le.mpr (le_trans Polynomial.natDegree_mul_le ?_)
          rw [Polynomial.natDegree_C, zero_add, natDegree_pow,
            (veluXDenomPoly_monic S_Q).natDegree_map
              (algebraMap F (V').FunctionField), natDegree_veluXDenomPoly]
      _ < _ := by
          rw [((veluXClearedPoly_monic W S_Q).1).degree_map,
            Polynomial.degree_eq_natDegree ((veluXClearedPoly_monic W S_Q).1).ne_zero,
            (veluXClearedPoly_monic W S_Q).2]
          exact_mod_cast Nat.lt_succ_self _
  · simp only [eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_map]
    rw [show ((algebraMap (V').FunctionField W.toAffine.FunctionField).comp
            (algebraMap F (V').FunctionField))
          = algebraMap F W.toAffine.FunctionField from
        RingHom.ext fun c => (ι).commutes c,
      ← Polynomial.eval_map, ← polyToFunctionField_eq_eval_map,
      ← Polynomial.eval_map, ← polyToFunctionField_eq_eval_map,
      show (algebraMap (V').FunctionField W.toAffine.FunctionField) (polyToFunctionField V' X)
          = kwVeluXGenFun W.toAffine S_Q from
        kw_oddOrderSummingSetFunctionFieldHom_odd_polyToFunctionField_X hp3 hpodd hord,
      kw_kwVeluXGenFun_mul_denom_sq_eq_cleared, sub_self]

include hp3 hpodd hord in
theorem kw_adjoin_X_yGen_eq_top_oddOrderSummingSet_odd :
    letI : Algebra (V').FunctionField W.toAffine.FunctionField := (ι).toRingHom.toAlgebra
    IntermediateField.adjoin (V').FunctionField
        ({polyToFunctionField W.toAffine X, yGen W.toAffine} : Set W.toAffine.FunctionField)
      = ⊤ := by
  letI : Algebra (V').FunctionField W.toAffine.FunctionField := (ι).toRingHom.toAlgebra
  rw [eq_top_iff]
  rintro z -
  set L := IntermediateField.adjoin (V').FunctionField
    ({polyToFunctionField W.toAffine X, yGen W.toAffine} : Set W.toAffine.FunctionField)
  have hconst : ∀ c : F, algebraMap F W.toAffine.FunctionField c ∈ L := fun c => by
    rw [← (ι).commutes c]; exact L.algebraMap_mem _
  have hxmem : polyToFunctionField W.toAffine X ∈ L :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hymem : yGen W.toAffine ∈ L :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  have hpoly : ∀ q : F[X], polyToFunctionField W.toAffine q ∈ L := fun q => by
    induction q using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, polyToFunctionField_C]
        exact mul_mem (hconst c) (pow_mem hxmem n)
  have hcr : ∀ r : W.toAffine.CoordinateRing,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈ L := fun r => by
    obtain ⟨a, b, rfl⟩ := exists_smul_basis_eq r
    rw [algebraMap_smul_basis]
    exact add_mem (hpoly a) (mul_mem (hpoly b) hymem)
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  rw [← hab]; exact div_mem (hcr a) (hcr b)

include hp3 hpodd hord in
theorem kw_oddOrderSummingSetFunctionFieldHom_odd_finiteAlong :
    FiniteAlong F (kw_oddOrderSummingSetFunctionFieldHom_odd (W := W) hp3 hpodd hord) := by
  letI : Algebra (V').FunctionField W.toAffine.FunctionField := (ι).toRingHom.toAlgebra
  show Module.Finite (V').FunctionField W.toAffine.FunctionField
  have hxint := kw_isIntegral_polyToFunctionField_X_oddOrderSummingSet_odd hp3 hpodd hord
  set Lx := IntermediateField.adjoin (V').FunctionField
    ({polyToFunctionField W.toAffine X} : Set W.toAffine.FunctionField) with hLx
  haveI hxfd : FiniteDimensional (V').FunctionField Lx :=
    IntermediateField.adjoin.finiteDimensional hxint
  have hyint : _root_.IsIntegral Lx (yGen W.toAffine) := by
    have hyFx : _root_.IsIntegral F[X] (yGen W.toAffine) := by
      haveI : Module.Finite F[X] W.toAffine.CoordinateRing :=
        Module.Finite.of_basis (CoordinateRing.basis W.toAffine)
      show _root_.IsIntegral F[X]
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (CoordinateRing.mk W.toAffine Y))
      exact ((Algebra.IsIntegral.of_finite F[X] W.toAffine.CoordinateRing).isIntegral _).map
        (IsScalarTower.toAlgHom F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField)
    have halg : ∀ r : F[X], (algebraMap F[X] W.toAffine.FunctionField) r ∈ Lx := by
      intro r
      induction r using Polynomial.induction_on' with
      | add f g hf hg => rw [map_add]; exact add_mem hf hg
      | monomial n c =>
          rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow,
            show algebraMap F[X] W.toAffine.FunctionField (C c)
              = algebraMap F W.toAffine.FunctionField c from rfl,
            show algebraMap F[X] W.toAffine.FunctionField X
              = polyToFunctionField W.toAffine X from rfl,
            ← (ι).commutes c]
          exact mul_mem (IntermediateField.algebraMap_mem _ _)
            (pow_mem (IntermediateField.mem_adjoin_simple_self _ _) n)
    obtain ⟨q, hqmon, hq0⟩ := hyFx
    let φ : F[X] →+* Lx :=
      (algebraMap F[X] W.toAffine.FunctionField).codRestrict Lx.toSubring halg
    refine ⟨q.map φ, hqmon.map φ, ?_⟩
    rw [Polynomial.eval₂_map,
      show (algebraMap Lx W.toAffine.FunctionField).comp φ
          = algebraMap F[X] W.toAffine.FunctionField from RingHom.ext fun _ => rfl]
    exact hq0
  have hyint' : _root_.IsIntegral (V').FunctionField (yGen W.toAffine) :=
    haveI : Algebra.IsIntegral (V').FunctionField Lx :=
      Algebra.IsIntegral.of_finite (V').FunctionField Lx
    isIntegral_trans (yGen W.toAffine) hyint
  have hfd : FiniteDimensional (V').FunctionField
      (IntermediateField.adjoin (V').FunctionField
        ({polyToFunctionField W.toAffine X, yGen W.toAffine}
          : Set W.toAffine.FunctionField)) := by
    refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
    rcases hz with rfl | rfl
    · exact hxint
    · exact hyint'
  rw [kw_adjoin_X_yGen_eq_top_oddOrderSummingSet_odd hp3 hpodd hord] at hfd
  exact (IntermediateField.topEquiv (F := (V').FunctionField)
    (E := W.toAffine.FunctionField)).toLinearEquiv.finiteDimensional

include hp3 hpodd hord in
theorem kw_oddOrderSummingSetFunctionFieldHom_odd_isIntegral :
    (kw_oddOrderSummingSetFunctionFieldHom_odd (W := W) hp3 hpodd hord).toRingHom.IsIntegral
    := by
  letI : Algebra (V').FunctionField W.toAffine.FunctionField := (ι).toRingHom.toAlgebra
  haveI : Module.Finite (V').FunctionField W.toAffine.FunctionField :=
    kw_oddOrderSummingSetFunctionFieldHom_odd_finiteAlong hp3 hpodd hord
  exact fun z => (Algebra.IsIntegral.of_finite _ _).isIntegral z

include hp3 hpodd hord in
theorem kw_isSeparable_polyToFunctionField_X_oddOrderSummingSet_odd :
    letI : Algebra (V').FunctionField W.toAffine.FunctionField := (ι).toRingHom.toAlgebra
    IsSeparable (V').FunctionField (polyToFunctionField W.toAffine X) := by
  letI : Algebra (V').FunctionField W.toAffine.FunctionField := (ι).toRingHom.toAlgebra
  have hφ : (algebraMap (V').FunctionField W.toAffine.FunctionField).comp
        (algebraMap F (V').FunctionField) = algebraMap F W.toAffine.FunctionField :=
    RingHom.ext fun c => (ι).commutes c
  have hX' : algebraMap (V').FunctionField W.toAffine.FunctionField (polyToFunctionField V' X)
      = kwVeluXGenFun W.toAffine S_Q :=
    kw_oddOrderSummingSetFunctionFieldHom_odd_polyToFunctionField_X hp3 hpodd hord
  have hev : ∀ q : F[X], aeval (polyToFunctionField W.toAffine X)
      (q.map (algebraMap F (V').FunctionField)) = polyToFunctionField W.toAffine q := by
    intro q
    rw [aeval_def, eval₂_map, hφ, ← eval_map, ← polyToFunctionField_eq_eval_map]
  have hNmon := veluXClearedPoly_monic W S_Q
  have hclear : kwVeluXGenFun W.toAffine S_Q
        * polyToFunctionField W.toAffine (veluXDenomPoly S_Q ^ 2)
      = polyToFunctionField W.toAffine (veluXClearedPoly W S_Q) := by
    rw [map_pow]; exact kw_kwVeluXGenFun_mul_denom_sq_eq_cleared W.toAffine S_Q
  refine kw_isSeparable_of_aeval_derivative_ne_zero
    (f := (veluXClearedPoly W S_Q).map (algebraMap F (V').FunctionField)
      - C (polyToFunctionField V' X) * (veluXDenomPoly S_Q ^ 2).map (algebraMap F (V').FunctionField))
    ?_ ?_
  · simp only [map_sub, map_mul, aeval_C, hev, hX']
    linear_combination -hclear
  · have hder : aeval (polyToFunctionField W.toAffine X)
          (derivative ((veluXClearedPoly W S_Q).map (algebraMap F (V').FunctionField)
            - C (polyToFunctionField V' X)
              * (veluXDenomPoly S_Q ^ 2).map (algebraMap F (V').FunctionField)))
          * polyToFunctionField W.toAffine (veluXDenomPoly S_Q ^ 2)
        = polyToFunctionField W.toAffine (derivative (veluXClearedPoly W S_Q) * veluXDenomPoly S_Q ^ 2
            - veluXClearedPoly W S_Q * derivative (veluXDenomPoly S_Q ^ 2)) := by
      rw [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add, derivative_map,
        derivative_map]
      simp only [map_sub, map_mul, aeval_C, hev, hX']
      linear_combination
        (-(polyToFunctionField W.toAffine (derivative (veluXDenomPoly S_Q ^ 2)))) * hclear
    have hkey : derivative (veluXClearedPoly W S_Q) * veluXDenomPoly S_Q ^ 2
        - veluXClearedPoly W S_Q * derivative (veluXDenomPoly S_Q ^ 2) ≠ 0 :=
      kw_derivative_mul_sq_sub_mul_derivative_sq_ne_zero hNmon.1 hNmon.2
        (veluXDenomPoly_monic S_Q) (natDegree_veluXDenomPoly S_Q)
    intro h0
    refine polyToFunctionField_ne_zero (W := W.toAffine) hkey ?_
    rw [← hder, h0, zero_mul]

include hp3 hpodd hord in

theorem kw_oddOrderSummingSetFunctionFieldHom_odd_separableAlong :
    SeparableAlong F (ι) := by
  letI : Algebra (V').FunctionField W.toAffine.FunctionField := (ι).toRingHom.toAlgebra
  show Algebra.IsSeparable (V').FunctionField W.toAffine.FunctionField
  have hx := kw_isSeparable_polyToFunctionField_X_oddOrderSummingSet_odd hp3 hpodd hord
  have hy : IsSeparable (V').FunctionField (yGen W.toAffine) := by
    set M := IntermediateField.adjoin (V').FunctionField
      ({polyToFunctionField W.toAffine X} : Set W.toAffine.FunctionField) with hM
    have hxM : polyToFunctionField W.toAffine X ∈ M := IntermediateField.mem_adjoin_simple_self _ _
    have hFM : ∀ a : F, algebraMap F W.toAffine.FunctionField a ∈ M := fun a => by
      rw [← (ι).commutes a]; exact IntermediateField.algebraMap_mem _ _
    have hbM : algebraMap F W.toAffine.FunctionField W.toAffine.a₁ * polyToFunctionField W.toAffine X
        + algebraMap F W.toAffine.FunctionField W.toAffine.a₃ ∈ M :=
      add_mem (mul_mem (hFM _) hxM) (hFM _)
    have hcM : polyToFunctionField W.toAffine X ^ 3
        + algebraMap F W.toAffine.FunctionField W.toAffine.a₂ * polyToFunctionField W.toAffine X ^ 2
        + algebraMap F W.toAffine.FunctionField W.toAffine.a₄ * polyToFunctionField W.toAffine X
        + algebraMap F W.toAffine.FunctionField W.toAffine.a₆ ∈ M :=
      add_mem (add_mem (add_mem (pow_mem hxM 3) (mul_mem (hFM _) (pow_mem hxM 2)))
        (mul_mem (hFM _) hxM)) (hFM _)
    have hyM : IsSeparable M (yGen W.toAffine) :=
      kw_isSeparable_yGen_of_algebraMap_eq (W := W.toAffine)
        (two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero' W
          (WeierstrassCurve.isUnit_Δ (W := W.toAffine)).ne_zero)
        (⟨_, hbM⟩ : M) (⟨_, hcM⟩ : M) rfl rfl
    haveI : Algebra.IsSeparable (V').FunctionField M :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (V').FunctionField
        W.toAffine.FunctionField).mpr hx
    exact IsSeparable.of_algebra_isSeparable_of_isSeparable (V').FunctionField hyM
  have hpair := IntermediateField.isSeparable_adjoin_pair_of_isSeparable
    (F := (V').FunctionField) (E := W.toAffine.FunctionField) hx hy
  rw [kw_adjoin_X_yGen_eq_top_oddOrderSummingSet_odd hp3 hpodd hord] at hpair
  exact Algebra.IsSeparable.of_algHom (V').FunctionField _
    (IntermediateField.topEquiv (F := (V').FunctionField) (E := W.toAffine.FunctionField)).symm.toAlgHom

end IntegralityOdd

/-! ### The `s2c` kernel arithmetic -/

lemma zsmul_eq_emod_zsmul_of_nsmul_eq_zero {G : Type*} [AddCommGroup G] {g : G} {p : ℕ}
    (hp : p • g = 0) (m : ℤ) : m • g = (m % (p : ℤ)) • g := by
  have hp' : (p : ℤ) • g = 0 := by rw [natCast_zsmul]; exact hp
  conv_lhs => rw [show m = (p : ℤ) * (m / (p : ℤ)) + m % (p : ℤ) from
    (Int.mul_ediv_add_emod m (p : ℤ)).symm]
  rw [add_zsmul, mul_comm ((p : ℤ)) (m / (p : ℤ)), ← smul_smul, hp', smul_zero, zero_add]

section S2cKernel

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
variable {Q : W.toAffine.Point} {n : ℕ}

theorem s2c_exists_fst_eq_of_mem_zmultiples (hord : addOrderOf Q = 2 * n + 1)
    {x y : F} {h : W.toAffine.Nonsingular x y}
    (hP : (Point.some x y h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q) :
    ∃ A ∈ W.oddOrderSummingSet Q n, x = A.1 := by
  have hpQ : (2 * n + 1) • Q = 0 := hord ▸ addOrderOf_nsmul_eq_zero Q
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
  have hP0 : (m % ((2 * n + 1 : ℕ) : ℤ)) • Q ≠ 0 := by
    rw [← zsmul_eq_emod_zsmul_of_nsmul_eq_zero hpQ, hm]; exact Point.some_ne_zero h
  have hr0 : 0 ≤ m % ((2 * n + 1 : ℕ) : ℤ) := Int.emod_nonneg m (by positivity)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = m % ((2 * n + 1 : ℕ) : ℤ) := ⟨_, Int.toNat_of_nonneg hr0⟩
  have hPr : (r • Q : W.toAffine.Point) = Point.some x y h := by
    rw [← natCast_zsmul, hr, ← zsmul_eq_emod_zsmul_of_nsmul_eq_zero hpQ, hm]
  rw [← hr, natCast_zsmul] at hP0
  have hrlt : r < 2 * n + 1 := by
    have := Int.emod_lt_of_pos m (show (0 : ℤ) < ((2 * n + 1 : ℕ) : ℤ) by positivity)
    omega
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exact absurd (by rw [h0, zero_nsmul]) hP0
    · exact h0
  rcases le_or_gt r n with hle | hgt
  · refine ⟨(r • Q).coordsOrZero, W.mem_oddOrderSummingSet.mpr ⟨r, hr1, hle, rfl⟩, ?_⟩
    rw [hPr, Point.coordsOrZero_some]
  · have hneg : ((2 * n + 1) - r) • Q = -(Point.some x y h) := by
      rw [sub_nsmul_eq_neg_of_nsmul_eq_zero hpQ (by omega : r ≤ 2 * n + 1), hPr]
    refine ⟨(((2 * n + 1) - r) • Q).coordsOrZero,
      W.mem_oddOrderSummingSet.mpr ⟨(2 * n + 1) - r, by omega, by omega, rfl⟩, ?_⟩
    rw [hneg, Affine.Point.neg_some, Point.coordsOrZero_some]

theorem s2c_mem_zmultiples_of_fst_eq (hord : addOrderOf Q = 2 * n + 1)
    {x y : F} (h : W.toAffine.Nonsingular x y)
    (hA : ∃ A ∈ W.oddOrderSummingSet Q n, x = A.1) :
    (Point.some x y h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q := by
  obtain ⟨A, hAmem, hAx⟩ := hA
  obtain ⟨k, hk1, hkn, hkA⟩ := W.mem_oddOrderSummingSet.mp hAmem
  have hk0 : k • Q ≠ 0 := fun h0 =>
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      (hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0)
  obtain ⟨x', y', h', heq', hco⟩ := exists_some_of_ne_zero hk0
  have hx : x = x' := by
    rw [hAx, ← hkA, hco]
  have hkmem : (k • Q : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q :=
    AddSubgroup.mem_zmultiples_iff.mpr ⟨(k : ℤ), natCast_zsmul Q k⟩
  subst hx
  rcases Affine.Y_eq_of_X_eq h.1 h'.1 rfl with hy | hy
  · subst hy
    rwa [heq'] at hkmem
  · have hneg : (Point.some x y h : W.toAffine.Point) = -(Point.some x y' h') := by
      rw [Affine.Point.neg_some]
      exact (Point.some.injEq _ _ _ _ _ _).mpr ⟨rfl, hy⟩ ▸ rfl
    rw [hneg, ← heq']
    exact AddSubgroup.neg_mem _ hkmem

end S2cKernel

/-! ### The seam: `restrictAlong` at the odd-order summing set -/

section SeamCasesOdd

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
variable [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine]
  [AbelTheorem W.toAffine]
variable {Q : W.toAffine.Point} {p : ℕ}
variable (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p)

local notation "S_Q" => W.oddOrderSummingSet Q ((p - 1) / 2)
set_option quotPrecheck false in
local notation "V'" => (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine
local notation "ι" => kw_oddOrderSummingSetFunctionFieldHom_odd (W := W) hp3 hpodd hord
local notation "hι" =>
  kw_oddOrderSummingSetFunctionFieldHom_odd_isIntegral (W := W) hp3 hpodd hord

include hp3 hpodd hord in
theorem kw_kwVeluXGenFun_notMem_placeOfEquation_of_mem_odd
    {r s : F} (hrs : W.toAffine.Equation r s) {A : F × F} (hA : A ∈ S_Q) (hrA : r = A.1) :
    kwVeluXGenFun W.toAffine S_Q ∉ (placeOfEquation hrs).toValuationSubring := by
  have hset := kw_isOddVeluSet_oddOrderSummingSet_odd (W := W) hp3 hpodd hord (le_refl _)
  have hDne : (veluXDenomPoly (F := F) S_Q) ≠ 0 := (veluXDenomPoly_monic S_Q).ne_zero
  have hNne : (veluXClearedPoly W S_Q) ≠ 0 := (veluXClearedPoly_monic W S_Q).1.ne_zero
  have hDeval : (veluXDenomPoly (F := F) S_Q).eval r = 0 := by
    subst hrA; unfold veluXDenomPoly
    rw [eval_prod]; exact Finset.prod_eq_zero hA (by simp)
  have hNeval : (veluXClearedPoly W S_Q).eval r ≠ 0 := by
    subst hrA; exact kw_eval_veluXClearedPoly_ne_zero_of_mem W.toAffine S_Q hset hA
  have hDord : 0 < (placeOfEquation hrs).ord
      (polyToFunctionField W.toAffine (veluXDenomPoly S_Q)) :=
    (ord_polyToFunctionField_pos_iff hrs hDne).mpr hDeval
  have hNord : (placeOfEquation hrs).ord
      (polyToFunctionField W.toAffine (veluXClearedPoly W S_Q)) = 0 :=
    (ord_polyToFunctionField_eq_zero_iff hrs hNne).mpr hNeval
  have hXne : kwVeluXGenFun W.toAffine S_Q ≠ 0 := fun h =>
    kw_transcendental_kwVeluXGenFun (W := W) S_Q (h ▸ isAlgebraic_zero)
  rw [(placeOfEquation hrs).mem_iff_ord_nonneg hXne, not_le]
  have hmul := (placeOfEquation hrs).ord_mul hXne
    (pow_ne_zero 2 (polyToFunctionField_ne_zero hDne))
  rw [kw_kwVeluXGenFun_mul_denom_sq_eq_cleared, hNord,
    (placeOfEquation hrs).ord_pow] at hmul
  push_cast at hmul
  linarith

theorem kw_kwVeluXGenFun_mem_placeOfEquation_of_ne_odd
    {r s : F} (hrs : W.toAffine.Equation r s) (hS : ∀ A ∈ S_Q, r ≠ A.1) :
    kwVeluXGenFun W.toAffine S_Q ∈ (placeOfEquation hrs).toValuationSubring := by
  unfold kwVeluXGenFun WeierstrassCurve.veluX liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU]
  refine add_mem (polyToFunctionField_X_mem_placeOfEquation hrs)
    (Subring.sum_mem _ fun A hA => ?_)
  have hδ : (polyToFunctionField W.toAffine X - algebraMap F W.toAffine.FunctionField A.1)⁻¹
      ∈ (placeOfEquation hrs).toValuationSubring := by
    refine (placeOfEquation hrs).mem_of_ord_nonneg
      (inv_ne_zero (sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap A.1))) ?_
    rw [(placeOfEquation hrs).ord_inv, ord_X_sub_const_placeOfEquation_of_ne hrs (hS A hA)]
    exact le_of_eq (_root_.neg_zero).symm
  refine add_mem ?_ ?_
  · rw [div_eq_mul_inv]; exact mul_mem ((placeOfEquation hrs).algebraMap_mem' _) hδ
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem ((placeOfEquation hrs).algebraMap_mem' _) (pow_mem hδ 2)

theorem kw_kwVeluYGenFun_mem_placeOfEquation_of_ne_odd
    {r s : F} (hrs : W.toAffine.Equation r s) (hS : ∀ A ∈ S_Q, r ≠ A.1) :
    kwVeluYGenFun W.toAffine S_Q ∈ (placeOfEquation hrs).toValuationSubring := by
  unfold kwVeluYGenFun WeierstrassCurve.veluY liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU,
    map_veluGx, map_veluGy, map_a₁, map_a₃]
  refine sub_mem (yGen_mem_placeOfEquation hrs) (Subring.sum_mem _ fun A hA => ?_)
  have hX := polyToFunctionField_X_mem_placeOfEquation hrs
  have hY := yGen_mem_placeOfEquation hrs
  have hF := fun c => (placeOfEquation hrs).algebraMap_mem' (c : F)
  have hδ : (polyToFunctionField W.toAffine X - algebraMap F W.toAffine.FunctionField A.1)⁻¹
      ∈ (placeOfEquation hrs).toValuationSubring := by
    refine (placeOfEquation hrs).mem_of_ord_nonneg
      (inv_ne_zero (sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap A.1))) ?_
    rw [(placeOfEquation hrs).ord_inv, ord_X_sub_const_placeOfEquation_of_ne hrs (hS A hA)]
    exact le_of_eq (_root_.neg_zero).symm
  refine add_mem (add_mem ?_ ?_) ?_
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (hF _)
      (add_mem (add_mem (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX)) (hF _)))
      (pow_mem hδ 3)
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (hF _) (sub_mem (add_mem (mul_mem (hF _)
      (sub_mem hX (hF _))) hY) (hF _))) (pow_mem hδ 2)
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (sub_mem (mul_mem (hF _) (hF _)) (mul_mem (hF _) (hF _))) (pow_mem hδ 2)

include hp3 hpodd hord in
theorem kw_map_XClass_oddOrderSummingSet_odd (c : F) :
    (ι) (algebraMap (V').CoordinateRing (V').FunctionField (XClass V' c))
      = kwVeluXGenFun W.toAffine S_Q - algebraMap F W.toAffine.FunctionField c := by
  rw [show algebraMap (V').CoordinateRing (V').FunctionField (XClass V' c)
        = polyToFunctionField V' (X : F[X]) - algebraMap F (V').FunctionField c by
      rw [← polyToFunctionField_C, ← map_sub]; rfl,
    map_sub, kw_oddOrderSummingSetFunctionFieldHom_odd_polyToFunctionField_X,
    AlgHom.commutes]

include hp3 hpodd hord in
theorem kw_map_YClass_oddOrderSummingSet_odd (c : F) :
    (ι) (algebraMap (V').CoordinateRing (V').FunctionField (YClass V' (C c)))
      = kwVeluYGenFun W.toAffine S_Q - algebraMap F W.toAffine.FunctionField c := by
  rw [show algebraMap (V').CoordinateRing (V').FunctionField (YClass V' (C c))
        = yGen V' - algebraMap F (V').FunctionField c by
      rw [YClass, map_sub, map_sub, yGen]; congr 1,
    map_sub, kw_oddOrderSummingSetFunctionFieldHom_odd_yGen, AlgHom.commutes]

include hp3 hpodd hord in
theorem kw_kwVeluYGenFun_ne_algebraMap_odd (c : F) :
    kwVeluYGenFun W.toAffine S_Q ≠ algebraMap F W.toAffine.FunctionField c := by
  intro heq
  have hinj : Function.Injective (ι) := (ι).toRingHom.injective
  have hYne : (algebraMap (V').CoordinateRing (V').FunctionField) (YClass V' (C c)) ≠ 0 :=
    (map_ne_zero_iff _
      (IsFractionRing.injective (V').CoordinateRing (V').FunctionField)).mpr (YClass_ne_zero _)
  exact hYne (hinj (by
    rw [kw_map_YClass_oddOrderSummingSet_odd hp3 hpodd hord, heq, sub_self, _root_.map_zero]))

variable [(W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).IsElliptic]
  [GenusOnePlaceGate (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine]
  [GenusOnePlaceGate.IsCentred (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine]
  [AbelTheorem (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine]

include hp3 hpodd hord in
theorem kw_restrictAlong_infinitePlace_oddOrderSummingSet_odd :
    (InfinitePlace.place : Place F W.toAffine.FunctionField).restrictAlong (ι) (hι)
      = (InfinitePlace.place : Place F (V').FunctionField) := by
  refine InfinitePlace.eq_of_not_isFinitePlace _ ?_
  intro hfin
  refine kw_kwVeluXGenFun_notMem_of_not_isFinitePlace (S := S_Q)
    (InfinitePlace.place : Place F W.toAffine.FunctionField) InfinitePlace.not_isFinitePlace ?_
  rw [← kw_oddOrderSummingSetFunctionFieldHom_odd_polyToFunctionField_X hp3 hpodd hord]
  exact hfin (algebraMap F[X] (V').CoordinateRing (X : F[X]))

include hp3 hpodd hord in
theorem kw_restrictAlong_placeOfEquation_of_mem_oddOrderSummingSet_odd
    {r s : F} (hrs : W.toAffine.Equation r s) {A : F × F} (hA : A ∈ S_Q) (hrA : r = A.1) :
    (placeOfEquation hrs).restrictAlong (ι) (hι) = InfinitePlace.place := by
  refine InfinitePlace.eq_of_not_isFinitePlace _ ?_
  intro hfin
  refine kw_kwVeluXGenFun_notMem_placeOfEquation_of_mem_odd hp3 hpodd hord hrs hA hrA ?_
  rw [← kw_oddOrderSummingSetFunctionFieldHom_odd_polyToFunctionField_X hp3 hpodd hord]
  exact hfin (algebraMap F[X] (V').CoordinateRing (X : F[X]))

include hp3 hpodd hord in
theorem kw_restrictAlong_placeOfEquation_of_ne_oddOrderSummingSet_odd
    {r s : F} (hrs : W.toAffine.Equation r s) (hS : ∀ A ∈ S_Q, r ≠ A.1)
    (h' : (V').Equation (W.veluX S_Q r) (W.veluY S_Q r s)) :
    (placeOfEquation hrs).restrictAlong (ι) (hι) = placeOfEquation h' := by
  have hrat := isRational_placeOfEquation hrs
  have hXmem := kw_kwVeluXGenFun_mem_placeOfEquation_of_ne_odd (W := W) (Q := Q) (p := p)
    hrs hS
  have hYmem := kw_kwVeluYGenFun_mem_placeOfEquation_of_ne_odd (W := W) (Q := Q) (p := p)
    hrs hS
  have hXeval : (placeOfEquation hrs).evalAt (kwVeluXGenFun W.toAffine S_Q) = W.veluX S_Q r :=
    evalAt_veluX_liftSummingSet_placeOfEquation hrs hS
  have hYeval : (placeOfEquation hrs).evalAt (kwVeluYGenFun W.toAffine S_Q)
      = W.veluY S_Q r s :=
    evalAt_veluY_liftSummingSet_placeOfEquation hrs hS
  have hfin : IsFinitePlace ((placeOfEquation hrs).restrictAlong (ι) (hι)) :=
    isFinitePlace_of_mem _ (by
      rw [Place.mem_restrictAlong_iff,
        kw_oddOrderSummingSetFunctionFieldHom_odd_polyToFunctionField_X hp3 hpodd hord]
      exact hXmem)
  refine eq_placeOfEquation_of_le_centre hfin h' ?_
  rw [XYIdeal, Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · rw [SetLike.mem_coe, hfin.mem_centre_iff_ord_ne_zero (XClass_ne_zero _),
      Place.ord_restrictAlong_ne_zero_iff, kw_map_XClass_oddOrderSummingSet_odd hp3 hpodd hord]
    have hXne : kwVeluXGenFun W.toAffine S_Q
        - algebraMap F W.toAffine.FunctionField (W.veluX S_Q r) ≠ 0 :=
      sub_ne_zero.mpr fun heq => (kw_transcendental_kwVeluXGenFun (W := W) S_Q)
        (heq ▸ isAlgebraic_algebraMap _)
    have := (placeOfEquation hrs).ord_sub_evalAt_pos hrat hXmem (hXeval ▸ hXne)
    rw [hXeval] at this; omega
  · rw [SetLike.mem_coe, hfin.mem_centre_iff_ord_ne_zero (YClass_ne_zero _),
      Place.ord_restrictAlong_ne_zero_iff, kw_map_YClass_oddOrderSummingSet_odd hp3 hpodd hord]
    have hYne : kwVeluYGenFun W.toAffine S_Q
        - algebraMap F W.toAffine.FunctionField (W.veluY S_Q r s) ≠ 0 :=
      sub_ne_zero.mpr (kw_kwVeluYGenFun_ne_algebraMap_odd hp3 hpodd hord _)
    have := (placeOfEquation hrs).ord_sub_evalAt_pos hrat hYmem (hYeval ▸ hYne)
    rw [hYeval] at this; omega

local notation "hmapeq" =>
  kw_kwVeluMapEquationAt_oddOrderSummingSet_odd (W := W) hp3 hpodd hord
    W.toAffine.isUnit_Δ.ne_zero

variable (hΔV : (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).Δ ≠ 0)

include hp3 hpodd hord hΔV in
theorem kw_restrictAlong_placeOfPoint_kwVeluPointMap_odd (P : W.toAffine.Point) :
    (placeOfPoint P).restrictAlong (ι) (hι)
      = placeOfPoint (kwVeluPointMap (hmapeq) hΔV P) := by
  cases P with
  | zero =>
      rw [kwVeluPointMap_zero]
      exact kw_restrictAlong_infinitePlace_oddOrderSummingSet_odd hp3 hpodd hord
  | some r s hns =>
      classical
      by_cases hx : ∀ A ∈ S_Q, r ≠ A.1
      · rw [kwVeluPointMap_some_of_ne _ hΔV hns hx, placeOfPoint_some', placeOfPoint_some']
        exact kw_restrictAlong_placeOfEquation_of_ne_oddOrderSummingSet_odd hp3 hpodd hord
          hns.1 hx _
      · simp only [not_forall, not_not] at hx
        obtain ⟨A, hA, hrA⟩ := hx
        rw [kwVeluPointMap_some_of_mem _ hΔV hns hA hrA, placeOfPoint_some']
        exact kw_restrictAlong_placeOfEquation_of_mem_oddOrderSummingSet_odd hp3 hpodd hord
          hns.1 hA hrA

end SeamCasesOdd

end WeierstrassCurve

/-! The pin's `relNorm_eq_pow_of_isMaximal_of_isSeparable`
(`S_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable.lean`, 155 lines):
the char-free replacement for `Ideal.relNorm_eq_pow_of_isMaximal`, whose
`PerfectField` side condition is automatic only in characteristic zero. -/

namespace AlgebraicCurve

namespace F10d

section Closure

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]

attribute [local instance 10] FractionRing.liftAlgebra

local notation3 "𝕂" => FractionRing R
local notation3 "𝕃" => FractionRing S
local notation3 "𝔼" => IntermediateField.normalClosure (FractionRing R) (FractionRing S)
    (AlgebraicClosure (FractionRing S))
local notation3 "𝕋" => Ring.NormalClosure R S

local instance : Algebra S 𝔼 := ((algebraMap 𝕃 𝔼).comp (algebraMap S 𝕃)).toAlgebra

local instance : IsScalarTower S 𝕃 𝔼 := IsScalarTower.of_algebraMap_eq' rfl

local instance : Algebra 𝕋 𝔼 := inferInstanceAs (Algebra (integralClosure S 𝔼) 𝔼)

local instance : IsScalarTower S 𝕋 𝔼 := inferInstanceAs (IsScalarTower S (integralClosure S 𝔼) 𝔼)

local instance : IsIntegralClosure 𝕋 S 𝔼 := integralClosure.isIntegralClosure S 𝔼

local instance : IsScalarTower R 𝕋 𝔼 :=
  IsScalarTower.of_algebraMap_eq fun r => Subtype.ext <| by
    show algebraMap R (AlgebraicClosure 𝕃) r
      = algebraMap 𝕃 (AlgebraicClosure 𝕃) (algebraMap S 𝕃 (algebraMap R S r))
    rw [IsScalarTower.algebraMap_apply R 𝕃 (AlgebraicClosure 𝕃), IsScalarTower.algebraMap_apply R S 𝕃]

local instance : FaithfulSMul S 𝔼 := (faithfulSMul_iff_algebraMap_injective S 𝔼).mpr <|
      (FaithfulSMul.algebraMap_injective 𝕃 𝔼).comp (FaithfulSMul.algebraMap_injective S 𝕃)

variable [Module.Finite R S]

local instance : FiniteDimensional 𝕃 𝔼 := Module.Finite.right 𝕂 𝕃 𝔼

local instance : IsFractionRing 𝕋 𝔼 := integralClosure.isFractionRing_of_finite_extension 𝕃 𝔼

variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

omit [Module.Finite R S] in

private theorem isSeparable_normalClosure : Algebra.IsSeparable 𝕂 𝔼 := by
  rw [← le_separableClosure_iff, normalClosure_le_iff]
  intro f x hx
  obtain ⟨y, rfl⟩ := f.mem_fieldRange.mp hx
  rw [mem_separableClosure_iff]
  exact IsSeparable.map f (f : 𝕃 →+* AlgebraicClosure 𝕃).injective
    (Algebra.IsSeparable.isSeparable 𝕂 y)

local instance : Algebra.IsSeparable 𝕂 𝔼 := isSeparable_normalClosure R S

local instance : Algebra.IsSeparable 𝕃 𝔼 := Algebra.isSeparable_tower_top_of_isSeparable 𝕂 𝕃 𝔼

local instance : IsAlgClosure 𝕂 (AlgebraicClosure 𝕃) :=
  IsAlgClosure.ofAlgebraic 𝕂 𝕃 (AlgebraicClosure 𝕃)

local instance : Normal 𝕂 𝔼 := normalClosure.normal _ _ _

local instance : IsGalois 𝕂 𝔼 := IsGalois.mk

local instance : IsGalois 𝕂 (FractionRing 𝕋) := by
  refine IsGalois.of_equiv_equiv (F := 𝕂) (E := 𝔼)
    (f := (FractionRing.algEquiv R 𝕂).symm.toRingEquiv)
    (g := (FractionRing.algEquiv 𝕋 𝔼).symm.toRingEquiv) ?_
  ext
  simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R 𝕂).symm
    (FractionRing.algEquiv 𝕋 𝔼).symm _

variable [IsDedekindDomain S]

local instance : Module.Finite S 𝕋 := IsIntegralClosure.finite S 𝕃 𝔼 𝕋

local instance : Module.Finite R 𝕋 := Module.Finite.trans S 𝕋

local instance : IsDedekindDomain 𝕋 := integralClosure.isDedekindDomain S 𝕃 𝔼

variable {R S}
variable [IsDedekindDomain R]

set_option maxHeartbeats 1600000 in

private theorem relNorm_eq_pow_of_isMaximal_fractionRing
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal 𝕋, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois 𝕃 (FractionRing 𝕋) := IsGalois.tower_top_of_isGalois 𝕂 𝕃 (FractionRing 𝕋)
  rwa [← Ideal.relNorm_relNorm R S, Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    ← Ideal.inertiaDeg'_eq_inertiaDeg p Q, ← Ideal.inertiaDeg'_eq_inertiaDeg P Q,
    Ideal.inertiaDeg'_algebra_tower p P Q, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr <| Ideal.inertiaDeg'_pos P Q

end Closure

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S]
  [IsDedekindDomain R] [IsDedekindDomain S]

attribute [local instance 10] FractionRing.liftAlgebra

private theorem relNorm_eq_pow_of_isMaximal_of_isSeparable (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv (by
        ext x
        simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
          (FractionRing.algEquiv S L).symm x)
  exact relNorm_eq_pow_of_isMaximal_fractionRing P p

end Transport

end F10d

/-- The pin's public node
`AlgebraicCurve.relNorm_eq_pow_of_isMaximal_of_isSeparable` (its `Theorems/`
wrapper; the `S_` file proves it by the `private` helper of the same name
transcribed in `AlgebraicCurve.F10d` above). Statement verbatim from the wrapper;
the helper stays `private`, matching the pin. -/
theorem relNorm_eq_pow_of_isMaximal_of_isSeparable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P :=
  F10d.relNorm_eq_pow_of_isMaximal_of_isSeparable K L P p

end AlgebraicCurve


/-! The port's fibre-centre norm argument (`PrincipalDivisors/Transcendence.lean`,
lines 134--361) re-run without `[CharZero F]`: it now consumes the pin's
separability-aware `relNorm` lemma above.  All declarations stay `private`, so the
public statement surface is unchanged. -/

namespace AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Place Divisor
section DVR

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal {r : v.toValuationSubring} {n : ℕ}
    (h : Ideal.span {r} = IsLocalRing.maximalIdeal v.toValuationSubring ^ n) :
    v.ord (r : F) = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h

  have hr : r = ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * π ^ n := by
    rw [mul_comm, Units.eq_mul_inv_iff_mul_eq]
    exact hu
  have hcoe : (r : F) = (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
      * (π : F) ^ (n : ℤ) := by
    rw [hr]
    push_cast
    rw [zpow_natCast]
  rw [hcoe, v.ord_unit_smul_zpow u⁻¹ hπ (n : ℤ)]

end DVR

/-! ## The ideal-norm and element-norm block -/

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

namespace Place


section IdealNorm

variable {v : Place K F} {w : Place K F'}

private theorem relNorm_fiberCenter (hw : w.restrict F = v) :
    Ideal.relNorm v.toValuationSubring (fiberCenter F' v hw).asIdeal
      = IsLocalRing.maximalIdeal v.toValuationSubring ^ w.inertiaDeg F := by
  haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  haveI : (fiberCenter F' v hw).asIdeal.LiesOver
      (IsLocalRing.maximalIdeal v.toValuationSubring) := fiberCenter_liesOver hw
  rw [AlgebraicCurve.F10d.relNorm_eq_pow_of_isMaximal_of_isSeparable F F'
    (fiberCenter F' v hw).asIdeal (IsLocalRing.maximalIdeal v.toValuationSubring),
    inertiaDeg_eq_inertiaDeg_fiberCenter hw]


private theorem count_normalizedFactors_span_singleton
    (hw : w.restrict F = v) {c : integralClosureAt F' v} (hc : c ≠ 0) :
    (normalizedFactors (Ideal.span {c})).count (fiberCenter F' v hw).asIdeal
      = (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat := by
  haveI : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime

  have hord0 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) :=
    w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw c)
  refine Ideal.count_normalizedFactors_eq (p := (fiberCenter F' v hw).asIdeal)
    (x := Ideal.span {c})
    (n := (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) ?_ ?_
  · rw [Ideal.span_singleton_le_iff_mem, ← le_ord_iff_mem_pow_fiberCenter hw hc]
    omega
  · rw [Ideal.span_singleton_le_iff_mem, ← le_ord_iff_mem_pow_fiberCenter hw hc]
    push_cast
    omega

private theorem relNorm_span_singleton {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
      = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiberOver F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
  have hspan : (Ideal.span {c} : Ideal (integralClosureAt F' v)) ≠ ⊥ := by simpa using hc
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (Ideal.span {c})
    with hS

  have hfactor : ∀ Q ∈ S.toFinset, ∃ w' : Place K F', ∃ hw' : w'.restrict F = v,
      (fiberCenter F' v hw').asIdeal = Q := by
    intro Q hQ
    rw [Multiset.mem_toFinset] at hQ
    have hQprime : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    have hQbot : Q ≠ ⊥ := hQprime.ne_zero
    haveI : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    exact ⟨placeOfPrime ⟨Q, inferInstance, hQbot⟩, restrict_placeOfPrime _,
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime
        (⟨Q, inferInstance, hQbot⟩ : HeightOneSpectrum (integralClosureAt F' v)))⟩

  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiberOver F').attach.image
    (fun w' => (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', (mem_fiberOver v).mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiberOver F'} =>
      (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal) (v.fiberOver F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq ((mem_fiberOver v).mp w₁.2) ((mem_fiberOver v).mp w₂.2)
      (HeightOneSpectrum.ext h))

  calc
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
        = Ideal.relNorm v.toValuationSubring (∏ Q ∈ S.toFinset, Q ^ S.count Q) := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hspan]
    _ = ∏ Q ∈ S.toFinset, Ideal.relNorm v.toValuationSubring Q ^ S.count Q := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun Q _ => map_pow _ Q _
    _ = ∏ Q ∈ S.toFinset, IsLocalRing.maximalIdeal v.toValuationSubring
          ^ ((IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q) := by
          refine Finset.prod_congr rfl fun Q hQ => ?_
          obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
          rw [relNorm_fiberCenter hw', ← pow_mul, inertiaDeg_eq_inertiaDeg_fiberCenter hw']
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ Q ∈ S.toFinset,
              (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q) :=
          Finset.prod_pow_eq_pow_sum S.toFinset
            (fun Q => (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q)
            (IsLocalRing.maximalIdeal v.toValuationSubring)
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiberOver F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
          congr 1

          calc
            ∑ Q ∈ S.toFinset,
                (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q
                = ∑ Q ∈ T,
                    (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q
                      * S.count Q := by
                  refine Finset.sum_subset hsub fun Q _ hQ => ?_
                  rw [Multiset.count_eq_zero_of_notMem
                    (fun h => hQ (Multiset.mem_toFinset.mpr h)), mul_zero]
            _ = ∑ w' ∈ (v.fiberOver F').attach,
                  (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
                      (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal
                    * S.count (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal := by
                  rw [hT, Finset.sum_image hinj]
            _ = ∑ w' ∈ (v.fiberOver F').attach, (w'.1.inertiaDeg F
                  * (w'.1.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
                  refine Finset.sum_congr rfl fun w' _ => ?_
                  rw [← inertiaDeg_eq_inertiaDeg_fiberCenter ((mem_fiberOver v).mp w'.2),
                    count_normalizedFactors_span_singleton ((mem_fiberOver v).mp w'.2) hc]
            _ = ∑ w ∈ v.fiberOver F',
                  w.inertiaDeg F
                    * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat :=
                  Finset.sum_attach (v.fiberOver F') fun w =>
                    w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat

end IdealNorm

section ElementNorm

variable (v : Place K F)

private theorem ord_norm_algebraMap_integralClosureAt
    {c : integralClosureAt F' v} (hc : c ≠ 0) :
    v.ord (Algebra.norm F (algebraMap (integralClosureAt F' v) F' c))
      = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
          * w.ord (algebraMap (integralClosureAt F' v) F' c) := by

  rw [← Algebra.algebraMap_intNorm (A := v.toValuationSubring) (K := F) (L := F')
    (B := integralClosureAt F' v)]

  have hrel := relNorm_span_singleton (v := v) hc
  rw [Ideal.relNorm_singleton] at hrel

  rw [ValuationSubring.algebraMap_apply, ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal v hrel]

  push_cast
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Int.toNat_of_nonneg
    (w.ord_nonneg_of_mem (forall_mem_of_restrict_eq ((mem_fiberOver v).mp hw) c))]

private theorem ord_norm_eq_sum_fiberOver {f : F'} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f := by

  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt F' v)) f
  have hs0 : (s : integralClosureAt F' v) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsF : algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hs0
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    rw [← hcs]
    exact mul_ne_zero hf hsF
  have hc0 : c ≠ 0 := fun h => hcF (by rw [h, map_zero])

  have hintc := ord_norm_algebraMap_integralClosureAt v hc0
  have hints := ord_norm_algebraMap_integralClosureAt v hs0

  rw [← hcs, map_mul, v.ord_mul (Algebra.norm_ne_zero_iff.mpr hf)
    (Algebra.norm_ne_zero_iff.mpr hsF), hints] at hintc
  have hsplit : ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
      * w.ord (f * algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v))
        = (∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f)
          + ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
              * w.ord (algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [w.ord_mul hf hsF]
    ring
  rw [hsplit] at hintc
  omega

end ElementNorm

end Place

namespace Divisor

private theorem pushforwardNormFormula_of_finiteDimensional :
    Divisor.PushforwardNormFormula K F F' := by
  intro f hf D hD v
  classical
  rw [Divisor.pushforward_apply, Place.ord_norm_eq_sum_fiberOver v hf]
  calc
    ∑ w ∈ D.support, (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0)
        = ∑ w ∈ D.support ∪ v.fiberOver F',
            (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine Finset.sum_subset Finset.subset_union_left fun w _ hw => ?_
          rw [Finsupp.notMem_support_iff.mp hw, zero_mul, ite_self]
    _ = ∑ w ∈ v.fiberOver F', (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
          rw [if_neg fun h => hw ((Place.mem_fiberOver v).mpr h)]
    _ = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [if_pos ((Place.mem_fiberOver v).mp hw), hD w, mul_comm]
end Divisor
end AlgebraicCurve

/-! The character-free norm formula, at the pin wrapper's binders.  (The
`[HasPrincipalDivisors K F']` argument is present to match the pin wrapper and to
keep the caller's `[W.IsElliptic]` in the elaborated signature; the fibre-centre
route below does not itself need it.) -/

namespace AlgebraicCurve

private theorem kw_normFormulaAlong_of_separableAlong_cf {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hPD : HasPrincipalDivisors K F')
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) : NormFormulaAlong K φ hfin := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  exact Divisor.pushforwardNormFormula_of_finiteDimensional

end AlgebraicCurve

/-! ### The restrictAlong column: the `_cf` helpers, the `IsogenyEndDatum`
identity, the `s2c` seam and the two headlines

The `_cf` block is the res `S_` file's characteristic-free copy of the
`ConditionalCurrency` vocabulary (the port's copies carry `[CharZero F]`). -/

namespace WeierstrassCurve

namespace Affine

universe u

section AutoNorm

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]

theorem normFormulaAlong_of_elliptic (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hfin : FiniteAlong F ι) (hsep : SeparableAlong F ι) : NormFormulaAlong F ι hfin :=
  kw_normFormulaAlong_of_separableAlong_cf (K := F) ι
    (kw_veluHPDSupplier W W.isUnit_Δ.ne_zero) hfin hsep

end AutoNorm

section CharFreePMOP

variable {F : Type u} [Field F] [DecidableEq F]
variable {V W : Affine F}
variable [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
variable (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)

theorem inertiaDegAlong_eq_one_cf (w : AlgebraicCurve.Place F W.FunctionField) :
    w.inertiaDegAlong ι hι = 1 := by
  have h := AlgebraicCurve.Place.deg_restrictAlong_mul_inertiaDegAlong ι hι w
  rw [deg_eq_one (W := V) (w.restrictAlong ι hι), deg_eq_one (W := W) w, one_mul] at h
  exact h

theorem pushforwardAlong_single_eq_cf (w : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    Divisor.pushforwardAlong ι hι (Finsupp.single w n)
      = Finsupp.single (w.restrictAlong ι hι) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one_cf ι hι w, Nat.cast_one, mul_one]

variable (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin)

theorem pushforwardAlongDegZero_pointDivisor_cf {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongDegZero ι hι (pointDivisor P) = pointDivisor Q := by
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, coe_pointDivisor, map_sub,
    pushforwardAlong_single_eq_cf ι hι, pushforwardAlong_single_eq_cf ι hι, hP, h0]

theorem pushforwardAlongHom_pointClass_cf {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P) = pointClass Q := by
  show Pic0.pushforwardAlongHom ι hι hfin hN (Pic0.mk (pointDivisor P))
      = Pic0.mk (pointDivisor Q)
  rw [Pic0.pushforwardAlongHom_mk, pushforwardAlongDegZero_pointDivisor_cf ι hι hP h0]

theorem pointMapOfPushforward_apply_cf (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P
      = genusOnePic0Equiv V (Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P)) := by
  rw [← genusOnePic0Equiv_symm_apply]
  rfl

theorem pointMapOfPushforward_eq_of_seam_cf (g : W.Point → V.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P)) (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P = g P := by
  rw [pointMapOfPushforward_apply_cf,
    pushforwardAlongHom_pointClass_cf ι hι hfin hN (hg P) ((hg 0).trans (by rw [hg0])),
    genusOnePic0Equiv_apply, pic0ToPoint_pointClass]

end CharFreePMOP

-- `IsogenyEndDatum.isIntegral_algHomId`, `finiteAlong_algHomId` and
-- `restrictAlong_algHomId` were extracted to the leaf module
-- `AlgebraicCurve/Defs/RestrictAlongAPI.lean` (H5 SET-1), imported above.

end Affine

section S2cKey

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic] {Q : W.toAffine.Point} {p : ℕ}

theorem s2c_key (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p)
    (hΔV : (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).Δ ≠ 0)
    [(W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine] [AbelTheorem W.toAffine]
    [GenusOnePlaceGate (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine]
    [GenusOnePlaceGate.IsCentred (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine]
    [AbelTheorem (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine] :
    ∃ (ι : (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong F ι),
      finrankAlong F ι = addOrderOf Q
        ∧ (∀ hN : NormFormulaAlong F ι hfin,
            (pointMapOfPushforward ι hι hfin hN).ker = AddSubgroup.zmultiples Q)
        ∧ (∀ P : W.toAffine.Point, P ∈ AddSubgroup.zmultiples Q →
            (placeOfPoint P).restrictAlong ι hι
              = placeOfPoint (0 : (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.Point))
        ∧ (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
            Point.some x y h ∉ AddSubgroup.zmultiples Q →
            ∃ h' : (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.Nonsingular
                (W.veluX (W.oddOrderSummingSet Q ((p - 1) / 2)) x)
                (W.veluY (W.oddOrderSummingSet Q ((p - 1) / 2)) x y),
              (placeOfPoint (Point.some x y h)).restrictAlong ι hι
                = placeOfPoint (Point.some _ _ h')) := by
  classical
  have hn : addOrderOf Q = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨k, hk⟩ := hpodd; rw [hord, hk]; omega
  have hmapeq : W.KwVeluMapEquationAt (W.oddOrderSummingSet Q ((p - 1) / 2)) :=
    kw_kwVeluMapEquationAt_oddOrderSummingSet_odd (W := W) hp3 hpodd hord
      W.toAffine.isUnit_Δ.ne_zero
  refine ⟨kw_oddOrderSummingSetFunctionFieldHom_odd (W := W) hp3 hpodd hord,
    kw_oddOrderSummingSetFunctionFieldHom_odd_isIntegral (W := W) hp3 hpodd hord,
    kw_oddOrderSummingSetFunctionFieldHom_odd_finiteAlong (W := W) hp3 hpodd hord, ?_⟩
  set ι := kw_oddOrderSummingSetFunctionFieldHom_odd (W := W) hp3 hpodd hord
  set hι := kw_oddOrderSummingSetFunctionFieldHom_odd_isIntegral (W := W) hp3 hpodd hord
  set hfin := kw_oddOrderSummingSetFunctionFieldHom_odd_finiteAlong (W := W) hp3 hpodd hord
  have hseam : ∀ P : W.toAffine.Point,
      (placeOfPoint P).restrictAlong ι hι = placeOfPoint (kwVeluPointMap hmapeq hΔV P) :=
    kw_restrictAlong_placeOfPoint_kwVeluPointMap_odd (W := W) hp3 hpodd hord hΔV

  have hker : ∀ P : W.toAffine.Point,
      kwVeluPointMap hmapeq hΔV P = 0 ↔ P ∈ AddSubgroup.zmultiples Q := by
    intro P
    cases P with
    | zero => exact ⟨fun _ => AddSubgroup.zero_mem _, fun _ => rfl⟩
    | some x y h =>
      constructor
      · intro h0
        by_cases hx : ∀ A ∈ (W.oddOrderSummingSet Q ((p - 1) / 2)), x ≠ A.1
        · rw [kwVeluPointMap_some_of_ne hmapeq hΔV h hx] at h0
          exact absurd h0 (Point.some_ne_zero _)
        · simp only [not_forall, not_not] at hx
          obtain ⟨A, hA, hxA⟩ := hx
          exact s2c_mem_zmultiples_of_fst_eq hn h ⟨A, hA, hxA⟩
      · intro hP
        obtain ⟨A, hA, hxA⟩ := s2c_exists_fst_eq_of_mem_zmultiples hn hP
        exact kwVeluPointMap_some_of_mem hmapeq hΔV h hA hxA

  have hpm : ∀ (hN : NormFormulaAlong F ι hfin) (P : W.toAffine.Point),
      pointMapOfPushforward ι hι hfin hN P = kwVeluPointMap hmapeq hΔV P :=
    fun hN P => pointMapOfPushforward_eq_of_seam_cf ι hι hfin hN _ rfl hseam P
  have hkerN : ∀ hN : NormFormulaAlong F ι hfin,
      (pointMapOfPushforward ι hι hfin hN).ker = AddSubgroup.zmultiples Q := by
    intro hN; ext P
    rw [AddMonoidHom.mem_ker, hpm hN P]
    exact hker P
  refine ⟨?_, hkerN, ?_, ?_⟩
  ·
    have hsep : SeparableAlong F ι :=
      kw_oddOrderSummingSetFunctionFieldHom_odd_separableAlong (W := W) hp3 hpodd hord
    have hN₀ : NormFormulaAlong F ι hfin := normFormulaAlong_of_elliptic ι hfin hsep
    haveI : HasPrincipalDivisors F W.toAffine.FunctionField :=
      kw_veluHPDSupplier W W.toAffine.isUnit_Δ.ne_zero
    haveI : HasPrincipalDivisors F
        (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine.FunctionField :=
      kw_veluHPDSupplier (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))) hΔV
    rw [← natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong W.toAffine
      (W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2))).toAffine ι hι hfin hsep hN₀, hkerN hN₀,
      Nat.card_zmultiples]
  · intro P hP
    rw [hseam P, (hker P).mpr hP]
  · intro x y h hP
    have hx : ∀ A ∈ (W.oddOrderSummingSet Q ((p - 1) / 2)), x ≠ A.1 := by
      intro A hA hxA
      exact hP (s2c_mem_zmultiples_of_fst_eq hn h ⟨A, hA, hxA⟩)
    exact ⟨kw_velu_map_nonsingular hmapeq hΔV h.1 hx, by
      rw [hseam, kwVeluPointMap_some_of_ne hmapeq hΔV h hx]⟩

theorem s2c_zero (V : WeierstrassCurve F) (hVW : V = W)
    [instV : V.toAffine.IsElliptic]
    [gW : GenusOnePlaceGate W.toAffine] [cW : GenusOnePlaceGate.IsCentred W.toAffine] [aW : AbelTheorem W.toAffine]
    [gV : GenusOnePlaceGate V.toAffine] [cV : GenusOnePlaceGate.IsCentred V.toAffine] [aV : AbelTheorem V.toAffine]
    (hQ : Q = 0) (S : Finset (F × F)) (hS : S = ∅) :
    ∃ (ι : V.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong F ι),
      finrankAlong F ι = addOrderOf Q
        ∧ (∀ hN : NormFormulaAlong F ι hfin,
            (pointMapOfPushforward ι hι hfin hN).ker = AddSubgroup.zmultiples Q)
        ∧ (∀ P : W.toAffine.Point, P ∈ AddSubgroup.zmultiples Q →
            (placeOfPoint P).restrictAlong ι hι = placeOfPoint (0 : V.toAffine.Point))
        ∧ (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
            Point.some x y h ∉ AddSubgroup.zmultiples Q →
            ∃ h' : V.toAffine.Nonsingular (W.veluX S x) (W.veluY S x y),
              (placeOfPoint (Point.some x y h)).restrictAlong ι hι
                = placeOfPoint (Point.some _ _ h')) := by
  subst hVW; subst hQ; subst hS

  haveI : IsDedekindDomain V.toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain_of_Δ_ne_zero V.toAffine.isUnit_Δ.ne_zero
  have hgg : gV = gW := GenusOnePlaceGate.ext_of_isCentred gV gW cV cW
  subst hgg
  refine ⟨AlgHom.id F _, IsogenyEndDatum.isIntegral_algHomId V.toAffine,
    IsogenyEndDatum.finiteAlong_algHomId V.toAffine, ?_, ?_, ?_, ?_⟩
  · rw [addOrderOf_zero]
    letI := algebraAlong (AlgHom.id F V.toAffine.FunctionField)
    show Module.finrank V.toAffine.FunctionField V.toAffine.FunctionField = 1
    convert Module.finrank_self V.toAffine.FunctionField
  · intro hN
    rw [AddSubgroup.zmultiples_zero_eq_bot, AddMonoidHom.ker_eq_bot_iff]
    intro P₁ P₂ h12
    have h1 := pointMapOfPushforward_eq_of_seam_cf (AlgHom.id F _) (IsogenyEndDatum.isIntegral_algHomId V.toAffine)
      (IsogenyEndDatum.finiteAlong_algHomId V.toAffine) hN id rfl
      (fun P => IsogenyEndDatum.restrictAlong_algHomId V.toAffine (placeOfPoint P))
    rw [h1, h1] at h12
    exact h12
  · intro P hP
    rw [AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot] at hP
    subst hP
    exact IsogenyEndDatum.restrictAlong_algHomId V.toAffine (placeOfPoint (0 : V.toAffine.Point))
  · intro x y h _
    have hX : V.veluX ∅ x = x := by simp [WeierstrassCurve.veluX]
    have hY : V.veluY ∅ x y = y := by simp [WeierstrassCurve.veluY]
    refine ⟨by rw [hX, hY]; exact h, ?_⟩
    rw [IsogenyEndDatum.restrictAlong_algHomId V.toAffine]
    congr 1
    exact (Point.some.injEq _ _ _ _ _ _).mpr ⟨hX.symm, hY.symm⟩ ▸ rfl

end S2cKey

/-! ### The two headlines
Statements are the pin `Theorems/` wrappers' verbatim; the plain statement is the
general one with `[CharZero F]` added, and its proof is the general theorem
applied directly. -/

/-- The general `restrictAlong` isomorphism, characteristic-agnostic. -/
theorem exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.IsElliptic]
    {Q : W.toAffine.Point} {n : ℕ} (hord : addOrderOf Q = 2 * n + 1)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    [(W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine] :
    ∃ (ι : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      AlgebraicCurve.finrankAlong F ι = 2 * n + 1
        ∧ (∀ hN : AlgebraicCurve.NormFormulaAlong F ι hfin,
            (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
              = AddSubgroup.zmultiples Q)
        ∧ (∀ P : W.toAffine.Point, P ∈ AddSubgroup.zmultiples Q →
            (WeierstrassCurve.Affine.placeOfPoint P).restrictAlong ι hι
              = WeierstrassCurve.Affine.placeOfPoint
                  (0 : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Point))
        ∧ (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
            WeierstrassCurve.Affine.Point.some x y h ∉ AddSubgroup.zmultiples Q →
            ∃ h' : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Nonsingular
                (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y),
              (WeierstrassCurve.Affine.placeOfPoint (WeierstrassCurve.Affine.Point.some x y h)).restrictAlong ι hι
                = WeierstrassCurve.Affine.placeOfPoint (WeierstrassCurve.Affine.Point.some _ _ h')) := by
  haveI : W.toAffine.IsElliptic := ‹W.IsElliptic›
  rw [← hord]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hQ : Q = 0 := by rwa [Nat.mul_zero, Nat.zero_add, AddMonoid.addOrderOf_eq_one_iff] at hord
    have hS : W.oddOrderSummingSet Q 0 = ∅ := by
      simp [WeierstrassCurve.oddOrderSummingSet]
    have hV : W.veluQuotient (W.oddOrderSummingSet Q 0) = W := by
      rw [hS]; simp [WeierstrassCurve.veluQuotient, WeierstrassCurve.veluT, WeierstrassCurve.veluW]
    exact s2c_zero (W.veluQuotient (W.oddOrderSummingSet Q 0)) hV hQ _ hS
  · have hhalf : n = (2 * n + 1 - 1) / 2 := by omega
    revert hΔ'
    rename_i i1 i2 i3 i4 i5 i6 i7
    revert i1 i5 i6 i7
    rw [hhalf]
    intro i1 i5 i6 i7 hΔ'
    exact s2c_key (W := W) (by omega) ⟨n, by ring⟩ hord hΔ'

/-- The plain `restrictAlong` isomorphism: the general statement with
`[CharZero F]` assumed.  Proved as a corollary of the general theorem (no
transcribed proof body). -/
theorem exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.IsElliptic]
    {Q : W.toAffine.Point} {n : ℕ} (hord : addOrderOf Q = 2 * n + 1)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    [(W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine] :
    ∃ (ι : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      AlgebraicCurve.finrankAlong F ι = 2 * n + 1
        ∧ (∀ hN : AlgebraicCurve.NormFormulaAlong F ι hfin,
            (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
              = AddSubgroup.zmultiples Q)
        ∧ (∀ P : W.toAffine.Point, P ∈ AddSubgroup.zmultiples Q →
            (WeierstrassCurve.Affine.placeOfPoint P).restrictAlong ι hι
              = WeierstrassCurve.Affine.placeOfPoint
                  (0 : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Point))
        ∧ (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
            WeierstrassCurve.Affine.Point.some x y h ∉ AddSubgroup.zmultiples Q →
            ∃ h' : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Nonsingular
                (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y),
              (WeierstrassCurve.Affine.placeOfPoint (WeierstrassCurve.Affine.Point.some x y h)).restrictAlong ι hι
                = WeierstrassCurve.Affine.placeOfPoint (WeierstrassCurve.Affine.Point.some _ _ h')) :=
  exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed hord hΔ'

end WeierstrassCurve

end
