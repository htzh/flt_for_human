/-
The multiplication-formula bridge, layer 3: the Jacobian re-packaging.

Ported from `Definitions/Def_WeierstrassCurve_EDSEngine.lean`, pinned at
`aa2d8b3` (section `PortEllSequenceZSMul`, `namespace Jacobian`). See
`logs/card-torsion-port.md`.

The affine formula `zsmul_point_eq_smulX_smulY` is re-read in projective
coordinates: `n • P` has homogeneous coordinates `[φ n, ω n, ψ n]`. This is the
form the counting argument uses, because `ψ n` is exactly the polynomial whose
vanishing cuts out the `n`-torsion.
-/
import FLTForHuman.Elliptic.MulFormula

open scoped Polynomial Polynomial.Bivariate
open scoped FLTForHuman.Elliptic
open scoped nonZeroDivisors
open Polynomial
open WeierstrassCurve
open WeierstrassCurve.Jacobian

namespace FLTForHuman.Elliptic

noncomputable section

namespace Univ

variable {m n : ℤ}

/-- Homogeneous coordinates `[φ n, ω n, ψ n]` of `n • P`. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, ωe curve n, curve.ψ n]

abbrev smulRing (n : ℤ) : Fin 3 → Univ.Ring := AdjoinRoot.mk _ ∘ smulPoly n

abbrev smulField (n : ℤ) : Fin 3 → Univ.Field := polyToField ∘ smulPoly n

lemma polyToField_comp_smul (P : Fin 3 → Poly) (u : Poly) :
    polyToField ∘ (u • P) = polyToField u • (polyToField ∘ P) :=
  Jacobian.comp_smul polyToField P u

lemma jacobian_map_curvePoly_polyToField :
    Jacobian.map curvePoly polyToField = curveField := rfl

lemma polyToField_jacobian_neg (P : Fin 3 → Poly) :
    polyToField ∘ Jacobian.neg curvePoly P = Jacobian.neg curveField (polyToField ∘ P) :=
  (Jacobian.map_neg polyToField P).symm

lemma algebraMap_comp_smulRing (n : ℤ) :
    algebraMap Univ.Ring Univ.Field ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl

lemma point_point : jacobianPoint.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl

lemma zsmul_affinePoint_ne_zero (h0 : n ≠ 0) : n • affinePoint ≠ 0 := by
  obtain ⟨h, heq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [heq]
  exact fun hc => by cases hc

lemma zsmul_jacobianPoint_ne_zero (h0 : n ≠ 0) : n • jacobianPoint ≠ 0 := by
  rw [jacobianPoint, ← Point.toAffineAddEquiv_symm_apply,
    ← map_zsmul (Point.toAffineAddEquiv _).symm, Ne,
    map_eq_zero_iff _ (Point.toAffineAddEquiv _).symm.injective]
  exact zsmul_affinePoint_ne_zero h0

lemma zsmul_point_ne (h : m ≠ n) : m • jacobianPoint ≠ n • jacobianPoint := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_jacobianPoint_ne_zero (sub_ne_zero.mpr h)

lemma smulPoly_zero : smulPoly 0 = ![1, 1, 0] := by simp [smulPoly]
lemma smulField_zero : smulField 0 = ![1, 1, 0] := by
  simp [smulField, smulPoly_zero, comp_fin3]

lemma addZ_smulPoly : addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m) := by
  have hES : IsEllipticSequence (WeierstrassCurve.ψ curve) := by
    rw [show WeierstrassCurve.ψ curve
        = normEDS curve.ψ₂ (C curve.Ψ₃) (C curve.preΨ₄) from rfl]
    exact normEDS_isEllipticSequence _ _ _
  simp_rw [addZ, smulPoly, WeierstrassCurve.φ]
  convert (rel₃_of_isEllipticSequence hES n m 1).symm using 1
  · simp only [fin3_def_ext]; ring
  · rw [ψ_one]; ring

lemma ωe_neg_eq_neg_negY : ωe curve (-n) = -Jacobian.negY curvePoly (smulPoly n) := by
  simp_rw [ωe_neg' (n := n), Jacobian.negY, smulPoly, fin3_def_ext, curvePoly,
    WeierstrassCurve.baseChange, WeierstrassCurve.map, coe_algebraMap_eq_CC]
  ring

lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • Jacobian.neg curvePoly (smulPoly n) := by
  funext i; fin_cases i <;>
    simp only [smulPoly, ωe_neg_eq_neg_negY, Jacobian.neg, Jacobian.smul_fin3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue, Fin.reduceFinMk, φ_neg, ψ_neg,
      show (-1 : Poly) ^ 2 = 1 by ring,
      show (-1 : Poly) ^ 3 = -1 by ring] <;>
    ring

lemma smulRing_neg : smulRing (-n) = (-1 : Univ.Ring) • Jacobian.neg curveRing (smulRing n) := by
  change AdjoinRoot.mk _ ∘ smulPoly (-n)
    = (-1 : Univ.Ring) • Jacobian.neg curveRing (AdjoinRoot.mk _ ∘ smulPoly n)
  simp only [smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]
  rfl

lemma smulField_neg : smulField (-n) = (-1 : Univ.Field) • Jacobian.neg curveField (smulField n) := by
  change polyToField ∘ smulPoly (-n)
    = (-1 : Univ.Field) • Jacobian.neg curveField (polyToField ∘ smulPoly n)
  rw [smulPoly_neg, polyToField_comp_smul, polyToField_jacobian_neg,
    show polyToField (-1 : Poly) = -1 by simp [polyToField_neg]]

lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  have hkey : ωe curve n - Jacobian.negY curvePoly (smulPoly n) = ψc curve n := by
    rw [sub_eq_add_neg, ← ωe_neg_eq_neg_negY, ωe_neg']
    linear_combination two_mul_ωe curve n
  rw [show dblZ curvePoly (smulPoly n)
      = curve.ψ n * (ωe curve n - Jacobian.negY curvePoly (smulPoly n)) from rfl, hkey,
    ψc_spec]

lemma zsmul_point_eq_smulField : (n • jacobianPoint).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n), smulField, smulPoly]
  simp_rw [Function.comp, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ωe_zero, ψ_zero, map_zero, map_one]; rfl
  obtain ⟨ns, heq⟩ := zsmul_point_eq_smulX_smulY hn
  rw [jacobianPoint, ← Point.toAffineAddEquiv_symm_apply, ← map_zsmul, heq]
  have hψ := ψᵤ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero hψ), ?_⟩
  simp_rw [Units.smul_def, smul_fin3]
  ext i; fin_cases i <;>
    simp only [Units.val_mk0, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    field_simp [smulX, smulY, hψ] <;> rfl

lemma nonsingular_smulField : Nonsingular curveField (smulField n) := by
  simpa only [zsmul_point_eq_smulField, nonsingularLift_iff] using
    (n • jacobianPoint).nonsingular

lemma dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero]
    have h0 : smulField (0 : ℤ) = ![1, 1, 0] := by
      ext i; fin_cases i <;> simp [smulField, smulPoly, φ_zero, ωe_zero, ψ_zero]
    rw [h0, dblXYZ_of_Z_eq_zero equation_zero rfl]
    simp
  have h2 : ((2 : ℤ) • (n • jacobianPoint)).point = ⟦dblXYZ curveField (smulField n)⟧ := by
    rw [two_zsmul, Point.add_point, zsmul_point_eq_smulField, addMap_eq, add_self]
  refine (equiv_iff_eq_of_Z_eq ?_ (ψᵤ_ne_zero <| mul_ne_zero two_ne_zero hn)).mp
    (Quotient.exact ?_)
  · rw [dblXYZ_Z, ← jacobian_map_curvePoly_polyToField,
      Jacobian.map_dblZ (W' := curvePoly) (f := polyToField), dblZ_smulPoly]
    rfl
  rw [← h2, ← mul_zsmul]
  exact zsmul_point_eq_smulField

lemma polyToField_dblZ (P : Fin 3 → Poly) :
    polyToField (dblZ curvePoly P) = dblZ curveField (polyToField ∘ P) := by
  rw [← jacobian_map_curvePoly_polyToField]
  exact (Jacobian.map_dblZ (W' := curvePoly) (f := polyToField) P).symm

lemma polyToField_addZ (P Q : Fin 3 → Poly) :
    addZ (polyToField ∘ P) (polyToField ∘ Q) = polyToField (addZ P Q) :=
  Jacobian.map_addZ polyToField P Q

lemma dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) :=
  (IsFractionRing.injective Univ.Ring Univ.Field).comp_left <| by
    simp_rw [← map_dblXYZ]; exact dblXYZ_smulField

lemma addXYZ_smulField :
    addXYZ curveField (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, ψ_zero, map_zero, smul_fin3,
      addXYZ_self nonsingular_smulField.1, zero_pow two_ne_zero, zero_pow (by decide)]
    simp_rw [zero_mul]
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · rw [← one_smul (M := Univ.Field) (smulField m), smulField_neg, neg_add_cancel,
      addXYZ_smul, one_mul, neg_one_sq (R := Univ.Field), addXYZ_neg nonsingular_smulField.1,
      one_smul, ← neg_add', ← two_mul, ψ_neg, polyToField_neg, ← dblZ_smulPoly, polyToField_dblZ,
      smulField_zero]
  have hne : ¬ smulField m ≈ smulField n := fun heq ↦ zsmul_point_ne h <| by
    rw [Point.ext_iff, zsmul_point_eq_smulField, zsmul_point_eq_smulField]
    exact Quotient.sound heq
  have key : (m • jacobianPoint + n • jacobianPoint).point =
      ⟦addXYZ curveField (smulField m) (smulField n)⟧ := by
    rw [Point.add_point, zsmul_point_eq_smulField, zsmul_point_eq_smulField, addMap_eq,
      add_of_not_equiv hne]
  erw [← equiv_iff_eq_of_Z_eq]
  · exact Quotient.exact (by
      rw [smul_eq _ (ψᵤ_ne_zero <| sub_ne_zero_of_ne h.symm).isUnit,
        ← zsmul_point_eq_smulField, add_comm, add_zsmul, key])
  · conv_rhs => rw [smulField, comp_fin3, smul_fin3, (fin3_def_ext _ _ _).2.2, mul_comm]
    simp only [addXYZ, fin3_def_ext, ← map_mul, ← addZ_smulPoly]
    rw [show addZ (smulField m) (smulField n)
        = polyToField (addZ (smulPoly m) (smulPoly n)) from polyToField_addZ _ _]
  · rw [(smul_fin3_ext _ _).2.2]
    apply mul_ne_zero <;> apply ψᵤ_ne_zero <;> omega

lemma addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) :=
  (IsFractionRing.injective Univ.Ring Univ.Field).comp_left <| by
    simp_rw [← map_addXYZ, Jacobian.comp_smul]; exact addXYZ_smulField

lemma addXYZ_smulField₁ :
    addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1) := by
  rw [addXYZ_smulField, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm,
    add_assoc]

lemma addXYZ_smulRing₁ :
    addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1) := by
  rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm,
    add_assoc]

end Univ

section Eval

open Univ

variable {R : Type*} [CommRing R]

/-- The multiplication-formula coordinates evaluated at `(x, y)`. -/
abbrev smulEval (W : WeierstrassCurve R) (x y : R) (n : ℤ) : Fin 3 → R :=
  evalEval x y ∘ ![W.φ n, ωe W n, W.ψ n]

lemma ringEval_comp_smulRing {W : WeierstrassCurve R} {x y : R}
    (eqn : W.toAffine.Equation x y) (n : ℤ) :
    ringEval eqn ∘ smulRing n = smulEval W x y n := by
  conv_rhs => rw [smulEval, ← map_specialize W, map_φ, map_ωe, map_ψ, ← coe_mapRingHom,
    ← Jacobian.comp_fin3, ← Function.comp_assoc, ← smulPoly, ← coe_evalEvalRingHom,
    ← RingHom.coe_comp, ← eval₂RingHom_eval₂RingHom]
  rw [smulRing, ← Function.comp_assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]

lemma ringEval_ψ {W : WeierstrassCurve R} {x y : R} (eqn : W.toAffine.Equation x y) (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2

lemma dblXYZ_smulEval {W : WeierstrassCurve R} {x y : R} (eqn : W.toAffine.Equation x y) (n : ℤ) :
    dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]

lemma addXYZ_smulEval {W : WeierstrassCurve R} {x y : R} (eqn : W.toAffine.Equation x y) (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
  rw [← Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]
  simp_rw [curveRing_map_ringEval]

lemma addXYZ_smulEval₁ {W : WeierstrassCurve R} {x y : R} (eqn : W.toAffine.Equation x y) (n : ℤ) :
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ,
    curveRing_map_ringEval]

end Eval

variable {F : Type*} [Field F]

open Univ WeierstrassCurve.Jacobian

theorem zsmul_eq_smulEval (W : WeierstrassCurve F) {x y : F}
    (h : WeierstrassCurve.Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (WeierstrassCurve.Affine.Point.some x y h)).point =
      ⟦smulEval W x y n⟧ := by
  have add_point_eq : ∀ (P Q : Point W) (P' Q' : Fin 3 → F),
      P.point = ⟦P'⟧ → Q.point = ⟦Q'⟧ → (P + Q).point = ⟦Jacobian.add W P' Q'⟧ := by
    intro P Q P' Q' hP hQ
    rw [Point.add_point, hP, hQ, addMap_eq]
  have two_zsmul_point : ∀ (P : Point W) (P' : Fin 3 → F), P.point = ⟦P'⟧ →
      (2 • P).point = ⟦dblXYZ W P'⟧ := by
    intro P P' hP
    rw [two_smul, add_point_eq P P P' P' hP hP, Jacobian.add_self]
  have add_point_of_ne : ∀ (P Q : Point W) (P' Q' : Fin 3 → F), P.point = ⟦P'⟧ →
      Q.point = ⟦Q'⟧ → P ≠ Q → (P + Q).point = ⟦addXYZ W P' Q'⟧ := by
    intro P Q P' Q' hP hQ ne
    rw [add_point_eq P Q P' Q' hP hQ, Jacobian.add_of_not_equiv fun h' ↦
      ne (Point.ext <| hP.trans <| (Quotient.sound h').trans hQ.symm)]
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _ | _ | n := n
    · rw [Nat.cast_zero, zero_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    · rw [Nat.cast_one, one_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    obtain ⟨n, rfl | rfl⟩ := n.even_or_odd'
    · rw [add_assoc, ← two_mul, ← left_distrib, Nat.cast_mul, mul_smul, natCast_zsmul,
        two_zsmul_point _ _ (ih _ <| by omega), dblXYZ_smulEval h.1 ((n + 1 : ℕ) : ℤ)]; rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul,
        add_point_of_ne _ _ _ _ (ih _ <| by omega) (ih _ <| by omega), Nat.cast_add (n + 1),
        Nat.cast_one, addXYZ_smulEval₁ h.1 ((n + 1 : ℕ) : ℤ), ← add_assoc, two_mul]
      simp_rw [Nat.cast_add]
      rw [ne_comm, ← sub_ne_zero, ← sub_smul, add_sub_cancel_left, Nat.cast_one, one_smul]
      apply Point.fromAffine_some_ne_zero
  | neg hn n =>
    simp_rw [_root_.neg_smul, Point.neg_point, hn, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg, Jacobian.comp_smul,
      ← Jacobian.map_neg, curveRing_map_ringEval, map_neg, map_one]
    rfl

end

end FLTForHuman.Elliptic
