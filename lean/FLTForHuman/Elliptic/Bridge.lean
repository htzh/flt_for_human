/-
The multiplication-formula bridge, layer 4: from `n • P = 0` to `ψ n(x, y) = 0`.

Ported from `Definitions/Def_WeierstrassCurve_EDSEngine.lean`, pinned at
`aa2d8b3` (section `PortEllSequenceAffineBridge`, FLT 1806-1865). See
`logs/card-torsion-port.md`.

The Jacobian statement `zsmul_eq_smulEval` says `n • P` has homogeneous
coordinates `[φ n, ω n, ψ n]`. Since a homogeneous point is zero exactly when its
`Z`-coordinate `ψ n` vanishes, `n`-torsion is cut out by the single polynomial
`ψ n` — the bridge into the counting argument. `evalEval_ψ_sq` and `evalEval_φ`
are the two auxiliary evaluations: `ψ n²` agrees with mathlib's univariate `ΨSq`
and `φ n` with mathlib's `Φ`.
-/
import FLTForHuman.Elliptic.JacobianMulFormula

open scoped Polynomial Polynomial.Bivariate
open Polynomial
open WeierstrassCurve WeierstrassCurve.Jacobian

namespace FLTForHuman.Elliptic

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
theorem evalEval_ψ_sq {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h0 : W.toAffine.polynomial.eval₂ (evalRingHom x) y = 0 := by
    rw [eval₂_evalRingHom]; exact h
  let e : W.toAffine.CoordinateRing →+* F := AdjoinRoot.lift (evalRingHom x) y h0
  have he : ∀ p : F[X][Y], e (WeierstrassCurve.Affine.CoordinateRing.mk W p) = p.evalEval x y :=
    fun p ↦ by
      show AdjoinRoot.lift (evalRingHom x) y h0 (AdjoinRoot.mk _ p) = _
      rw [AdjoinRoot.lift_mk, eval₂_evalRingHom]
  calc ((W.ψ n).evalEval x y) ^ 2
      = e (WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n)) ^ 2 := by rw [he]
    _ = e (WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n) ^ 2) := (map_pow e _ 2).symm
    _ = e (WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.ΨSq n))) := by
        rw [WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
          WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]
    _ = (C (W.ΨSq n)).evalEval x y := he _
    _ = (W.ΨSq n).eval x := evalEval_C x y _

omit [DecidableEq F] in
theorem evalEval_φ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

theorem smul_eq_zero_iff_evalEval_ψ {x y : F} (h : W.toAffine.Nonsingular x y)
    (n : ℤ) : n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔
      (W.ψ n).evalEval x y = 0 := by
  have key := zsmul_eq_smulEval W h n
  have hQns := (n • Point.fromAffine (WeierstrassCurve.Affine.Point.some x y h)).nonsingular
  rw [key] at hQns
  calc n • (WeierstrassCurve.Affine.Point.some x y h) = 0
      ↔ (Point.toAffineAddEquiv W).symm (n • WeierstrassCurve.Affine.Point.some x y h) =
        (Point.toAffineAddEquiv W).symm 0 := (AddEquiv.injective _).eq_iff.symm
    _ ↔ n • Point.fromAffine (WeierstrassCurve.Affine.Point.some x y h) = 0 := by
        rw [map_zsmul, map_zero, Point.toAffineAddEquiv_symm_apply]
    _ ↔ (⟦smulEval W x y n⟧ : PointClass F) = ⟦![1, 1, 0]⟧ := by
        rw [Point.ext_iff, key, Point.zero_point]
    _ ↔ (W.ψ n).evalEval x y = 0 := by
        constructor
        · intro heq
          have hz := (Z_eq_zero_of_equiv (Quotient.eq.mp heq)).mpr rfl
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz
        · intro hz
          refine Quotient.eq.mpr (equiv_zero_of_Z_eq_zero
            ((nonsingularLift_iff _).mp hQns) ?_)
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz

end FLTForHuman.Elliptic
