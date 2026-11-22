/-
  The division-polynomial point arithmetic of a Weierstrass curve.

  Five rows of the group law read through the division polynomials `ψ`, `ΨSq` and `Φ`:

  * `Affine.evalEval_psi_sq`: on the curve, `ψ n` evaluated at a point equals `ΨSq n` at its
    `x`-coordinate, squared — the polynomial identity behind the multiplication-by-`n` formula;
  * `Affine.Point.zsmul_some_eq_some_div`: `n • P` has `x`-coordinate `Φ n / ΨSq n` (with some
    `y`-coordinate), for `ψ n` non-vanishing at `P`;
  * `Affine.Point.smul_some_eq_zero_iff`: `n • P = 0` iff `ψ n` vanishes at `P`;
  * `Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one`: on `y² = x³ + B`, the three points
    `(x, y)`, `(wx, y)`, `(w²x, y)` with `w³ = 1`, `w ≠ 1` satisfy `P + P' = -P''` — the 3-torsion
    cycle;
  * `Affine.Point.some_zero_add_self_eq_neg_of_a6_model`: on the same model in odd characteristic,
    `(0, y) + (0, y) = -(0, y)`.

  Transcribed from the five pins below (pinned `aa2d8b3`, 100 + 40 + 34 + 29 + 28 lines), all
  public.  High outbound demand (project fan-in 41, 44, 51) for a small surface.

  Premises.  The **definitions** are mathlib's division polynomials
  (`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`: `ψ`, `ΨSq`, `Φ`, `evalEval`),
  but mathlib has no *point* arithmetic for them — in v4.34 the whole `DivisionPolynomial` directory
  never mentions `Affine.Point`.  The multiplication formula `n • P = [φ n, ω n, ψ n]` is the port's
  own transcription of FLT's `Definitions/Def_WeierstrassCurve_EDSEngine.lean`:
  `FLTForHuman/Elliptic/{MulFormula,JacobianMulFormula,Bridge}.lean`, holding `smulEval`,
  `zsmul_eq_smulEval`, `smul_eq_zero_iff_evalEval_ψ`, `evalEval_ψ_sq` and `evalEval_φ`.  This module
  imports the tail of that chain (`Elliptic.Bridge`) — the pin's own premise — and re-derives the
  coordinate consequence here at the pin's ℤ-exponent statements.

  Rows kept as the pins spell them.  `PortCard.*` is the pin's own inner namespace (its
  `PortCardMulX` section), kept because `PortCard.zsmul_some_eq_some_div` and the headline
  `Affine.Point.zsmul_some_eq_some_div` would otherwise collide on one full name (FR-0274).
  Two **duplicate pairs are the pin's own**, not the port's, and are recorded here for the dedup
  gate (`dedup.py --within` reads 2 `shape` clusters, 12 removable lines — this paragraph is the
  reason, no action): `PortCard.evalEval_ψ_sq` (`S_…_evalEval_psi_sq.lean:8`) and `evalEval_psi_sq`
  (`:28`) are the same statement in the pin, and `ws13_some_congr`
  (`S_…_pow_three_eq_one.lean:9`) and `ws13_some_congr'` (`S_…_a6_model.lean:9`) are the same
  statement in two pins; the checker requires all four rows by name, so the port carries them
  verbatim.

  No `set_option` is transcribed: none of the five pins carries a `linter.*` line or a
  `maxHeartbeats` bump (they carry `autoImplicit false`, which the project sets at file level).

  Heartbeat probe (FR-0225, recorded not installed): the module is silent at
  `-DmaxHeartbeats=3200` and fails at `-DmaxHeartbeats=3000` (deterministic timeout at `whnf`,
  `:163` — the `show` that unfolds the `smulEval` abbreviation in
  `PortCard.zsmul_some_eq_some_of_evalEval_ψ_ne_zero`), i.e. it costs ≈3 k heartbeats, ~1.5 % of the
  200 k default.  No `set_option maxHeartbeats` anywhere.

  spec-pin: P2M/Sol/S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_Affine_evalEval_psi_sq.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff.lean
-/
import FLTForHuman.Elliptic.Bridge
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

/-! ### The polynomial identities of `ψ`, `φ`, `ΨSq` and `Φ` on the curve -/

/-- On a point of the curve, `ψ n` squared is `ΨSq n` at the `x`-coordinate: the coordinate ring
`mk` of `ψ n ^ 2` and of `C (ΨSq n)` agree, and evaluating the difference of representatives at
`(x, y)` kills it because `(x, y)` is on the curve. -/
theorem WeierstrassCurve.Affine.evalEval_psi_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have h0 : W.toAffine.polynomial.eval₂ (evalRingHom x) y = 0 := by
    rw [eval₂_evalRingHom]; exact h
  let e : W.toAffine.CoordinateRing →+* R := AdjoinRoot.lift (evalRingHom x) y h0
  have he : ∀ p : R[X][Y], e (WeierstrassCurve.Affine.CoordinateRing.mk W p) = p.evalEval x y :=
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

/-- The pin's own spelling of the row above (`S_…_evalEval_psi_sq.lean:8`); the pin states the same
identity twice, once as this engine row and once as its `solution` (`:28`, the headline). -/
theorem WeierstrassCurve.Affine.PortCard.evalEval_ψ_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x :=
  WeierstrassCurve.Affine.evalEval_psi_sq W h n

/-- On a point of the curve, `φ n` agrees with mathlib's univariate `Φ n` at the `x`-coordinate. -/
theorem WeierstrassCurve.Affine.PortCard.evalEval_φ {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

/-! ### `Point.some` congruence: the `Nonsingular` proof is irrelevant -/

/-- Two `Point.some` values with equal coordinates are equal, whatever their `Nonsingular` proofs. -/
theorem WeierstrassCurve.Affine.Point.ws13_some_congr {k : Type*} [Field k] {V : Affine k} {x₁ x₂ y₁ y₂ : k}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

/-- The second pin's copy of the same congruence (`S_…_a6_model.lean:9`); kept verbatim because the
checker reads both pins. -/
theorem WeierstrassCurve.Affine.Point.ws13_some_congr' {k : Type*} [Field k] {V : Affine k} {x₁ x₂ y₁ y₂ : k}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

/-! ### The multiplication formula

`n • P` is the affine read-off of the Jacobian point `n • P = [φ n, ω n, ψ n]`; the three engine
rows below rewrite that in `Φ`/`ΨSq`, and the fourth clears the denominator. -/

section PointCard

open FLTForHuman.Elliptic

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- `n • P` has coordinates `(φ n / ψ n ^ 2, ω n / ψ n ^ 3)`; here both coordinate equations are
kept, in `ψ`/`φ` form and in `Φ`/`ΨSq` form. -/
theorem WeierstrassCurve.Affine.Point.PortCard.zsmul_some_eq_some_of_evalEval_ψ_ne_zero {x y : F}
    (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧
        x' * (W.ψ n).evalEval x y ^ 2 = (W.φ n).evalEval x y ∧
        x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have heq : W.toAffine.Equation x y := h.left
  have hψsq := WeierstrassCurve.Affine.evalEval_psi_sq W heq n
  have key := zsmul_eq_smulEval W h n
  have hVz : smulEval W x y n 2 ≠ 0 := hψ
  have hV := key ▸ (n • Jacobian.Point.fromAffine (Point.some x y h)).nonsingular
  have hQeq : (n • Jacobian.Point.fromAffine (Point.some x y h)) =
      Jacobian.Point.mk hV := Jacobian.Point.ext key
  refine ⟨smulEval W x y n 0 / smulEval W x y n 2 ^ 2,
    smulEval W x y n 1 / smulEval W x y n 2 ^ 3,
    (Jacobian.nonsingular_of_Z_ne_zero hVz).mp hV, ?_, ?_, ?_⟩
  · calc n • Point.some x y h
        = Jacobian.Point.toAffineAddEquiv W
            (n • Jacobian.Point.fromAffine (Point.some x y h)) := by
          rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
            AddEquiv.apply_symm_apply]
      _ = _ := by
          rw [hQeq, Jacobian.Point.toAffineAddEquiv_apply]
          exact Jacobian.Point.toAffineLift_of_Z_ne_zero hVz
  · show (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ψ n).evalEval x y ^ 2 =
        (W.φ n).evalEval x y
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hψ)]
  · show (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ΨSq n).eval x = (W.Φ n).eval x
    rw [← hψsq, div_mul_cancel₀ _ (pow_ne_zero 2 hψ), WeierstrassCurve.Affine.PortCard.evalEval_φ W heq n]

/-- The same formula under the non-vanishing of `ΨSq n`, which forces `ψ n` not to vanish on the
curve. -/
theorem WeierstrassCurve.Affine.Point.PortCard.zsmul_some_eq_some_of_eval_ΨSq_ne_zero {x y : F}
    (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : (W.ΨSq n).eval x ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧ x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have hψ : (W.ψ n).evalEval x y ≠ 0 := fun h0 =>
    hn (by rw [← WeierstrassCurve.Affine.evalEval_psi_sq W h.left n, h0]; exact zero_pow two_ne_zero)
  obtain ⟨x', y', h', hP, -, hx⟩ :=
    WeierstrassCurve.Affine.Point.PortCard.zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  exact ⟨x', y', h', hP, hx⟩

/-- `n • P = 0` exactly at the roots of `ΨSq n`: a homogenised point is zero iff its `Z`-coordinate
`ψ n` vanishes, and `ψ n ^ 2 = ΨSq n` on the curve. -/
theorem WeierstrassCurve.Affine.Point.PortCard.zsmul_some_eq_zero_iff_eval_ΨSq {x y : F}
    (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • Point.some x y h = 0 ↔ (W.ΨSq n).eval x = 0 := by
  rw [smul_eq_zero_iff_evalEval_ψ W h n,
    ← WeierstrassCurve.Affine.evalEval_psi_sq W h.left n]
  exact ⟨fun h0 => by rw [h0]; exact zero_pow two_ne_zero, fun h0 => (sq_eq_zero_iff).mp h0⟩

/-- The headline's coordinate formula with the denominator cleared: `x`-coordinate `Φ n / ΨSq n`. -/
theorem WeierstrassCurve.Affine.Point.PortCard.zsmul_some_eq_some_div {x y : F}
    (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'),
      n • Point.some x y h = Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' := by
  obtain ⟨x', y', h', hP, -, hx⟩ :=
    WeierstrassCurve.Affine.Point.PortCard.zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  have hΨ : (W.ΨSq n).eval x ≠ 0 := by
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq W h.left n]; exact pow_ne_zero 2 hψ
  obtain rfl : x' = (W.Φ n).eval x / (W.ΨSq n).eval x := by rw [eq_div_iff hΨ]; exact hx
  exact ⟨y', h', hP⟩

end PointCard

/-! ### The headlines -/

theorem WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'),
      n • WeierstrassCurve.Affine.Point.some x y h =
        WeierstrassCurve.Affine.Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' :=
  WeierstrassCurve.Affine.Point.PortCard.zsmul_some_eq_some_div W h hψ

theorem WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 :=
  FLTForHuman.Elliptic.smul_eq_zero_iff_evalEval_ψ W h n

/-! ### Two chord–tangent rows on `y² = x³ + B` -/

/-- The 3-torsion cycle: with `w³ = 1`, `w ≠ 1`, the three points `(x, y)`, `(wx, y)`, `(w²x, y)`
of `y² = x³ + B` satisfy `P + P' = -P''`.  The chord through the first two is horizontal, so the
slope is `0` and the third point of the intersection is their `x`-sum. -/
theorem WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one
    {k : Type*} [Field k] [DecidableEq k] (B w : k) (hw : w ^ 3 = 1) (hw1 : w ≠ 1) {x y : k}
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular x y)
    (hwx : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w * x) y)
    (hw2x : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w ^ 2 * x) y) (hx : x ≠ 0) :
    (WeierstrassCurve.Affine.Point.some x y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some (w * x) y hwx
      = -(WeierstrassCurve.Affine.Point.some (w ^ 2 * x) y hw2x) := by
  have hsum : 1 + w + w ^ 2 = 0 := by
    have h0 : (w - 1) * (1 + w + w ^ 2) = 0 := by linear_combination hw
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hw1
    · exact h1
  have hxne : x ≠ w * x := by
    intro heq
    have h0 : (1 - w) * x = 0 := by linear_combination heq
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hw1 (by linear_combination -h1)
    · exact hx h1
  rw [Point.add_of_X_ne hxne, Point.neg_some]
  refine WeierstrassCurve.Affine.Point.ws13_some_congr ?_ ?_
  · rw [slope_of_X_ne hxne, sub_self, zero_div]
    simp only [Affine.addX]
    linear_combination -x * hsum
  · rw [slope_of_X_ne hxne, sub_self, zero_div]
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]
    ring

/-- In odd characteristic, `(0, y)` on `y² = x³ + B` with `y ≠ 0` satisfies `2P = -P`: the tangent
at `(0, y)` is the line `y = const`, whose third intersection point is `(0, -y)`. -/
theorem WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model
    {k : Type*} [Field k] [DecidableEq k] (B : k) (h2 : (2 : k) ≠ 0) {y : k} (hy0 : y ≠ 0)
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular 0 y) :
    (WeierstrassCurve.Affine.Point.some 0 y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some 0 y h
      = -(WeierstrassCurve.Affine.Point.some 0 y h) := by
  have hyne : y ≠ Affine.negY (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k) 0 y := by
    simp only [Affine.negY]
    intro heq
    have : (2 : k) * y = 0 := by linear_combination heq
    rcases mul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hy0 h'
  rw [Point.add_of_Y_ne hyne, Point.neg_some]
  refine WeierstrassCurve.Affine.Point.ws13_some_congr' ?_ ?_
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addX, Affine.negY]
    ring
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]
    ring

end
