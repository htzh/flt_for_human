/-
The multiplication-formula bridge, layer 1: evaluation at the universal point.

Ported from `Definitions/Def_WeierstrassCurve_EDSEngine.lean`, pinned at
`aa2d8b3`, the start of `PortEllSequenceZSMul`. See `logs/card-torsion-port.md`.

This layer transports the division polynomials (`ψ₂`, `Ψ₃`, `preΨ₄`, `ψ`, `φ`,
`ωe`) along `specialize : MvPolynomial Coeff ℤ →+* R`, giving the evaluations
`polyEval W x y`, and introduces `ψᵤ = polyToField (curve.ψ n)`, the universal
division polynomial seen in the fraction field of the universal coordinate ring.
-/
import FLTForHuman.Elliptic.Omega
import FLTForHuman.Elliptic.Universal

open scoped Polynomial Polynomial.Bivariate
open scoped FLTForHuman.Elliptic
open scoped nonZeroDivisors
open Polynomial
open WeierstrassCurve
open WeierstrassCurve.Affine (polynomial polynomialY polynomialX negPolynomial)

namespace FLTForHuman.Elliptic

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
variable {x y : R}

noncomputable section

namespace Univ

lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]

lemma evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]

lemma evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]

variable {m n : ℤ}

lemma evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]

lemma evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]

lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by
  simp [cusp, ψ₂, Affine.polynomialY, map_ofNat]

lemma cusp_Ψ₃ : cusp.Ψ₃ = 3 * X ^ 4 := by simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]
lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]

lemma polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n := by
  rw [WeierstrassCurve.ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄,
    cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval, normEDS_two_three_two]

lemma polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1 := by
  have hψ : ∀ m : ℤ, eval₂ (eval₂RingHom (specialize cusp) 1) 1 (curve.ψ m) = m :=
    fun m => polyEval_cusp_ψ (n := m)
  rw [WeierstrassCurve.φ, show polyEval cusp 1 1
      = eval₂RingHom (eval₂RingHom (specialize cusp) 1) 1 from rfl]
  simp only [coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, hψ]
  ring

lemma polyEval_cusp_ψc : polyEval cusp 1 1 (ψc curve n) = 2 := by
  rw [ψc, map_complEDS₂, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]
  simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, complEDS₂_two_three_two]

/-- The universal division polynomial, in the fraction field of the universal
coordinate ring. -/
abbrev ψᵤ (n : ℤ) : Univ.Field := polyToField (curve.ψ n)

lemma ψᵤ_eq_normEDS : ψᵤ = normEDS (polyToField curve.ψ₂) (polyToField (C curve.Ψ₃))
    (polyToField (C curve.preΨ₄)) := by
  ext; rw [← map_normEDS]; rfl

lemma isEllipticSequence_ψᵤ : IsEllipticSequence ψᵤ := by
  rw [ψᵤ_eq_normEDS]
  exact normEDS_isEllipticSequence _ _ _

lemma net_ψᵤ (p q r s : ℤ) : net ψᵤ p q r s = 0 := by
  rw [ψᵤ_eq_normEDS]
  exact net_normEDS (polyToField curve.ψ₂) (polyToField (C curve.Ψ₃))
    (polyToField (C curve.preΨ₄)) p q r s

lemma ψᵤ_ne_zero (h0 : n ≠ 0) : ψᵤ n ≠ 0 := fun h ↦ by
  rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h
  exact h0 h

lemma polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h

lemma polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]

/-! ### The affine multiplication formula

mathlib's generic `map_sub` / `map_neg` do not fire on `polyToField` (a `def`
returning a `RingHom`), so we state them explicitly; `map_add` / `map_mul` /
`map_pow` work as usual. -/

lemma polyToField_sub (a b : Poly) : polyToField (a - b) = polyToField a - polyToField b :=
  map_sub polyToField a b

lemma polyToField_neg (a : Poly) : polyToField (-a) = -polyToField a :=
  map_neg polyToField a

/-- `x(n • P)`: the `x`-coordinate of `n • P` on the universal curve. -/
def smulX (n : ℤ) : Univ.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2

/-- `y(n • P)`: the `y`-coordinate of `n • P` on the universal curve. -/
def smulY (n : ℤ) : Univ.Field := polyToField (ωe curve n) / (ψᵤ n) ^ 3

@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX, ψᵤ]
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY, ψᵤ]
@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX, ψᵤ]
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]

lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2 := by
  rw [smulX, smulX_one, WeierstrassCurve.φ, polyToField_sub, map_mul, map_pow, map_mul,
    sub_div, mul_div_cancel_right₀]
  exact pow_ne_zero _ (ψᵤ_ne_zero hn)

lemma smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero, ψᵤ]

lemma smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = (ψᵤ (n + m) * ψᵤ (n - m)) / (ψᵤ n * ψᵤ m) ^ 2 := by
  rw [smulX_eq hm, smulX_eq hn, sub_sub_sub_cancel_left, div_sub_div]
  · rw [mul_pow]; congr
    convert (rel₃_of_isEllipticSequence isEllipticSequence_ψᵤ n m 1).symm using 1
    · ring
    · simp [ψᵤ]
  all_goals exact pow_ne_zero _ (ψᵤ_ne_zero <| by assumption)

lemma smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) =
      (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]; ring_nf

lemma smulX_neg : smulX (-n) = smulX n := by
  simp only [smulX, ψᵤ, φ_neg, ψ_neg, polyToField_neg, neg_sq]

lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)

lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [smulX_zero]; exact smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply ψᵤ_ne_zero <;> assumption

lemma smulX_eq_smulX_iff : smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h; exact smulX_ne_smulX h.1 h.2
  · rintro (rfl | rfl); exacts [rfl, smulX_neg]

private lemma smulY_sub_negY_aux {F : Type*} [Field F] {a₁ a₃ x y z : F} (h0 : z ≠ 0) :
    y / z ^ 3 - (-(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃) =
      z * (2 * y + a₁ * x * z + a₃ * z ^ 3) / z ^ 4 := by
  field_simp; ring

lemma smulY_sub_negY (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) = ψᵤ (2 * n) / (ψᵤ n) ^ 4 := by
  simp only [WeierstrassCurve.Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY,
    ψᵤ, ← ψc_spec curve, ← ωe_spec curve, map_mul, map_add, map_pow, map_ofNat]
  exact smulY_sub_negY_aux (ψᵤ_ne_zero h0)

lemma smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one, map_one, one_pow, div_one]

lemma smulY_one_ne_negY : smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1) := by
  rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero

/-- The slope of the tangent at the universal point. -/
def slopeOne : Univ.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

lemma slopeOne_eq_neg_div : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  rw [slopeOne, WeierstrassCurve.Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY,
    WeierstrassCurve.Affine.polynomialX]
  congr
  simp [algebraMap_field_eq_comp, Polynomial.algebraMap_apply, map_ofNat,
    polyToField_sub]

private lemma addX_smul_one_smul_one_aux {F : Type*} [Field F] {a₁ a₂ x dx dy : F} (h0 : dy ≠ 0) :
    (-dx / dy) ^ 2 + a₁ * (-dx / dy) - a₂ - x - x - x =
      (dx ^ 2 - a₁ * dx * dy - (3 * x + a₂) * dy ^ 2) / dy ^ 2 := by
  field_simp; ring

lemma addX_smul_one_smul_one :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := .symm <| by
  rw [smulX_two, WeierstrassCurve.Affine.addX, sub_eq_neg_add, ← eq_sub_iff_add_eq,
    ← neg_div _ (polyToField _), slopeOne_eq_neg_div,
    addX_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)]
  simp only [polyToField_sub, map_add, map_mul, map_pow, map_ofNat, polyToField_ψ₂Sq, ψᵤ,
    ψ_two, ψ_three, C_Ψ₃_eq, polyToField_polynomial, pointedCurve_a₁, pointedCurve_a₂,
    smulX_one]
  ring

private lemma addY_smul_one_smul_one_aux {F : Type*} [Field F] {a₁ a₃ dx dy x y ψ₃ t : F}
    (h0 : dy ≠ 0) :
    ((a₁ * dy - dx) * ψ₃ + 0 * t + (-y - (a₁ * x + a₃)) * dy ^ 3) / dy ^ 3 =
      -(-dx / dy * (x - ψ₃ / dy ^ 2 - x) + y) - a₁ * (x - ψ₃ / dy ^ 2) - a₃ := by
  field_simp; ring

lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := .symm <| by
  rw [smulY, ωe, redInvarDenom_two, one_mul, complEDSAux_two, sub_zero,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, addX_smul_one_smul_one,
    smulX_two, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negPolynomial,
    slopeOne_eq_neg_div, smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]
  simp only [polyToField_sub, polyToField_neg, map_add, map_mul, map_pow, map_ofNat,
    polyToField_polynomial, mul_zero, pointedCurve_a₁, pointedCurve_a₃, ψ_two, ψ₂]
  have hψ2 : polyToField curve.polynomialY ≠ 0 := by
    simpa [ψᵤ, ψ_two, ψ₂] using ψᵤ_ne_zero two_ne_zero
  field_simp
  ring

private lemma smulY_neg_aux {F : Type*} [Field F] {a₁ a₃ x y z : F} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]; field_simp; ring

open Polynomial (CC) in
lemma ωe_neg' : ωe curve (-n) =
    ωe curve n + CC curve.a₁ * curve.φ n * curve.ψ n + CC curve.a₃ * curve.ψ n ^ 3 := by
  refine mul_left_cancel₀ Poly.two_ne_zero ?_
  simp_rw [left_distrib, two_mul_ωe, ψc_neg, ψ_neg, φ_neg]; ring

lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [WeierstrassCurve.Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY,
    ψ_neg, ωe_neg', map_add, polyToField_neg, map_mul, map_pow, ψᵤ]
  exact smulY_neg_aux (ψᵤ_ne_zero h0)

private lemma smulX_add_aux {F : Type*} [Field F] {m n m₂ n₂ a s : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    n₂ / n ^ 4 * (m₂ / m ^ 4) / (a * s / (n * m) ^ 2) ^ 2 = n₂ * m₂ / (a * s) ^ 2 := by
  field_simp

lemma smulX_add (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    smulX (n + m) = smulX (n - m) -
      ψ₂ (smulX n) (smulY n) * ψ₂ (smulX m) (smulY m) / (smulX m - smulX n) ^ 2 := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', smulX_sub_sub_smulX_add add_ne sub_ne]
  simp_rw [smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hm hn]
  apply smulX_add_aux <;> apply ψᵤ_ne_zero <;> assumption

private lemma smulY_add_sub_negY_aux {F : Type*} [Field F] {m n m₂ n₂ a s am an : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    (m₂ / m ^ 4 * (an * m / (a * n) ^ 2) - n₂ / n ^ 4 * (am * n / (a * m) ^ 2))
      / (a * s / (n * m) ^ 2)
      = (an * m₂ * n - am * n₂ * m) * a / (s * n * m) / a ^ 4 := by
  field_simp

lemma smulY_add_sub_negY (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    ψ₂ (smulX (n + m)) (smulY (n + m)) =
      (ψ₂ (smulX m) (smulY m) * (smulX n - smulX (n + m))
        - ψ₂ (smulX n) (smulY n) * (smulX m - smulX (n + m))) / (smulX m - smulX n) := by
  simp_rw [smulY_sub_negY add_ne, smulY_sub_negY hm, smulY_sub_negY hn,
    smulX_sub_smulX hn add_ne, smulX_sub_smulX hm add_ne, smulX_sub_smulX hm hn,
    add_sub_cancel_left, add_sub_cancel_right]
  rw [smulY_add_sub_negY_aux]
  · congr; rw [eq_div_iff]
    · linear_combination (norm := ring_nf) (net_add_sub_iff (W := ψᵤ) n m).mp (net_ψᵤ _ _ _ _)
    apply_rules [mul_ne_zero, ψᵤ_ne_zero]
  all_goals apply ψᵤ_ne_zero; assumption

open WeierstrassCurve.Affine.Point

instance : AddGroup (curve⟮Univ.Field⟯) := inferInstance

/-- The affine multiplication formula: `n • P = (smulX n, smulY n)` on the
universal curve. -/
theorem zsmul_point_eq_smulX_smulY : n ≠ 0 →
    ∃ h : WeierstrassCurve.Affine.Nonsingular curveField (smulX n) (smulY n),
      n • affinePoint = .some (smulX n) (smulY n) h := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih h0 ↦ ?_
    obtain _ | _ | _ | n := n
    · exact (h0 rfl).elim
    · simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]
      exact ⟨(pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        (by simpa only [pointedCurve, WeierstrassCurve.baseChange, map_Δ,
          map_ne_zero_iff _ algebraMap_field_injective] using Δ_curve_ne_zero)).mp
          equation_point, rfl⟩
    all_goals obtain ⟨ns, eq⟩ := ih 1 (by omega) one_ne_zero
    · erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]
      exact ⟨WeierstrassCurve.Affine.nonsingular_add ns ns fun h ↦ smulY_one_ne_negY h.2,
        dite_eq_right fun h ↦ smulY_one_ne_negY h.2⟩
    set n2 := n + 1 + 1
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)
    simp_rw [show (n + 1 : ℕ) = n2 + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    let _U := pointedCurve.toAffine
    erw [eq2, eq, WeierstrassCurve.Affine.Point.add_of_X_ne ne, some.injEq] at eq1
    let L := _U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX (n2 + 1 : ℕ) = _U.addX (smulX n2) (smulX 1) L := by
      rw [Nat.cast_add, Nat.cast_one, smulX_add one_ne_zero (by omega) (by omega) (by omega),
        WeierstrassCurve.Affine.addX_eq_addX_negY_sub _ _ ne, sub_eq_add_neg (n2 : ℤ), ← eq1.1]
      rfl
    have Y_eq : smulY (n2 + 1 : ℕ) = _U.addY (smulX n2) (smulX 1) (smulY n2) L := by
      refine mul_left_cancel₀ (Univ.Field.two_ne_zero) ?_
      rw [← add_right_cancel_iff (a := _U.a₁ * smulX (n2 + 1 : ℕ) + _U.a₃)]
      convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1
      · simp_rw [WeierstrassCurve.Affine.negY, Nat.cast_add]; simp only [_U]; ring_nf
      convert _U.addY_sub_negY_addY (smulY n2) (smulY 1) ne using 1
      · rw [WeierstrassCurve.Affine.negY, ← X_eq]; ring
      · rw [← X_eq]; rfl
    rw [X_eq, Y_eq, n2.cast_add, add_zsmul, eq, eq2]
    exact ⟨WeierstrassCurve.Affine.nonsingular_add ns2 ns fun h ↦ (ne h.1).elim,
      WeierstrassCurve.Affine.Point.add_of_X_ne ne⟩
  | neg hn n =>
    rw [neg_ne_zero]; intro h0
    obtain ⟨ns, eq⟩ := hn n h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, WeierstrassCurve.Affine.Point.neg_some]
    exact ⟨(WeierstrassCurve.Affine.nonsingular_neg ..).mpr ns, trivial⟩

end Univ

end

end FLTForHuman.Elliptic
