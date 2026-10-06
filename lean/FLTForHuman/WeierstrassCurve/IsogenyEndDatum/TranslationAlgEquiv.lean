/-
V3 — the translation automorphism of the function field of a Weierstrass curve by a
point, and its action on the places of the curve.

Public surface (the two pin headlines, statements verbatim from the wrappers):

* `WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add`
  (characteristic-free — the theorem that is proved);
* `WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add`
  (the `[CharZero F]` sibling, derived in one line).

Everything else is `private`: the pin's second-order Taylor block (`taylorRemainder₂`
… `evalEval_polynomialY_eq_zero_iff_eq_negY`), the one `ord log` leaf the chain
needs that DualEndData does not carry, and the whole
`kwWdp`/`Point.translateFF`/`kwTISD*`/`kw_affod_*`/`kw_taseq_*` chain. The pin's
`solution` is deliberately not declared — the headline *is* the solution.

Source (public mirror, pinned `aa2d8b3`):

* statements:
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_exists_algEquiv_restrictAlong_placeOfPoint_eq_add.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add.lean>;
* proof bodies: `P2M/Sol/S_WeierstrassCurve_Affine_exists_algEquiv_restrictAlong_placeOfPoint_eq_add.lean`
  (the taylor block at L576–972, the ord pair at L2065/L2533, and the `kw_*` chain
  at L3195–4272); the sibling `S_` file supplies the characteristic-free binder
  list.

Assumed from the single import `…IsogenyEndDatum.DualEndData` (whose 100-module
closure transitively supplies `IsogenyEndDatum.Engine`, `Velu.Engine` and
`Place.Dictionary`, and hence `translationAlgEquivOf` with its
`_polyToFunctionField_X`/`_yGen` face, `addXFun`/`addYFun`, the `CoordinateRing`
`XYIdeal`/`XClass`/`YClass` dictionary with `mk_mem_XYIdeal_iff` and the
`ord_placeOfEquation_*` family, the `InfinitePlace` instance, `AbstractSeam.*`, and
the additivity seam `ModularCurve.Es1a1.es1a6_addSeam_restrictAlong_eq_placeOfEquation`).
Two further declarations come from `DualEndData` itself, so they are *not*
re-proved here: `AlgebraicCurve.Place.ord_ofHeightOneSpectrum_eq_neg_log` and
`WeierstrassCurve.Affine.ord_placeOfEquation_XClass_self` (the latter carrying the
`XYIdeal²` non-membership chain `XClass_notMem_XYIdeal_sq` and its five-lemma
support). See `lean/topics/velu/TOPIC-V3-translation-place-action.md` §2.4 (amended
2026-10-06) and §4.2.
-/
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DualEndData

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

universe u

open Polynomial
open scoped Polynomial.Bivariate
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open AlgebraicCurve AlgebraicCurve.Place
open IsDedekindDomain WithZero
open ModularCurve.Es1a1
open scoped WeierstrassCurve.Affine

/-! ## The one `ord log` leaf the chain needs (`DualEndData` lacks the `= 0` form) -/

namespace AlgebraicCurve.Place

variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L]
variable [Algebra K R] [Algebra K L] [IsScalarTower K R L]

private theorem ord_ofHeightOneSpectrum_algebraMap_eq_zero (w : HeightOneSpectrum R) {r : R}
    (hr0 : r ≠ 0) (hr : r ∉ w.asIdeal) :
    (ofHeightOneSpectrum (K := K) (F := L) w).ord (algebraMap R L r) = 0 := by
  have hrL : algebraMap R L r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr hr0
  rw [ord_ofHeightOneSpectrum_eq_neg_log w hrL, w.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hr, log_one, _root_.neg_zero]

end AlgebraicCurve.Place

/-! ## The `ord` leaf at a place of equation and the second-order Taylor block -/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

variable [IsDedekindDomain W.CoordinateRing]

private theorem ord_placeOfEquation_eq_zero_of_evalEval_ne_zero {x₀ y₀ : F}
    (heq : W.Equation x₀ y₀) {q : F[X][Y]} (hq : q.evalEval x₀ y₀ ≠ 0) :
    (placeOfEquation heq).ord
      (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W q)) = 0 := by
  have hnotmem : CoordinateRing.mk W q ∉ XYIdeal W x₀ (C y₀) := fun h =>
    hq ((mk_mem_XYIdeal_iff heq q).mp h)
  have hne : CoordinateRing.mk W q ≠ 0 := fun h => hnotmem (h ▸ Submodule.zero_mem _)
  exact ord_ofHeightOneSpectrum_algebraMap_eq_zero
    (heightOneSpectrumOfEquation heq) hne hnotmem

variable {R : Type*} [CommRing R]

private def taylorRemainder₂ (W : Affine R) (x₀ y₀ : R) : R[X][Y] :=
  (Y - C (C y₀)) ^ 2 + C (C W.a₁ * (X - C x₀)) * (Y - C (C y₀))
    - C ((X - C x₀) ^ 2 * (X + C (2 * x₀ + W.a₂)))

private theorem taylor₂_polynomial (W : Affine R) (x₀ y₀ : R) :
    W.polynomial =
      C (C (W.polynomial.evalEval x₀ y₀))
        + C (C (W.polynomialX.evalEval x₀ y₀) * (X - C x₀))
        + C (C (W.polynomialY.evalEval x₀ y₀)) * (Y - C (C y₀))
        + W.taylorRemainder₂ x₀ y₀ := by
  rw [taylorRemainder₂, evalEval_polynomial, evalEval_polynomialX, evalEval_polynomialY,
    polynomial]
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  ring1

variable {F : Type*} [Field F] {W : Affine F}

private theorem sub_negY_eq_evalEval_polynomialY (x₀ y₀ : F) :
    y₀ - W.negY x₀ y₀ = W.polynomialY.evalEval x₀ y₀ := by
  rw [negY, evalEval_polynomialY]; ring

private theorem evalEval_polynomialY_eq_zero_iff_eq_negY (x₀ y₀ : F) :
    W.polynomialY.evalEval x₀ y₀ = 0 ↔ y₀ = W.negY x₀ y₀ := by
  rw [← sub_negY_eq_evalEval_polynomialY, sub_eq_zero]

private theorem mk_taylorRemainder₂_mem_XYIdeal_sq (x₀ y₀ : F) :
    CoordinateRing.mk W (W.taylorRemainder₂ x₀ y₀) ∈ XYIdeal W x₀ (C y₀) ^ 2 := by
  have hX : XClass W x₀ ∈ XYIdeal W x₀ (C y₀) := Submodule.subset_span (Set.mem_insert _ _)
  have hY : YClass W (C y₀) ∈ XYIdeal W x₀ (C y₀) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hX2 : XClass W x₀ ^ 2 ∈ XYIdeal W x₀ (C y₀) ^ 2 := by
    simpa only [sq] using Ideal.mul_mem_mul hX hX
  have hY2 : YClass W (C y₀) ^ 2 ∈ XYIdeal W x₀ (C y₀) ^ 2 := by
    simpa only [sq] using Ideal.mul_mem_mul hY hY
  have hXY : XClass W x₀ * YClass W (C y₀) ∈ XYIdeal W x₀ (C y₀) ^ 2 := by
    rw [sq]; exact Ideal.mul_mem_mul hX hY
  have key : CoordinateRing.mk W (W.taylorRemainder₂ x₀ y₀) =
      YClass W (C y₀) ^ 2
        + CoordinateRing.mk W (C (C W.a₁)) * (XClass W x₀ * YClass W (C y₀))
        - CoordinateRing.mk W (C (X + C (2 * x₀ + W.a₂))) * XClass W x₀ ^ 2 := by
    simp only [taylorRemainder₂, XClass, YClass, map_sub, map_add, map_mul, map_pow]
    ring1
  rw [key]
  exact sub_mem (add_mem hY2 (Ideal.mul_mem_left _ _ hXY)) (Ideal.mul_mem_left _ _ hX2)

private theorem taylor_linear_mem_XYIdeal_sq {x₀ y₀ : F} (hP : W.Equation x₀ y₀) :
    (algebraMap F W.CoordinateRing) (W.polynomialX.evalEval x₀ y₀) * XClass W x₀
        + (algebraMap F W.CoordinateRing) (W.polynomialY.evalEval x₀ y₀) * YClass W (C y₀)
      ∈ XYIdeal W x₀ (C y₀) ^ 2 := by
  have h0 : CoordinateRing.mk W W.polynomial = 0 := AdjoinRoot.mk_self
  have hF0 : W.polynomial.evalEval x₀ y₀ = 0 := hP
  have hexp := congrArg (CoordinateRing.mk W) (W.taylor₂_polynomial x₀ y₀)
  rw [h0, hF0] at hexp
  have hlin : (algebraMap F W.CoordinateRing) (W.polynomialX.evalEval x₀ y₀) * XClass W x₀
        + (algebraMap F W.CoordinateRing) (W.polynomialY.evalEval x₀ y₀) * YClass W (C y₀)
      = - CoordinateRing.mk W (W.taylorRemainder₂ x₀ y₀) := by
    rw [eq_neg_iff_add_eq_zero]
    rw [show (algebraMap F W.CoordinateRing) (W.polynomialX.evalEval x₀ y₀)
        = CoordinateRing.mk W (C (C (W.polynomialX.evalEval x₀ y₀))) from rfl,
      show (algebraMap F W.CoordinateRing) (W.polynomialY.evalEval x₀ y₀)
        = CoordinateRing.mk W (C (C (W.polynomialY.evalEval x₀ y₀))) from rfl,
      XClass, YClass]
    simp only [map_add, map_mul, _root_.map_zero, zero_add] at hexp
    exact hexp.symm
  rw [hlin]
  exact neg_mem (mk_taylorRemainder₂_mem_XYIdeal_sq x₀ y₀)

end WeierstrassCurve.Affine

/-! ## `translateFF` and the elliptic discriminant -/

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

private theorem kwWdp_Δ_ne_zero_of_isElliptic {W : Affine F} [W.IsElliptic] : W.Δ ≠ 0 :=
  W.coe_Δ' ▸ W.Δ'.ne_zero

section Translate

variable (W : Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]
  [AbelTheorem W]

private def Point.translateFF : W.Point → (W.FunctionField ≃ₐ[F] W.FunctionField)
  | 0 => AlgEquiv.refl
  | .some _ _ h => translationAlgEquivOf (kwWdp_Δ_ne_zero_of_isElliptic (W := W)) h.1

private theorem Point.translateFF_zero : Point.translateFF (W := W) 0 = AlgEquiv.refl := rfl

end Translate

end WeierstrassCurve.Affine

/-! ## The `kw_*_charFree` translation chain -/

namespace WeierstrassCurve.Affine

section GenericW

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
variable (W : Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]
  [AbelTheorem W]

local notation "ι" => algebraMap F W.FunctionField

private theorem kw_ord_yGen_of_not_isFinitePlace_charFree (v : Place F W.FunctionField)
    (hv : ¬ IsFinitePlace v) : v.ord W.yGen = -3 :=
  ord_Y_eq_neg_three_of_not_isFinitePlace v hv

variable (a b : F)

private def kwTISDα_charFree : F := W.a₄ - W.a₁ * b + 3 * a ^ 2 + 2 * W.a₂ * a

private def kwTISDβ_charFree : F := 2 * b + W.a₁ * a + W.a₃

private def kwTISDγ_charFree : F := W.a₆ + b ^ 2 + W.a₁ * a * b - 2 * a ^ 3 - W.a₂ * a ^ 2

private theorem kw_addXFun_sub_mul_sq_num_charFree :
    (W.addXFun a b - ι a) * (W.polyToFunctionField X - ι a) ^ 2 =
      ι (kwTISDα_charFree W a b) * W.polyToFunctionField X
        - ι (kwTISDβ_charFree W a b) * W.yGen + ι (kwTISDγ_charFree W a b) := by
  have hxne : W.polyToFunctionField X ≠ ι a := polyToFunctionField_X_ne_algebraMap a
  have hd : W.polyToFunctionField X - ι a ≠ 0 := sub_ne_zero.mpr hxne
  have hEq := equation_map_polyToFunctionField_yGen (W := W)
  rw [Affine.equation_iff] at hEq
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hEq
  show ((W.map ι).addX (W.polyToFunctionField X) (ι a)
      ((W.map ι).slope (W.polyToFunctionField X) (ι a) W.yGen (ι b)) - ι a)
        * (W.polyToFunctionField X - ι a) ^ 2 = _
  rw [slope_of_X_ne hxne, addX]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, kwTISDα_charFree,
    kwTISDβ_charFree, kwTISDγ_charFree, map_add, map_sub, map_mul, map_pow, map_ofNat]
  field_simp
  linear_combination hEq

private def kwTISDδ2_charFree : F :=
  3 * a * kwTISDβ_charFree W a b + W.a₂ * kwTISDβ_charFree W a b
    - W.a₁ * kwTISDα_charFree W a b

private def kwTISDδ1_charFree : F :=
  W.a₄ * kwTISDβ_charFree W a b + kwTISDα_charFree W a b * b
    + W.a₁ * a * kwTISDα_charFree W a b - W.a₁ * kwTISDγ_charFree W a b
    - 3 * a ^ 2 * kwTISDβ_charFree W a b

private def kwTISDδY_charFree : F :=
  -kwTISDγ_charFree W a b - kwTISDβ_charFree W a b * b
    - W.a₁ * a * kwTISDβ_charFree W a b - W.a₃ * kwTISDβ_charFree W a b

private def kwTISDδ0_charFree : F :=
  a ^ 3 * kwTISDβ_charFree W a b + kwTISDγ_charFree W a b * b
    + W.a₁ * a * kwTISDγ_charFree W a b + W.a₆ * kwTISDβ_charFree W a b

private theorem kw_addYFun_sub_mul_linear_charFree :
    (W.addYFun a b - ι b) * (W.polyToFunctionField X - ι a) =
      -(ι (kwTISDβ_charFree W a b)) * (W.polyToFunctionField X - ι a)
        - ((W.yGen - ι b) + ι W.a₁ * (W.polyToFunctionField X - ι a))
          * (W.addXFun a b - ι a) := by
  have hxne : W.polyToFunctionField X ≠ ι a := polyToFunctionField_X_ne_algebraMap a
  have hd : W.polyToFunctionField X - ι a ≠ 0 := sub_ne_zero.mpr hxne
  show ((W.map ι).addY (W.polyToFunctionField X) (ι a) W.yGen
      ((W.map ι).slope (W.polyToFunctionField X) (ι a) W.yGen (ι b)) - ι b)
        * (W.polyToFunctionField X - ι a) =
      -(ι (kwTISDβ_charFree W a b)) * (W.polyToFunctionField X - ι a)
        - ((W.yGen - ι b) + ι W.a₁ * (W.polyToFunctionField X - ι a))
          * ((W.map ι).addX (W.polyToFunctionField X) (ι a)
              ((W.map ι).slope (W.polyToFunctionField X) (ι a) W.yGen (ι b)) - ι a)
  rw [slope_of_X_ne hxne, addY, negAddY, negY, addX]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    kwTISDβ_charFree, map_add, map_mul, map_ofNat]
  field_simp
  ring

private theorem kw_addYFun_sub_mul_cube_num_charFree :
    (W.addYFun a b - ι b) * (W.polyToFunctionField X - ι a) ^ 3 =
      ι (kwTISDδ2_charFree W a b) * W.polyToFunctionField X ^ 2
        - ι (kwTISDα_charFree W a b) * (W.polyToFunctionField X * W.yGen)
        + ι (kwTISDδ1_charFree W a b) * W.polyToFunctionField X
        + ι (kwTISDδY_charFree W a b) * W.yGen + ι (kwTISDδ0_charFree W a b) := by
  have hEq := equation_map_polyToFunctionField_yGen (W := W)
  rw [Affine.equation_iff] at hEq
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hEq
  have h0a := kw_addXFun_sub_mul_sq_num_charFree W a b
  have step_i := kw_addYFun_sub_mul_linear_charFree W a b
  simp only [kwTISDδ2_charFree, kwTISDδ1_charFree, kwTISDδY_charFree, kwTISDδ0_charFree,
    kwTISDα_charFree, kwTISDβ_charFree, kwTISDγ_charFree,
    map_add, map_sub, map_mul, map_pow, map_ofNat, _root_.map_neg] at h0a step_i ⊢
  linear_combination (W.polyToFunctionField X - ι a) ^ 2 * step_i
    - ((W.yGen - ι b) + ι W.a₁ * (W.polyToFunctionField X - ι a)) * h0a
    + (2 * ι b + ι W.a₁ * ι a + ι W.a₃) * hEq

variable {a b}

private theorem kw_addXFun_ne_algebraMap_any_charFree (hA : W.Equation a b) (c : F) :
    W.addXFun a b ≠ ι c := by
  have hΔ : W.Δ ≠ 0 := W.kwWdp_Δ_ne_zero_of_isElliptic
  intro heq
  refine polyToFunctionField_X_ne_algebraMap (W := W) c
    ((translationAlgEquivOf hΔ hA).injective ?_)
  rw [translationAlgEquivOf_polyToFunctionField_X hΔ hA, heq, AlgEquiv.commutes]

private theorem kw_addYFun_ne_algebraMap_any_charFree (hA : W.Equation a b) (c : F) :
    W.addYFun a b ≠ ι c := by
  have hΔ : W.Δ ≠ 0 := W.kwWdp_Δ_ne_zero_of_isElliptic
  intro heq
  have hy : W.yGen = ι c := (translationAlgEquivOf hΔ hA).injective <| by
    rw [translationAlgEquivOf_yGen hΔ hA, heq, AlgEquiv.commutes]
  have hord := kw_ord_yGen_of_not_isFinitePlace_charFree W
    (InfinitePlace.place (W := W)) InfinitePlace.not_isFinitePlace
  rw [hy, Place.ord_algebraMap] at hord
  exact absurd hord (by norm_num)

private theorem kw_ord_addXFun_sub_pos_charFree (hA : W.Equation a b)
    (v : Place F W.FunctionField) (hv : ¬ IsFinitePlace v) :
    0 < v.ord (W.addXFun a b - ι a) := by
  have hne : W.addXFun a b - ι a ≠ 0 :=
    sub_ne_zero.mpr (kw_addXFun_ne_algebraMap_any_charFree W hA a)
  have hXa : W.polyToFunctionField X - ι a ≠ 0 := X_sub_algebraMap_ne_zero a
  have hXa2 : (W.polyToFunctionField X - ι a) ^ 2 ≠ 0 := pow_ne_zero 2 hXa
  have hY0 : W.yGen ≠ (0 : W.FunctionField) := Y_image_ne_zero
  have hordY : v.ord W.yGen = -3 := kw_ord_yGen_of_not_isFinitePlace_charFree W v hv
  set num := ι (kwTISDα_charFree W a b) * W.polyToFunctionField X
      - ι (kwTISDβ_charFree W a b) * W.yGen + ι (kwTISDγ_charFree W a b) with hnumdef
  have hkey := kw_addXFun_sub_mul_sq_num_charFree W a b
  rw [← hnumdef] at hkey
  have hnum0 : num ≠ 0 := by rw [← hkey]; exact mul_ne_zero hne hXa2
  have hordeq : v.ord (W.addXFun a b - ι a) = v.ord num + 4 := by
    have h := v.ord_mul hne hXa2
    rw [hkey, v.ord_pow, ord_X_sub_algebraMap_of_not_isFinitePlace v hv a] at h
    omega
  rw [hordeq]
  have hmem : num * W.yGen⁻¹ ∈ v.toValuationSubring := by
    have hYinv : W.yGen⁻¹ ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (inv_ne_zero hY0) (by rw [v.ord_inv, hordY]; omega)
    have hXYinv : W.polyToFunctionField X * W.yGen⁻¹ ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (mul_ne_zero (polyToFunctionField_ne_zero X_ne_zero) (inv_ne_zero hY0))
        (by rw [v.ord_mul (polyToFunctionField_ne_zero X_ne_zero) (inv_ne_zero hY0), v.ord_inv,
              ord_X_eq_neg_two_of_not_isFinitePlace v hv, hordY]; omega)
    rw [hnumdef, add_mul, sub_mul, mul_assoc _ (W.polyToFunctionField X), mul_assoc _ W.yGen,
      mul_inv_cancel₀ hY0, mul_one]
    exact add_mem (sub_mem (mul_mem (v.algebraMap_mem' _) hXYinv) (v.algebraMap_mem' _))
      (mul_mem (v.algebraMap_mem' _) hYinv)
  have hnumord : -3 ≤ v.ord num := by
    have := (v.mem_iff_ord_nonneg (mul_ne_zero hnum0 (inv_ne_zero hY0))).mp hmem
    rw [v.ord_mul hnum0 (inv_ne_zero hY0), v.ord_inv, hordY] at this
    linarith
  linarith

private theorem kw_ord_addYFun_sub_pos_charFree (hA : W.Equation a b)
    (v : Place F W.FunctionField) (hv : ¬ IsFinitePlace v) :
    0 < v.ord (W.addYFun a b - ι b) := by
  have hne : W.addYFun a b - ι b ≠ 0 :=
    sub_ne_zero.mpr (kw_addYFun_ne_algebraMap_any_charFree W hA b)
  have hXa : W.polyToFunctionField X - ι a ≠ 0 := X_sub_algebraMap_ne_zero a
  have hXa3 : (W.polyToFunctionField X - ι a) ^ 3 ≠ 0 := pow_ne_zero 3 hXa
  have hX0 : W.polyToFunctionField X ≠ (0 : W.FunctionField) :=
    polyToFunctionField_ne_zero X_ne_zero
  have hY0 : W.yGen ≠ (0 : W.FunctionField) := Y_image_ne_zero
  have hXY0 : W.polyToFunctionField X * W.yGen ≠ 0 := mul_ne_zero hX0 hY0
  have hordX : v.ord (W.polyToFunctionField X) = -2 := ord_X_eq_neg_two_of_not_isFinitePlace v hv
  have hordY : v.ord W.yGen = -3 := kw_ord_yGen_of_not_isFinitePlace_charFree W v hv
  set numY := ι (kwTISDδ2_charFree W a b) * W.polyToFunctionField X ^ 2
      - ι (kwTISDα_charFree W a b) * (W.polyToFunctionField X * W.yGen)
      + ι (kwTISDδ1_charFree W a b) * W.polyToFunctionField X
      + ι (kwTISDδY_charFree W a b) * W.yGen + ι (kwTISDδ0_charFree W a b) with hnumYdef
  have hkey := kw_addYFun_sub_mul_cube_num_charFree W a b
  rw [← hnumYdef] at hkey
  have hnumY0 : numY ≠ 0 := by rw [← hkey]; exact mul_ne_zero hne hXa3
  have hordeq : v.ord (W.addYFun a b - ι b) = v.ord numY + 6 := by
    have h := v.ord_mul hne hXa3
    rw [hkey, v.ord_pow, ord_X_sub_algebraMap_of_not_isFinitePlace v hv a] at h
    omega
  rw [hordeq]
  have hmem : numY * (W.polyToFunctionField X * W.yGen)⁻¹ ∈ v.toValuationSubring := by
    have hXYinv : (W.polyToFunctionField X * W.yGen)⁻¹ ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (inv_ne_zero hXY0)
        (by rw [v.ord_inv, v.ord_mul hX0 hY0, hordX, hordY]; omega)
    have hXinv : (W.polyToFunctionField X)⁻¹ ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (inv_ne_zero hX0) (by rw [v.ord_inv, hordX]; omega)
    have hYinv : W.yGen⁻¹ ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (inv_ne_zero hY0) (by rw [v.ord_inv, hordY]; omega)
    have hXoYinv : W.polyToFunctionField X * W.yGen⁻¹ ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (mul_ne_zero hX0 (inv_ne_zero hY0))
        (by rw [v.ord_mul hX0 (inv_ne_zero hY0), v.ord_inv, hordX, hordY]; omega)
    have hsplit : numY * (W.polyToFunctionField X * W.yGen)⁻¹
        = ι (kwTISDδ2_charFree W a b) * (W.polyToFunctionField X * W.yGen⁻¹)
          - ι (kwTISDα_charFree W a b)
          + ι (kwTISDδ1_charFree W a b) * W.yGen⁻¹
          + ι (kwTISDδY_charFree W a b) * (W.polyToFunctionField X)⁻¹
          + ι (kwTISDδ0_charFree W a b) * (W.polyToFunctionField X * W.yGen)⁻¹ := by
      rw [hnumYdef]; field_simp
    rw [hsplit]
    exact add_mem (add_mem (add_mem
      (sub_mem (mul_mem (v.algebraMap_mem' _) hXoYinv) (v.algebraMap_mem' _))
      (mul_mem (v.algebraMap_mem' _) hYinv))
      (mul_mem (v.algebraMap_mem' _) hXinv))
      (mul_mem (v.algebraMap_mem' _) hXYinv)
  have hnumYord : -5 ≤ v.ord numY := by
    have := (v.mem_iff_ord_nonneg (mul_ne_zero hnumY0 (inv_ne_zero hXY0))).mp hmem
    rw [v.ord_mul hnumY0 (inv_ne_zero hXY0), v.ord_inv, v.ord_mul hX0 hY0, hordX, hordY] at this
    linarith
  linarith

private theorem kw_affod_numX_eval_eq_zero_charFree {p q : F} (hP : W.Equation p q)
    (hne : p ≠ a) :
    kwTISDα_charFree W a b * p - kwTISDβ_charFree W a b * q + kwTISDγ_charFree W a b
      - (W.addX p a (W.slope p a q b) - a) * (p - a) ^ 2 = 0 := by
  have hEq := (Affine.equation_iff ..).mp hP
  have hd : p - a ≠ 0 := sub_ne_zero.mpr hne
  simp only [kwTISDα_charFree, kwTISDβ_charFree, kwTISDγ_charFree,
    Affine.slope_of_X_ne hne, Affine.addX]
  field_simp
  linear_combination -hEq

private theorem kw_affod_numYcube_eval_eq_zero_charFree {p q : F} (hP : W.Equation p q)
    (hne : p ≠ a) :
    kwTISDδ2_charFree W a b * p ^ 2 - kwTISDα_charFree W a b * (p * q)
      + kwTISDδ1_charFree W a b * p + kwTISDδY_charFree W a b * q
      + kwTISDδ0_charFree W a b
      - (W.addY p a q (W.slope p a q b) - b) * (p - a) ^ 3 = 0 := by
  have hEq := (Affine.equation_iff ..).mp hP
  have hd : p - a ≠ 0 := sub_ne_zero.mpr hne
  simp only [kwTISDδ2_charFree, kwTISDδ1_charFree, kwTISDδY_charFree, kwTISDδ0_charFree,
    kwTISDα_charFree, kwTISDβ_charFree, kwTISDγ_charFree,
    Affine.slope_of_X_ne hne, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY]
  field_simp
  linear_combination ((q - b) + W.a₁ * (p - a) - (2 * b + W.a₁ * a + W.a₃)) * hEq

variable {p q : F}

private theorem kw_ord_addXFun_sub_addX_pos_charFree (h : W.Nonsingular a b)
    (hP : W.Nonsingular p q) (hne : p ≠ a) :
    0 < (placeOfEquation hP.1).ord
      (W.addXFun a b - ι (W.addX p a (W.slope p a q b))) := by
  set v := placeOfEquation hP.1
  set x₃ := W.addX p a (W.slope p a q b)
  have hXa : W.polyToFunctionField X - ι a ≠ 0 := X_sub_algebraMap_ne_zero a
  have hXa2 : (W.polyToFunctionField X - ι a) ^ 2 ≠ 0 := pow_ne_zero 2 hXa
  have hne_x₃ : W.addXFun a b - ι x₃ ≠ 0 :=
    sub_ne_zero.mpr (kw_addXFun_ne_algebraMap_any_charFree W h.1 x₃)
  set qX : F[X][Y] :=
    C (C (kwTISDα_charFree W a b) * X + C (kwTISDγ_charFree W a b)
        - C (x₃ - a) * (X - C a) ^ 2)
      - C (C (kwTISDβ_charFree W a b)) * Y with hqX
  have hprod :
      (W.addXFun a b - ι x₃) * (W.polyToFunctionField X - ι a) ^ 2
        = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qX) := by
    have h0a := kw_addXFun_sub_mul_sq_num_charFree W a b
    have hmk : CoordinateRing.mk W qX
        = algebraMap F[X] W.CoordinateRing
            (C (kwTISDα_charFree W a b) * X + C (kwTISDγ_charFree W a b)
              - C (x₃ - a) * (X - C a) ^ 2)
          - algebraMap F[X] W.CoordinateRing (C (kwTISDβ_charFree W a b))
            * CoordinateRing.mk W Y := by
      simp only [hqX, map_sub, map_mul]; rfl
    have hyGen : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
        = W.yGen := rfl
    rw [hmk, map_sub, map_mul, ← polyToFunctionField_apply, ← polyToFunctionField_apply, hyGen]
    simp only [map_sub, map_add, map_mul, map_pow, polyToFunctionField_C]
    linear_combination h0a
  have heval : qX.evalEval p q = 0 := by
    simp only [hqX, evalEval, eval_sub, eval_mul, eval_C, eval_add, eval_X, eval_pow,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination kw_affod_numX_eval_eq_zero_charFree W hP.1 hne
  have hmk_ne : CoordinateRing.mk W qX ≠ 0 := by
    intro h0
    rw [h0, _root_.map_zero] at hprod
    exact (mul_ne_zero hne_x₃ hXa2) hprod
  have hordnum :
      0 < v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qX)) :=
    (ord_placeOfEquation_pos_iff hP.1 hmk_ne).mpr
      ((mk_mem_XYIdeal_iff hP.1 qX).mpr heval)
  have hordXa : v.ord (W.polyToFunctionField X - ι a) = 0 := by
    rw [show W.polyToFunctionField X - ι a = W.polyToFunctionField (X - C a) by
      rw [map_sub, polyToFunctionField_C],
      ord_polyToFunctionField_eq_zero_iff hP.1 (X_sub_C_ne_zero a)]
    simp [sub_ne_zero.mpr hne]
  have heqord := v.ord_mul hne_x₃ hXa2
  rw [hprod, v.ord_pow, hordXa] at heqord
  omega

private theorem kw_ord_addYFun_sub_addY_pos_charFree (h : W.Nonsingular a b)
    (hP : W.Nonsingular p q) (hne : p ≠ a) :
    0 < (placeOfEquation hP.1).ord
      (W.addYFun a b - ι (W.addY p a q (W.slope p a q b))) := by
  set v := placeOfEquation hP.1
  set y₃ := W.addY p a q (W.slope p a q b)
  have hXa : W.polyToFunctionField X - ι a ≠ 0 := X_sub_algebraMap_ne_zero a
  have hXa3 : (W.polyToFunctionField X - ι a) ^ 3 ≠ 0 := pow_ne_zero 3 hXa
  have hne_y₃ : W.addYFun a b - ι y₃ ≠ 0 :=
    sub_ne_zero.mpr (kw_addYFun_ne_algebraMap_any_charFree W h.1 y₃)
  set qY : F[X][Y] :=
    C (C (kwTISDδ2_charFree W a b) * X ^ 2 + C (kwTISDδ1_charFree W a b) * X
        + C (kwTISDδ0_charFree W a b) - C (y₃ - b) * (X - C a) ^ 3)
      + C (C (kwTISDδY_charFree W a b) - C (kwTISDα_charFree W a b) * X) * Y with hqY
  have hprod :
      (W.addYFun a b - ι y₃) * (W.polyToFunctionField X - ι a) ^ 3
        = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qY) := by
    have h0b := kw_addYFun_sub_mul_cube_num_charFree W a b
    have hmk : CoordinateRing.mk W qY
        = algebraMap F[X] W.CoordinateRing
            (C (kwTISDδ2_charFree W a b) * X ^ 2 + C (kwTISDδ1_charFree W a b) * X
              + C (kwTISDδ0_charFree W a b) - C (y₃ - b) * (X - C a) ^ 3)
          + algebraMap F[X] W.CoordinateRing
              (C (kwTISDδY_charFree W a b) - C (kwTISDα_charFree W a b) * X)
            * CoordinateRing.mk W Y := by
      simp only [hqY, map_add, map_sub, map_mul]; rfl
    have hyGen : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
        = W.yGen := rfl
    rw [hmk, map_add, map_mul, ← polyToFunctionField_apply, ← polyToFunctionField_apply, hyGen]
    simp only [map_sub, map_add, map_mul, map_pow, polyToFunctionField_C]
    linear_combination h0b
  have heval : qY.evalEval p q = 0 := by
    simp only [hqY, evalEval, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination kw_affod_numYcube_eval_eq_zero_charFree W hP.1 hne
  have hmk_ne : CoordinateRing.mk W qY ≠ 0 := by
    intro h0
    rw [h0, _root_.map_zero] at hprod
    exact (mul_ne_zero hne_y₃ hXa3) hprod
  have hordnum :
      0 < v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qY)) :=
    (ord_placeOfEquation_pos_iff hP.1 hmk_ne).mpr
      ((mk_mem_XYIdeal_iff hP.1 qY).mpr heval)
  have hordXa : v.ord (W.polyToFunctionField X - ι a) = 0 := by
    rw [show W.polyToFunctionField X - ι a = W.polyToFunctionField (X - C a) by
      rw [map_sub, polyToFunctionField_C],
      ord_polyToFunctionField_eq_zero_iff hP.1 (X_sub_C_ne_zero a)]
    simp [sub_ne_zero.mpr hne]
  have heqord := v.ord_mul hne_y₃ hXa3
  rw [hprod, v.ord_pow, hordXa] at heqord
  omega

variable {W}

private theorem kw_translateFF_toAlgHom_isIntegral_charFree (R : W.Point) :
    (Point.translateFF (W := W) R).toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ (Point.translateFF (W := W) R).surjective

private theorem kw_translateFF_some_X_charFree (h : W.Nonsingular a b) :
    (Point.translateFF (W := W) (.some a b h)).toAlgHom (polyToFunctionField W X)
      = W.addXFun a b :=
  translationAlgEquivOf_polyToFunctionField_X (hΔ := kwWdp_Δ_ne_zero_of_isElliptic) (hA := h.1)

private theorem kw_translateFF_some_yGen_charFree (h : W.Nonsingular a b) :
    (Point.translateFF (W := W) (.some a b h)).toAlgHom (yGen W)
      = W.addYFun a b :=
  translationAlgEquivOf_yGen (hΔ := kwWdp_Δ_ne_zero_of_isElliptic) (hA := h.1)

private theorem kw_translAffineSeam_at_of_coordSeamData_charFree (h : W.Nonsingular a b)
    (v : AlgebraicCurve.Place F W.FunctionField) (Q : W.Point)
    (hdat : Q.rec
      (W.addXFun a b ∉ v.toValuationSubring)
      (fun x₃ y₃ _ =>
        0 < v.ord (W.addXFun a b - ι x₃) ∧ 0 < v.ord (W.addYFun a b - ι y₃))) :
    v.restrictAlong (Point.translateFF (W := W) (.some a b h)).toAlgHom
        (kw_translateFF_toAlgHom_isIntegral_charFree (.some a b h))
      = placeOfPoint Q := by
  have hX := kw_translateFF_some_X_charFree h
  have hY := kw_translateFF_some_yGen_charFree h
  cases Q with
  | zero =>
    rw [placeOfPoint_zero]
    exact AbstractSeam.restrictAlong_eq_infinitePlace _ _ hX v (hX ▸ hdat)
  | some x₃ y₃ h₃ =>
    rw [placeOfPoint_some]
    have hdx := hdat.1; have hdy := hdat.2
    have hreg : W.addXFun a b ∈ v.toValuationSubring := by
      by_cases hz : W.addXFun a b - ι x₃ = 0
      · rw [sub_eq_zero.mp hz]; exact v.algebraMap_mem' x₃
      · have := add_mem (v.mem_of_ord_nonneg hz hdx.le) (v.algebraMap_mem' x₃)
        rwa [sub_add_cancel] at this
    exact es1a6_addSeam_restrictAlong_eq_placeOfEquation _ _ hX hY v h₃.1 hreg hdx hdy

private theorem kw_TISD_linear_eval_negA_charFree (h : W.Equation a b) :
    kwTISDα_charFree W a b * a - kwTISDβ_charFree W a b * W.negY a b
      + kwTISDγ_charFree W a b = kwTISDβ_charFree W a b ^ 2 := by
  have hEq := (Affine.equation_iff ..).mp h
  simp only [kwTISDα_charFree, kwTISDβ_charFree, kwTISDγ_charFree, Affine.negY]
  ring_nf
  linear_combination -hEq

private theorem kw_addXFun_notMem_placeOfEquation_negA_charFree (h : W.Nonsingular a b)
    (hβ : kwTISDβ_charFree W a b ≠ 0) :
    W.addXFun a b ∉ (placeOfEquation (W := W)
      ((W.nonsingular_neg a b).mpr h).1).toValuationSubring := by
  intro hmem
  set hnegA := ((W.nonsingular_neg a b).mpr h).1 with hnegA_def
  let v := placeOfEquation (W := W) hnegA
  have hne : W.addXFun a b - ι a ≠ 0 :=
    sub_ne_zero.mpr (kw_addXFun_ne_algebraMap_any_charFree W h.1 a)
  have hXa : W.polyToFunctionField X - ι a ≠ 0 := X_sub_algebraMap_ne_zero a
  have hXa2 : (W.polyToFunctionField X - ι a) ^ 2 ≠ 0 := pow_ne_zero 2 hXa
  set qpoly : F[X][Y] :=
    C (C (kwTISDα_charFree W a b) * X + C (kwTISDγ_charFree W a b))
      - C (C (kwTISDβ_charFree W a b)) * Y with hq
  have hnum_mk :
      ι (kwTISDα_charFree W a b) * W.polyToFunctionField X
        - ι (kwTISDβ_charFree W a b) * W.yGen + ι (kwTISDγ_charFree W a b)
      = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qpoly) := by
    have hmk : CoordinateRing.mk W qpoly
        = algebraMap F[X] W.CoordinateRing (C (kwTISDα_charFree W a b) * X
              + C (kwTISDγ_charFree W a b))
          - algebraMap F[X] W.CoordinateRing (C (kwTISDβ_charFree W a b))
            * CoordinateRing.mk W Y := by
      simp only [hq, map_sub, map_mul]; rfl
    have hyGen : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
        = W.yGen := rfl
    rw [hmk, map_sub, map_mul, ← polyToFunctionField_apply, ← polyToFunctionField_apply,
      map_add, map_mul, polyToFunctionField_C, polyToFunctionField_C, polyToFunctionField_C,
      hyGen]
    ring
  have heval : qpoly.evalEval a (W.negY a b) ≠ 0 := by
    have : qpoly.evalEval a (W.negY a b) = kwTISDβ_charFree W a b ^ 2 := by
      simp only [hq, evalEval, eval_sub, eval_mul, eval_C, eval_add, eval_X,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X]
      linear_combination kw_TISD_linear_eval_negA_charFree (W := W) h.1
    rw [this]; exact pow_ne_zero 2 hβ
  have hordnum : v.ord (ι (kwTISDα_charFree W a b) * W.polyToFunctionField X
      - ι (kwTISDβ_charFree W a b) * W.yGen + ι (kwTISDγ_charFree W a b)) = 0 := by
    rw [hnum_mk]
    exact ord_placeOfEquation_eq_zero_of_evalEval_ne_zero hnegA heval
  have hordXa : 1 ≤ v.ord (W.polyToFunctionField X - ι a) := by
    have hroot : (X - C a : F[X]).IsRoot a := by simp
    have hpos : 0 < v.ord (W.polyToFunctionField (X - C a)) :=
      (ord_polyToFunctionField_pos_iff hnegA (X_sub_C_ne_zero a)).mpr hroot
    rw [map_sub, polyToFunctionField_C] at hpos
    omega
  have hmem' : W.addXFun a b - ι a ∈ v.toValuationSubring :=
    sub_mem hmem (v.algebraMap_mem' a)
  have hord' : 0 ≤ v.ord (W.addXFun a b - ι a) := (v.mem_iff_ord_nonneg hne).mp hmem'
  have heqord := v.ord_mul hne hXa2
  rw [kw_addXFun_sub_mul_sq_num_charFree W a b, v.ord_pow, hordnum] at heqord
  omega

private theorem kw_taseq_α_eq_neg_polyX_charFree :
    kwTISDα_charFree W a b = -(W.polynomialX.evalEval a b) := by
  simp only [kwTISDα_charFree, evalEval_polynomialX]; ring

private theorem kw_taseq_β_eq_polyY_charFree :
    kwTISDβ_charFree W a b = W.polynomialY.evalEval a b := by
  simp only [kwTISDβ_charFree, evalEval_polynomialY]

private theorem kw_taseq_α_ne_zero_of_β_eq_zero_charFree (h : W.Nonsingular a b)
    (hβ : kwTISDβ_charFree W a b = 0) : kwTISDα_charFree W a b ≠ 0 := by
  rw [kw_taseq_α_eq_neg_polyX_charFree, neg_ne_zero]
  have hβ' : W.polynomialY.evalEval a b = 0 := by
    rw [← kw_taseq_β_eq_polyY_charFree]; exact hβ
  exact h.2.resolve_right (absurd hβ')

private theorem kw_taseq_β_eq_zero_iff_eq_negY_charFree :
    kwTISDβ_charFree W a b = 0 ↔ b = W.negY a b := by
  rw [kw_taseq_β_eq_polyY_charFree, evalEval_polynomialY_eq_zero_iff_eq_negY]

private theorem kw_taseq_linear_eval_self_charFree (h : W.Equation a b) :
    kwTISDα_charFree W a b * a - kwTISDβ_charFree W a b * b
      + kwTISDγ_charFree W a b = 0 := by
  have hEq := (Affine.equation_iff ..).mp h
  simp only [kwTISDα_charFree, kwTISDβ_charFree, kwTISDγ_charFree]
  linear_combination -hEq

private theorem kw_taseq_le_ord_sub_charFree {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : Place K L) {N : ℤ} {f g : L} (hfg : f - g ≠ 0)
    (hf : f = 0 ∨ N ≤ v.ord f) (hg : g = 0 ∨ N ≤ v.ord g) :
    N ≤ v.ord (f - g) := by
  have hneg : ∀ x : L, v.ord (-x) = v.ord x := fun x => by
    simp only [Place.ord, Valuation.map_neg]
  rcases hf with rfl | hf
  · rw [zero_sub, hneg]
    exact hg.resolve_left (by simpa using hfg)
  rcases hg with rfl | hg
  · rwa [sub_zero]
  · rw [sub_eq_add_neg]
    have hmin := v.min_ord_le_ord_add (f := f) (g := -g) (by rwa [← sub_eq_add_neg])
    rw [hneg] at hmin
    omega

private theorem kw_taseq_ord_ge_of_mem_XYIdeal_pow_charFree (h : W.Equation a b)
    {r : W.CoordinateRing} (hr0 : r ≠ 0) {n : ℕ} (hr : r ∈ XYIdeal W a (C b) ^ n) :
    (n : ℤ) ≤ (placeOfEquation h).ord (algebraMap W.CoordinateRing W.FunctionField r) := by
  have hrL : algebraMap W.CoordinateRing W.FunctionField r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hr0
  rw [placeOfEquation, Place.ord_ofHeightOneSpectrum_eq_neg_log _ hrL,
    (heightOneSpectrumOfEquation h).valuation_of_algebraMap]
  have h1 : (heightOneSpectrumOfEquation h).intValuation r ≤ exp (-(n : ℤ)) := by
    rw [show (-(n : ℤ)) = -((n : ℕ) : ℤ) from rfl,
      HeightOneSpectrum.intValuation_le_pow_iff_mem, heightOneSpectrumOfEquation_asIdeal]
    exact hr
  rw [(heightOneSpectrumOfEquation h).intValuation_if_neg hr0] at h1 ⊢
  rw [exp_le_exp] at h1
  rw [log_exp]
  omega

private theorem kw_addXFun_notMem_placeOfEquation_self_of_β_eq_zero_charFree
    (h : W.Nonsingular a b) (hβ : kwTISDβ_charFree W a b = 0) :
    W.addXFun a b ∉ (placeOfEquation h.1).toValuationSubring := by
  intro hmem
  have hα : kwTISDα_charFree W a b ≠ 0 := kw_taseq_α_ne_zero_of_β_eq_zero_charFree h hβ
  have hιαne : ι (kwTISDα_charFree W a b) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr hα
  have hne : W.addXFun a b - ι a ≠ 0 :=
    sub_ne_zero.mpr (kw_addXFun_ne_algebraMap_any_charFree W h.1 a)
  have hXa : W.polyToFunctionField X - ι a ≠ 0 := X_sub_algebraMap_ne_zero a
  have hXa2 : (W.polyToFunctionField X - ι a) ^ 2 ≠ 0 := pow_ne_zero 2 hXa
  have hprod :
      (W.addXFun a b - ι a) * (W.polyToFunctionField X - ι a) ^ 2
        = ι (kwTISDα_charFree W a b) * (W.polyToFunctionField X - ι a) := by
    rw [kw_addXFun_sub_mul_sq_num_charFree W a b, hβ, _root_.map_zero, zero_mul, sub_zero]
    have hval : kwTISDγ_charFree W a b = -(kwTISDα_charFree W a b * a) := by
      have h0 := kw_taseq_linear_eval_self_charFree (W := W) h.1
      rw [hβ, zero_mul, sub_zero] at h0; linear_combination h0
    rw [hval, _root_.map_neg, map_mul]; ring
  have hordXa : 0 < (placeOfEquation h.1).ord (W.polyToFunctionField X - ι a) := by
    rw [show W.polyToFunctionField X - ι a = W.polyToFunctionField (X - C a) by
      rw [map_sub, polyToFunctionField_C]]
    exact (ord_polyToFunctionField_pos_iff h.1 (X_sub_C_ne_zero a)).mpr (by simp)
  have hordα : (placeOfEquation h.1).ord (ι (kwTISDα_charFree W a b)) = 0 :=
    (placeOfEquation h.1).ord_algebraMap _
  have hmem' : W.addXFun a b - ι a ∈ (placeOfEquation h.1).toValuationSubring :=
    sub_mem hmem ((placeOfEquation h.1).algebraMap_mem' a)
  have hord' : 0 ≤ (placeOfEquation h.1).ord (W.addXFun a b - ι a) :=
    ((placeOfEquation h.1).mem_iff_ord_nonneg hne).mp hmem'
  have heqord := (placeOfEquation h.1).ord_mul hne hXa2
  rw [hprod, (placeOfEquation h.1).ord_mul hιαne hXa, (placeOfEquation h.1).ord_pow,
    hordα] at heqord
  omega

private theorem kw_taseq_linear_eq_neg_taylorLinear_charFree (h : W.Equation a b) :
    ι (kwTISDα_charFree W a b) * W.polyToFunctionField X
        - ι (kwTISDβ_charFree W a b) * W.yGen + ι (kwTISDγ_charFree W a b)
      = - algebraMap W.CoordinateRing W.FunctionField
          (algebraMap F W.CoordinateRing (W.polynomialX.evalEval a b) * XClass W a
            + algebraMap F W.CoordinateRing (W.polynomialY.evalEval a b)
              * YClass W (C b)) := by
  have hXC : algebraMap W.CoordinateRing W.FunctionField (XClass W a)
      = W.polyToFunctionField X - ι a := by
    have : (XClass W a : W.CoordinateRing) = algebraMap F[X] W.CoordinateRing (X - C a) := rfl
    rw [this, ← polyToFunctionField_apply, map_sub, polyToFunctionField_C]
  have hYC : algebraMap W.CoordinateRing W.FunctionField (YClass W (C b))
      = W.yGen - ι b := by
    have : (YClass W (C b) : W.CoordinateRing)
        = CoordinateRing.mk W Y - algebraMap F W.CoordinateRing b := by
      show CoordinateRing.mk W (Y - C (C b)) = _; simp only [map_sub]; rfl
    rw [this, map_sub]; rfl
  have hval := kw_taseq_linear_eval_self_charFree (W := W) h
  have hιval : ι (kwTISDγ_charFree W a b)
      = -(ι (kwTISDα_charFree W a b) * ι a) + ι (kwTISDβ_charFree W a b) * ι b := by
    rw [← map_mul, ← map_mul, ← _root_.map_neg, ← map_add]
    exact congrArg ι (by linear_combination hval)
  have hιpX : ι (W.polynomialX.evalEval a b) = -ι (kwTISDα_charFree W a b) := by
    rw [kw_taseq_α_eq_neg_polyX_charFree, _root_.map_neg, neg_neg]
  have hιpY : ι (W.polynomialY.evalEval a b) = ι (kwTISDβ_charFree W a b) := by
    rw [← kw_taseq_β_eq_polyY_charFree]
  rw [map_add, map_mul, map_mul, hXC, hYC,
    ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField,
    ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField,
    hιpX, hιpY, hιval]
  ring

private theorem kw_taseq_linear_eq_algebraMap_mk_taylorRemainder₂_charFree (h : W.Equation a b) :
    ι (kwTISDα_charFree W a b) * W.polyToFunctionField X
        - ι (kwTISDβ_charFree W a b) * W.yGen + ι (kwTISDγ_charFree W a b)
      = algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (W.taylorRemainder₂ a b)) := by
  rw [kw_taseq_linear_eq_neg_taylorLinear_charFree h, neg_eq_iff_eq_neg, ← _root_.map_neg]
  refine congrArg _ ?_
  have h0 : CoordinateRing.mk W W.polynomial = 0 := AdjoinRoot.mk_self
  have hF0 : W.polynomial.evalEval a b = 0 := h
  have hexp := congrArg (CoordinateRing.mk W) (W.taylor₂_polynomial a b)
  rw [h0, hF0] at hexp
  rw [eq_neg_iff_add_eq_zero,
    show (algebraMap F W.CoordinateRing) (W.polynomialX.evalEval a b)
      = CoordinateRing.mk W (C (C (W.polynomialX.evalEval a b))) from rfl,
    show (algebraMap F W.CoordinateRing) (W.polynomialY.evalEval a b)
      = CoordinateRing.mk W (C (C (W.polynomialY.evalEval a b))) from rfl,
    XClass, YClass]
  simp only [map_add, map_mul, _root_.map_zero, zero_add] at hexp
  linear_combination -hexp

private theorem kw_taseq_ord_X_sub_eq_one_charFree (h : W.Nonsingular a b)
    (hβ : kwTISDβ_charFree W a b ≠ 0) :
    (placeOfEquation h.1).ord (W.polyToFunctionField X - ι a) = 1 := by
  have hY : W.polynomialY.evalEval a b ≠ 0 := kw_taseq_β_eq_polyY_charFree (W := W) ▸ hβ
  have hXC : W.polyToFunctionField X - ι a
      = algebraMap W.CoordinateRing W.FunctionField (XClass W a) := by
    have : (XClass W a : W.CoordinateRing) = algebraMap F[X] W.CoordinateRing (X - C a) := rfl
    rw [this, ← polyToFunctionField_apply, map_sub, polyToFunctionField_C]
  rw [hXC]; exact ord_placeOfEquation_XClass_self h.1 hY

private theorem kw_taseq_betasq_x2_sub_a_charFree (hβ : kwTISDβ_charFree W a b ≠ 0) :
    kwTISDβ_charFree W a b ^ 2 * (W.addX a a (W.slope a a b b) - a)
      = kwTISDα_charFree W a b ^ 2 + W.a₁ * kwTISDα_charFree W a b * kwTISDβ_charFree W a b
        - (3 * a + W.a₂) * kwTISDβ_charFree W a b ^ 2 := by
  have hYne : b ≠ W.negY a b := fun hy => hβ (kw_taseq_β_eq_zero_iff_eq_negY_charFree.mpr hy)
  have hd : b - W.negY a b ≠ 0 := sub_ne_zero.mpr hYne
  rw [Affine.slope_of_Y_ne rfl hYne, Affine.addX]
  simp only [kwTISDα_charFree, kwTISDβ_charFree, Affine.negY] at hd ⊢
  field_simp
  ring

private theorem kw_taseq_beta_y2_coeff_charFree (hβ : kwTISDβ_charFree W a b ≠ 0) :
    kwTISDβ_charFree W a b
        * (kwTISDβ_charFree W a b + W.addY a a b (W.slope a a b b) - b
            + W.a₁ * (W.addX a a (W.slope a a b b) - a))
      + kwTISDα_charFree W a b * (W.addX a a (W.slope a a b b) - a) = 0 := by
  have hYne : b ≠ W.negY a b := fun hy => hβ (kw_taseq_β_eq_zero_iff_eq_negY_charFree.mpr hy)
  have hd : b - W.negY a b ≠ 0 := sub_ne_zero.mpr hYne
  rw [Affine.slope_of_Y_ne rfl hYne]
  simp only [kwTISDα_charFree, kwTISDβ_charFree, Affine.addX, Affine.addY, Affine.negAddY,
    Affine.negY] at hd ⊢
  field_simp
  ring

section DoubleOrd

variable (h : W.Nonsingular a b) (hβ : kwTISDβ_charFree W a b ≠ 0)

local notation "x₂" => W.addX a a (W.slope a a b b)
local notation "y₂" => W.addY a a b (W.slope a a b b)
local notation "α" => kwTISDα_charFree W a b
local notation "β" => kwTISDβ_charFree W a b
local notation "Lcot" =>
  algebraMap F W.CoordinateRing (W.polynomialX.evalEval a b) * XClass W a
    + algebraMap F W.CoordinateRing (W.polynomialY.evalEval a b) * YClass W (C b)
local notation "ι'" => algebraMap F W.CoordinateRing

include h hβ

private theorem kw_taseq_ord_addXFun_sub_double_pos_charFree :
    0 < (placeOfEquation h.1).ord (W.addXFun a b - ι x₂) := by
  set R_X : W.CoordinateRing :=
    CoordinateRing.mk W (W.taylorRemainder₂ a b) - ι' (x₂ - a) * XClass W a ^ 2 with hR_X
  have hXa : W.polyToFunctionField X - ι a ≠ 0 := X_sub_algebraMap_ne_zero a
  have hXa2 : (W.polyToFunctionField X - ι a) ^ 2 ≠ 0 := pow_ne_zero 2 hXa
  have hne_x₂ : W.addXFun a b - ι x₂ ≠ 0 :=
    sub_ne_zero.mpr (kw_addXFun_ne_algebraMap_any_charFree W h.1 x₂)
  have hprod :
      (W.addXFun a b - ι x₂) * (W.polyToFunctionField X - ι a) ^ 2
        = algebraMap W.CoordinateRing W.FunctionField R_X := by
    have hXC : algebraMap W.CoordinateRing W.FunctionField (XClass W a)
        = W.polyToFunctionField X - ι a := by
      have : (XClass W a : W.CoordinateRing)
          = algebraMap F[X] W.CoordinateRing (X - C a) := rfl
      rw [this, ← polyToFunctionField_apply, map_sub, polyToFunctionField_C]
    have h0a := kw_addXFun_sub_mul_sq_num_charFree W a b
    have heqR := kw_taseq_linear_eq_algebraMap_mk_taylorRemainder₂_charFree (W := W) h.1
    rw [hR_X, map_sub, map_mul, map_pow, hXC,
      ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField,
      ← heqR, ← h0a, map_sub]
    ring
  have hR_Xne : R_X ≠ 0 := by
    intro h0; rw [h0, _root_.map_zero] at hprod
    exact mul_ne_zero hne_x₂ hXa2 hprod
  have hβ'sq_mem : ι' β ^ 2 * R_X ∈ XYIdeal W a (C b) ^ 3 := by
    have hXmem : XClass W a ∈ XYIdeal W a (C b) :=
      Ideal.subset_span (Set.mem_insert _ _)
    have hLmem : (Lcot : W.CoordinateRing) ∈ XYIdeal W a (C b) ^ 2 :=
      taylor_linear_mem_XYIdeal_sq h.1
    have hkey :
        ι' β ^ 2 * R_X
          = ι' (2 * α + W.a₁ * β) * (XClass W a * Lcot) + Lcot * Lcot
            - ι' β ^ 2 * XClass W a ^ 3 := by
      have hLcot : (Lcot : W.CoordinateRing)
          = ι' (-α) * XClass W a + ι' β * YClass W (C b) := by
        congr 2
        · exact congrArg ι' (by rw [kw_taseq_α_eq_neg_polyX_charFree]; ring)
        · exact congrArg ι' kw_taseq_β_eq_polyY_charFree.symm
      have hXgen : CoordinateRing.mk W (C (X : F[X])) = XClass W a + ι' a := by
        rw [CoordinateRing.algebraMap_eq_mk_C_C, XClass, ← map_add, ← Polynomial.C_add,
          sub_add_cancel]
      have htR₂ : CoordinateRing.mk W (W.taylorRemainder₂ a b)
          = YClass W (C b) ^ 2 + ι' W.a₁ * (XClass W a * YClass W (C b))
            - (XClass W a + ι' (3 * a + W.a₂)) * XClass W a ^ 2 := by
        have hc : (C (2 * a + W.a₂) : F[X]) = C 2 * C a + C W.a₂ := by
          rw [Polynomial.C_add, Polynomial.C_mul]
        simp only [taylorRemainder₂, map_sub, map_add, map_mul, map_pow, hc,
          ← CoordinateRing.algebraMap_eq_mk_C_C, map_ofNat,
          show CoordinateRing.mk W (Y - C (C b)) = YClass W (C b) from rfl,
          hXgen]
        ring
      have hι'βx₂ := congrArg ι'
        (kw_taseq_betasq_x2_sub_a_charFree (W := W) (a := a) (b := b) hβ)
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, _root_.map_neg] at hι'βx₂ hLcot
      rw [hR_X, hLcot, htR₂]
      simp only [map_sub, map_add, map_mul, map_ofNat]
      linear_combination (-(XClass W a) ^ 2 : W.CoordinateRing) * hι'βx₂
    rw [hkey, show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
    refine sub_mem (add_mem ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hXmem hLmem)
    · exact Ideal.mul_mem_mul (Ideal.pow_le_self two_ne_zero hLmem) hLmem
    · rw [show (XClass W a : W.CoordinateRing) ^ 3 = XClass W a * XClass W a ^ 2 by ring]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hXmem (Ideal.pow_mem_pow hXmem 2))
  have hR_Xmem : R_X ∈ XYIdeal W a (C b) ^ 3 := by
    have hunit : IsUnit (ι' β ^ 2) := (IsUnit.map ι' (isUnit_iff_ne_zero.mpr hβ)).pow 2
    obtain ⟨u, hu⟩ := hunit
    have : R_X = (↑u⁻¹ : W.CoordinateRing) * (ι' β ^ 2 * R_X) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]; exact Ideal.mul_mem_left _ _ hβ'sq_mem
  have hordR : (3 : ℤ) ≤ (placeOfEquation h.1).ord
      (algebraMap W.CoordinateRing W.FunctionField R_X) := by
    have := kw_taseq_ord_ge_of_mem_XYIdeal_pow_charFree h.1 hR_Xne (n := 3) hR_Xmem
    exact_mod_cast this
  have hordXa1 := kw_taseq_ord_X_sub_eq_one_charFree h hβ
  have heqord := (placeOfEquation h.1).ord_mul hne_x₂ hXa2
  rw [hprod, (placeOfEquation h.1).ord_pow, hordXa1] at heqord
  omega

private theorem kw_taseq_ord_addYFun_sub_double_pos_charFree :
    0 < (placeOfEquation h.1).ord (W.addYFun a b - ι y₂) := by
  set u := W.polyToFunctionField X - ι a with hu
  set M := (W.yGen - ι b) + ι W.a₁ * u with hM
  have hXa : u ≠ 0 := X_sub_algebraMap_ne_zero a
  have hXa2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hXa
  have hne_y₂ : W.addYFun a b - ι y₂ ≠ 0 :=
    sub_ne_zero.mpr (kw_addYFun_ne_algebraMap_any_charFree W h.1 y₂)
  set S : W.FunctionField := -ι (β + y₂ - b + W.a₁ * (x₂ - a)) * u ^ 2
      - ι (x₂ - a) * u * (W.yGen - ι b) with hS
  have hstep :
      (W.addYFun a b - ι y₂) * u ^ 2 = S - M * u * (W.addXFun a b - ι x₂) := by
    have step_i := kw_addYFun_sub_mul_linear_charFree W a b
    rw [hS, hM, hu]
    simp only [map_add, map_sub, map_mul] at step_i ⊢
    linear_combination (W.polyToFunctionField X - ι a) * step_i
  set R_S : W.CoordinateRing :=
    -ι' (β + y₂ - b + W.a₁ * (x₂ - a)) * XClass W a ^ 2
      - ι' (x₂ - a) * XClass W a * YClass W (C b) with hR_S
  have hSmap : S = algebraMap W.CoordinateRing W.FunctionField R_S := by
    have hXC : algebraMap W.CoordinateRing W.FunctionField (XClass W a) = u := by
      rw [hu]
      have : (XClass W a : W.CoordinateRing)
          = algebraMap F[X] W.CoordinateRing (X - C a) := rfl
      rw [this, ← polyToFunctionField_apply, map_sub, polyToFunctionField_C]
    have hYC : algebraMap W.CoordinateRing W.FunctionField (YClass W (C b))
        = W.yGen - ι b := by
      have : (YClass W (C b) : W.CoordinateRing)
          = CoordinateRing.mk W Y - algebraMap F W.CoordinateRing b := by
        show CoordinateRing.mk W (Y - C (C b)) = _; simp only [map_sub]; rfl
      rw [this, map_sub]; rfl
    rw [hR_S, map_sub, map_mul, map_mul, map_mul, _root_.map_neg, map_pow, hXC, hYC,
      ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField,
      ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField, hS]
  have hβR_S : ι' β * R_S = -ι' (x₂ - a) * (XClass W a * Lcot) := by
    rw [hR_S, show (Lcot : W.CoordinateRing)
        = ι' (-α) * XClass W a + ι' β * YClass W (C b) from by
          congr 2
          · exact congrArg ι' (by rw [kw_taseq_α_eq_neg_polyX_charFree]; ring)
          · exact congrArg ι' kw_taseq_β_eq_polyY_charFree.symm]
    have hyc := kw_taseq_beta_y2_coeff_charFree (W := W) (a := a) (b := b) hβ
    have hι'yc : ι' (β * (β + y₂ - b + W.a₁ * (x₂ - a)) + α * (x₂ - a)) = ι' 0 :=
      congrArg ι' hyc
    simp only [map_mul, map_add, map_sub, _root_.map_neg, _root_.map_zero] at hι'yc ⊢
    linear_combination -(XClass W a ^ 2) * hι'yc
  have hR_Smem : R_S ∈ XYIdeal W a (C b) ^ 3 := by
    have hβ'mem : ι' β * R_S ∈ XYIdeal W a (C b) ^ 3 := by
      rw [hβR_S, show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
      exact Ideal.mul_mem_left _ _
        (Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_insert _ _))
          (taylor_linear_mem_XYIdeal_sq h.1))
    have hunit : IsUnit (ι' β) := IsUnit.map ι' (isUnit_iff_ne_zero.mpr hβ)
    obtain ⟨v, hv⟩ := hunit
    have : R_S = (↑v⁻¹ : W.CoordinateRing) * (ι' β * R_S) := by
      rw [← hv, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]; exact Ideal.mul_mem_left _ _ hβ'mem
  have hordXa1 := kw_taseq_ord_X_sub_eq_one_charFree h hβ
  rw [← hu] at hordXa1
  have hordS : S = 0 ∨ (3 : ℤ) ≤ (placeOfEquation h.1).ord S := by
    rcases eq_or_ne R_S 0 with h0 | h0
    · left; rw [hSmap, h0, _root_.map_zero]
    · right; rw [hSmap]
      have := kw_taseq_ord_ge_of_mem_XYIdeal_pow_charFree h.1 h0 (n := 3) hR_Smem
      exact_mod_cast this
  have hordMterm : M * u * (W.addXFun a b - ι x₂) = 0
      ∨ (3 : ℤ) ≤ (placeOfEquation h.1).ord (M * u * (W.addXFun a b - ι x₂)) := by
    rcases eq_or_ne (M * u * (W.addXFun a b - ι x₂)) 0 with h0 | h0
    · exact Or.inl h0
    · right
      have hMne : M ≠ 0 := by
        intro hM0; rw [hM0, zero_mul, zero_mul] at h0; exact h0 rfl
      have hXFne : W.addXFun a b - ι x₂ ≠ 0 :=
        sub_ne_zero.mpr (kw_addXFun_ne_algebraMap_any_charFree W h.1 x₂)
      rw [(placeOfEquation h.1).ord_mul (mul_ne_zero hMne hXa) hXFne,
        (placeOfEquation h.1).ord_mul hMne hXa, hordXa1]
      have hXord := kw_taseq_ord_addXFun_sub_double_pos_charFree h hβ
      have hMmap : M = algebraMap W.CoordinateRing W.FunctionField
          (YClass W (C b) + ι' W.a₁ * XClass W a) := by
        have hXC : algebraMap W.CoordinateRing W.FunctionField (XClass W a) = u := by
          rw [hu]
          have : (XClass W a : W.CoordinateRing)
              = algebraMap F[X] W.CoordinateRing (X - C a) := rfl
          rw [this, ← polyToFunctionField_apply, map_sub, polyToFunctionField_C]
        have hYC : algebraMap W.CoordinateRing W.FunctionField (YClass W (C b))
            = W.yGen - ι b := by
          have : (YClass W (C b) : W.CoordinateRing)
              = CoordinateRing.mk W Y - algebraMap F W.CoordinateRing b := by
            show CoordinateRing.mk W (Y - C (C b)) = _; simp only [map_sub]; rfl
          rw [this, map_sub]; rfl
        rw [hM, map_add, map_mul, hXC, hYC,
          ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
      have hMmem : YClass W (C b) + ι' W.a₁ * XClass W a ∈ XYIdeal W a (C b) :=
        add_mem (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      have hMcne : (YClass W (C b) + ι' W.a₁ * XClass W a : W.CoordinateRing) ≠ 0 := by
        intro h0
        rw [h0, _root_.map_zero] at hMmap; exact hMne hMmap
      have hMord : (1 : ℤ) ≤ (placeOfEquation h.1).ord M := by
        rw [hMmap]
        have := kw_taseq_ord_ge_of_mem_XYIdeal_pow_charFree h.1 hMcne (n := 1)
          (by simpa using hMmem)
        exact_mod_cast this
      omega
  have hfg_ne : (W.addYFun a b - ι y₂) * u ^ 2 ≠ 0 := mul_ne_zero hne_y₂ hXa2
  rw [hstep] at hfg_ne
  have hordLHS : (3 : ℤ) ≤ (placeOfEquation h.1).ord
      (S - M * u * (W.addXFun a b - ι x₂)) :=
    kw_taseq_le_ord_sub_charFree (placeOfEquation h.1) hfg_ne hordS hordMterm
  have heqord := (placeOfEquation h.1).ord_mul hne_y₂ hXa2
  rw [hstep, (placeOfEquation h.1).ord_pow, hordXa1] at heqord
  omega

end DoubleOrd

private theorem kw_translAffineSeamAtEqX_charFree (h : W.Nonsingular a b) (hP : W.Nonsingular a b) :
    (placeOfEquation hP.1).restrictAlong
        (Point.translateFF (W := W) (.some a b h)).toAlgHom
        (kw_translateFF_toAlgHom_isIntegral_charFree (.some a b h))
      = placeOfPoint (Point.some a b hP + Point.some a b h) := by
  have hPeq : (placeOfEquation hP.1 : Place F W.FunctionField) = placeOfEquation h.1 := rfl
  rw [hPeq, show (Point.some a b hP : W.Point) = Point.some a b h from rfl]
  rcases eq_or_ne (kwTISDβ_charFree W a b) 0 with hβ | hβ
  ·
    have h2A : Point.some a b h + Point.some a b h = 0 := by
      have hbn : W.negY a b = b := (kw_taseq_β_eq_zero_iff_eq_negY_charFree.mp hβ).symm
      have hneg : (-Point.some a b h : W.Point) = Point.some a b h := by
        rw [Point.neg_some, Point.some.injEq]; exact ⟨rfl, hbn⟩
      nth_rw 2 [← hneg]; exact add_neg_cancel _
    rw [h2A]
    refine kw_translAffineSeam_at_of_coordSeamData_charFree h _ 0 ?_
    exact kw_addXFun_notMem_placeOfEquation_self_of_β_eq_zero_charFree h hβ
  ·
    have hYne : b ≠ W.negY a b := fun hy => hβ (kw_taseq_β_eq_zero_iff_eq_negY_charFree.mpr hy)
    rw [Point.add_self_of_Y_ne hYne]
    refine kw_translAffineSeam_at_of_coordSeamData_charFree h _ _ ?_
    exact ⟨kw_taseq_ord_addXFun_sub_double_pos_charFree h hβ,
      kw_taseq_ord_addYFun_sub_double_pos_charFree h hβ⟩

private theorem kw_restrictAlong_translateFF_infinitePlace_charFree (h : W.Nonsingular a b) :
    (InfinitePlace.place : Place F W.FunctionField).restrictAlong
        (Point.translateFF (W := W) (.some a b h)).toAlgHom
        (kw_translateFF_toAlgHom_isIntegral_charFree (.some a b h))
      = placeOfPoint (.some a b h) :=
  kw_translAffineSeam_at_of_coordSeamData_charFree h _ (.some a b h)
    ⟨kw_ord_addXFun_sub_pos_charFree W h.1 _ InfinitePlace.not_isFinitePlace,
     kw_ord_addYFun_sub_pos_charFree W h.1 _ InfinitePlace.not_isFinitePlace⟩

private theorem kw_restrictAlong_translateFF_some_placeOfPoint_charFree (h : W.Nonsingular a b)
    (Q : W.Point) :
    (placeOfPoint Q).restrictAlong
        (Point.translateFF (W := W) (.some a b h)).toAlgHom
        (kw_translateFF_toAlgHom_isIntegral_charFree (.some a b h))
      = placeOfPoint (Q + .some a b h) := by
  cases Q with
  | zero =>
    rw [placeOfPoint_zero]
    exact kw_restrictAlong_translateFF_infinitePlace_charFree h
  | some p q hP =>
    rw [placeOfPoint_some]
    rcases eq_or_ne p a with rfl | hne
    ·
      rcases eq_or_ne q b with rfl | hq
      ·
        exact kw_translAffineSeamAtEqX_charFree h hP
      ·
        have hqn : q = W.negY p b :=
          (Affine.Y_eq_of_X_eq hP.1 h.1 rfl).resolve_left hq
        subst hqn
        have hβ : kwTISDβ_charFree W p b ≠ 0 := by
          intro h0
          exact hq (by simp only [Affine.negY]; simp only [kwTISDβ_charFree] at h0
                       linear_combination -h0)
        have hsum : Point.some p (W.negY p b) hP + Point.some p b h = 0 := by
          have hneg : Point.some p (W.negY p b) hP = -Point.some p b h := by
            rw [Point.neg_some]
          rw [hneg]; exact _root_.neg_add_cancel _
        rw [hsum]
        refine kw_translAffineSeam_at_of_coordSeamData_charFree h _ 0 ?_
        exact kw_addXFun_notMem_placeOfEquation_negA_charFree h hβ
    ·
      rw [Point.add_of_X_ne hne]
      refine kw_translAffineSeam_at_of_coordSeamData_charFree h _ _ ?_
      exact ⟨kw_ord_addXFun_sub_addX_pos_charFree W h hP hne,
        kw_ord_addYFun_sub_addY_pos_charFree W h hP hne⟩

end GenericW

end WeierstrassCurve.Affine

/-! ## The two headlines -/

theorem WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (R : W.Point) :
    ∃ (τ : W.FunctionField ≃ₐ[F] W.FunctionField) (hτ : τ.toAlgHom.toRingHom.IsIntegral),
      ∀ Q : W.Point, (placeOfPoint Q).restrictAlong τ.toAlgHom hτ = placeOfPoint (Q + R) := by
  refine ⟨Point.translateFF (W := W) R, kw_translateFF_toAlgHom_isIntegral_charFree R,
    fun Q => ?_⟩
  cases R with
  | zero =>
      rw [show (Point.zero : W.Point) = 0 from rfl, add_zero]
      exact IsogenyEndDatum.restrictAlong_algHomId W (placeOfPoint Q)
  | some a b h => exact kw_restrictAlong_translateFF_some_placeOfPoint_charFree h Q

theorem WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (R : W.Point) :
    ∃ (τ : W.FunctionField ≃ₐ[F] W.FunctionField) (hτ : τ.toAlgHom.toRingHom.IsIntegral),
      ∀ Q : W.Point, (placeOfPoint Q).restrictAlong τ.toAlgHom hτ = placeOfPoint (Q + R) := by
  exact exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add R
