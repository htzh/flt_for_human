/-
The variable change of a Weierstrass curve acts on the function field: for a
variable change `C` over a field `F` there is an `F`-algebra equivalence
`W.toAffine.FunctionField ≃ₐ[F] (C • W).toAffine.FunctionField`. This is set **D-3**
of `topics/velu/WORKORDER-P2-basechange.md`.

Statements are transcribed verbatim from the pinned FLT `aa2d8b3`
`P2M/Sol/S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.lean`
(744 lines); the wrapper
`Theorems/Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.lean`
is the statement authority for the headline, and the `S_` file for the `mrtw60a*`
block. That block is the node-unique content: the affine formulas
`mrtw60a_pXFwd`/`mrtw60a_pYLinFwd` and their images `mrtw60a_xFwd`/`mrtw60a_yFwd` on the
generic point, the rigidity lemmas `mrtw60a_coordHom_ext`/`mrtw60a_funHom_ext`, the
function-field map `mrtw60aVCFunHom` with its two inverse identities, and the
resulting `mrtw60aVCPlaceSeamAlgEquiv`. The pin writes them in the solution-file
namespaces `FLT.Mrtw60aVCPlaceSeamS1`/`S3`; the port drops that file noise and keeps
the names, which is what the statement checker keys on.

Assumes from D-1 (`Isogeny/BaseChange.lean`): the general-`L` function-field
`pointPullbackHomTo*` column and `functionField_algHom_ext` (§3.1: written once, in the
shared prelude). The variable-change *vocabulary* `vcX`/`vcY` and
`equation_variableChange_iff` is the ported `Velu/Equivariance.lean`, re-exported by the
pin's declared prerequisite `Velu/VariableChangePoint.lean`; nothing is re-derived.
`mrtw60a_funHom_ext` is a one-line invocation of D-1's `functionField_algHom_ext`
(the pin's proof routes through its own `mrtw60a_coordHom_ext`, which the port keeps as
part of the verified surface).

Only proof bodies are adapted to mathlib `v4.34.0`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.lean>
-/
import FLTForHuman.WeierstrassCurve.Isogeny.BaseChange
import FLTForHuman.WeierstrassCurve.Velu.VariableChangePoint

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate WeierstrassCurve

universe u

namespace WeierstrassCurve
namespace Affine

variable {F : Type u} [Field F]

/-! ### The forward variable-change coordinates

`mrtw60a_pXFwd`/`mrtw60a_pYLinFwd` are the affine formulas of the variable change `C`
read as polynomials over `F`, and `mrtw60a_xFwd C V`/`mrtw60a_yFwd C V` are their values
at the generic point of `V`, matching `vcX`/`vcY` of the `C`-translate. -/

theorem mrtw60a_inv_smul {C : VariableChange F} {W V : Affine F} (h : C • W = V) :
    C⁻¹ • V = W := by
  rw [← h, inv_smul_smul]

variable (C : VariableChange F)

def mrtw60a_pXFwd : F[X] := Polynomial.C ((C.u : F) ^ 2) * X + Polynomial.C C.r

def mrtw60a_pYLinFwd : F[X] := Polynomial.C ((C.u : F) ^ 2 * C.s) * X + Polynomial.C C.t

section Values

variable (V : Affine F)

def mrtw60a_xFwd : V.FunctionField := polyToFunctionField V (mrtw60a_pXFwd C)

def mrtw60a_yFwd : V.FunctionField :=
  algebraMap F V.FunctionField ((C.u : F) ^ 3) * yGen V
    + polyToFunctionField V (mrtw60a_pYLinFwd C)

theorem mrtw60a_xFwd_shape :
    mrtw60a_xFwd C V
      = algebraMap F V.FunctionField ((C.u : F) ^ 2) * polyToFunctionField V X
        + algebraMap F V.FunctionField C.r := by
  simp [mrtw60a_xFwd, mrtw60a_pXFwd, polyToFunctionField_C]

theorem mrtw60a_yFwd_shape :
    mrtw60a_yFwd C V
      = algebraMap F V.FunctionField ((C.u : F) ^ 3) * yGen V
        + algebraMap F V.FunctionField ((C.u : F) ^ 2 * C.s) * polyToFunctionField V X
        + algebraMap F V.FunctionField C.t := by
  simp [mrtw60a_yFwd, mrtw60a_pYLinFwd, polyToFunctionField_C, add_assoc]

theorem mrtw60a_xInv_shape :
    mrtw60a_xFwd C⁻¹ V
      = algebraMap F V.FunctionField (((C.u⁻¹ : Fˣ) : F) ^ 2)
        * (polyToFunctionField V X - algebraMap F V.FunctionField C.r) := by
  simp only [mrtw60a_xFwd, mrtw60a_pXFwd, VariableChange.inv_def, map_add, map_mul,
    polyToFunctionField_C, _root_.map_neg, map_pow]
  ring

theorem mrtw60a_yInv_shape :
    mrtw60a_yFwd C⁻¹ V
      = algebraMap F V.FunctionField (((C.u⁻¹ : Fˣ) : F) ^ 3)
        * (yGen V - algebraMap F V.FunctionField C.t
            - algebraMap F V.FunctionField C.s
              * (polyToFunctionField V X - algebraMap F V.FunctionField C.r)) := by
  simp only [mrtw60a_yFwd, mrtw60a_pYLinFwd, VariableChange.inv_def, map_add, map_mul,
    polyToFunctionField_C, map_sub, _root_.map_neg, map_pow]
  ring

theorem mrtw60a_xFwd_eq_vcX :
    mrtw60a_xFwd C V
      = vcX (C.map (algebraMap F V.FunctionField)) (polyToFunctionField V X) := by
  rw [mrtw60a_xFwd_shape, vcX]
  simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_coe, map_pow]

theorem mrtw60a_yFwd_eq_vcY :
    mrtw60a_yFwd C V
      = vcY (C.map (algebraMap F V.FunctionField)) (polyToFunctionField V X) (yGen V) := by
  rw [mrtw60a_yFwd_shape, vcY]
  simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_coe, map_pow, map_mul]

end Values

/-! ### The generic point of `V` lies on the `C`-translate -/

variable {C} {W V : Affine F}

theorem mrtw60a_equation_fwd (h : C • W = V) :
    (W.map (algebraMap F V.FunctionField)).toAffine.Equation
      (mrtw60a_xFwd C V) (mrtw60a_yFwd C V) := by
  have hmap : (C.map (algebraMap F V.FunctionField))
      • (W.map (algebraMap F V.FunctionField)) = V.map (algebraMap F V.FunctionField) := by
    rw [WeierstrassCurve.map_variableChange, h]
  have hgen : ((C.map (algebraMap F V.FunctionField))
      • (W.map (algebraMap F V.FunctionField))).toAffine.Equation
      (polyToFunctionField V X) (yGen V) := by
    rw [hmap]
    exact equation_map_polyToFunctionField_yGen
  rw [mrtw60a_xFwd_eq_vcX, mrtw60a_yFwd_eq_vcY]
  exact (equation_variableChange_iff (C := C.map (algebraMap F V.FunctionField))
    (W := (W.map (algebraMap F V.FunctionField)).toAffine)
    (polyToFunctionField V X) (yGen V)).mp hgen

theorem mrtw60a_transcendental_affine {L : Type u} [Field L] [Algebra F L] {z : L}
    (hz : Transcendental F z) {c d : F} (hc : c ≠ 0) :
    Transcendental F (algebraMap F L c * z + algebraMap F L d) := by
  rw [transcendental_iff] at hz ⊢
  intro p hp
  have hcomp : Polynomial.aeval z (p.comp (Polynomial.C c * X + Polynomial.C d)) = 0 := by
    rw [Polynomial.aeval_comp]
    simpa using hp
  have h0 := hz _ hcomp
  by_contra hp0
  have hlc : (p.comp (Polynomial.C c * X + Polynomial.C d)).leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_linear hc]; norm_num)]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp0)
      (pow_ne_zero _ (by rw [Polynomial.leadingCoeff_linear hc]; exact hc))
  exact hlc (by rw [h0, Polynomial.leadingCoeff_zero])

variable (C) (V : Affine F) in

theorem mrtw60a_transcendental_xFwd : Transcendental F (mrtw60a_xFwd C V) := by
  rw [mrtw60a_xFwd_shape]
  exact mrtw60a_transcendental_affine (L := V.FunctionField)
    (z := polyToFunctionField V X) (c := (C.u : F) ^ 2) (d := C.r)
    (transcendental_polyToFunctionField_X (W := V)) (pow_ne_zero 2 C.u.ne_zero)

variable (C) (V : Affine F) in

theorem mrtw60a_aeval_xFwd_injective :
    Function.Injective (Polynomial.aeval (R := F) (mrtw60a_xFwd C V)) :=
  (injective_iff_map_eq_zero _).mpr fun p hp =>
    transcendental_iff.mp (mrtw60a_transcendental_xFwd C V) p hp

/-! ### Rigidity: an algebra map out of the coordinate ring is its two coordinates -/

theorem mrtw60a_coordHom_ext {W : Affine F} {S : Type u} [CommRing S] [Algebra F S]
    {φ ψ : W.CoordinateRing →ₐ[F] S}
    (hX : φ (CoordinateRing.mk W (Polynomial.C X)) = ψ (CoordinateRing.mk W (Polynomial.C X)))
    (hY : φ (CoordinateRing.mk W Y) = ψ (CoordinateRing.mk W Y)) : φ = ψ := by
  have hpoly : ∀ p : F[X],
      φ (CoordinateRing.mk W (Polynomial.C p)) = ψ (CoordinateRing.mk W (Polynomial.C p)) := by
    intro p
    have hC : (φ.toRingHom.comp (CoordinateRing.mk W)).comp (Polynomial.C : F[X] →+* F[X][Y])
        = (ψ.toRingHom.comp (CoordinateRing.mk W)).comp (Polynomial.C : F[X] →+* F[X][Y]) := by
      refine Polynomial.ringHom_ext (fun c => ?_) hX
      show φ (CoordinateRing.mk W (Polynomial.C (Polynomial.C c)))
        = ψ (CoordinateRing.mk W (Polynomial.C (Polynomial.C c)))
      rw [← CoordinateRing.algebraMap_eq_mk_C_C, φ.commutes, ψ.commutes]
    exact DFunLike.congr_fun hC p
  have hh : φ.toRingHom.comp (CoordinateRing.mk W) = ψ.toRingHom.comp (CoordinateRing.mk W) :=
    Polynomial.ringHom_ext hpoly hY
  have hRing : φ.toRingHom = ψ.toRingHom :=
    (RingHom.cancel_right AdjoinRoot.mk_surjective).mp hh
  exact AlgHom.ext fun z => DFunLike.congr_fun hRing z

end Affine

end WeierstrassCurve

namespace WeierstrassCurve
namespace Affine

/-! ### The variable-change map of function fields

`mrtw60aVCFunHom h` is the `F`-algebra map `W.FunctionField →ₐ[F] V.FunctionField` sending
the generic point of `W` to that of `V` along the equation `mrtw60a_equation_fwd`; the two
`…_X`/`…_yGen` computation lemmas pin it down, `mrtw60a_funHom_ext` shows that is enough,
and the two inverse identities make it an `AlgEquiv`. -/

variable {F : Type u} [Field F]

theorem mrtw60a_funHom_ext {W : Affine F} {L : Type u} [Field L] [Algebra F L]
    {φ ψ : W.FunctionField →ₐ[F] L}
    (hX : φ (polyToFunctionField W X) = ψ (polyToFunctionField W X))
    (hY : φ (yGen W) = ψ (yGen W)) : φ = ψ :=
  functionField_algHom_ext hX hY

variable {C : VariableChange F} {W V : Affine F}

def mrtw60aVCFunHom (h : C • W = V) : W.FunctionField →ₐ[F] V.FunctionField :=
  pointPullbackHomTo (mrtw60a_equation_fwd h) (mrtw60a_aeval_xFwd_injective C V)

@[scoped simp] theorem mrtw60aVCFunHom_X (h : C • W = V) :
    mrtw60aVCFunHom h (polyToFunctionField W X) = mrtw60a_xFwd C V :=
  pointPullbackHomTo_polyToFunctionField_X _ _

@[scoped simp] theorem mrtw60aVCFunHom_yGen (h : C • W = V) :
    mrtw60aVCFunHom h (yGen W) = mrtw60a_yFwd C V :=
  pointPullbackHomTo_yGen _ _

def mrtw60aVCFunHomInv (h : C • W = V) : V.FunctionField →ₐ[F] W.FunctionField :=
  mrtw60aVCFunHom (mrtw60a_inv_smul h)

@[scoped simp] theorem mrtw60aVCFunHomInv_X (h : C • W = V) :
    mrtw60aVCFunHomInv h (polyToFunctionField V X) = mrtw60a_xFwd C⁻¹ W :=
  mrtw60aVCFunHom_X (mrtw60a_inv_smul h)

@[scoped simp] theorem mrtw60aVCFunHomInv_yGen (h : C • W = V) :
    mrtw60aVCFunHomInv h (yGen V) = mrtw60a_yFwd C⁻¹ W :=
  mrtw60aVCFunHom_yGen (mrtw60a_inv_smul h)

theorem mrtw60a_invu_mul_u {E : Affine F} (C : VariableChange F) :
    algebraMap F E.FunctionField (((C.u⁻¹ : Fˣ) : F))
      * algebraMap F E.FunctionField ((C.u : F)) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

theorem mrtw60a_funHomInv_comp_funHom (h : C • W = V) :
    (mrtw60aVCFunHomInv h).comp (mrtw60aVCFunHom h) = AlgHom.id F W.FunctionField := by
  have h1 := mrtw60a_invu_mul_u (E := W) C
  refine mrtw60a_funHom_ext ?_ ?_
  · rw [AlgHom.comp_apply, mrtw60aVCFunHom_X, AlgHom.id_apply, mrtw60a_xFwd_shape, map_add,
      map_mul, AlgHom.commutes, AlgHom.commutes, mrtw60aVCFunHomInv_X, mrtw60a_xInv_shape]
    simp only [map_pow]
    linear_combination ((polyToFunctionField W X - algebraMap F W.FunctionField C.r)
      * (algebraMap F W.FunctionField ((C.u : F))
          * algebraMap F W.FunctionField (((C.u⁻¹ : Fˣ) : F)) + 1)) * h1
  · rw [AlgHom.comp_apply, mrtw60aVCFunHom_yGen, AlgHom.id_apply, mrtw60a_yFwd_shape,
      map_add, map_add, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes,
      AlgHom.commutes, mrtw60aVCFunHomInv_X, mrtw60aVCFunHomInv_yGen, mrtw60a_xInv_shape,
      mrtw60a_yInv_shape]
    simp only [map_pow, map_mul]
    linear_combination (((algebraMap F W.FunctionField (((C.u⁻¹ : Fˣ) : F))
          * algebraMap F W.FunctionField ((C.u : F))) ^ 2
        + algebraMap F W.FunctionField (((C.u⁻¹ : Fˣ) : F))
          * algebraMap F W.FunctionField ((C.u : F)) + 1)
        * (yGen W - algebraMap F W.FunctionField C.t)
      - (algebraMap F W.FunctionField (((C.u⁻¹ : Fˣ) : F))
          * algebraMap F W.FunctionField ((C.u : F))) ^ 2
        * algebraMap F W.FunctionField C.s
        * (polyToFunctionField W X - algebraMap F W.FunctionField C.r)) * h1

theorem mrtw60a_funHom_comp_funHomInv (h : C • W = V) :
    (mrtw60aVCFunHom h).comp (mrtw60aVCFunHomInv h) = AlgHom.id F V.FunctionField := by
  have h1 := mrtw60a_invu_mul_u (E := V) C
  refine mrtw60a_funHom_ext ?_ ?_
  · rw [AlgHom.comp_apply, mrtw60aVCFunHomInv_X, AlgHom.id_apply, mrtw60a_xInv_shape,
      map_mul, map_sub, AlgHom.commutes, AlgHom.commutes, mrtw60aVCFunHom_X,
      mrtw60a_xFwd_shape]
    simp only [map_pow]
    linear_combination (polyToFunctionField V X
      * (algebraMap F V.FunctionField (((C.u⁻¹ : Fˣ) : F))
          * algebraMap F V.FunctionField ((C.u : F)) + 1)) * h1
  · rw [AlgHom.comp_apply, mrtw60aVCFunHomInv_yGen, AlgHom.id_apply, mrtw60a_yInv_shape,
      map_mul, map_sub, map_sub, map_mul, map_sub, AlgHom.commutes, AlgHom.commutes,
      AlgHom.commutes, AlgHom.commutes, mrtw60aVCFunHom_X, mrtw60aVCFunHom_yGen,
      mrtw60a_xFwd_shape, mrtw60a_yFwd_shape]
    simp only [map_pow, map_mul]
    linear_combination (((algebraMap F V.FunctionField (((C.u⁻¹ : Fˣ) : F))
          * algebraMap F V.FunctionField ((C.u : F))) ^ 2
        + algebraMap F V.FunctionField (((C.u⁻¹ : Fˣ) : F))
          * algebraMap F V.FunctionField ((C.u : F)) + 1) * yGen V) * h1

def mrtw60aVCPlaceSeamAlgEquiv (h : C • W = V) : V.FunctionField ≃ₐ[F] W.FunctionField :=
  AlgEquiv.ofAlgHom (mrtw60aVCFunHomInv h) (mrtw60aVCFunHom h)
    (mrtw60a_funHomInv_comp_funHom h) (mrtw60a_funHom_comp_funHomInv h)

end Affine
end WeierstrassCurve

namespace WeierstrassCurve

open WeierstrassCurve.Affine

/-- A variable change of a Weierstrass curve induces an `F`-algebra equivalence of the
function fields of the curve and of its translate. -/
theorem nonempty_functionField_algEquiv_of_variableChange
    {F : Type u} [Field F] (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) :
    Nonempty (W.toAffine.FunctionField ≃ₐ[F] (C • W).toAffine.FunctionField) :=
  ⟨(mrtw60aVCPlaceSeamAlgEquiv (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl).symm⟩

end WeierstrassCurve

end
