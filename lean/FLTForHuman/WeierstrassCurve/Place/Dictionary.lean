/-
The Weierstrass `CoordinateRing` place dictionary: the `XYIdeal` maximality and
uniqueness facts, the Dedekind-domain theorem `isDedekindDomain_of_Δ_ne_zero`,
the finite-place predicate `IsFinitePlace` with its centre, `placeOfEquation` and
its degree, `isFinitePlace_iff_exists_placeOfEquation`, the infinite-place class
`InfinitePlace`, `exists_equation`, and the `ord`-at-infinity laws
(`isFinitePlace_of_mem`, `ord_X_neg_of_not_isFinitePlace`,
`two_mul_ord_Y_eq_three_mul_ord_X`, `two_mul_ord_eq_of_not_isFinitePlace`).

Statements are transcribed verbatim from the pinned FLT `aa2d8b3`:

* `P2M/Sol/S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean`
  (A1, lines 47–1719);
* `P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean`
  for the transport block (`isFinitePlace_smul_iff_forall_symm_mem`,
  `forall_place_ord_nonneg_iff_finite_and_not_finite`).

The RR/class-group/Abel block of the A1 file (`rrParam`, `RRSpace`, `basisAux`,
`geomPlaceOfPoint`, `unitIdealOf*`, `AbelTheorem`, `isPrincipal_of_geomDivisorSum_eq_zero'`,
`instAbelTheorem`) is deliberately not ported (it belongs to a later home), so the
two A1 lemmas whose proofs consume it (`mem_iff_natDegree_norm_le`,
`deg_eq_one_of_not_isFinitePlace`, `exists_smul_sub_natDegree_norm_lt`) are also
not carried; the map/res files that consume this dictionary do not reference them.

The `placeOfEquation` ord/centre dictionary and the polynomial-at-a-point bridge
(`algebraMap_coordinateRing_ne_zero`, `IsFinitePlace.mem_centre_iff_ord_ne_zero`,
`algebraMap_polynomial_eq_mk_C`, `mk_mem_XYIdeal_iff`, `ord_placeOfEquation_*`,
`centre_placeOfEquation`, `isRational_placeOfEquation`,
`eq_placeOfEquation_of_le_centre`, `ord_polyToFunctionField_*`) were transcribed by
the Vélu sets in delimited `Prerequisites` sections of
`Velu/Discharge.lean`/`Velu/Engine.lean`/`Velu/RestrictAlong.lean`; the H5r
refactor round moved them here, because the `IsogenyEndDatum` and base-change
homes consume them and must not import Vélu.

Only proof bodies are adapted to mathlib `v4.34.0`; declaration names and
statements are kept. Already ported and imported: `polyToFunctionField*`,
`yCoord`, `weierstrassQuadratic*`, `adjoin_yCoord_eq_top`,
`ord_nonneg_of_mem`/`mem_of_ord_nonneg`/`mem_iff_ord_nonneg`/`ord_algebraMap`,
`Place.ofHeightOneSpectrum*`, `mem_of_eval_monic_eq_zero`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean>
-/
import FLTForHuman.WeierstrassCurve.FunctionFieldQuadratic
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Defs.RatFuncPlaces
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
open Polynomial
open scoped nonZeroDivisors Polynomial.Bivariate

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem deg_eq_one_of_surjective (v : Place K F)
    (h : Function.Surjective (algebraMap K v.ResidueField)) : v.deg = 1 := by
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    ⟨(algebraMap K v.ResidueField).injective, h⟩
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable [Algebra K R] [IsScalarTower K R F]

theorem deg_ofHeightOneSpectrum_eq_one (w : HeightOneSpectrum R)
    (hw : ∀ r : R, ∃ c : K, r - algebraMap K R c ∈ w.asIdeal) :
    (ofHeightOneSpectrum (K := K) (F := F) w).deg = 1 := by
  set v : Place K F := ofHeightOneSpectrum (K := K) w with hv
  apply deg_eq_one_of_surjective
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z

  obtain ⟨n, d, hd, hnd⟩ : ∃ (n d : R) (_ : d ∈ w.asIdeal.primeCompl),
      (a : F) * algebraMap R F d = algebraMap R F n := by
    obtain ⟨n, d, hcase | hcase⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := F) (a : F)
    · exact ⟨n, d, d.2, hcase⟩
    · refine ⟨(d : R), n, ?_, hcase⟩

      intro hn
      refine d.2 ?_
      replace hn : n ∈ w.asIdeal := hn
      show (d : R) ∈ w.asIdeal
      rw [← w.valuation_lt_one_iff_mem (K := F)] at hn ⊢
      calc w.valuation F (algebraMap R F (d : R))
          = w.valuation F (a : F) * w.valuation F (algebraMap R F n) := by
            rw [← map_mul, hcase]
        _ ≤ 1 * w.valuation F (algebraMap R F n) := mul_le_mul_left a.2 _
        _ = w.valuation F (algebraMap R F n) := one_mul _
        _ < 1 := hn

  obtain ⟨cn, hcn⟩ := hw n
  obtain ⟨cd, hcd⟩ := hw d
  have hcd0 : cd ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero, sub_zero] at hcd
    exact hd hcd

  have hcdR : algebraMap K R cd ∉ w.asIdeal := fun hmem =>
    hd (by simpa using w.asIdeal.add_mem hcd hmem)
  have hvd : w.valuation F (algebraMap R F d) = 1 :=
    le_antisymm (w.valuation_le_one d)
      (not_lt.mp fun hlt => hd ((w.valuation_lt_one_iff_mem (K := F) d).mp hlt))
  have hvcd : w.valuation F (algebraMap K F cd) = 1 := by
    rw [IsScalarTower.algebraMap_apply K R F]
    exact le_antisymm (w.valuation_le_one _)
      (not_lt.mp fun hlt => hcdR ((w.valuation_lt_one_iff_mem (K := F) _).mp hlt))
  have hcdF : algebraMap K F cd ≠ 0 := by
    simpa using hcd0

  refine ⟨cn / cd, ?_⟩
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]
  refine (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal v.toValuationSubring)).mpr ?_
  have hmem : algebraMap K R cn * d - algebraMap K R cd * n ∈ w.asIdeal := by
    have heq : algebraMap K R cn * d - algebraMap K R cd * n
        = -((n - algebraMap K R cn) * d) + n * (d - algebraMap K R cd) := by ring
    rw [heq]
    exact w.asIdeal.add_mem (w.asIdeal.neg_mem (w.asIdeal.mul_mem_right _ hcn))
      (w.asIdeal.mul_mem_left _ hcd)
  have key : ((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F))
      * (algebraMap K F cd * algebraMap R F d)
      = algebraMap R F (algebraMap K R cn * d - algebraMap K R cd * n) := by
    rw [coe_algebraMap, map_div₀, map_sub, map_mul, map_mul]
    simp only [← IsScalarTower.algebraMap_apply K R F]
    field_simp
    linear_combination (-(algebraMap K F cd)) * hnd
  refine (Valuation.mem_maximalIdeal_iff (v := w.valuation F)).mpr ?_
  show w.valuation F ((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F)) < 1
  calc w.valuation F ((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F))
      = w.valuation F ((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F))
        * (w.valuation F (algebraMap K F cd) * w.valuation F (algebraMap R F d)) := by
          rw [hvcd, hvd, one_mul, mul_one]
    _ = w.valuation F (((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F))
        * (algebraMap K F cd * algebraMap R F d)) := by rw [map_mul, map_mul]
    _ = w.valuation F (algebraMap R F (algebraMap K R cn * d - algebraMap K R cd * n)) := by
          rw [key]
    _ < 1 := (w.valuation_lt_one_iff_mem (K := F) _).mpr hmem

end Place

end AlgebraicCurve

namespace WeierstrassCurve

namespace Affine

universe u

variable {F : Type u} [Field F] {W : Affine F}

namespace CoordinateRing

theorem exists_eq_XYIdeal_of_isMaximal [IsAlgClosed F] (𝔪 : Ideal W.CoordinateRing)
    (h𝔪 : 𝔪.IsMaximal) : ∃ x y : F, W.Equation x y ∧ XYIdeal W x (C y) = 𝔪 := by
  haveI := h𝔪

  letI : Field (W.CoordinateRing ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite F (W.CoordinateRing ⧸ 𝔪) :=
    finite_of_finite_type_of_isJacobsonRing F (W.CoordinateRing ⧸ 𝔪)
  have he : Function.Bijective (algebraMap F (W.CoordinateRing ⧸ 𝔪)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral

  obtain ⟨x, hx⟩ := he.2 (Ideal.Quotient.mk 𝔪 (mk W (Polynomial.C Polynomial.X)))
  obtain ⟨y, hy⟩ := he.2 (Ideal.Quotient.mk 𝔪 (mk W Y))

  have hconst : ∀ a : F, Ideal.Quotient.mk 𝔪 ((mk W) (Polynomial.C (Polynomial.C a)))
      = algebraMap F (W.CoordinateRing ⧸ 𝔪) a := by
    intro a
    have h1 : (mk W) (Polynomial.C (Polynomial.C a)) = algebraMap F W.CoordinateRing a := by
      rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply,
        Algebra.algebraMap_self_apply]
      rfl
    rw [h1, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have key : ((Ideal.Quotient.mk 𝔪).comp
        (mk W : Polynomial (Polynomial F) →+* W.CoordinateRing)) =
      (algebraMap F (W.CoordinateRing ⧸ 𝔪)).comp
        ((Polynomial.evalRingHom x).comp (Polynomial.evalRingHom (Polynomial.C y))) := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
    ·
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      exact hconst a
    ·
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.eval_C]
      exact hx.symm
    ·
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.eval_C]
      exact hy.symm

  have heval : W.Equation x y := by
    have h0 := DFunLike.congr_fun key W.polynomial
    simp only [RingHom.comp_apply, AdjoinRoot.mk_self, _root_.map_zero,
      Polynomial.coe_evalRingHom] at h0
    exact (map_eq_zero_iff (algebraMap F (W.CoordinateRing ⧸ 𝔪)) he.1).mp h0.symm

  have hXmem : XClass W x ∈ 𝔪 := by
    have h2 : ((Ideal.Quotient.mk 𝔪).comp (mk W))
        (Polynomial.C (Polynomial.X - Polynomial.C x)) = 0 := by
      rw [key]
      simp
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact h2
  have hYmem : YClass W (Polynomial.C y) ∈ 𝔪 := by
    have h2 : ((Ideal.Quotient.mk 𝔪).comp (mk W))
        (Y - Polynomial.C (Polynomial.C y)) = 0 := by
      rw [key]
      simp
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact h2
  refine ⟨x, y, heval, ?_⟩

  have hXY_le : XYIdeal W x (Polynomial.C y) ≤ 𝔪 := by
    rw [XYIdeal, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hXmem
    · exact hYmem
  have hXY_max : (XYIdeal W x (Polynomial.C y)).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _
      ((quotientXYIdealEquiv (W' := W) (x := x) (y := Polynomial.C y)
        heval).toMulEquiv.isField (Field.toIsField F))
  exact hXY_max.eq_of_le h𝔪.ne_top hXY_le

end CoordinateRing

variable {R : Type*} (K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem isUnit_coeIdeal_of_forall_isMaximal [IsNoetherianRing R]
    (hmax : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 𝔪 ≠ ⊥ → IsUnit (𝔪 : FractionalIdeal R⁰ K))
    (I : Ideal R) : I ≠ ⊥ → IsUnit (I : FractionalIdeal R⁰ K) := by
  refine IsNoetherian.induction
    (P := fun I : Ideal R => I ≠ ⊥ → IsUnit (I : FractionalIdeal R⁰ K)) (fun I ih hI => ?_) I

  rcases eq_or_ne I ⊤ with rfl | hItop
  · rw [FractionalIdeal.coeIdeal_top]
    exact isUnit_one

  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hItop
  have h𝔪0 : 𝔪 ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hI𝔪))
  have h𝔪unit : IsUnit (𝔪 : FractionalIdeal R⁰ K) := hmax 𝔪 h𝔪 h𝔪0
  have h𝔪inv : (𝔪 : FractionalIdeal R⁰ K) * (𝔪 : FractionalIdeal R⁰ K)⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr h𝔪unit

  have hle : (I : FractionalIdeal R⁰ K) * (𝔪 : FractionalIdeal R⁰ K)⁻¹ ≤ 1 := by
    calc (I : FractionalIdeal R⁰ K) * (𝔪 : FractionalIdeal R⁰ K)⁻¹
        ≤ (𝔪 : FractionalIdeal R⁰ K) * (𝔪 : FractionalIdeal R⁰ K)⁻¹ := by gcongr
      _ = 1 := h𝔪inv
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle

  have hJ𝔪 : J * 𝔪 = I := by
    rw [← FractionalIdeal.coeIdeal_inj (K := K), FractionalIdeal.coeIdeal_mul, hJ, mul_assoc,
      mul_comm (𝔪 : FractionalIdeal R⁰ K)⁻¹, h𝔪inv, mul_one]
  have hIJ : I ≤ J := hJ𝔪 ▸ Ideal.mul_le_left
  have hJ0 : J ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hIJ))

  have hne : I ≠ J := by
    rintro rfl
    have hsmul : I ≤ 𝔪 • I := by
      rw [Ideal.smul_eq_mul, mul_comm]
      exact le_of_eq hJ𝔪.symm
    obtain ⟨r, hr𝔪, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 I
      (IsNoetherian.noetherian I) hsmul
    obtain ⟨n, hnI, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hr0 : r = 0 := by
      have hrn := hr n hnI
      rw [smul_eq_mul] at hrn
      exact (mul_eq_zero.mp hrn).resolve_right hn0
    exact h𝔪.ne_top (𝔪.eq_top_of_isUnit_mem (by simpa [hr0] using hr𝔪) isUnit_one.neg)

  have hJunit : IsUnit (J : FractionalIdeal R⁰ K) := ih J (lt_of_le_of_ne hIJ hne) hJ0
  rw [← hJ𝔪, FractionalIdeal.coeIdeal_mul]
  exact hJunit.mul h𝔪unit

theorem isUnit_of_forall_isMaximal [IsNoetherianRing R]
    (hmax : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 𝔪 ≠ ⊥ → IsUnit (𝔪 : FractionalIdeal R⁰ K))
    (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) : IsUnit I := by
  obtain ⟨a, J, ha, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have ha' : algebraMap R K a ≠ 0 := mt IsFractionRing.to_map_eq_zero_iff.mp ha
  refine IsUnit.mul ?_ (isUnit_coeIdeal_of_forall_isMaximal K hmax J ?_)
  · exact isUnit_iff_exists_inv.mpr ⟨FractionalIdeal.spanSingleton R⁰ (algebraMap R K a), by
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ ha',
        FractionalIdeal.spanSingleton_one]⟩
  · rintro rfl
    simp at hI

theorem isDedekindDomain_of_forall_isMaximal_isUnit {R : Type*} (K : Type*) [CommRing R]
    [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [IsNoetherianRing R]
    (hmax : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 𝔪 ≠ ⊥ → IsUnit (𝔪 : FractionalIdeal R⁰ K)) :
    IsDedekindDomain R :=
  (isDedekindDomain_iff_mul_inv_cancel (K := K)).mpr fun I hI =>
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr
      (isUnit_of_forall_isMaximal K hmax I hI)

namespace CoordinateRing

theorem isUnit_coeIdeal_of_isMaximal [IsAlgClosed F] (hΔ : W.Δ ≠ 0)
    {𝔪 : Ideal W.CoordinateRing} (h𝔪 : 𝔪.IsMaximal) :
    IsUnit (𝔪 : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
  obtain ⟨x, y, hxy, hXY⟩ := exists_eq_XYIdeal_of_isMaximal 𝔪 h𝔪
  rw [← hXY, ← XYIdeal'_eq ((W.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hxy)]
  exact (XYIdeal' _).isUnit

theorem isDedekindDomain_of_Δ_ne_zero [IsAlgClosed F] (hΔ : W.Δ ≠ 0) :
    IsDedekindDomain W.CoordinateRing :=
  isDedekindDomain_of_forall_isMaximal_isUnit W.FunctionField
    fun _𝔪 h𝔪 _ => isUnit_coeIdeal_of_isMaximal hΔ h𝔪

scoped instance [IsAlgClosed F] [W.IsElliptic] : IsDedekindDomain W.CoordinateRing :=
  isDedekindDomain_of_Δ_ne_zero (W.coe_Δ' ▸ W.Δ'.ne_zero)

theorem algebraMap_eq_mk_C_C (a : F) :
    algebraMap F W.CoordinateRing a = CoordinateRing.mk W (C (C a)) := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply,
    Algebra.algebraMap_self_apply]
  rfl

theorem XYIdeal_isMaximal {x y : F} (h : W.Equation x y) :
    (XYIdeal W x (C y)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((quotientXYIdealEquiv (W' := W) (x := x) (y := C y) h).toMulEquiv.isField
      (Field.toIsField F))

theorem XYIdeal_ne_bot (x : F) (y : F[X]) : XYIdeal W x y ≠ ⊥ := by
  intro hbot
  have hX : XClass W x ∈ XYIdeal W x y := Ideal.subset_span (Set.mem_insert _ _)
  rw [hbot, Ideal.mem_bot] at hX
  exact XClass_ne_zero x hX

theorem eq_of_XYIdeal_eq {x₁ y₁ x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h : XYIdeal W x₁ (C y₁) = XYIdeal W x₂ (C y₂)) : x₁ = x₂ ∧ y₁ = y₂ := by
  have hne : XYIdeal W x₂ (C y₂) ≠ ⊤ := (XYIdeal_isMaximal h₂).ne_top
  have hX₁ : XClass W x₁ ∈ XYIdeal W x₂ (C y₂) :=
    h ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hX₂ : XClass W x₂ ∈ XYIdeal W x₂ (C y₂) := Ideal.subset_span (Set.mem_insert _ _)
  have hY₁ : YClass W (C y₁) ∈ XYIdeal W x₂ (C y₂) :=
    h ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hY₂ : YClass W (C y₂) ∈ XYIdeal W x₂ (C y₂) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  constructor
  · by_contra hx
    apply hne
    have hsub : XClass W x₁ - XClass W x₂ = algebraMap F W.CoordinateRing (x₂ - x₁) := by
      rw [XClass, XClass, ← map_sub, algebraMap_eq_mk_C_C]
      congr 1
      rw [← map_sub]
      congr 1
      rw [map_sub]
      ring
    have hmem := (XYIdeal W x₂ (C y₂)).sub_mem hX₁ hX₂
    rw [hsub] at hmem
    exact Ideal.eq_top_of_isUnit_mem _ hmem
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun hxy => hx hxy.symm)).map
        (algebraMap F W.CoordinateRing))
  · by_contra hy
    apply hne
    have hsub : YClass W (C y₁) - YClass W (C y₂) = algebraMap F W.CoordinateRing (y₂ - y₁) := by
      rw [YClass, YClass, ← map_sub, algebraMap_eq_mk_C_C]
      congr 1
      simp only [map_sub]
      ring
    have hmem := (XYIdeal W x₂ (C y₂)).sub_mem hY₁ hY₂
    rw [hsub] at hmem
    exact Ideal.eq_top_of_isUnit_mem _ hmem
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun hxy => hy hxy.symm)).map
        (algebraMap F W.CoordinateRing))

def heightOneSpectrumOfEquation {x y : F} (h : W.Equation x y) :
    HeightOneSpectrum W.CoordinateRing where
  asIdeal := XYIdeal W x (C y)
  isPrime := (XYIdeal_isMaximal h).isPrime
  ne_bot := XYIdeal_ne_bot x (C y)

@[scoped simp]
theorem heightOneSpectrumOfEquation_asIdeal {x y : F} (h : W.Equation x y) :
    (heightOneSpectrumOfEquation h).asIdeal = XYIdeal W x (C y) := rfl

theorem exists_sub_algebraMap_mem {x y : F} (h : W.Equation x y) (r : W.CoordinateRing) :
    ∃ c : F, r - algebraMap F W.CoordinateRing c ∈ XYIdeal W x (C y) := by
  set e := quotientXYIdealEquiv (W' := W) (x := x) (y := C y) h
  refine ⟨e (Ideal.Quotient.mk _ r), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  apply e.injective
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
    Algebra.algebraMap_self_apply]

end CoordinateRing

open CoordinateRing

def IsFinitePlace (v : AlgebraicCurve.Place F W.FunctionField) : Prop :=
  ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ v.toValuationSubring

def IsFinitePlace.ringHom {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) :
    W.CoordinateRing →+* v.toValuationSubring where
  toFun r := ⟨algebraMap W.CoordinateRing W.FunctionField r, hv r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (_root_.map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

@[scoped simp]
theorem IsFinitePlace.coe_ringHom_apply {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) (r : W.CoordinateRing) :
    (hv.ringHom r : W.FunctionField) = algebraMap W.CoordinateRing W.FunctionField r := rfl

def IsFinitePlace.centre {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) :
    Ideal W.CoordinateRing :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).comap hv.ringHom

theorem IsFinitePlace.centre_isPrime {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) : hv.centre.IsPrime :=
  Ideal.IsPrime.comap _

theorem IsFinitePlace.inv_mem {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) {r : W.CoordinateRing} (hr : r ∉ hv.centre) :
    (algebraMap W.CoordinateRing W.FunctionField r)⁻¹ ∈ v.toValuationSubring := by
  have hunit : IsUnit (hv.ringHom r) := by
    rw [IsFinitePlace.centre, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, not_not] at hr
    exact hr
  obtain ⟨t, ht⟩ := hunit.exists_right_inv
  have ht' : algebraMap W.CoordinateRing W.FunctionField r * (t : W.FunctionField) = 1 := by
    have := congrArg (fun a : v.toValuationSubring => (a : W.FunctionField)) ht
    simp at this
    exact this
  rw [inv_eq_of_mul_eq_one_right ht']
  exact t.2

theorem IsFinitePlace.centre_ne_bot {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) : hv.centre ≠ ⊥ := by
  intro hbot
  apply v.ne_top'
  rw [eq_top_iff]
  rintro z -
  obtain ⟨r, s, hs, hz⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  have hs0 : s ∉ hv.centre := by
    rw [hbot, Ideal.mem_bot]
    exact fun h => nonZeroDivisors.ne_zero hs h
  rw [← hz, div_eq_mul_inv]
  exact mul_mem (hv r) (hv.inv_mem hs0)

variable [IsDedekindDomain W.CoordinateRing]

def placeOfEquation {x y : F} (h : W.Equation x y) :
    AlgebraicCurve.Place F W.FunctionField :=
  AlgebraicCurve.Place.ofHeightOneSpectrum (heightOneSpectrumOfEquation h)

theorem deg_placeOfEquation {x y : F} (h : W.Equation x y) : (placeOfEquation h).deg = 1 :=
  AlgebraicCurve.Place.deg_ofHeightOneSpectrum_eq_one _ (exists_sub_algebraMap_mem h)

theorem placeOfEquation_injective {x₁ y₁ x₂ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (h : placeOfEquation h₁ = placeOfEquation h₂) :
    x₁ = x₂ ∧ y₁ = y₂ :=
  eq_of_XYIdeal_eq h₂
    (congrArg HeightOneSpectrum.asIdeal (AlgebraicCurve.Place.ofHeightOneSpectrum_injective h))

theorem isFinitePlace_placeOfEquation {x y : F} (h : W.Equation x y) :
    IsFinitePlace (placeOfEquation h) := fun r =>
  (heightOneSpectrumOfEquation h).valuation_le_one r

theorem isFinitePlace_iff_exists_placeOfEquation [IsAlgClosed F]
    (v : AlgebraicCurve.Place F W.FunctionField) :
    IsFinitePlace v ↔ ∃ (x y : F) (h : W.Equation x y), v = placeOfEquation h := by
  constructor
  · intro hv

    haveI := hv.centre_isPrime
    have hmax : hv.centre.IsMaximal := Ideal.IsPrime.isMaximal hv.centre_isPrime hv.centre_ne_bot
    obtain ⟨x, y, hxy, hXY⟩ := CoordinateRing.exists_eq_XYIdeal_of_isMaximal hv.centre hmax
    refine ⟨x, y, hxy, ?_⟩

    set w : HeightOneSpectrum W.CoordinateRing := heightOneSpectrumOfEquation hxy with hw
    set A : ValuationSubring W.FunctionField :=
      HeightOneSpectrum.valuationSubringAtPrime W.FunctionField w with hA
    haveI hAded : IsDedekindDomain A := by rw [hA]; infer_instance
    have hle : A ≤ v.toValuationSubring := by
      intro z hz
      rw [hA] at hz
      obtain ⟨r, s, hs, rfl⟩ := hz
      have hs' : s ∉ hv.centre := by
        intro hmem
        rw [← hXY] at hmem
        exact hs hmem
      exact mul_mem (hv r) (hv.inv_mem hs')

    have hSP : A.ofPrime (A.idealOfLE v.toValuationSubring hle) = v.toValuationSubring :=
      ValuationSubring.ofPrime_idealOfLE A v.toValuationSubring hle
    rcases eq_or_ne (A.idealOfLE v.toValuationSubring hle) ⊥ with hP | hP
    ·
      exfalso
      apply v.ne_top'
      have h2 : A.ofPrime ⊥ ≤ A.ofPrime (A.idealOfLE v.toValuationSubring hle) :=
        ValuationSubring.ofPrime_le_of_le (h := hP.le)
      rw [ValuationSubring.ofPrime_bot] at h2
      exact top_le_iff.mp (le_trans h2 hSP.le)
    ·
      have hPmax : (A.idealOfLE v.toValuationSubring hle).IsMaximal :=
        Ideal.IsPrime.isMaximal inferInstance hP
      have hPeq : A.idealOfLE v.toValuationSubring hle = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal hPmax
      have h3 : A.ofPrime (A.idealOfLE v.toValuationSubring hle)
          = A.ofPrime (IsLocalRing.maximalIdeal A) :=
        le_antisymm (ValuationSubring.ofPrime_le_of_le (h := hPeq.ge))
          (ValuationSubring.ofPrime_le_of_le (h := hPeq.le))
      rw [ValuationSubring.ofPrime_top] at h3
      have hAv : A = v.toValuationSubring := h3.symm.trans hSP
      refine (AlgebraicCurve.Place.ext ?_).symm
      show (AlgebraicCurve.Place.ofHeightOneSpectrum w).toValuationSubring = v.toValuationSubring
      rw [AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring,
        ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hAv
  · rintro ⟨x, y, h, rfl⟩
    exact isFinitePlace_placeOfEquation h

/-! ### The `placeOfEquation` order/centre dictionary

The `placeOfEquation` ord/centre dictionary and the polynomial-at-a-point bridge
below were transcribed by the Vélu sets in delimited `Prerequisites` sections of
`Velu/Discharge.lean`, `Velu/Engine.lean` and `Velu/RestrictAlong.lean` because
the dictionary had not been ported yet. They are dictionary-level — the
`IsogenyEndDatum` and base-change homes consume them and must not import Vélu —
so the H5r refactor round moved them here. The section instances mirror the pin's
own sections: `mk_mem_XYIdeal_iff`, `algebraMap_coordinateRing_ne_zero`,
`IsFinitePlace.mem_centre_iff_ord_ne_zero` and `algebraMap_polynomial_eq_mk_C`
carry none, the `ord_placeOfEquation_*` family carries `IsDedekindDomain`, and
`ord_polyToFunctionField_*` inherits it. -/

omit [IsDedekindDomain W.CoordinateRing] in
theorem algebraMap_coordinateRing_ne_zero {r : W.CoordinateRing} (hr : r ≠ 0) :
    algebraMap W.CoordinateRing W.FunctionField r ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hr

omit [IsDedekindDomain W.CoordinateRing] in
theorem IsFinitePlace.mem_centre_iff_ord_ne_zero {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) {r : W.CoordinateRing} (hr : r ≠ 0) :
    r ∈ hv.centre ↔ v.ord (algebraMap W.CoordinateRing W.FunctionField r) ≠ 0 := by
  have hr' : algebraMap W.CoordinateRing W.FunctionField r ≠ 0 :=
    algebraMap_coordinateRing_ne_zero hr
  rw [IsFinitePlace.centre, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ne_eq, v.ord_eq_zero_iff_adicValuation_eq_one hr']
  exact not_congr (v.adicValuation_coe_eq_one_iff (hv.ringHom r)).symm

omit [IsDedekindDomain W.CoordinateRing] in
theorem algebraMap_polynomial_eq_mk_C (p : F[X]) :
    algebraMap F[X] W.CoordinateRing p = CoordinateRing.mk W (C p) :=
  rfl

omit [IsDedekindDomain W.CoordinateRing] in
theorem mk_mem_XYIdeal_iff {x y : F} (h : W.Equation x y) (P : F[X][Y]) :
    CoordinateRing.mk W P ∈ XYIdeal W x (C y) ↔ P.evalEval x y = 0 := by
  have hmap : XYIdeal W x (C y)
      = Ideal.map (CoordinateRing.mk W) (Ideal.span {C (X - C x), Y - C (C y)}) := by
    rw [Ideal.map_span, Set.image_pair]
    rfl
  rw [hmap]
  constructor
  · intro hP
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective).mp hP

    obtain ⟨c, hc⟩ := AdjoinRoot.mk_eq_mk.mp hQP
    have hQ0 : Q.evalEval x y = 0 :=
      Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mp hQ
    have hW0 : W.polynomial.evalEval x y = 0 := h
    have hPQ : P = Q - W.polynomial * c := by rw [← hc]; ring
    rw [hPQ]
    simp only [evalEval, eval_sub, eval_mul] at hQ0 hW0 ⊢
    rw [hQ0, hW0, zero_mul, sub_zero]
  · intro hP
    exact Ideal.mem_map_of_mem _
      (Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr hP)

omit [IsDedekindDomain W.CoordinateRing] in
theorem ord_placeOfEquation_ne_zero_iff [IsDedekindDomain W.CoordinateRing] {x y : F}
    (h : W.Equation x y) {r : W.CoordinateRing} (hr : r ≠ 0) :
    (placeOfEquation h).ord (algebraMap W.CoordinateRing W.FunctionField r) ≠ 0
      ↔ r ∈ XYIdeal W x (C y) := by
  rw [placeOfEquation, AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff _ hr,
    CoordinateRing.heightOneSpectrumOfEquation_asIdeal]

omit [IsDedekindDomain W.CoordinateRing] in
theorem ord_placeOfEquation_nonneg [IsDedekindDomain W.CoordinateRing] {x y : F}
    (h : W.Equation x y) (r : W.CoordinateRing) :
    0 ≤ (placeOfEquation h).ord (algebraMap W.CoordinateRing W.FunctionField r) :=
  (placeOfEquation h).ord_nonneg_of_mem (isFinitePlace_placeOfEquation h r)

omit [IsDedekindDomain W.CoordinateRing] in
theorem ord_placeOfEquation_pos_iff [IsDedekindDomain W.CoordinateRing] {x y : F}
    (h : W.Equation x y) {r : W.CoordinateRing} (hr : r ≠ 0) :
    0 < (placeOfEquation h).ord (algebraMap W.CoordinateRing W.FunctionField r)
      ↔ r ∈ XYIdeal W x (C y) := by
  rw [← ord_placeOfEquation_ne_zero_iff h hr]
  have := ord_placeOfEquation_nonneg h r
  omega

omit [IsDedekindDomain W.CoordinateRing] in
theorem centre_placeOfEquation [IsDedekindDomain W.CoordinateRing] {x y : F}
    (h : W.Equation x y) :
    (isFinitePlace_placeOfEquation h).centre = XYIdeal W x (C y) := by
  ext r
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [Submodule.zero_mem]
  rw [(isFinitePlace_placeOfEquation h).mem_centre_iff_ord_ne_zero hr,
    ord_placeOfEquation_ne_zero_iff h hr]

section IsRationalPlaceOfEquation

variable {r s : F} (hrs : W.Equation r s)

theorem isRational_placeOfEquation : (placeOfEquation hrs).IsRational :=
  (AlgebraicCurve.Place.isRational_iff_deg_eq_one _).2 (deg_placeOfEquation hrs)

end IsRationalPlaceOfEquation

omit [IsDedekindDomain W.CoordinateRing] in
theorem eq_placeOfEquation_of_le_centre [IsAlgClosed F] [IsDedekindDomain W.CoordinateRing]
    {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) {x y : F}
    (h : W.Equation x y) (hle : XYIdeal W x (C y) ≤ hv.centre) : v = placeOfEquation h := by
  obtain ⟨x', y', h', hveq⟩ := (isFinitePlace_iff_exists_placeOfEquation v).mp hv
  subst hveq
  have hc : hv.centre = XYIdeal W x' (C y') := by
    rw [Subsingleton.elim hv (isFinitePlace_placeOfEquation h')]
    exact centre_placeOfEquation h'
  rw [hc] at hle
  have heq : XYIdeal W x (C y) = XYIdeal W x' (C y') :=
    (CoordinateRing.XYIdeal_isMaximal h).eq_of_le (CoordinateRing.XYIdeal_isMaximal h').ne_top
      hle
  obtain ⟨rfl, rfl⟩ := CoordinateRing.eq_of_XYIdeal_eq h' heq
  rfl

theorem ord_polyToFunctionField_pos_iff {x y : F} (h : W.Equation x y) {p : F[X]}
    (hp : p ≠ 0) :
    0 < (placeOfEquation h).ord (polyToFunctionField W p) ↔ p.eval x = 0 := by
  rw [polyToFunctionField_apply, algebraMap_polynomial_eq_mk_C,
    ord_placeOfEquation_pos_iff h (fun hcon => polyToFunctionField_ne_zero hp
      (by rw [polyToFunctionField_apply, algebraMap_polynomial_eq_mk_C, hcon, _root_.map_zero])),
    mk_mem_XYIdeal_iff h, Polynomial.evalEval_C]

theorem ord_polyToFunctionField_eq_zero_iff {x y : F} (h : W.Equation x y) {p : F[X]}
    (hp : p ≠ 0) :
    (placeOfEquation h).ord (polyToFunctionField W p) = 0 ↔ p.eval x ≠ 0 := by
  have h1 := ord_polyToFunctionField_pos_iff h hp (y := y)
  have h2 : 0 ≤ (placeOfEquation h).ord (polyToFunctionField W p) := by
    rw [polyToFunctionField_apply]
    exact ord_placeOfEquation_nonneg h _
  constructor
  · intro h0 hcon
    have h3 := h1.mpr hcon
    omega
  · intro hne
    rcases lt_or_eq_of_le h2 with hlt | heq
    · exact absurd (h1.mp hlt) hne
    · exact heq.symm

variable (W) in

class InfinitePlace : Type _ where

  place : AlgebraicCurve.Place F W.FunctionField

  not_isFinitePlace : ¬ IsFinitePlace place

  deg_eq_one : place.deg = 1

  eq_of_not_isFinitePlace : ∀ v : AlgebraicCurve.Place F W.FunctionField,
    ¬ IsFinitePlace v → v = place

variable [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W]

omit [IsDedekindDomain W.CoordinateRing] [IsAlgClosed F] [InfinitePlace W] in
theorem isElliptic_Δ_ne_zero : W.Δ ≠ 0 := W.coe_Δ' ▸ W.Δ'.ne_zero

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
theorem natDegree_norm_smul_basis_left {p : F[X]} (hp : p ≠ 0) :
    ((Algebra.norm F[X] (p • (1 : W.CoordinateRing)
        + (0 : F[X]) • CoordinateRing.mk W Y)).natDegree : ℤ) = 2 * p.natDegree := by
  have hdeg := degree_norm_smul_basis (W' := W) p 0
  rw [Polynomial.degree_zero, show (2 : ℕ) • (⊥ : WithBot ℕ) + 3 = ⊥ by
      rw [two_nsmul]; simp, max_eq_left bot_le, Polynomial.degree_eq_natDegree hp, two_nsmul,
    ← Nat.cast_add] at hdeg
  rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  push_cast
  ring

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
theorem natDegree_norm_smul_basis_right {q : F[X]} (hq : q ≠ 0) :
    ((Algebra.norm F[X] ((0 : F[X]) • (1 : W.CoordinateRing)
        + q • CoordinateRing.mk W Y)).natDegree : ℤ) = 2 * q.natDegree + 3 := by
  have hdeg := degree_norm_smul_basis (W' := W) 0 q
  rw [Polynomial.degree_zero, show (2 : ℕ) • (⊥ : WithBot ℕ) = ⊥ by
      rw [two_nsmul]; simp, max_eq_right bot_le, Polynomial.degree_eq_natDegree hq, two_nsmul,
    ← Nat.cast_add, show ((3 : WithBot ℕ)) = ((3 : ℕ) : WithBot ℕ) from rfl,
    ← Nat.cast_add] at hdeg
  rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  push_cast
  ring

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
theorem natDegree_norm_smul_basis_max {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    ((Algebra.norm F[X] (p • (1 : W.CoordinateRing)
        + q • CoordinateRing.mk W Y)).natDegree : ℤ)
      = max (2 * (p.natDegree : ℤ)) (2 * (q.natDegree : ℤ) + 3) := by
  have hdeg := degree_norm_smul_basis (W' := W) p q
  rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq, two_nsmul,
    two_nsmul, ← Nat.cast_add, ← Nat.cast_add,
    show ((3 : WithBot ℕ)) = ((3 : ℕ) : WithBot ℕ) from rfl, ← Nat.cast_add] at hdeg
  rcases le_total (q.natDegree + q.natDegree + 3) (p.natDegree + p.natDegree) with h | h
  · rw [max_eq_left (by exact_mod_cast h)] at hdeg
    rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
    push_cast
    omega
  · rw [max_eq_right (by exact_mod_cast h)] at hdeg
    rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
    push_cast
    omega

variable (v : AlgebraicCurve.Place F W.FunctionField)

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
theorem isFinitePlace_of_mem
    (hx : polyToFunctionField W X ∈ v.toValuationSubring) : IsFinitePlace v := by

  have hpoly : ∀ p : F[X], polyToFunctionField W p ∈ v.toValuationSubring := by
    intro p
    induction p using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
        refine mul_mem ?_ (pow_mem hx n)
        rw [polyToFunctionField_C]
        exact v.algebraMap_mem' c

  set η := algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) with hηdef
  set c₁ : F[X] := C W.a₁ * X + C W.a₃ with hc₁def
  set cb : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ with hcbdef

  have hrel : η * η = polyToFunctionField W cb - polyToFunctionField W c₁ * η := by
    have h1 := smul_basis_mul_Y (W' := W) 0 1
    rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at h1
    have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) h1
    rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
    exact h2
  have hy : η ∈ v.toValuationSubring := by

    refine v.mem_of_eval_monic_eq_zero (P := Polynomial.X ^ 2
      + (Polynomial.C (polyToFunctionField W c₁) * Polynomial.X
        - Polynomial.C (polyToFunctionField W cb))) ?_ ?_ (x := η) ?_
    ·
      refine Polynomial.monic_X_pow_add (n := 2) ?_
      rw [sub_eq_add_neg, ← Polynomial.C_neg]
      refine lt_of_le_of_lt Polynomial.degree_linear_le ?_
      exact_mod_cast Nat.one_lt_two
    ·
      intro i
      rw [show (Polynomial.C (polyToFunctionField W c₁) * Polynomial.X : Polynomial _)
          = Polynomial.C (polyToFunctionField W c₁) * Polynomial.X ^ 1 by ring]
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_C]
      refine add_mem ?_ (sub_mem ?_ ?_)
      · split <;> simp [v.toValuationSubring.one_mem, v.toValuationSubring.zero_mem]
      · split
        · rw [mul_one]; exact hpoly _
        · rw [mul_zero]; exact v.toValuationSubring.zero_mem
      · split
        · exact hpoly _
        · exact v.toValuationSubring.zero_mem
    ·
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [sq]
      linear_combination hrel

  intro r
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq r
  rw [algebraMap_smul_basis]
  exact add_mem (hpoly p) (mul_mem (hpoly q) hy)

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
theorem ord_X_neg_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) :
    v.ord (polyToFunctionField W X) < 0 := by
  by_contra hcon
  push Not at hcon
  exact hv (isFinitePlace_of_mem v
    (v.mem_of_ord_nonneg (polyToFunctionField_ne_zero Polynomial.X_ne_zero) hcon))

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
theorem two_mul_ord_Y_eq_three_mul_ord_X (hv : ¬ IsFinitePlace v) :
    2 * v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
      = 3 * v.ord (polyToFunctionField W X) := by
  set η := algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) with hηdef
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have hη0 : η ≠ 0 := Y_image_ne_zero
  set c₁ : F[X] := C W.a₁ * X + C W.a₃ with hc₁def
  set cb : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ with hcbdef

  have hrel : η * η = polyToFunctionField W cb - polyToFunctionField W c₁ * η := by
    have h1 := smul_basis_mul_Y (W' := W) 0 1
    rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at h1
    have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) h1
    rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
    exact h2
  have hrelL : (η + polyToFunctionField W c₁) * η = polyToFunctionField W cb := by
    rw [add_mul]
    linear_combination hrel

  have hcbdeg : cb.natDegree = 3 := by
    rw [hcbdef, ← one_mul (X ^ 3 : F[X]), ← C_1]
    exact Polynomial.natDegree_cubic one_ne_zero
  have hcb0 : cb ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hcbdeg
    exact absurd hcbdeg (by norm_num)
  have hcbord : v.ord (polyToFunctionField W cb) = 3 * v.ord (polyToFunctionField W X) := by
    rw [v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA
      hcb0, hcbdeg]
    push_cast
    ring

  have hc₁ord : (1 : ℤ) * v.ord (polyToFunctionField W X)
      ≤ v.ord (polyToFunctionField W c₁) := by
    refine v.le_ord_ringHom_of_natDegree_le polyToFunctionField_injective polyToFunctionField_C
      hA ?_
    rw [hc₁def]
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [Polynomial.natDegree_C, max_le_iff]
    refine ⟨le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp), by omega⟩
  rw [one_mul] at hc₁ord

  have hfac0 : η + polyToFunctionField W c₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrelL
    exact polyToFunctionField_ne_zero hcb0 hrelL.symm

  have hLHS : v.ord (η + polyToFunctionField W c₁) + v.ord η
      = 3 * v.ord (polyToFunctionField W X) := by
    rw [← hcbord, ← hrelL, v.ord_mul hfac0 hη0]

  rcases eq_or_ne (polyToFunctionField W c₁) 0 with hc₁0 | hc₁0
  · rw [hc₁0, add_zero] at hLHS
    omega
  · by_cases hBc : v.ord η = v.ord (polyToFunctionField W c₁)
    ·

      exfalso
      have hmin : min (v.ord η) (v.ord (polyToFunctionField W c₁))
          ≤ v.ord (η + polyToFunctionField W c₁) := v.min_ord_le_ord_add hfac0
      rw [← hBc, min_self] at hmin
      have hBA : v.ord (polyToFunctionField W X) ≤ v.ord η := hBc ▸ hc₁ord
      omega
    · have hsum : v.ord (η + polyToFunctionField W c₁)
          = min (v.ord η) (v.ord (polyToFunctionField W c₁)) :=
        v.ord_add_eq_min hη0 hc₁0 hBc
      rcases min_cases (v.ord η) (v.ord (polyToFunctionField W c₁)) with
        ⟨hm, hle⟩ | ⟨hm, hlt⟩ <;> rw [hm] at hsum
      · rw [hsum] at hLHS
        omega
      ·

        exfalso
        rw [hsum] at hLHS
        omega

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
private theorem ne_arith {A B s t : ℤ} (hA : A < 0) (hY : 2 * B = 3 * A) :
    s * A ≠ t * A + B := by
  intro hcon
  have h4 : (2 * s - (2 * t + 3)) * A = 0 := by linear_combination 2 * hcon + hY
  rcases mul_eq_zero.mp h4 with h5 | h5
  · omega
  · omega

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
private theorem two_mul_min_arith {A B s t : ℤ} (hA : A < 0) (hY : 2 * B = 3 * A) :
    2 * min (s * A) (t * A + B) = A * max (2 * s) (2 * t + 3) := by
  rcases le_or_gt (2 * t + 3) (2 * s) with h | h
  · rw [max_eq_left h, min_eq_left (by nlinarith)]
    ring
  · rw [max_eq_right h.le, min_eq_right (by nlinarith)]
    linear_combination hY

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
theorem two_mul_ord_eq_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    {f : W.CoordinateRing} (hf : f ≠ 0) :
    2 * v.ord (algebraMap W.CoordinateRing W.FunctionField f)
      = v.ord (polyToFunctionField W X) * ((Algebra.norm F[X] f).natDegree : ℤ) := by
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have hη0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) ≠ 0 :=
    Y_image_ne_zero
  have hYord := two_mul_ord_Y_eq_three_mul_ord_X v hv
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  by_cases hq : q = 0
  ·
    subst hq
    have hp : p ≠ 0 := fun h => hf (by rw [h, zero_smul, zero_smul, add_zero])
    rw [natDegree_norm_smul_basis_left hp, algebraMap_smul_basis, _root_.map_zero, zero_mul, add_zero,
      v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA hp]
    ring
  · by_cases hp : p = 0
    ·
      subst hp
      rw [natDegree_norm_smul_basis_right hq, algebraMap_smul_basis, _root_.map_zero, zero_add,
        v.ord_mul (polyToFunctionField_ne_zero hq) hη0,
        v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA hq]
      linear_combination hYord
    ·
      rw [natDegree_norm_smul_basis_max hp hq, algebraMap_smul_basis]
      have hordp : v.ord (polyToFunctionField W p)
          = (p.natDegree : ℤ) * v.ord (polyToFunctionField W X) :=
        v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA hp
      have hordqy : v.ord (polyToFunctionField W q
            * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
          = (q.natDegree : ℤ) * v.ord (polyToFunctionField W X)
            + v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
        rw [v.ord_mul (polyToFunctionField_ne_zero hq) hη0,
          v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA
            hq]

      have hne : v.ord (polyToFunctionField W p) ≠ v.ord (polyToFunctionField W q
          * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
        rw [hordp, hordqy]
        exact ne_arith hA hYord
      have hqy0 : polyToFunctionField W q
          * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) ≠ 0 :=
        mul_ne_zero (polyToFunctionField_ne_zero hq) hη0
      rw [v.ord_add_eq_min (polyToFunctionField_ne_zero hp) hqy0 hne, hordp, hordqy]
      exact two_mul_min_arith hA hYord

omit [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] [IsDedekindDomain W.CoordinateRing] in
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

omit [W.IsElliptic] [InfinitePlace W] in
theorem exists_equation [IsAlgClosed F] (W : Affine F) (x₀ : F) :
    ∃ y₀ : F, W.Equation x₀ y₀ := by
  set P : F[X] := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x₀ + W.a₃) * Polynomial.X
    - Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hPdef
  have hPdeg : P.degree ≠ 0 := by
    have hcoeff : P.coeff 2 = 1 := by
      rw [hPdef]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
    intro hcon
    have h2 : P.coeff 2 = 0 := by
      refine Polynomial.coeff_eq_zero_of_degree_lt ?_
      rw [hcon]
      norm_num
    rw [hcoeff] at h2
    exact one_ne_zero h2
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root P hPdeg
  refine ⟨y₀, ?_⟩
  rw [equation_iff]
  have h3 : P.eval y₀ = 0 := hy₀
  rw [hPdef] at h3
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h3
  linear_combination h3

omit [IsDedekindDomain W.CoordinateRing] [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W] in
theorem isFinitePlace_smul_iff_forall_symm_mem (σ : W.FunctionField ≃ₐ[F] W.FunctionField)
    (v : AlgebraicCurve.Place F W.FunctionField) :
    IsFinitePlace (σ • v) ↔
      ∀ r : W.CoordinateRing,
        σ.symm (algebraMap W.CoordinateRing W.FunctionField r) ∈ v.toValuationSubring := by
  unfold IsFinitePlace
  exact forall_congr' fun r => AlgebraicCurve.Place.mem_smul_iff_symm_mem σ v _

omit [IsDedekindDomain W.CoordinateRing] [W.IsElliptic] [InfinitePlace W] [IsAlgClosed F] in
theorem forall_place_ord_nonneg_iff_finite_and_not_finite (g : W.FunctionField) :
    (∀ v : AlgebraicCurve.Place F W.FunctionField, 0 ≤ v.ord g)
      ↔ (∀ v : AlgebraicCurve.Place F W.FunctionField, IsFinitePlace v → 0 ≤ v.ord g)
        ∧ (∀ v : AlgebraicCurve.Place F W.FunctionField, ¬ IsFinitePlace v → 0 ≤ v.ord g) := by
  constructor
  · exact fun h => ⟨fun v _ => h v, fun v _ => h v⟩
  · rintro ⟨hfin, hinf⟩ v
    by_cases hv : IsFinitePlace v
    · exact hfin v hv
    · exact hinf v hv

end Affine

end WeierstrassCurve
