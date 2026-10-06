/-
The H5 vocabulary tail (`IsogenyEndDatum` / `IsogenyHomDatum`).

Canonical sources: the pinned FLT `aa2d8b3` `S_` files

* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub.lean`,
* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_sub.lean`,
* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add.lean`,
* `P2M/Sol/S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean`;

the statements are taken from the corresponding `Theorems/` wrappers.  SET-V4
appends the H5 vocabulary tail proper: the function-field rigidity node
`WeierstrassCurve.Affine.algHom_ext_of_forall_restrictAlong_placeOfPoint_eq` and
the kernel-to-range node
`WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred`
(the latter consumes the V3 translation headline
`exists_algEquiv_restrictAlong_placeOfPoint_eq_add`, hence the
`TranslationAlgEquiv` import below).  The one H5 vocabulary node still **not**
here is `IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq`, blocked on
unported `Theorems/` nodes outside this cone (see the module report).  Statements
are transcribed verbatim; only proof bodies are adapted to mathlib `v4.34.0`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean>
-/
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DualEndData
import FLTForHuman.WeierstrassCurve.Isogeny.NatCard
import FLTForHuman.WeierstrassCurve.Isogeny.ConditionalCurrency
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.TranslationAlgEquiv
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial Finset
open scoped Polynomial.Bivariate Classical
open WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing
open AlgebraicCurve
open IsDedekindDomain

universe u

namespace WeierstrassCurve

namespace Affine

namespace IsogenyEndDatum

theorem pointEnd_apply_eq_sub
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) (P : W.Point) :
    D.pointEnd hN P
      = (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι)
        - (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) := by
  set Q : W.Point := (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι) with hQ
  set Q₀ : W.Point :=
    (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) with hQ₀
  have hP : (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint Q :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm
  have h0 : (placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι = placeOfPoint Q₀ :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm
  have hdiv : (Pic0.pushforwardAlongDegZero D.ι D.hι (pointDivisor P) :
      AlgebraicCurve.Divisor F W.FunctionField)
        = Finsupp.single (placeOfPoint Q) 1 - Finsupp.single (placeOfPoint Q₀) 1 := by
    rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
      pushforwardAlong_single_eq D.ι D.hι, pushforwardAlong_single_eq D.ι D.hι, hP, h0]
  rw [IsogenyEndDatum.pointEnd_apply, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]

end IsogenyEndDatum

namespace IsogenyHomDatum

theorem pointHom_apply_eq_sub
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {V₀ V₁ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁]
    (φ : IsogenyHomDatum V₀ V₁) (hN : NormFormulaAlong F φ.ι φ.hfin) (P : V₀.Point) :
    φ.pointHom hN P
      = (pointEquivPlace (W := V₁)).symm ((placeOfPoint P).restrictAlong φ.ι φ.hι)
        - (pointEquivPlace (W := V₁)).symm ((placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι) := by
  set Q : V₁.Point := (pointEquivPlace (W := V₁)).symm ((placeOfPoint P).restrictAlong φ.ι φ.hι) with hQ
  set Q₀ : V₁.Point :=
    (pointEquivPlace (W := V₁)).symm ((placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι) with hQ₀
  have hP : (placeOfPoint P).restrictAlong φ.ι φ.hι = placeOfPoint Q :=
    ((pointEquivPlace (W := V₁)).apply_symm_apply _).symm
  have h0 : (placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι = placeOfPoint Q₀ :=
    ((pointEquivPlace (W := V₁)).apply_symm_apply _).symm
  have hdiv : (Pic0.pushforwardAlongDegZero φ.ι φ.hι (pointDivisor P) :
      AlgebraicCurve.Divisor F V₁.FunctionField)
        = Finsupp.single (placeOfPoint Q) 1 - Finsupp.single (placeOfPoint Q₀) 1 := by
    rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
      pushforwardAlong_single_eq φ.ι φ.hι, pushforwardAlong_single_eq φ.ι φ.hι, hP, h0]
  rw [IsogenyHomDatum.pointHom_apply, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]

end IsogenyHomDatum

namespace IsogenyEndDatum

/-- The pin's local `normFormulaAlong_of_finiteAlong_aux` helper (from the
`exists_pointEnd_eq_add` `S_` file), kept local to this module. -/
private theorem normFormulaAlong_of_finiteAlong_aux
    {F : Type u} [Field F] [CharZero F] {V W : WeierstrassCurve.Affine F}
    [HasPrincipalDivisors F W.FunctionField]
    (ι : V.FunctionField →ₐ[F] W.FunctionField) (hfin : FiniteAlong F ι) :
    NormFormulaAlong F ι hfin := by
  haveI : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite V.FunctionField W.FunctionField := hfin
    show Algebra.IsSeparable V.FunctionField W.FunctionField
    infer_instance
  exact AlgebraicCurve.normFormulaAlong ι hfin hsep

theorem exists_pointEnd_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (D₁ : IsogenyEndDatum W) (hN₁ : NormFormulaAlong F D₁.ι D₁.hfin)
    (D₂ : IsogenyEndDatum W) (hN₂ : NormFormulaAlong F D₂.ι D₂.hfin)
    (h : D₁.pointEnd hN₁ + D₂.pointEnd hN₂ ≠ 0) :
    ∃ (D₃ : IsogenyEndDatum W) (hN₃ : NormFormulaAlong F D₃.ι D₃.hfin),
      D₃.pointEnd hN₃ = D₁.pointEnd hN₁ + D₂.pointEnd hN₂ := by
  obtain ⟨D₃, hD₃⟩ :=
    IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add D₁ hN₁ D₂ hN₂ h
  haveI : HasPrincipalDivisors F W.FunctionField := hasPrincipalDivisors_functionField W
  have hN₃ : NormFormulaAlong F D₃.ι D₃.hfin := normFormulaAlong_of_finiteAlong_aux D₃.ι D₃.hfin
  refine ⟨D₃, hN₃, ?_⟩
  refine AddMonoidHom.ext fun P => ?_
  show D₃.pointEnd hN₃ P = D₁.pointEnd hN₁ P + D₂.pointEnd hN₂ P
  rw [IsogenyEndDatum.pointEnd_apply_eq_sub D₃ hN₃, IsogenyEndDatum.pointEnd_apply_eq_sub D₁ hN₁,
    IsogenyEndDatum.pointEnd_apply_eq_sub D₂ hN₂, hD₃ P, hD₃ 0,
    pointEquivPlace_symm_placeOfPoint, pointEquivPlace_symm_placeOfPoint]
  abel

end IsogenyEndDatum

end Affine

end WeierstrassCurve

namespace WeierstrassCurve

namespace Affine

/-- The plain (no `SeparableAlong`/`HasPrincipalDivisors` binder) sibling of the
landed `_of_separableAlong` headline; the pin `S_` file derives both from
`[IsAlgClosed F] [CharZero F]`. -/
theorem natCard_ker_pointMapOfPushforward_eq_finrankAlong
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (E E' : WeierstrassCurve.Affine F) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[F] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin) :
    Nat.card (pointMapOfPushforward ι hι hfin hN).ker = finrankAlong F ι := by
  haveI : HasPrincipalDivisors F E.FunctionField := hasPrincipalDivisors_functionField E
  haveI : HasPrincipalDivisors F E'.FunctionField := hasPrincipalDivisors_functionField E'
  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite E'.FunctionField E.FunctionField := hfin
    haveI : CharZero E'.FunctionField :=
      charZero_of_injective_algebraMap (algebraMap F E'.FunctionField).injective
    show Algebra.IsSeparable E'.FunctionField E.FunctionField
    infer_instance
  exact WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong
    E E' ι hι hfin hsep hN

end Affine

end WeierstrassCurve
namespace WeierstrassCurve

namespace KwNo3aHbadRiqsucrA1a

open AlgebraicCurve

section RouteEta

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem no3ahbad_riqsucr_a1a_ord_pos_of_restrictAlong_ord_pos
    (φ : F' →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (v : Place K F)
    (f : F') (c : K) (hord : (v.restrictAlong φ hφ).ord (f - algebraMap K F' c) > 0) :
    v.ord (φ f - algebraMap K F c) > 0 := by
  have hrw : φ f - algebraMap K F c = φ (f - algebraMap K F' c) := by
    rw [map_sub, AlgHom.commutes]
  rw [hrw, Place.ord_restrictAlong φ hφ v (f - algebraMap K F' c)]
  refine mul_pos ?_ hord
  exact_mod_cast Place.ramificationIndexAlong_pos φ hφ v

end RouteEta

section FiniteZeros

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {V : Affine F} [IsDedekindDomain V.CoordinateRing] [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]

private theorem no3ahbad_riqsucr_a1a_finite_ord_ne_zero (h : V.FunctionField) (hne : h ≠ 0) :
    {P : V.Point | (placeOfPoint P).ord h ≠ 0}.Finite := by
  haveI : HasPrincipalDivisors F V.FunctionField := hasPrincipalDivisors_functionField V
  have hfin : {v : Place F V.FunctionField | v.ord h ≠ 0}.Finite :=
    finite_setOf_ord_ne_zero_of_hasPrincipalDivisors (K := F) (F := V.FunctionField) hne
  refine Set.Finite.of_finite_image (f := placeOfPoint)
    (hfin.subset ?_) (Set.injOn_of_injective placeOfPoint_injective)
  rintro v ⟨P, hP, rfl⟩; exact hP

end FiniteZeros

section Ext

variable {K F' : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Field F'] [Algebra K F']
variable {V : Affine K} [DecidableEq K] [IsDedekindDomain V.CoordinateRing] [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]

private theorem no3ahbad_riqsucr_a1a_exists_residue (w : Place K F')
    (hsurj : Function.Surjective (algebraMap K w.ResidueField))
    (f : F') (hf : w.ord f ≥ 0) :
    ∃ c : K, f = algebraMap K F' c ∨ w.ord (f - algebraMap K F' c) > 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, Or.inl (algebraMap K F').map_zero.symm⟩
  refine ⟨w.evalAt f, ?_⟩
  rcases eq_or_ne (f - algebraMap K F' (w.evalAt f)) 0 with heq | hne
  · exact Or.inl (sub_eq_zero.mp heq)
  · exact Or.inr (w.ord_sub_evalAt_pos hsurj (w.mem_of_ord_nonneg hf0 hf) hne)

private theorem no3ahbad_riqsucr_a1a_ord_sub_pos_of_pos {L : Type*} [Field L] [Algebra K L]
    (v : Place K L) {a b : L} (ha : v.ord a > 0) (hb : v.ord b > 0) (hab : a ≠ b) :
    v.ord (a - b) > 0 := by
  have ha0 : a ≠ 0 := fun h => absurd (h ▸ ha) (by simp [v.ord_zero])
  have hb0 : b ≠ 0 := fun h => absurd (h ▸ hb) (by simp [v.ord_zero])
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hval : v.adicValuation (a - b) ≤ max (v.adicValuation a) (v.adicValuation b) := by
    have h := v.adicValuation.map_add a (-b)
    rwa [← sub_eq_add_neg, Valuation.map_neg] at h
  rcases max_cases (v.adicValuation a) (v.adicValuation b) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
    rw [hmax] at hval
  · have := (WithZero.log_le_log (v.adicValuation_ne_zero hne)
      (v.adicValuation_ne_zero ha0)).mpr hval
    simp only [Place.ord] at ha ⊢; omega
  · have := (WithZero.log_le_log (v.adicValuation_ne_zero hne)
      (v.adicValuation_ne_zero hb0)).mpr hval
    simp only [Place.ord] at hb ⊢; omega

private theorem no3ahbad_riqsucr_a1a_algHom_ext_of_restrictAlong_placeOfPoint_eq
    (hVinf : Infinite V.Point) (hrat : ∀ w : Place K F', w.IsRational)
    (φ₁ φ₂ : F' →ₐ[K] V.FunctionField)
    (hφ₁ : φ₁.toRingHom.IsIntegral) (hφ₂ : φ₂.toRingHom.IsIntegral)
    (hres : ∀ P : V.Point,
      (placeOfPoint P).restrictAlong φ₁ hφ₁ = (placeOfPoint P).restrictAlong φ₂ hφ₂) :
    φ₁ = φ₂ := by
  ext f
  by_contra hne
  have hne' : φ₁ f - φ₂ f ≠ 0 := sub_ne_zero.mpr hne
  have hfin := no3ahbad_riqsucr_a1a_finite_ord_ne_zero (V := V) (φ₁ f - φ₂ f) hne'
  have hpoles : {P : V.Point |
      ((placeOfPoint P).restrictAlong φ₁ hφ₁).ord f < 0}.Finite := by
    rcases eq_or_ne (φ₁ f) 0 with h0 | h0
    ·
      exact absurd (by
        have hf0 : f = 0 := φ₁.injective (by simp [h0])
        simp [hf0]) hne'
    · refine (no3ahbad_riqsucr_a1a_finite_ord_ne_zero (V := V) (φ₁ f) h0).subset ?_
      intro P hP
      simp only [Set.mem_ofPred_eq] at hP ⊢
      rw [Place.ord_restrictAlong φ₁ hφ₁ (placeOfPoint P) f]
      exact ne_of_lt (mul_neg_of_pos_of_neg (by
        unfold Place.ramificationIndexAlong
        letI := algebraAlong φ₁; haveI := isScalarTower_along φ₁
        haveI := isIntegral_along φ₁ hφ₁
        exact_mod_cast (placeOfPoint P).ramificationIndex_pos (F := F')) hP)
  have hcofin : {P : V.Point | (placeOfPoint P).ord (φ₁ f - φ₂ f) > 0}ᶜ ⊆
      {P | ((placeOfPoint P).restrictAlong φ₁ hφ₁).ord f < 0} := by
    intro P hP
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hP ⊢
    by_contra hge
    simp only [not_lt] at hge
    obtain ⟨c, hc⟩ := no3ahbad_riqsucr_a1a_exists_residue
      ((placeOfPoint P).restrictAlong φ₁ hφ₁) (hrat _) f hge
    rcases hc with heq | hc
    ·
      exact absurd (heq ▸ (φ₁.commutes c).trans (φ₂.commutes c).symm) hne
    have h1 := no3ahbad_riqsucr_a1a_ord_pos_of_restrictAlong_ord_pos φ₁ hφ₁
      (placeOfPoint P) f c hc
    have h2 := no3ahbad_riqsucr_a1a_ord_pos_of_restrictAlong_ord_pos φ₂ hφ₂
      (placeOfPoint P) f c (hres P ▸ hc)
    have h12 := no3ahbad_riqsucr_a1a_ord_sub_pos_of_pos (placeOfPoint P) h1 h2
      (fun heq => hne (sub_left_inj.mp heq))
    simp only [sub_sub_sub_cancel_right] at h12
    exact absurd h12 (not_lt.mpr hP)
  have hcof_fin : {P : V.Point | (placeOfPoint P).ord (φ₁ f - φ₂ f) > 0}ᶜ.Finite :=
    hpoles.subset hcofin
  have hset_fin : (Set.univ : Set V.Point).Finite := by
    rw [← Set.compl_union_self {P | (placeOfPoint P).ord (φ₁ f - φ₂ f) > 0}]
    exact hcof_fin.union (hfin.subset (fun P hP => ne_of_gt hP))
  exact hVinf.not_finite (Set.finite_univ_iff.mp hset_fin)

end Ext

end KwNo3aHbadRiqsucrA1a

namespace Affine

/-- Prerequisite headline (statement from the wrapper). -/
theorem algHom_ext_of_forall_restrictAlong_placeOfPoint_eq
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    {V : WeierstrassCurve.Affine K} [V.IsElliptic]
    [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]
    {F' : Type*} [Field F'] [Algebra K F'] (hrat : ∀ w : AlgebraicCurve.Place K F', w.IsRational)
    (φ₁ φ₂ : F' →ₐ[K] V.FunctionField)
    (hφ₁ : φ₁.toRingHom.IsIntegral) (hφ₂ : φ₂.toRingHom.IsIntegral)
    (hres : ∀ P : V.Point,
      (placeOfPoint P).restrictAlong φ₁ hφ₁ = (placeOfPoint P).restrictAlong φ₂ hφ₂) :
    φ₁ = φ₂ :=
  WeierstrassCurve.KwNo3aHbadRiqsucrA1a.no3ahbad_riqsucr_a1a_algHom_ext_of_restrictAlong_placeOfPoint_eq
    (WeierstrassCurve.point_infinite (W := V)) hrat φ₁ φ₂ hφ₁ hφ₂ hres


namespace IsogenyHomDatumTail

section Generic

variable {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A] [Algebra K B]

private theorem exists_factor_of_range_le {C : Type*} [Field C] [Algebra K C]
    (ι : A →ₐ[K] B) (μ : C →ₐ[K] B) (hrange : μ.range ≤ ι.range) :
    ∃ ξ : C →ₐ[K] A, ι.comp ξ = μ := by
  have hιinj : Function.Injective ι := RingHom.injective ι.toRingHom
  let e : A ≃ₐ[K] ι.range := AlgEquiv.ofInjective ι hιinj
  refine ⟨e.symm.toAlgHom.comp ((Subalgebra.inclusion hrange).comp μ.rangeRestrict), ?_⟩
  ext b
  have key : ∀ x : ι.range, ι (e.symm x) = ↑x := fun x => by
    conv_rhs => rw [← e.apply_symm_apply x]
    rfl
  simp only [AlgHom.comp_apply]
  exact key _

private theorem finiteAlong_factor {C : Type*} [Field C] [Algebra K C]
    (ι : A →ₐ[K] B) (ξ : C →ₐ[K] A)
    (hfin : FiniteAlong K (ι.comp ξ)) : FiniteAlong K ξ := by
  let mCA : Module C A := (algebraAlong ξ).toModule
  let mCB : Module C B := (algebraAlong (ι.comp ξ)).toModule
  let ιLin : @LinearMap C C _ _ (RingHom.id C) A B _ _ mCA mCB :=
    { toFun := ι
      map_add' := map_add ι
      map_smul' := fun r a => by
        show ι (ξ r * a) = ι (ξ r) * ι a
        exact map_mul ι (ξ r) a }
  have hCB : @FiniteDimensional C B _ _ mCB := hfin
  exact @FiniteDimensional.of_injective C A _ _ mCA B _ mCB ιLin
    (RingHom.injective ι.toRingHom) hCB

private theorem isIntegral_of_finiteAlong {C : Type*} [Field C] [Algebra K C] (ξ : C →ₐ[K] A)
    (hfin : FiniteAlong K ξ) : ξ.toRingHom.IsIntegral := by
  letI := algebraAlong ξ
  haveI : Module.Finite C A := hfin
  have h : Algebra.IsIntegral C A := Algebra.IsIntegral.of_finite C A
  intro a
  exact h.isIntegral a

private theorem finrankAlong_eq_finrank_fieldRange (φ : A →ₐ[K] B) :
    finrankAlong K φ = Module.finrank φ.fieldRange B := by
  show (letI := algebraAlong φ; Module.finrank A B) = Module.finrank φ.fieldRange B
  letI := algebraAlong φ
  exact Algebra.finrank_eq_of_equiv_equiv
    (AlgEquiv.ofInjectiveField φ).toRingEquiv (RingEquiv.refl B) (by ext x; rfl)

private theorem finrank_toSubfield_eq {L : Type*} [Field L] [Algebra K L] (E : IntermediateField K L) :
    Module.finrank E.toSubfield L = Module.finrank E L :=
  Algebra.finrank_eq_of_equiv_equiv
    (⟨⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩,
      fun _ _ => rfl, fun _ _ => rfl⟩ : E.toSubfield ≃+* E)
    (RingEquiv.refl L) (by ext x; rfl)

end Generic

section HMap

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {U V : WeierstrassCurve.Affine F}
variable [U.IsElliptic] [GenusOnePlaceGate U] [AbelTheorem U]
variable [V.IsElliptic] [GenusOnePlaceGate V] [AbelTheorem V]

private def hmap (η : IsogenyHomDatum U V) (P : U.Point) : V.Point :=
  (pointEquivPlace (W := V)).symm ((placeOfPoint P).restrictAlong η.ι η.hι)

private theorem hmap_seam (η : IsogenyHomDatum U V) (P : U.Point) :
    (placeOfPoint P).restrictAlong η.ι η.hι = placeOfPoint (hmap η P) :=
  ((pointEquivPlace (W := V)).apply_symm_apply _).symm

private theorem pointHom_eq_hmap_sub (η : IsogenyHomDatum U V) (hN : NormFormulaAlong F η.ι η.hfin)
    (P : U.Point) :
    η.pointHom hN P = hmap η P - hmap η 0 :=
  IsogenyHomDatum.pointHom_apply_eq_sub η hN P

private theorem hmap_add_of_ker (η : IsogenyHomDatum U V) (hN : NormFormulaAlong F η.ι η.hfin)
    (P T : U.Point) (hT : η.pointHom hN T = 0) : hmap η (P + T) = hmap η P := by
  have h1 := pointHom_eq_hmap_sub η hN (P + T)
  have h2 := pointHom_eq_hmap_sub η hN P
  rw [map_add, hT, add_zero, h2] at h1
  exact (sub_left_inj.mp h1).symm

private theorem placeOfPoint_inj {W : WeierstrassCurve.Affine F} [GenusOnePlaceGate W] {P Q : W.Point}
    (h : placeOfPoint P = placeOfPoint Q) : P = Q :=
  (pointEquivPlace (W := W)).injective h

end HMap

section Main

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {V₀ V₁ V₂ : WeierstrassCurve.Affine F}
variable [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
variable [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁]
variable [V₂.IsElliptic] [GenusOnePlaceGate V₂] [AbelTheorem V₂]
variable [GenusOnePlaceGate.IsCentred V₀]

private theorem hrat_of_gate {V : WeierstrassCurve.Affine F} [V.IsElliptic] [GenusOnePlaceGate V] :
    ∀ w : Place F V.FunctionField, w.IsRational :=
  fun w => AlgebraicCurve.Place.isRational_of_deg_eq_one w (GenusOnePlaceGate.deg_eq_one w)

private def τ (R : V₀.Point) : V₀.FunctionField ≃ₐ[F] V₀.FunctionField :=
  (exists_algEquiv_restrictAlong_placeOfPoint_eq_add (W := V₀) R).choose

private theorem τ_isIntegral (R : V₀.Point) : (τ R).toAlgHom.toRingHom.IsIntegral :=
  (exists_algEquiv_restrictAlong_placeOfPoint_eq_add (W := V₀) R).choose_spec.choose

private theorem τ_seam (R Q : V₀.Point) :
    (placeOfPoint Q).restrictAlong (τ R).toAlgHom (τ_isIntegral R) = placeOfPoint (Q + R) :=
  (exists_algEquiv_restrictAlong_placeOfPoint_eq_add (W := V₀) R).choose_spec.choose_spec Q

private theorem algEquiv_isIntegral (e : V₀.FunctionField ≃ₐ[F] V₀.FunctionField) :
    e.toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ e.surjective

private theorem restrictAlong_congr_proof {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (h h' : φ.toRingHom.IsIntegral) (w : Place K B) :
    w.restrictAlong φ h = w.restrictAlong φ h' := rfl

private theorem τ_add (S T : V₀.Point) : τ (S + T) = (τ S) * (τ T) := by
  apply AlgEquiv.ext
  intro f
  have hint : ((τ S).toAlgHom.comp (τ T).toAlgHom).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ (τ_isIntegral T) (τ_isIntegral S)
  have key : (τ (S + T)).toAlgHom = (τ S).toAlgHom.comp (τ T).toAlgHom := by
    refine algHom_ext_of_forall_restrictAlong_placeOfPoint_eq (V := V₀) hrat_of_gate
      (τ (S + T)).toAlgHom ((τ S).toAlgHom.comp (τ T).toAlgHom) (τ_isIntegral (S + T))
      hint (fun P => ?_)
    rw [τ_seam, ← Place.restrictAlong_restrictAlong (τ T).toAlgHom (τ S).toAlgHom (τ_isIntegral T)
      (τ_isIntegral S) hint (placeOfPoint P), τ_seam, τ_seam, add_assoc]
  exact DFunLike.congr_fun key f

private theorem τ_zero : τ (0 : V₀.Point) = 1 := by
  apply AlgEquiv.ext
  intro f
  have key : (τ (0 : V₀.Point)).toAlgHom =
      (1 : V₀.FunctionField ≃ₐ[F] V₀.FunctionField).toAlgHom := by
    refine algHom_ext_of_forall_restrictAlong_placeOfPoint_eq (V := V₀) hrat_of_gate
      _ _ (τ_isIntegral 0) (algEquiv_isIntegral _) (fun P => ?_)
    rw [τ_seam, add_zero]
    exact (IsogenyEndDatum.restrictAlong_algHomId V₀ (placeOfPoint P)).symm
  exact DFunLike.congr_fun key f

private theorem τ_eq_one_imp {T : V₀.Point} (h : τ T = 1) : T = 0 := by
  have h1 := τ_seam T 0
  have h2 : (placeOfPoint (0 : V₀.Point)).restrictAlong (τ T).toAlgHom (τ_isIntegral T)
      = placeOfPoint (0 : V₀.Point) := by
    have : (τ T).toAlgHom = AlgHom.id F V₀.FunctionField := by rw [h]; rfl
    simp only [this]
    exact IsogenyEndDatum.restrictAlong_algHomId V₀ _
  rw [h2, zero_add] at h1
  exact ((placeOfPoint_inj (W := V₀)) h1).symm

variable (φ : IsogenyHomDatum V₀ V₁) (hNφ : NormFormulaAlong F φ.ι φ.hfin)

private def kerActHom :
    Multiplicative (φ.pointHom hNφ).ker →* (V₀.FunctionField ≃ₐ[F] V₀.FunctionField) where
  toFun T := τ ((Multiplicative.toAdd T : (φ.pointHom hNφ).ker) : V₀.Point)
  map_one' := by
    show τ ((Multiplicative.toAdd 1 : (φ.pointHom hNφ).ker) : V₀.Point) = 1
    rw [toAdd_one]; exact τ_zero
  map_mul' S T := by
    show τ (((Multiplicative.toAdd (S * T)) : (φ.pointHom hNφ).ker) : V₀.Point) = _
    rw [toAdd_mul, AddSubgroup.coe_add, τ_add]

private theorem kerActHom_apply (T : (φ.pointHom hNφ).ker) :
    kerActHom φ hNφ (Multiplicative.ofAdd T) = τ (T : V₀.Point) := rfl

private theorem kerActHom_injective : Function.Injective (kerActHom φ hNφ) := by
  rw [injective_iff_map_eq_one]
  intro T hT
  have h0 : ((Multiplicative.toAdd T : (φ.pointHom hNφ).ker) : V₀.Point) = 0 := τ_eq_one_imp hT
  have : Multiplicative.toAdd T = (0 : (φ.pointHom hNφ).ker) := Subtype.ext h0
  exact Multiplicative.toAdd.injective this

private instance instMulSemiringActionKer :
    MulSemiringAction (Multiplicative (φ.pointHom hNφ).ker) V₀.FunctionField :=
  MulSemiringAction.compHom _ (kerActHom φ hNφ)

private theorem ker_smul_def (T : Multiplicative (φ.pointHom hNφ).ker) (f : V₀.FunctionField) :
    T • f = kerActHom φ hNφ T f := rfl

private instance instFaithfulKer : FaithfulSMul (Multiplicative (φ.pointHom hNφ).ker) V₀.FunctionField where
  eq_of_smul_eq_smul h := kerActHom_injective φ hNφ (AlgEquiv.ext h)

private theorem mem_fixedPoints_iff (f : V₀.FunctionField) :
    f ∈ FixedPoints.subfield (Multiplicative (φ.pointHom hNφ).ker) V₀.FunctionField ↔
      ∀ T : V₀.Point, φ.pointHom hNφ T = 0 → τ T f = f := by
  constructor
  · intro hf T hT
    exact hf (Multiplicative.ofAdd (⟨T, hT⟩ : (φ.pointHom hNφ).ker))
  · intro hf g
    exact hf ((Multiplicative.toAdd g : (φ.pointHom hNφ).ker) : V₀.Point) (Multiplicative.toAdd g).2

private theorem τ_comp_eq_of_ker {V : WeierstrassCurve.Affine F} [V.IsElliptic] [GenusOnePlaceGate V] [AbelTheorem V]
    (η : IsogenyHomDatum V₀ V) (hN : NormFormulaAlong F η.ι η.hfin) (T : V₀.Point)
    (hT : η.pointHom hN T = 0) : (τ T).toAlgHom.comp η.ι = η.ι := by
  have hint : ((τ T).toAlgHom.comp η.ι).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ η.hι (τ_isIntegral T)
  refine algHom_ext_of_forall_restrictAlong_placeOfPoint_eq (V := V₀) hrat_of_gate
    _ _ hint η.hι (fun P => ?_)
  rw [← Place.restrictAlong_restrictAlong η.ι (τ T).toAlgHom η.hι (τ_isIntegral T) hint,
    τ_seam, hmap_seam, hmap_seam, hmap_add_of_ker η hN P T hT]

private theorem fieldRange_le_fixedPoints :
    φ.ι.fieldRange.toSubfield
      ≤ FixedPoints.subfield (Multiplicative (φ.pointHom hNφ).ker) V₀.FunctionField := by
  intro f hf
  rw [mem_fixedPoints_iff]
  intro T hT
  obtain ⟨g, rfl⟩ : ∃ g, φ.ι g = f := by
    simpa [AlgHom.fieldRange, IntermediateField.mem_toSubfield] using hf
  exact DFunLike.congr_fun (τ_comp_eq_of_ker φ hNφ T hT) g

private theorem natCard_ker : Nat.card (φ.pointHom hNφ).ker = finrankAlong F φ.ι :=
  natCard_ker_pointMapOfPushforward_eq_finrankAlong V₀ V₁ φ.ι φ.hι φ.hfin hNφ

private theorem finrankAlong_pos : 0 < finrankAlong F φ.ι := by
  letI := algebraAlong φ.ι
  haveI : Module.Finite V₁.FunctionField V₀.FunctionField := φ.hfin
  exact Module.finrank_pos

private instance instFiniteKer : Finite (φ.pointHom hNφ).ker :=
  Nat.finite_of_card_ne_zero (by rw [natCard_ker]; exact (finrankAlong_pos φ).ne')

private instance instFintypeKer : Fintype (φ.pointHom hNφ).ker := Fintype.ofFinite _

private instance instFintypeKerMul : Fintype (Multiplicative (φ.pointHom hNφ).ker) := Fintype.ofFinite _

private theorem fieldRange_eq_fixedPoints :
    φ.ι.fieldRange.toSubfield
      = FixedPoints.subfield (Multiplicative (φ.pointHom hNφ).ker) V₀.FunctionField := by
  set A : Subfield V₀.FunctionField := φ.ι.fieldRange.toSubfield with hA
  set B : Subfield V₀.FunctionField :=
    FixedPoints.subfield (Multiplicative (φ.pointHom hNφ).ker) V₀.FunctionField with hB
  have hAB : A ≤ B := fieldRange_le_fixedPoints φ hNφ
  have hcard : Fintype.card (Multiplicative (φ.pointHom hNφ).ker) = finrankAlong F φ.ι := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (φ.pointHom hNφ).ker ≃ _),
      natCard_ker]
  have hfA : Module.finrank A V₀.FunctionField = finrankAlong F φ.ι := by
    rw [hA, finrank_toSubfield_eq, ← finrankAlong_eq_finrank_fieldRange]
  have hfB : Module.finrank B V₀.FunctionField = finrankAlong F φ.ι := by
    rw [hB, FixedPoints.finrank_eq_card (Multiplicative (φ.pointHom hNφ).ker) V₀.FunctionField, hcard]
  have htower := Subfield.relfinrank_mul_finrank_top hAB
  rw [hfA, hfB] at htower
  have hpos := finrankAlong_pos φ
  have hrel : Subfield.relfinrank A B = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (htower.trans (one_mul _).symm)
  exact le_antisymm hAB (Subfield.relfinrank_eq_one_iff.mp hrel)

variable (ψ : IsogenyHomDatum V₀ V₂) (hNψ : NormFormulaAlong F ψ.ι ψ.hfin)
variable (hker : ∀ P : V₀.Point, φ.pointHom hNφ P = 0 → ψ.pointHom hNψ P = 0)

include hker in
private theorem psi_range_le : ψ.ι.range ≤ φ.ι.range := by
  intro f hf
  obtain ⟨g, rfl⟩ := (AlgHom.mem_range ψ.ι).mp hf
  have hfix : ψ.ι g ∈
      FixedPoints.subfield (Multiplicative (φ.pointHom hNφ).ker) V₀.FunctionField := by
    rw [mem_fixedPoints_iff]
    intro T hT
    exact DFunLike.congr_fun (τ_comp_eq_of_ker ψ hNψ T (hker T hT)) g
  rw [← fieldRange_eq_fixedPoints φ hNφ] at hfix

  obtain ⟨g', hg'⟩ : ∃ g', φ.ι g' = ψ.ι g := by
    simpa [AlgHom.fieldRange, IntermediateField.mem_toSubfield] using hfix
  exact (AlgHom.mem_range φ.ι).mpr ⟨g', hg'⟩

end Main

end IsogenyHomDatumTail

namespace IsogenyHomDatum

open IsogenyHomDatumTail

/-- The kernel-to-range theorem (statement from the wrapper). -/
theorem exists_pointHom_comp_eq_of_ker_le_of_isCentred
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {V₀ V₁ V₂ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁] [V₂.IsElliptic] [GenusOnePlaceGate V₂] [AbelTheorem V₂]
    [GenusOnePlaceGate.IsCentred V₀]
    (φ : IsogenyHomDatum V₀ V₁) (hNφ : NormFormulaAlong F φ.ι φ.hfin)
    (ψ : IsogenyHomDatum V₀ V₂) (hNψ : NormFormulaAlong F ψ.ι ψ.hfin)
    (hker : ∀ P : V₀.Point, φ.pointHom hNφ P = 0 → ψ.pointHom hNψ P = 0) :
    ∃ (χ : IsogenyHomDatum V₁ V₂) (hNχ : NormFormulaAlong F χ.ι χ.hfin),
      ∀ P : V₀.Point, χ.pointHom hNχ (φ.pointHom hNφ P) = ψ.pointHom hNψ P := by
  obtain ⟨ξ, hξ⟩ := exists_factor_of_range_le φ.ι ψ.ι (psi_range_le φ hNφ ψ hNψ hker)
  have hξfin : FiniteAlong F ξ := finiteAlong_factor φ.ι ξ (by rw [hξ]; exact ψ.hfin)
  have hξint : ξ.toRingHom.IsIntegral := isIntegral_of_finiteAlong ξ hξfin
  let χ : IsogenyHomDatum V₁ V₂ := ⟨ξ, hξint, hξfin⟩
  haveI : AlgebraicCurve.HasPrincipalDivisors F V₁.FunctionField :=
    hasPrincipalDivisors_functionField V₁
  have hNχ : NormFormulaAlong F χ.ι χ.hfin := IsogenyEndDatum.normFormulaAlong_of_finiteAlong_aux ξ hξfin
  refine ⟨χ, hNχ, fun P => ?_⟩
  have hcomp : ∀ Q : V₀.Point, hmap ψ Q = hmap χ (hmap φ Q) := by
    intro Q
    have hint : (φ.ι.comp ξ).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hξint φ.hι
    apply placeOfPoint_inj
    rw [← hmap_seam ψ Q, AlgebraicCurve.Place.restrictAlong_congr hξ.symm ψ.hι hint (placeOfPoint Q),
      ← Place.restrictAlong_restrictAlong ξ φ.ι hξint φ.hι hint (placeOfPoint Q), hmap_seam φ Q]
    exact hmap_seam χ (hmap φ Q)
  rw [pointHom_eq_hmap_sub ψ hNψ P, pointHom_eq_hmap_sub φ hNφ P, map_sub,
    pointHom_eq_hmap_sub χ hNχ, pointHom_eq_hmap_sub χ hNχ, hcomp P, hcomp 0]
  abel

end IsogenyHomDatum

end Affine

end WeierstrassCurve
