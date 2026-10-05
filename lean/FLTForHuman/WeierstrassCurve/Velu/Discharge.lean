/-
The deficit-fun `ord`/`evalAt` discharge (cluster G) of the explicit-Vélu port.

Statements are transcribed verbatim from the pinned FLT `aa2d8b3` files

* `P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean`
  (the canonical statement copy), and
* `P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq.lean`
  (the proof bodies);

only proof bodies are adapted to mathlib `v4.34.0`. Cluster H (the `kw_*_odd`
odd-order combinatorics) lives in `Velu/OddOrder.lean`, which imports this file.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Engine
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

open Polynomial Finset
open scoped Polynomial.Bivariate
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem isRational_of_deg_eq_one (h : v.deg = 1) : v.IsRational :=
  (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).2 h

end Place

end AlgebraicCurve

namespace WeierstrassCurve

open WeierstrassCurve.Affine

/-! ### Prerequisites

Shared-prelude declarations that G consumes but that are not yet available in
`Velu/Engine.lean`, `Place/Dictionary.lean` or `Velu/Formula.lean`. They are
transcribed verbatim from the pinned FLT file (names, namespaces and declaration
kinds unchanged); `spec/check_flt_statements.py` validates their statements
against the pin. They are gathered in this one delimited section so the
manager's refactor round can relocate them mechanically:

* `nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd`, `sub_nsmul_eq_neg_of_nsmul_eq_zero`
  — the pin's `OrderArithmetic` block.

The A1 Weierstrass place dictionary (`mk_mem_XYIdeal_iff`, `ord_placeOfEquation_*`,
`centre_placeOfEquation`, `isRational_placeOfEquation`) and the
`algebraMap_polynomial_eq_mk_C`/`ord_polyToFunctionField_*` bridge that the
`IsogenyEndDatum` and base-change homes need were relocated to
`WeierstrassCurve/Place/Dictionary.lean` by the H5r refactor round; they are
imported, not redeclared. -/

section Prerequisites

variable {G : Type*} [AddCommGroup G]

lemma nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd {Q : G} {p : ℕ}
    (hord : addOrderOf Q = p) {k : ℕ} (hk : ¬ p ∣ k) : k • Q ≠ 0 := fun h =>
  hk (hord ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr h)

lemma sub_nsmul_eq_neg_of_nsmul_eq_zero {Q : G} {p : ℕ} (hp : p • Q = 0) {k : ℕ}
    (hk : k ≤ p) : (p - k) • Q = -(k • Q) := by
  rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hk, hp]

end Prerequisites

namespace Affine

open CoordinateRing

variable {F : Type u} [Field F] {W : Affine F}

section MemEval

variable {F : Type u} [Field F] {W : Affine F}

theorem XClass_mem_XYIdeal_iff_eq {x' y' : F} (h' : W.Equation x' y') (a : F) :
    XClass W a ∈ XYIdeal W x' (C y') ↔ x' = a := by
  rw [show (XClass W a : W.CoordinateRing) = CoordinateRing.mk W (C (X - C a)) from rfl,
    mk_mem_XYIdeal_iff h']
  simp [evalEval, sub_eq_zero]

theorem YClass_C_mem_XYIdeal_iff_eq {x' y' : F} (h' : W.Equation x' y') (c : F) :
    YClass W (C c) ∈ XYIdeal W x' (C y') ↔ y' = c := by
  rw [show (YClass W (C c) : W.CoordinateRing) = CoordinateRing.mk W (Y - C (C c)) from rfl,
    mk_mem_XYIdeal_iff h']
  simp [evalEval, sub_eq_zero]

end MemEval

section PerCurveEngine

variable [IsAlgClosed F] [IsDedekindDomain W.CoordinateRing]

theorem exists_YClass_negY_notMem_centre {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) {a b₀ : F} (hab₀ : W.Equation a b₀) (h2tor : W.negY a b₀ ≠ b₀)
    (hXa : XClass W a ∈ hv.centre) :
    ∃ b : F, W.Equation a b ∧ XClass W a ∈ hv.centre ∧
      YClass W (C (W.negY a b)) ∉ hv.centre := by
  classical

  obtain ⟨x', y', h', rfl⟩ := (isFinitePlace_iff_exists_placeOfEquation v).mp hv
  have hcen : hv.centre = XYIdeal W x' (C y') := by
    rw [Subsingleton.elim hv (isFinitePlace_placeOfEquation h')]; exact centre_placeOfEquation h'

  have hxa : x' = a := (XClass_mem_XYIdeal_iff_eq h' a).mp (hcen ▸ hXa)
  subst hxa

  refine ⟨y', h', hXa, hcen ▸ ?_⟩
  refine fun hmem => ?_
  have heq : y' = W.negY x' y' := (YClass_C_mem_XYIdeal_iff_eq h' (W.negY x' y')).mp hmem

  rcases Y_eq_of_X_eq h' hab₀ rfl with hy | hy
  · exact h2tor (hy ▸ heq.symm)
  · rw [hy, negY_negY] at heq; exact h2tor heq

end PerCurveEngine

end WeierstrassCurve.Affine

namespace WeierstrassCurve

section YNotCentreDischarge

variable (F : Type*) [Field F] [DecidableEq F] [IsAlgClosed F]

theorem negY_ne_self_of_veluGy_ne_zero {R : Type*} [CommRing R] {W : WeierstrassCurve R}
    {a b : R} (hgy : W.veluGy a b ≠ 0) : W.toAffine.negY a b ≠ b := by
  intro heq
  apply hgy
  have hkey : W.toAffine.negY a b - b = W.veluGy a b := by
    simp only [Affine.negY, veluGy]; ring
  rw [← hkey, heq, sub_self]

end YNotCentreDischarge

namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

section OrdPins

variable (v : AlgebraicCurve.Place F W.FunctionField)

theorem veluTSum_liftSummingSet_mem (S : Finset (F × F)) :
    (W.map (algebraMap F W.FunctionField)).veluTSum (W.liftSummingSet S)
      ∈ v.toValuationSubring := by
  unfold WeierstrassCurve.veluTSum
  refine sum_mem fun Q hQ => ?_
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
  obtain ⟨B, -, rfl⟩ := hQ
  rw [Prod.map_fst, Prod.map_snd, map_veluT]
  exact v.algebraMap_mem' _

end OrdPins

section LaurentLift

variable (W : Affine F)

local notation "W'" => W.map (algebraMap F W.FunctionField)

theorem equation_of_mem_liftSummingSet {S : Finset (F × F)}
    (hS : ∀ A ∈ S, W.Equation A.1 A.2) :
    ∀ A ∈ W.liftSummingSet S, (W').toAffine.Equation A.1 A.2 := by
  intro A hA
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  exact (hS B hB).map (algebraMap F W.FunctionField)

theorem polyToFunctionField_X_ne_of_mem_liftSummingSet {S : Finset (F × F)} :
    ∀ A ∈ W.liftSummingSet S, polyToFunctionField W X ≠ A.1 := by
  intro A hA
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hA
  obtain ⟨B, -, rfl⟩ := hA
  exact polyToFunctionField_X_ne_algebraMap B.1

theorem veluDeficitFun_eq_laurentSum_add_bracket {S : Finset (F × F)}
    (hS : ∀ A ∈ S, W.Equation A.1 A.2) :
    W.veluDeficitFun S
      = (∑ Q ∈ W.liftSummingSet S, (-((W').veluU Q.1 Q.2) ^ 2 / (polyToFunctionField W X - Q.1) ^ 3
          - 3 * (W').veluT Q.1 Q.2 * (W').veluU Q.1 Q.2 / (polyToFunctionField W X - Q.1) ^ 2
          - (3 * ((W').veluT Q.1 Q.2) ^ 2 + 6 * ((W').Ψ₃).eval Q.1)
              / (polyToFunctionField W X - Q.1)))
        + (W').veluDeficitBracket (W.liftSummingSet S) (polyToFunctionField W X) (yGen W) :=
  (W').veluDeficit_eq_laurentSum_add_bracket equation_map_polyToFunctionField_yGen
    (equation_of_mem_liftSummingSet W hS) (polyToFunctionField_X_ne_of_mem_liftSummingSet W)

end LaurentLift

section Corrections

variable {v : AlgebraicCurve.Place F W.FunctionField}

local notation "W'" => W.map (algebraMap F W.FunctionField)
local notation "ι" => algebraMap F W.FunctionField
local notation "𝕏" => polyToFunctionField W X
local notation "𝕐" => yGen W

theorem veluX_sub_self_genericPoint_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    (S : Finset (F × F)) :
    (W').veluX (W.liftSummingSet S) 𝕏 - 𝕏 ∈ v.toValuationSubring := by
  rw [(W').veluX_sub_self_eq_sum_veluXCorr]
  refine sum_mem fun Q hQ => ?_
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
  obtain ⟨B, -, rfl⟩ := hQ
  exact veluXCorr_genericPoint_mem_of_not_isFinitePlace hv B.1 B.2

theorem X_mul_veluX_sub_self_genericPoint_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    (S : Finset (F × F)) :
    𝕏 * ((W').veluX (W.liftSummingSet S) 𝕏 - 𝕏) ∈ v.toValuationSubring := by
  rw [mul_comm, (W').veluX_sub_self_mul_r (W.liftSummingSet S)
    (polyToFunctionField_X_ne_of_mem_liftSummingSet W)]
  refine add_mem (veluTSum_liftSummingSet_mem v S) (sum_mem fun Q hQ => ?_)
  · simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
    obtain ⟨B, -, rfl⟩ := hQ
    have hδ := inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv B.1
    simp only [Prod.map_fst, Prod.map_snd, map_veluW, map_veluU, div_eq_mul_inv, ← inv_pow]
    exact add_mem (mul_mem (v.algebraMap_mem' _) hδ)
      (mul_mem (mul_mem (v.algebraMap_mem' _) (v.algebraMap_mem' _)) (pow_mem hδ 2))

end Corrections

section Engine

variable {v : AlgebraicCurve.Place F W.FunctionField}

local notation "W'" => W.map (algebraMap F W.FunctionField)
local notation "ι" => algebraMap F W.FunctionField
local notation "𝕏" => polyToFunctionField W X
local notation "𝕐" => yGen W

theorem veluDeficitBracket_genericPoint_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    (S : Finset (F × F)) :
    (W').veluDeficitBracket (W.liftSummingSet S) 𝕏 𝕐 ∈ v.toValuationSubring := by
  set α := (W').veluX (W.liftSummingSet S) 𝕏 - 𝕏 with hαdef
  set β := (W').veluY (W.liftSummingSet S) 𝕏 𝕐 - 𝕐 with hβdef
  have hα : α ∈ v.toValuationSubring :=
    veluX_sub_self_genericPoint_mem_of_not_isFinitePlace hv S
  have hβ : β ∈ v.toValuationSubring :=
    veluY_sub_self_genericPoint_mem_of_not_isFinitePlace hv S
  have hXα : 𝕏 * α ∈ v.toValuationSubring :=
    X_mul_veluX_sub_self_genericPoint_mem_of_not_isFinitePlace hv S
  have ht : (W').veluTSum (W.liftSummingSet S) ∈ v.toValuationSubring :=
    veluTSum_liftSummingSet_mem v S
  have h5 : (5 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 5; push_cast at this; exact this
  have h3 : (3 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 3; push_cast at this; exact this

  have key : (W').veluDeficitBracket (W.liftSummingSet S) 𝕏 𝕐
      = β ^ 2 + ι W.a₁ * α * β - (3 * (𝕏 * α) * α + ι W.a₂ * α ^ 2) - α ^ 3
        + 5 * (W').veluTSum (W.liftSummingSet S) * α := by
    unfold WeierstrassCurve.veluDeficitBracket
    rw [← hαdef, ← hβdef, map_a₁, map_a₂]
    ring
  rw [key]
  exact add_mem (sub_mem (sub_mem (add_mem (pow_mem hβ 2)
    (mul_mem (mul_mem (v.algebraMap_mem' _) hα) hβ))
    (add_mem (mul_mem (mul_mem h3 hXα) hα) (mul_mem (v.algebraMap_mem' _) (pow_mem hα 2))))
    (pow_mem hα 3)) (mul_mem (mul_mem h5 ht) hα)

theorem veluDeficitFun_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    {S : Finset (F × F)} (hS : ∀ A ∈ S, W.Equation A.1 A.2) :
    W.veluDeficitFun S ∈ v.toValuationSubring := by
  rw [veluDeficitFun_eq_laurentSum_add_bracket W hS]
  refine add_mem (sum_mem fun Q hQ => ?_)
    (veluDeficitBracket_genericPoint_mem_of_not_isFinitePlace hv S)

  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
  obtain ⟨B, -, rfl⟩ := hQ
  have hδ := inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv B.1
  have hδ2 : ((𝕏 - ι B.1)⁻¹ : W.FunctionField) ^ 2 ∈ v.toValuationSubring := pow_mem hδ 2
  have hδ3 : ((𝕏 - ι B.1)⁻¹ : W.FunctionField) ^ 3 ∈ v.toValuationSubring := pow_mem hδ 3

  have h3 : (3 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 3; push_cast at this; exact this
  have h6 : (6 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 6; push_cast at this; exact this
  rw [Prod.map_fst, Prod.map_snd, map_veluU, map_veluT,
    div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, ← inv_pow]
  refine sub_mem (sub_mem (mul_mem ?_ hδ3) (mul_mem ?_ hδ2)) (mul_mem ?_ hδ)
  · exact neg_mem (pow_mem (v.algebraMap_mem' _) 2)
  · exact mul_mem (mul_mem h3 (v.algebraMap_mem' _)) (v.algebraMap_mem' _)
  ·
    have hΨ : ((W').Ψ₃).eval (ι B.1) = ι (W.Ψ₃.eval B.1) := by
      rw [WeierstrassCurve.map_Ψ₃, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [hΨ]
    exact add_mem (mul_mem h3 (pow_mem (v.algebraMap_mem' _) 2))
      (mul_mem h6 (v.algebraMap_mem' _))

theorem ord_veluDeficitFun_nonneg_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    {S : Finset (F × F)} (hS : ∀ A ∈ S, W.Equation A.1 A.2) :
    0 ≤ v.ord (W.veluDeficitFun S) :=
  v.ord_nonneg_of_mem (veluDeficitFun_mem_of_not_isFinitePlace hv hS)

end Engine

end WeierstrassCurve.Affine

namespace WeierstrassCurve

section LiouvilleCarriers

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunOrdNonnegAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ v : AlgebraicCurve.Place F W.toAffine.FunctionField,
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

def VeluDeficitFunSpecializesConstAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ c : F, W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2))
              = algebraMap F W.toAffine.FunctionField c →
        ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
          W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s = c

end LiouvilleCarriers

section LiouvilleBridge

variable {F : Type*} [Field F] [DecidableEq F]

theorem veluDeficitIsConstantAt_of_ordNonneg_of_specializesConst' {p : ℕ}
    (hPD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      AlgebraicCurve.HasPrincipalDivisors F W.toAffine.FunctionField)
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      IsDedekindDomain W.toAffine.CoordinateRing)
    (hreg : VeluDeficitFunOrdNonnegAt F p)
    (hspec : VeluDeficitFunSpecializesConstAt F p) :
    VeluDeficitIsConstantAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  haveI := hPD W hΔ
  haveI := hDD W hΔ
  obtain ⟨c, hc⟩ := Affine.functionField_liouville_of_equation h₀.left
    (hreg W hΔ x₀ y₀ h₀ hord)
  exact ⟨c, fun r s hrs hav => hspec W hΔ x₀ y₀ h₀ hord c hc hrs hav⟩

end LiouvilleBridge

section BinaryCarriers

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunOrdNonnegAtInftyAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ v : AlgebraicCurve.Place F W.toAffine.FunctionField, ¬ IsFinitePlace v →
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

def VeluDeficitFunOrdNonnegAtFiniteAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ v : AlgebraicCurve.Place F W.toAffine.FunctionField, IsFinitePlace v →
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

end BinaryCarriers

section BinaryRecombination

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegAt_iff_atFinite_and_atInfty {p : ℕ} :
    VeluDeficitFunOrdNonnegAt F p
      ↔ VeluDeficitFunOrdNonnegAtFiniteAt F p ∧ VeluDeficitFunOrdNonnegAtInftyAt F p := by
  constructor
  · exact fun h => ⟨fun W hΔ x₀ y₀ h₀ hord v _ => h W hΔ x₀ y₀ h₀ hord v,
      fun W hΔ x₀ y₀ h₀ hord v _ => h W hΔ x₀ y₀ h₀ hord v⟩
  · rintro ⟨hfin, hinf⟩ W hΔ x₀ y₀ h₀ hord v
    exact ((Affine.forall_place_ord_nonneg_iff_finite_and_not_finite _).mpr
      ⟨hfin W hΔ x₀ y₀ h₀ hord, hinf W hΔ x₀ y₀ h₀ hord⟩) v

theorem veluDeficitFunOrdNonnegAt_of_atFinite_of_atInfty {p : ℕ}
    (hfin : VeluDeficitFunOrdNonnegAtFiniteAt F p)
    (hinf : VeluDeficitFunOrdNonnegAtInftyAt F p) :
    VeluDeficitFunOrdNonnegAt F p :=
  (veluDeficitFunOrdNonnegAt_iff_atFinite_and_atInfty F).mpr ⟨hfin, hinf⟩

end BinaryRecombination

section KernelCarriers

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunOrdNonnegAtKernelAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : AlgebraicCurve.Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∈ hv.centre) →
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

def VeluDeficitFunOrdNonnegOffKernelAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : AlgebraicCurve.Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∉ hv.centre) →
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

theorem veluDeficitFunOrdNonnegAtFiniteAt_of_atKernel_of_offKernel {p : ℕ}
    (hker : VeluDeficitFunOrdNonnegAtKernelAt F p)
    (hoff : VeluDeficitFunOrdNonnegOffKernelAt F p) :
    VeluDeficitFunOrdNonnegAtFiniteAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv
  by_cases hk : ∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
      XClass W.toAffine A.1 ∈ hv.centre
  · exact hker W hΔ x₀ y₀ h₀ hord v hv hk
  · exact hoff W hΔ x₀ y₀ h₀ hord v hv (fun A hA hmem => hk ⟨A, hA, hmem⟩)

end KernelCarriers

section TrichotomyRecombination

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegAt_of_atInfty_of_atKernel_of_offKernel {p : ℕ}
    (hinf : VeluDeficitFunOrdNonnegAtInftyAt F p)
    (hker : VeluDeficitFunOrdNonnegAtKernelAt F p)
    (hoff : VeluDeficitFunOrdNonnegOffKernelAt F p) :
    VeluDeficitFunOrdNonnegAt F p :=
  veluDeficitFunOrdNonnegAt_of_atFinite_of_atInfty F
    (veluDeficitFunOrdNonnegAtFiniteAt_of_atKernel_of_offKernel F hker hoff) hinf

end TrichotomyRecombination

section ResidueCarrier

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunEvalAtPlaceAt
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0),
    letI := hDD W hΔ
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
      ∀ ⦃r s : F⦄ (hrs : W.toAffine.Equation r s),
        (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
        (placeOfEquation hrs).evalAt
            (W.toAffine.veluDeficitFun
              (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))
          = W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s

end ResidueCarrier

section ResidueBridge

variable {F : Type*} [Field F] [DecidableEq F]

theorem veluDeficitFunSpecializesConstAt_of_evalAtPlace {p : ℕ}
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    (heval : VeluDeficitFunEvalAtPlaceAt F hDD p) :
    VeluDeficitFunSpecializesConstAt F p := by
  intro W hΔ x₀ y₀ h₀ hord c hc r s hrs hav
  haveI := hDD W hΔ
  rw [← heval W hΔ x₀ y₀ h₀ hord hrs hav, hc, AlgebraicCurve.Place.evalAt_algebraMap]

end ResidueBridge

section Wire

variable {F : Type*} [Field F] [DecidableEq F]

theorem veluDeficitIsConstantAt_of_ordNonneg_of_evalAtPlace {p : ℕ}
    (hPD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      AlgebraicCurve.HasPrincipalDivisors F W.toAffine.FunctionField)
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      IsDedekindDomain W.toAffine.CoordinateRing)
    (hreg : VeluDeficitFunOrdNonnegAt F p)
    (heval : VeluDeficitFunEvalAtPlaceAt F hDD p) :
    VeluDeficitIsConstantAt F p :=
  veluDeficitIsConstantAt_of_ordNonneg_of_specializesConst' hPD hDD hreg
    (veluDeficitFunSpecializesConstAt_of_evalAtPlace hDD heval)

end Wire

section KernelTranslationCarrier

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunKernelTranslationAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : AlgebraicCurve.Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∈ hv.centre) →
          ∃ τ : W.toAffine.FunctionField ≃ₐ[F] W.toAffine.FunctionField,
            τ (W.toAffine.veluDeficitFun
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))
              = W.toAffine.veluDeficitFun
                  (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2))
            ∧ ¬ IsFinitePlace (τ • v)

end KernelTranslationCarrier

section KernelReduction

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegAtKernelAt_of_kernelTranslation_of_atInfty {p : ℕ}
    (htr : VeluDeficitFunKernelTranslationAt F p)
    (hinf : VeluDeficitFunOrdNonnegAtInftyAt F p) :
    VeluDeficitFunOrdNonnegAtKernelAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv hk
  obtain ⟨τ, hfix, hninf⟩ := htr W hΔ x₀ y₀ h₀ hord v hv hk
  exact AlgebraicCurve.Place.ord_nonneg_of_ord_smul_nonneg τ v hfix
    (hinf W hΔ x₀ y₀ h₀ hord (τ • v) hninf)

end KernelReduction

section Wire2

variable {F : Type*} [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegAt_of_kernelTranslation_of_atInfty_of_offKernel {p : ℕ}
    (htr : VeluDeficitFunKernelTranslationAt F p)
    (hinf : VeluDeficitFunOrdNonnegAtInftyAt F p)
    (hoff : VeluDeficitFunOrdNonnegOffKernelAt F p) :
    VeluDeficitFunOrdNonnegAt F p :=
  veluDeficitFunOrdNonnegAt_of_atInfty_of_atKernel_of_offKernel F hinf
    (veluDeficitFunOrdNonnegAtKernelAt_of_kernelTranslation_of_atInfty F htr hinf) hoff

end Wire2

namespace Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

section Atomic

variable [IsDedekindDomain W.CoordinateRing] {r s : F} (hrs : W.Equation r s)

theorem evalAt_algebraMap_placeOfEquation_of_mem_XYIdeal {z : W.CoordinateRing}
    (hz : z ∈ XYIdeal W r (C s)) :
    (placeOfEquation hrs).evalAt (algebraMap W.CoordinateRing W.FunctionField z) = 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [_root_.map_zero, AlgebraicCurve.Place.evalAt_zero]
  have hpos := (ord_placeOfEquation_pos_iff hrs hz0).mpr hz
  have hmem : algebraMap W.CoordinateRing W.FunctionField z
      ∈ (placeOfEquation hrs).toValuationSubring := isFinitePlace_placeOfEquation hrs z
  rw [(placeOfEquation hrs).evalAt_of_mem hmem]

  have hres : IsLocalRing.residue _
      (⟨algebraMap W.CoordinateRing W.FunctionField z, hmem⟩
        : (placeOfEquation hrs).toValuationSubring) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr
      (((placeOfEquation hrs).mem_maximalIdeal_iff_ord_pos
        (algebraMap_coordinateRing_ne_zero hz0) hmem).mpr hpos)
  rw [hres, ← _root_.map_zero (algebraMap F (placeOfEquation hrs).ResidueField),
    (placeOfEquation hrs).residueInv_algebraMap]

theorem polyToFunctionField_X_mem_placeOfEquation :
    polyToFunctionField W X ∈ (placeOfEquation hrs).toValuationSubring := by
  rw [polyToFunctionField_apply]; exact isFinitePlace_placeOfEquation hrs _

theorem yGen_mem_placeOfEquation :
    yGen W ∈ (placeOfEquation hrs).toValuationSubring :=
  isFinitePlace_placeOfEquation hrs _

include hrs in

theorem evalAt_polyToFunctionField_X_placeOfEquation :
    (placeOfEquation hrs).evalAt (polyToFunctionField W X) = r := by
  have hX : XClass W r ∈ XYIdeal W r (C s) := Ideal.subset_span (Set.mem_insert _ _)
  have h0 := evalAt_algebraMap_placeOfEquation_of_mem_XYIdeal hrs hX

  have hbridge : algebraMap W.CoordinateRing W.FunctionField (XClass W r)
      = polyToFunctionField W X - algebraMap F W.FunctionField r := by
    rw [show XClass W r = algebraMap F[X] W.CoordinateRing (X - C r) from rfl,
      ← polyToFunctionField_apply, _root_.map_sub, polyToFunctionField_C]
  rw [hbridge, (placeOfEquation hrs).evalAt_sub (isRational_placeOfEquation hrs)
    (polyToFunctionField_X_mem_placeOfEquation hrs)
    ((placeOfEquation hrs).algebraMap_mem' r),
    AlgebraicCurve.Place.evalAt_algebraMap, sub_eq_zero] at h0
  exact h0

include hrs in

theorem evalAt_yGen_placeOfEquation :
    (placeOfEquation hrs).evalAt (yGen W) = s := by
  have hY : YClass W (C s) ∈ XYIdeal W r (C s) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have h0 := evalAt_algebraMap_placeOfEquation_of_mem_XYIdeal hrs hY

  have hbridge : algebraMap W.CoordinateRing W.FunctionField (YClass W (C s))
      = yGen W - algebraMap F W.FunctionField s := by
    rw [YClass, _root_.map_sub, _root_.map_sub, yGen]; congr 1
  rw [hbridge, (placeOfEquation hrs).evalAt_sub (isRational_placeOfEquation hrs)
    (yGen_mem_placeOfEquation hrs)
    ((placeOfEquation hrs).algebraMap_mem' s),
    AlgebraicCurve.Place.evalAt_algebraMap, sub_eq_zero] at h0
  exact h0

include hrs in

theorem evalAt_X_sub_const_placeOfEquation (c : F) :
    (placeOfEquation hrs).evalAt (polyToFunctionField W X - algebraMap F W.FunctionField c)
      = r - c := by
  rw [(placeOfEquation hrs).evalAt_sub (isRational_placeOfEquation hrs)
    (polyToFunctionField_X_mem_placeOfEquation hrs)
    ((placeOfEquation hrs).algebraMap_mem' c),
    evalAt_polyToFunctionField_X_placeOfEquation hrs, AlgebraicCurve.Place.evalAt_algebraMap]

include hrs in

theorem ord_X_sub_const_placeOfEquation_of_ne {c : F} (hrc : r ≠ c) :
    (placeOfEquation hrs).ord (polyToFunctionField W X - algebraMap F W.FunctionField c) = 0 := by

  have hbridge : polyToFunctionField W X - algebraMap F W.FunctionField c
      = algebraMap W.CoordinateRing W.FunctionField (XClass W c) := by
    rw [show XClass W c = algebraMap F[X] W.CoordinateRing (X - C c) from rfl,
      ← polyToFunctionField_apply, _root_.map_sub, polyToFunctionField_C]
  rw [hbridge]
  refine le_antisymm ?_ (ord_placeOfEquation_nonneg hrs _)
  rw [show (0 : ℤ) = 0 from rfl, ← not_lt]
  intro hpos
  have hmem := (ord_placeOfEquation_pos_iff hrs (XClass_ne_zero c)).mp hpos

  rw [show XClass W c = CoordinateRing.mk W (C (X - C c)) from rfl,
    mk_mem_XYIdeal_iff hrs] at hmem
  simp only [evalEval_C, eval_sub, eval_X, eval_C, sub_eq_zero] at hmem
  exact hrc hmem

end Atomic

section VeluCoord

variable [IsDedekindDomain W.CoordinateRing] {r s : F} (hrs : W.Equation r s)
  {S : Finset (F × F)}

private lemma const_mem_placeOfEquation (c : F) :
    algebraMap F W.FunctionField c ∈ (placeOfEquation hrs).toValuationSubring :=
  (placeOfEquation hrs).algebraMap_mem' c

omit [IsDedekindDomain W.CoordinateRing] in

private lemma X_sub_const_ne_zero (c : F) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c : W.FunctionField) ≠ 0 :=
  sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap c)

private lemma inv_X_sub_const_mem_placeOfEquation {c : F} (hrc : r ≠ c) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹
      ∈ (placeOfEquation hrs).toValuationSubring := by
  have hord := ord_X_sub_const_placeOfEquation_of_ne hrs hrc
  refine (placeOfEquation hrs).mem_of_ord_nonneg (inv_ne_zero (X_sub_const_ne_zero c)) ?_
  rw [(placeOfEquation hrs).ord_inv, hord]
  exact le_of_eq (_root_.neg_zero).symm

lemma veluX_summand_mem (A : F × F) (hrA : r ≠ A.1) :
    (algebraMap F W.FunctionField (W.veluT A.1 A.2)
        / (polyToFunctionField W X - algebraMap F W.FunctionField A.1)
      + algebraMap F W.FunctionField (W.veluU A.1 A.2)
        / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2)
      ∈ (placeOfEquation hrs).toValuationSubring := by
  have hδ := inv_X_sub_const_mem_placeOfEquation hrs hrA
  refine add_mem ?_ ?_
  · rw [div_eq_mul_inv]; exact mul_mem (const_mem_placeOfEquation hrs _) hδ
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (const_mem_placeOfEquation hrs _) (pow_mem hδ 2)

include hrs in

theorem evalAt_veluX_liftSummingSet_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (placeOfEquation hrs).evalAt
        ((W.map (algebraMap F W.FunctionField)).veluX (W.liftSummingSet S)
          (polyToFunctionField W X)) = W.veluX S r := by
  have hv := isRational_placeOfEquation hrs
  unfold WeierstrassCurve.veluX WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU]
  rw [(placeOfEquation hrs).evalAt_add hv (polyToFunctionField_X_mem_placeOfEquation hrs)
    (Subring.sum_mem _ fun A hA => veluX_summand_mem hrs A (hS A hA)),
    evalAt_polyToFunctionField_X_placeOfEquation hrs,
    (placeOfEquation hrs).evalAt_sum hv _ _ (fun A hA => veluX_summand_mem hrs A (hS A hA))]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have hδ0 := X_sub_const_ne_zero (W := W) A.1
  have hδord := ord_X_sub_const_placeOfEquation_of_ne hrs (hS A hA)
  have hδ := inv_X_sub_const_mem_placeOfEquation hrs (hS A hA)
  have hδ2ord : (placeOfEquation hrs).ord
      ((polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2) = 0 := by
    have := (placeOfEquation hrs).ord_zpow
      (polyToFunctionField W X - algebraMap F W.FunctionField A.1) 2
    rw [zpow_two] at this
    rw [pow_two, this, hδord, mul_zero]
  have hm1 : (algebraMap F W.FunctionField (W.veluT A.1 A.2)
        / (polyToFunctionField W X - algebraMap F W.FunctionField A.1))
      ∈ (placeOfEquation hrs).toValuationSubring := by
    rw [div_eq_mul_inv]; exact mul_mem (const_mem_placeOfEquation hrs _) hδ
  have hm2 : (algebraMap F W.FunctionField (W.veluU A.1 A.2)
        / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2)
      ∈ (placeOfEquation hrs).toValuationSubring := by
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (const_mem_placeOfEquation hrs _) (pow_mem hδ 2)
  rw [(placeOfEquation hrs).evalAt_add hv hm1 hm2,
    (placeOfEquation hrs).evalAt_div' hv (const_mem_placeOfEquation hrs _) hδ0 hδord,
    (placeOfEquation hrs).evalAt_div' hv (const_mem_placeOfEquation hrs _)
      (pow_ne_zero 2 hδ0) hδ2ord,
    evalAt_X_sub_const_placeOfEquation hrs,
    (placeOfEquation hrs).evalAt_pow hv
      (sub_mem (polyToFunctionField_X_mem_placeOfEquation hrs)
        (const_mem_placeOfEquation hrs _)) 2,
    evalAt_X_sub_const_placeOfEquation hrs,
    AlgebraicCurve.Place.evalAt_algebraMap, AlgebraicCurve.Place.evalAt_algebraMap]

lemma veluX_liftSummingSet_mem_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (W.map (algebraMap F W.FunctionField)).veluX (W.liftSummingSet S)
        (polyToFunctionField W X) ∈ (placeOfEquation hrs).toValuationSubring := by
  unfold WeierstrassCurve.veluX WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU]
  exact add_mem (polyToFunctionField_X_mem_placeOfEquation hrs)
    (Subring.sum_mem _ fun A hA => veluX_summand_mem hrs A (hS A hA))

lemma veluY_summand_mem (A : F × F) (hrA : r ≠ A.1) :
    (algebraMap F W.FunctionField (W.veluU A.1 A.2)
          * (2 * yGen W + algebraMap F W.FunctionField W.a₁ * polyToFunctionField W X
              + algebraMap F W.FunctionField W.a₃)
          / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 3
      + algebraMap F W.FunctionField (W.veluT A.1 A.2)
          * (algebraMap F W.FunctionField W.a₁
              * (polyToFunctionField W X - algebraMap F W.FunctionField A.1)
            + yGen W - algebraMap F W.FunctionField A.2)
          / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2
      + (algebraMap F W.FunctionField W.a₁ * algebraMap F W.FunctionField (W.veluU A.1 A.2)
          - algebraMap F W.FunctionField (W.veluGx A.1 A.2)
              * algebraMap F W.FunctionField (W.veluGy A.1 A.2))
          / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2)
      ∈ (placeOfEquation hrs).toValuationSubring := by
  have hδ := inv_X_sub_const_mem_placeOfEquation hrs hrA
  have hX := polyToFunctionField_X_mem_placeOfEquation hrs
  have hY := yGen_mem_placeOfEquation hrs
  have hF := const_mem_placeOfEquation hrs
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

lemma veluY_liftSummingSet_mem_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (W.map (algebraMap F W.FunctionField)).veluY (W.liftSummingSet S)
        (polyToFunctionField W X) (yGen W) ∈ (placeOfEquation hrs).toValuationSubring := by
  unfold WeierstrassCurve.veluY WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU,
    map_veluGx, map_veluGy, map_a₁, map_a₃]
  exact sub_mem (yGen_mem_placeOfEquation hrs)
    (Subring.sum_mem _ fun A hA => veluY_summand_mem hrs A (hS A hA))

include hrs in

theorem evalAt_veluY_liftSummingSet_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (placeOfEquation hrs).evalAt
        ((W.map (algebraMap F W.FunctionField)).veluY (W.liftSummingSet S)
          (polyToFunctionField W X) (yGen W)) = W.veluY S r s := by
  have hv := isRational_placeOfEquation hrs
  have hX := polyToFunctionField_X_mem_placeOfEquation hrs
  have hY := yGen_mem_placeOfEquation hrs
  have hF := const_mem_placeOfEquation hrs
  unfold WeierstrassCurve.veluY WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU,
    map_veluGx, map_veluGy, map_a₁, map_a₃]
  rw [(placeOfEquation hrs).evalAt_sub hv hY
      (Subring.sum_mem _ fun A hA => veluY_summand_mem hrs A (hS A hA)),
    evalAt_yGen_placeOfEquation hrs,
    (placeOfEquation hrs).evalAt_sum hv _ _ (fun A hA => veluY_summand_mem hrs A (hS A hA))]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have hδ0 := X_sub_const_ne_zero (W := W) A.1
  have hδord := ord_X_sub_const_placeOfEquation_of_ne hrs (hS A hA)
  have hδ := inv_X_sub_const_mem_placeOfEquation hrs (hS A hA)
  have hδpowmem : ∀ n : ℕ,
      ((polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ n)⁻¹
        ∈ (placeOfEquation hrs).toValuationSubring :=
    fun n => by rw [← inv_pow]; exact pow_mem hδ n
  have hδpow : ∀ n : ℕ, (placeOfEquation hrs).ord
      ((polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ n) = 0 := fun n => by
    have := (placeOfEquation hrs).ord_zpow
      (polyToFunctionField W X - algebraMap F W.FunctionField A.1) n
    rw [zpow_natCast] at this; rw [this, hδord, mul_zero]
  have hδeval := evalAt_X_sub_const_placeOfEquation hrs A.1
  have hδpoweval : ∀ n : ℕ, (placeOfEquation hrs).evalAt
      ((polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ n) = (r - A.1) ^ n :=
    fun n => by
      rw [(placeOfEquation hrs).evalAt_pow hv (sub_mem hX (hF _)) n, hδeval]

  have hN1 : (algebraMap F W.FunctionField (W.veluU A.1 A.2)
      * (2 * yGen W + algebraMap F W.FunctionField W.a₁ * polyToFunctionField W X
          + algebraMap F W.FunctionField W.a₃)) ∈ (placeOfEquation hrs).toValuationSubring :=
    mul_mem (hF _)
      (add_mem (add_mem (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX)) (hF _))
  have hN2 : (algebraMap F W.FunctionField (W.veluT A.1 A.2)
      * (algebraMap F W.FunctionField W.a₁
          * (polyToFunctionField W X - algebraMap F W.FunctionField A.1)
        + yGen W - algebraMap F W.FunctionField A.2))
      ∈ (placeOfEquation hrs).toValuationSubring :=
    mul_mem (hF _) (sub_mem (add_mem (mul_mem (hF _) (sub_mem hX (hF _))) hY) (hF _))
  have hN3 : (algebraMap F W.FunctionField W.a₁ * algebraMap F W.FunctionField (W.veluU A.1 A.2)
      - algebraMap F W.FunctionField (W.veluGx A.1 A.2)
          * algebraMap F W.FunctionField (W.veluGy A.1 A.2))
      ∈ (placeOfEquation hrs).toValuationSubring :=
    sub_mem (mul_mem (hF _) (hF _)) (mul_mem (hF _) (hF _))
  rw [(placeOfEquation hrs).evalAt_add hv
      (add_mem (by rw [div_eq_mul_inv]; exact mul_mem hN1 (hδpowmem 3))
        (by rw [div_eq_mul_inv]; exact mul_mem hN2 (hδpowmem 2)))
      (by rw [div_eq_mul_inv]; exact mul_mem hN3 (hδpowmem 2)),
    (placeOfEquation hrs).evalAt_add hv
      (by rw [div_eq_mul_inv]; exact mul_mem hN1 (hδpowmem 3))
      (by rw [div_eq_mul_inv]; exact mul_mem hN2 (hδpowmem 2)),
    (placeOfEquation hrs).evalAt_div' hv hN1 (pow_ne_zero 3 hδ0) (hδpow 3), hδpoweval 3,
    (placeOfEquation hrs).evalAt_div' hv hN2 (pow_ne_zero 2 hδ0) (hδpow 2), hδpoweval 2,
    (placeOfEquation hrs).evalAt_div' hv hN3 (pow_ne_zero 2 hδ0) (hδpow 2), hδpoweval 2]
  congr 1; congr 1
  ·
    rw [(placeOfEquation hrs).evalAt_mul hv (hF _)
        (add_mem (add_mem (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX)) (hF _)),
      AlgebraicCurve.Place.evalAt_algebraMap,
      (placeOfEquation hrs).evalAt_add hv
        (add_mem (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX)) (hF _),
      (placeOfEquation hrs).evalAt_add hv (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX),
      (placeOfEquation hrs).evalAt_mul hv (ofNat_mem _ 2) hY,
      (placeOfEquation hrs).evalAt_mul hv (hF _) hX,
      (placeOfEquation hrs).evalAt_ofNat 2,
      evalAt_yGen_placeOfEquation hrs, evalAt_polyToFunctionField_X_placeOfEquation hrs,
      AlgebraicCurve.Place.evalAt_algebraMap, AlgebraicCurve.Place.evalAt_algebraMap]
  ·
    rw [(placeOfEquation hrs).evalAt_mul hv (hF _)
        (sub_mem (add_mem (mul_mem (hF _) (sub_mem hX (hF _))) hY) (hF _)),
      AlgebraicCurve.Place.evalAt_algebraMap,
      (placeOfEquation hrs).evalAt_sub hv
        (add_mem (mul_mem (hF _) (sub_mem hX (hF _))) hY) (hF _),
      (placeOfEquation hrs).evalAt_add hv (mul_mem (hF _) (sub_mem hX (hF _))) hY,
      (placeOfEquation hrs).evalAt_mul hv (hF _) (sub_mem hX (hF _)),
      hδeval, evalAt_yGen_placeOfEquation hrs,
      AlgebraicCurve.Place.evalAt_algebraMap, AlgebraicCurve.Place.evalAt_algebraMap]
  ·
    rw [(placeOfEquation hrs).evalAt_sub hv (mul_mem (hF _) (hF _)) (mul_mem (hF _) (hF _)),
      (placeOfEquation hrs).evalAt_mul hv (hF _) (hF _),
      (placeOfEquation hrs).evalAt_mul hv (hF _) (hF _),
      AlgebraicCurve.Place.evalAt_algebraMap, AlgebraicCurve.Place.evalAt_algebraMap,
      AlgebraicCurve.Place.evalAt_algebraMap, AlgebraicCurve.Place.evalAt_algebraMap]

end VeluCoord

section Discharge

variable [IsDedekindDomain W.CoordinateRing] {r s : F} (hrs : W.Equation r s)
  {S : Finset (F × F)}

include hrs in

theorem evalAt_veluDeficitFun_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (placeOfEquation hrs).evalAt (W.veluDeficitFun S) = W.veluDeficit S r s := by
  have hv := isRational_placeOfEquation hrs
  unfold WeierstrassCurve.veluDeficitFun WeierstrassCurve.veluDeficit
  set X' := (W.map (algebraMap F W.FunctionField)).veluX (W.liftSummingSet S)
    (polyToFunctionField W X) with hX'
  set Y' := (W.map (algebraMap F W.FunctionField)).veluY (W.liftSummingSet S)
    (polyToFunctionField W X) (yGen W) with hY'
  have hXm : X' ∈ (placeOfEquation hrs).toValuationSubring :=
    veluX_liftSummingSet_mem_placeOfEquation hrs hS
  have hYm : Y' ∈ (placeOfEquation hrs).toValuationSubring :=
    veluY_liftSummingSet_mem_placeOfEquation hrs hS
  have hF : ∀ c : F, algebraMap F W.FunctionField c
      ∈ (placeOfEquation hrs).toValuationSubring :=
    (placeOfEquation hrs).algebraMap_mem'
  have hXe : (placeOfEquation hrs).evalAt X' = W.veluX S r :=
    evalAt_veluX_liftSummingSet_placeOfEquation hrs hS
  have hYe : (placeOfEquation hrs).evalAt Y' = W.veluY S r s :=
    evalAt_veluY_liftSummingSet_placeOfEquation hrs hS

  rw [veluQuotient_a₄, veluQuotient_a₆,
    show (W.liftSummingSet S : Finset _) = S.map ⟨Prod.map (algebraMap F W.FunctionField)
      (algebraMap F W.FunctionField), (RingHom.injective _).prodMap
      (RingHom.injective _)⟩ from rfl,
    map_veluTSum _ _ S (RingHom.injective _), map_veluWSum _ _ S (RingHom.injective _),
    map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_b₂]

  have hcoef4 : (algebraMap F W.FunctionField W.a₄
      - 5 * algebraMap F W.FunctionField (W.veluTSum S))
      ∈ (placeOfEquation hrs).toValuationSubring :=
    sub_mem (hF _) (mul_mem (ofNat_mem _ 5) (hF _))
  have hcoef6 : (algebraMap F W.FunctionField W.a₆
      - algebraMap F W.FunctionField W.b₂ * algebraMap F W.FunctionField (W.veluTSum S)
      - 7 * algebraMap F W.FunctionField (W.veluWSum S))
      ∈ (placeOfEquation hrs).toValuationSubring :=
    sub_mem (sub_mem (hF _) (mul_mem (hF _) (hF _))) (mul_mem (ofNat_mem _ 7) (hF _))
  rw [(placeOfEquation hrs).evalAt_sub hv
      (add_mem (add_mem (pow_mem hYm 2) (mul_mem (mul_mem (hF _) hXm) hYm))
        (mul_mem (hF _) hYm))
      (add_mem (add_mem (add_mem (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2)))
        (mul_mem hcoef4 hXm)) hcoef6),
    (placeOfEquation hrs).evalAt_add hv
      (add_mem (pow_mem hYm 2) (mul_mem (mul_mem (hF _) hXm) hYm)) (mul_mem (hF _) hYm),
    (placeOfEquation hrs).evalAt_add hv (pow_mem hYm 2) (mul_mem (mul_mem (hF _) hXm) hYm),
    (placeOfEquation hrs).evalAt_pow hv hYm 2, hYe,
    (placeOfEquation hrs).evalAt_mul hv (mul_mem (hF _) hXm) hYm,
    (placeOfEquation hrs).evalAt_mul hv (hF _) hXm, AlgebraicCurve.Place.evalAt_algebraMap, hXe, hYe,
    (placeOfEquation hrs).evalAt_mul hv (hF _) hYm, AlgebraicCurve.Place.evalAt_algebraMap, hYe,
    (placeOfEquation hrs).evalAt_add hv
      (add_mem (add_mem (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2)))
        (mul_mem hcoef4 hXm)) hcoef6,
    (placeOfEquation hrs).evalAt_add hv
      (add_mem (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2))) (mul_mem hcoef4 hXm),
    (placeOfEquation hrs).evalAt_add hv (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2)),
    (placeOfEquation hrs).evalAt_pow hv hXm 3, hXe,
    (placeOfEquation hrs).evalAt_mul hv (hF _) (pow_mem hXm 2),
    (placeOfEquation hrs).evalAt_pow hv hXm 2, hXe, AlgebraicCurve.Place.evalAt_algebraMap,
    (placeOfEquation hrs).evalAt_mul hv hcoef4 hXm,
    (placeOfEquation hrs).evalAt_sub hv (hF _) (mul_mem (ofNat_mem _ 5) (hF _)),
    (placeOfEquation hrs).evalAt_mul hv (ofNat_mem _ 5) (hF _),
    (placeOfEquation hrs).evalAt_ofNat 5, AlgebraicCurve.Place.evalAt_algebraMap,
    AlgebraicCurve.Place.evalAt_algebraMap, hXe,
    (placeOfEquation hrs).evalAt_sub hv (sub_mem (hF _) (mul_mem (hF _) (hF _)))
      (mul_mem (ofNat_mem _ 7) (hF _)),
    (placeOfEquation hrs).evalAt_sub hv (hF _) (mul_mem (hF _) (hF _)),
    (placeOfEquation hrs).evalAt_mul hv (hF _) (hF _),
    (placeOfEquation hrs).evalAt_mul hv (ofNat_mem _ 7) (hF _),
    (placeOfEquation hrs).evalAt_ofNat 7, AlgebraicCurve.Place.evalAt_algebraMap,
    AlgebraicCurve.Place.evalAt_algebraMap,
    AlgebraicCurve.Place.evalAt_algebraMap, AlgebraicCurve.Place.evalAt_algebraMap,
    veluQuotient_a₄, veluQuotient_a₆]

end Discharge

end WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F]

theorem veluDeficitFunEvalAtPlaceAt
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    (p : ℕ) : VeluDeficitFunEvalAtPlaceAt F hDD p := by
  intro W hΔ x₀ y₀ h₀ _hord r s hrs hav
  haveI := hDD W hΔ
  exact Affine.evalAt_veluDeficitFun_placeOfEquation hrs hav

theorem veluDeficitIsConstantAt_of_ordNonneg_of_dedekind {p : ℕ}
    (hPD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      AlgebraicCurve.HasPrincipalDivisors F W.toAffine.FunctionField)
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      IsDedekindDomain W.toAffine.CoordinateRing)
    (hreg : VeluDeficitFunOrdNonnegAt F p) :
    VeluDeficitIsConstantAt F p :=
  veluDeficitIsConstantAt_of_ordNonneg_of_evalAtPlace hPD hDD hreg
    (veluDeficitFunEvalAtPlaceAt hDD p)

end WeierstrassCurve

namespace WeierstrassCurve

section Psi2Sq

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem Ψ₂Sq_ne_zero_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) : W.Ψ₂Sq ≠ 0 := by
  intro h0
  apply hΔ

  have h4 : (4 : F) = 0 := by
    have hc := congrArg (·.coeff 3) h0
    simpa only [W.coeff_Ψ₂Sq, coeff_zero] using hc
  have hb₂ : W.b₂ = 0 := by
    have hc := congrArg (·.coeff 2) h0
    simp only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_zero, coeff_X,
      mul_ite, mul_one, mul_zero] at hc

    norm_num at hc
    exact hc
  have hb₆ : W.b₆ = 0 := by
    have hc := congrArg (·.coeff 0) h0
    simp only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_zero, coeff_X,
      mul_ite, mul_one, mul_zero] at hc
    norm_num at hc
    exact hc

  rw [WeierstrassCurve.Δ, hb₂, hb₆]
  linear_combination -(2 * W.b₄ ^ 3) * h4

end Psi2Sq

section Parity

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem veluDeficitCrossQuadBetaOnly_negY_of_equation {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficitCrossQuadBetaOnly S r (W.toAffine.negY r s)
      = W.veluDeficitCrossQuadBetaOnly S r s := by
  unfold veluDeficitCrossQuadBetaOnly veluDeficitCrossQuadCubeBeta
  rw [W.veluDeficitCrossQuad_negY_of_equation hP]

end Parity

section SubCarriers

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunKernelTranslationFixesAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0)
    (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (a b : F) (hab : W.toAffine.Equation a b),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), A.1 = a) →
          (Affine.translationAlgEquivOf hΔ hab)
              (W.toAffine.veluDeficitFun
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))
            = W.toAffine.veluDeficitFun
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2))

def VeluDeficitFunKernelTranslationToInftyAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0)
    (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : AlgebraicCurve.Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∈ hv.centre) →
          ∃ (a b : F) (hab : W.toAffine.Equation a b),
            (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), A.1 = a) ∧
            ¬ IsFinitePlace (Affine.translationAlgEquivOf hΔ hab • v)

end SubCarriers

section Recombination

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunKernelTranslationAt_of_fixes_of_toInfty {p : ℕ}
    (hfix : VeluDeficitFunKernelTranslationFixesAt F p)
    (hto : VeluDeficitFunKernelTranslationToInftyAt F p) :
    VeluDeficitFunKernelTranslationAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv hk
  obtain ⟨a, b, hab, hka, hninf⟩ := hto W hΔ x₀ y₀ h₀ hord v hv hk
  exact ⟨Affine.translationAlgEquivOf hΔ hab, hfix W hΔ x₀ y₀ h₀ hord a b hab hka, hninf⟩

end Recombination

section YNotCentreCarrier

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunKernelTranslationYNotCentreAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F) (_ : W.Δ ≠ 0)
    (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : AlgebraicCurve.Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∈ hv.centre) →
          ∃ (a b : F) (_ : W.toAffine.Equation a b),
            (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), A.1 = a) ∧
            XClass W.toAffine a ∈ hv.centre ∧
            YClass W.toAffine (C (W.toAffine.negY a b)) ∉ hv.centre

end YNotCentreCarrier

section ToInftyFromYNotCentre

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunKernelTranslationToInftyAt_of_yNotCentre {p : ℕ}
    (hY : VeluDeficitFunKernelTranslationYNotCentreAt F p) :
    VeluDeficitFunKernelTranslationToInftyAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv hk
  obtain ⟨a, b, hab, hka, hXcen, hYcen⟩ := hY W hΔ x₀ y₀ h₀ hord v hv hk
  refine ⟨a, b, hab, hka, ?_⟩
  intro hfin
  apply Affine.addXFun_negY_notMem_of_XClass_mem_centre hv hXcen hYcen
  rw [← Affine.translationAlgEquivOf_symm_polyToFunctionField_X hΔ hab]
  refine (AlgebraicCurve.Place.mem_smul_iff_symm_mem
    (Affine.translationAlgEquivOf hΔ hab) v (polyToFunctionField W.toAffine X)).mp ?_
  have hmem := hfin (algebraMap F[X] W.toAffine.CoordinateRing X)
  rwa [← Affine.polyToFunctionField_apply X] at hmem

end ToInftyFromYNotCentre

namespace Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

theorem algebraMap_polynomial_X_sub_C (c : F) :
    algebraMap F[X] W.CoordinateRing (X - C c) = XClass W c := by
  rw [XClass, AdjoinRoot.algebraMap_eq]; rfl

theorem algebraMap_coordinateRing_XClass (c : F) :
    algebraMap W.CoordinateRing W.FunctionField (XClass W c)
      = polyToFunctionField W X - algebraMap F W.FunctionField c := by
  rw [← algebraMap_polynomial_X_sub_C, ← polyToFunctionField_apply, map_sub,
    polyToFunctionField_C]

theorem IsFinitePlace.inv_X_sub_const_mem_of_XClass_notMem_centre
    {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) {c : F}
    (hc : XClass W c ∉ hv.centre) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹ ∈ v.toValuationSubring := by
  rw [← algebraMap_coordinateRing_XClass]
  exact hv.inv_mem hc

theorem IsFinitePlace.polyToFunctionField_X_mem {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) : polyToFunctionField W X ∈ v.toValuationSubring := by
  rw [polyToFunctionField_apply]; exact hv _

theorem IsFinitePlace.yGen_mem {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) : yGen W ∈ v.toValuationSubring := hv _

section OffKernelMembership

variable {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) {S : Finset (F × F)}
  (hS : ∀ A ∈ S, XClass W A.1 ∉ hv.centre)

local notation "ι" => algebraMap F W.FunctionField
local notation "x" => polyToFunctionField W X
local notation "y" => yGen W
local notation "𝒪" => v.toValuationSubring

include hS in

theorem IsFinitePlace.veluX_liftSummingSet_mem_of_forall_XClass_notMem_centre :
    (W.map ι).veluX (W.liftSummingSet S) x ∈ 𝒪 := by
  unfold WeierstrassCurve.veluX WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  refine add_mem hv.polyToFunctionField_X_mem (Subring.sum_mem _ fun A hA => ?_)
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU]
  have hδ : (x - ι A.1)⁻¹ ∈ 𝒪 :=
    hv.inv_X_sub_const_mem_of_XClass_notMem_centre (hS A hA)
  refine add_mem ?_ ?_
  · rw [div_eq_mul_inv]; exact mul_mem (v.algebraMap_mem' _) hδ
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (v.algebraMap_mem' _) (pow_mem hδ 2)

include hS in

theorem IsFinitePlace.veluY_liftSummingSet_mem_of_forall_XClass_notMem_centre :
    (W.map ι).veluY (W.liftSummingSet S) x y ∈ 𝒪 := by
  unfold WeierstrassCurve.veluY WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  refine sub_mem hv.yGen_mem (Subring.sum_mem _ fun A hA => ?_)
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU,
    map_veluGx, map_veluGy, map_a₁, map_a₃]
  have hδ : (x - ι A.1)⁻¹ ∈ 𝒪 :=
    hv.inv_X_sub_const_mem_of_XClass_notMem_centre (hS A hA)
  have hx : x ∈ 𝒪 := hv.polyToFunctionField_X_mem
  have hy : y ∈ 𝒪 := hv.yGen_mem
  have hF : ∀ c : F, ι c ∈ 𝒪 := v.algebraMap_mem'
  refine add_mem (add_mem ?_ ?_) ?_
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (hF _)
      (add_mem (add_mem (mul_mem (ofNat_mem 𝒪 2) hy) (mul_mem (hF _) hx)) (hF _)))
      (pow_mem hδ 3)
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (hF _)
      (sub_mem (add_mem (mul_mem (hF _) (sub_mem hx (hF _))) hy) (hF _))) (pow_mem hδ 2)
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (sub_mem (mul_mem (hF _) (hF _)) (mul_mem (hF _) (hF _))) (pow_mem hδ 2)

include hS in

theorem IsFinitePlace.veluDeficitFun_mem_of_forall_XClass_notMem_centre :
    W.veluDeficitFun S ∈ 𝒪 := by
  unfold WeierstrassCurve.veluDeficitFun WeierstrassCurve.veluDeficit
  set X' := (W.map ι).veluX (W.liftSummingSet S) x with hX'
  set Y' := (W.map ι).veluY (W.liftSummingSet S) x y with hY'
  have hXm : X' ∈ 𝒪 := hv.veluX_liftSummingSet_mem_of_forall_XClass_notMem_centre hS
  have hYm : Y' ∈ 𝒪 := hv.veluY_liftSummingSet_mem_of_forall_XClass_notMem_centre hS
  have hF : ∀ c : F, ι c ∈ 𝒪 := v.algebraMap_mem'

  rw [veluQuotient_a₄, veluQuotient_a₆,
    show (W.liftSummingSet S : Finset _) = S.map ⟨Prod.map ι ι, (RingHom.injective ι).prodMap
      (RingHom.injective ι)⟩ from rfl,
    map_veluTSum _ _ S (RingHom.injective ι), map_veluWSum _ _ S (RingHom.injective ι),
    map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_b₂]
  refine sub_mem (add_mem (add_mem (pow_mem hYm 2) (mul_mem (mul_mem (hF _) hXm) hYm))
    (mul_mem (hF _) hYm)) ?_
  refine add_mem (add_mem (add_mem (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2)))
    (mul_mem ?_ hXm)) ?_
  · exact sub_mem (hF _) (mul_mem (ofNat_mem 𝒪 5) (hF _))
  · exact sub_mem (sub_mem (hF _) (mul_mem (hF _) (hF _))) (mul_mem (ofNat_mem 𝒪 7) (hF _))

end OffKernelMembership

theorem IsFinitePlace.ord_nonneg_veluDeficitFun_of_forall_XClass_notMem_centre
    {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) {S : Finset (F × F)}
    (hS : ∀ A ∈ S, XClass W A.1 ∉ hv.centre) :
    0 ≤ v.ord (W.veluDeficitFun S) :=
  v.ord_nonneg_of_mem (hv.veluDeficitFun_mem_of_forall_XClass_notMem_centre hS)

end WeierstrassCurve.Affine

namespace WeierstrassCurve

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegOffKernelAt (p : ℕ) : VeluDeficitFunOrdNonnegOffKernelAt F p :=
  fun _ _ _ _ _ _ _ hv hoff =>
    hv.ord_nonneg_veluDeficitFun_of_forall_XClass_notMem_centre hoff

end WeierstrassCurve

end
