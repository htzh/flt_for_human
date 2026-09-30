/-
The place-evaluation algebra: the integrality/unit/residue bridges and the divisor
evaluation laws the ℙ¹ reciprocity proofs consume, after FLT's
`Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean>).

The pin splits this algebra over two homes: the nine `Place`/`Divisor` laws are in
the `Definitions/` file itself, while the six `Divisor.evalFun_*` statements the
ℙ¹ dictionary actually calls are published only through their
`Theorems/Thm_AlgebraicCurve_Divisor_evalFun_*` wrappers. This module carries the
`Definitions/` layer verbatim at its pin names (minus the `deg_eq_one_of_isRational`
copy, already landed in `P1Dictionary.lean` from the ℙ¹ `S_` file), plus
`evalFun_single_sub_single`, whose statement is the wrapper's.

The pin's proofs are transcribed; the only adaptations are the v4.34.0 prod-lemma
spellings (`Finset.prod_zpow` takes explicit arguments).
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem mem_toValuationSubring_of_ord_nonneg_alt {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem isUnit_mk_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  have huf : (⟨f, v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge⟩ : v.toValuationSubring)
      = (u : v.toValuationSubring) := Subtype.ext hu
  rw [huf]
  exact u.isUnit

theorem residue_ne_zero_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    residue v.toValuationSubring (⟨f, v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge⟩ : v.toValuationSubring)
      ≠ 0 :=
  (residue_ne_zero_iff_isUnit _).mpr (v.isUnit_mk_of_ord_eq_zero hf h)

theorem evalAt_ne_zero_of_ord_eq_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f ≠ 0 := by
  intro h0
  have hres := v.algebraMap_evalAt hv (v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge)
  rw [h0, map_zero] at hres
  exact v.residue_ne_zero_of_ord_eq_zero hf h hres.symm

theorem evalAt_mul_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

private theorem evalAt_inv (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hi : v.ord f⁻¹ = 0 := by rw [v.ord_inv, h, neg_zero]
  have hmul := v.evalAt_mul_of_mem hv (v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge)
    (v.mem_toValuationSubring_of_ord_nonneg_alt hfi hi.ge)
  rw [mul_inv_cancel₀ hf, v.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

private theorem evalAt_zpow (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) (n : ℤ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  have hpow : ∀ m : ℕ, v.evalAt (f ^ m) = v.evalAt f ^ m := by
    intro m
    induction m with
    | zero => simp [v.evalAt_one]
    | succ m ih =>
      have hm : v.ord (f ^ (m : ℤ)) = 0 := by rw [v.ord_zpow, h, mul_zero]
      rw [pow_succ, v.evalAt_mul_of_mem hv ?_
        (v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge), ih, pow_succ]
      have : (f ^ m : F) = f ^ (m : ℤ) := by rw [zpow_natCast]
      rw [this]
      exact v.mem_toValuationSubring_of_ord_nonneg_alt (zpow_ne_zero _ hf) hm.ge
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact hpow m
  · rw [zpow_negSucc, zpow_negSucc, ← hpow (m + 1)]
    refine v.evalAt_inv hv (pow_ne_zero _ hf) ?_
    have : (f ^ (m + 1) : F) = f ^ ((m + 1 : ℕ) : ℤ) := by rw [zpow_natCast]
    rw [this, v.ord_zpow, h, mul_zero]

theorem evalAt_algebraMap_eq (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have ha : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [ha, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    v.residueInv_algebraMap]

end Place

namespace Divisor

theorem evalFun_ne_zero_of_forall_ne_zero {f : F} {D : Divisor K F}
    (h : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) :
    evalFun f D ≠ 0 := by
  rw [evalFun_def]
  exact Finset.prod_ne_zero_iff.mpr fun v hv => zpow_ne_zero _ (h v hv)

theorem evalFun_add_of_forall_ne_zero (f : F) {D E : Divisor K F}
    (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0)
    (hE : ∀ v ∈ E.support, Place.evalAt v f ≠ 0) :
    evalFun f (D + E) = evalFun f D * evalFun f E := by
  classical
  refine Finsupp.prod_add_index (fun v _ => zpow_zero _) (fun v hv b₁ b₂ => ?_)
  refine zpow_add₀ ?_ b₁ b₂
  rcases Finset.mem_union.mp hv with h | h
  · exact hD v h
  · exact hE v h

theorem evalFun_mul_of_forall_mem {f g : F} {D : Divisor K F}
    (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring)
    (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) :
    evalFun (f * g) D = evalFun f D * evalFun g D := by
  rw [show evalFun (f * g) D = D.prod fun v n => v.evalAt f ^ n * v.evalAt g ^ n from
    Finsupp.prod_congr fun v hv => by
      rw [Place.evalAt_mul_of_mem v (hrat v hv) (hf v hv) (hg v hv), mul_zpow]]
  exact Finsupp.prod_mul

theorem support_smul_subset (n : ℤ) (D : Divisor K F) :
    (n • D).support ⊆ D.support := Finsupp.support_smul

theorem evalFun_natCast_smul_divisor (f : F) (D : Divisor K F) (n : ℕ) :
    evalFun f ((n : ℤ) • D) = evalFun f D ^ n := by
  rw [show evalFun f ((n : ℤ) • D)
        = ∏ v ∈ D.support, v.evalAt f ^ (((n : ℤ) • D) v) from
      Finsupp.prod_of_support_subset _ (support_smul_subset (n : ℤ) D) _
        fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm ((n : ℤ)) (D v), zpow_mul, zpow_natCast]

theorem evalFun_zsmul_divisor (f : F) (D : Divisor K F) (n : ℤ) :
    evalFun f (n • D) = evalFun f D ^ n := by
  rw [show evalFun f (n • D) = ∏ v ∈ D.support, v.evalAt f ^ ((n • D) v) from
      Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm n (D v), zpow_mul]

theorem evalFun_zpow_left_of_ord_eq_zero {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ)
    (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hord : ∀ v ∈ D.support, Place.ord v f = 0) :
    evalFun (f ^ n) D = evalFun f D ^ n := by
  rw [evalFun_def, evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Place.evalAt_zpow v (hrat v hv) hf (hord v hv) n, ← zpow_mul, ← zpow_mul, mul_comm]

theorem evalFun_single_sub_single {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F)
    {v₁ v₂ : Place K F} (h₁ : v₁.evalAt f ≠ 0) (h₂ : v₂.evalAt f ≠ 0) :
    Divisor.evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) = v₁.evalAt f / v₂.evalAt f := by
  have hsupp : ∀ (w : Place K F) (n : ℤ), w.evalAt f ≠ 0 →
      ∀ v ∈ (Finsupp.single w n).support, v.evalAt f ≠ 0 := by
    intro w n hw v hv
    have := Finsupp.support_single_subset hv
    rw [Finset.mem_singleton] at this
    rw [this]
    exact hw
  rw [evalFun_add_of_forall_ne_zero f (hsupp v₁ 1 h₁) (hsupp v₂ (-1) h₂),
    Divisor.evalFun_single, Divisor.evalFun_single, zpow_one, zpow_neg_one, div_eq_mul_inv]

end Divisor

end AlgebraicCurve
