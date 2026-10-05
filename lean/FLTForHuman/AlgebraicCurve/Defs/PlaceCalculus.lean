/-
The general `AlgebraicCurve.Place` calculus: the arithmetic laws for `ord`,
`evalAt` and the Galois action that the Weierstrass place dictionary and the Vélu
formulas consume. Statements are transcribed verbatim from the pinned FLT
(`anthropics/fermats-last-theorem`, `aa2d8b3`):

* `P2M/Sol/S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean`
  (`min_ord_le_ord_add`, `ord_add_eq_min`, `ord_pow`, `ord_ringHom_eq_natDegree_mul`,
  `le_ord_ringHom_of_natDegree_le`);
* `P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean`
  and its `_of_isAlgClosed` sibling (`ord_div`, `evalAt_zero`, `evalAt_add`,
  `evalAt_neg`, `evalAt_sub`, `evalAt_sum`, `evalAt_pow`, `evalAt_natCast`,
  `evalAt_ofNat`, `evalAt_div'`, `ord_sub_evalAt_pos`, `mem_smul_iff_symm_mem`,
  `ord_smul_of_fixed`, `ord_nonneg_of_ord_smul_nonneg`).

Only proof bodies are adapted to mathlib `v4.34.0`; the pin's declaration names
and statements are kept. The already-ported `ord_nonneg_of_mem` /
`mem_of_ord_nonneg` / `mem_iff_ord_nonneg` / `ord_algebraMap` /
`evalAt_inv` / `evalAt_ne_zero` / `isRational_of_deg_eq_one` are imported, not
re-proved.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean>
-/
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluationAlgebra
import FLTForHuman.AlgebraicCurve.Defs.SemilinearAut

set_option autoImplicit false

noncomputable section

open Polynomial

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Pin `Place.mem_smul_iff_symm_mem`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:7786`). -/
theorem mem_smul_iff_symm_mem (σ : F ≃ₐ[K] F) (v : Place K F) (f : F) :
    f ∈ (σ • v).toValuationSubring ↔ σ.symm f ∈ v.toValuationSubring := by
  change f ∈ (SemilinearAut.ofAlgAut σ • v).toValuationSubring ↔ σ.symm f ∈ v.toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  simp

/-- Pin `Place.ord_div`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:3298`). -/
theorem ord_div (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    v.ord (f / g) = v.ord f - v.ord g := by
  rw [div_eq_mul_inv, v.ord_mul hf (inv_ne_zero hg), v.ord_inv]
  ring

variable (v : Place K F)

/-- Pin `Place.min_ord_le_ord_add`
(`S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean:1070`). -/
theorem min_ord_le_ord_add {f g : F} (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have h1 : v.adicValuation (f + g) ≤ max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add _ f g
  have hje : v.adicValuation (f + g) ≠ 0 := v.adicValuation_ne_zero hfg
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
    rw [hmax] at h1
  · have h2 := (WithZero.log_le_log hje (v.adicValuation_ne_zero hf)).mpr h1
    simp only [ord]
    omega
  · have h2 := (WithZero.log_le_log hje (v.adicValuation_ne_zero hg)).mpr h1
    simp only [ord]
    omega

/-- Pin `Place.ord_add_eq_min`
(`S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean:1090`). -/
theorem ord_add_eq_min {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f ≠ v.ord g) :
    v.ord (f + g) = min (v.ord f) (v.ord g) := by
  have hval : v.adicValuation f ≠ v.adicValuation g := by
    intro hcon
    exact h (by simp only [ord, hcon])
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ hval
  have hfg : f + g ≠ 0 := by
    intro hcon
    rw [hcon, _root_.map_zero] at h1
    rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
      rw [hmax] at h1
    · exact v.adicValuation_ne_zero hf h1.symm
    · exact v.adicValuation_ne_zero hg h1.symm
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, hle⟩ | ⟨hmax, hlt⟩ <;>
    rw [hmax] at h1
  ·
    have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hg)
      (v.adicValuation_ne_zero hf)).mpr hle
    have h2 : v.ord (f + g) = v.ord f := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hf)
      (v.adicValuation_ne_zero hg)).mpr hlt.le
    have h2 : v.ord (f + g) = v.ord g := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega

/-- Pin `Place.ord_pow`
(`S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean:1132`). -/
theorem ord_pow (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

/-- Pin `Place.ord_ringHom_eq_natDegree_mul`
(`S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean:1137`). -/
theorem ord_ringHom_eq_natDegree_mul {φ : K[X] →+* F} (hφinj : Function.Injective φ)
    (hφC : ∀ c : K, φ (C c) = algebraMap K F c) (hz : v.ord (φ X) < 0) :
    ∀ {p : K[X]}, p ≠ 0 → v.ord (φ p) = p.natDegree * v.ord (φ X) := by
  have hX0 : φ X ≠ 0 := fun h => by simp [Place.ord, h] at hz
  have hmono : ∀ (c : K) (n : ℕ), c ≠ 0 → v.ord (φ (C c * X ^ n)) = n * v.ord (φ X) := by
    intro c n hc
    have hc0 : φ (C c) ≠ 0 := by
      rw [hφC]
      simpa using hc
    rw [map_mul, map_pow, v.ord_mul hc0 (pow_ne_zero n hX0), hφC, v.ord_algebraMap,
      v.ord_pow, zero_add]
  intro p
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    intro hp
    subst hd
    rcases eq_or_ne p.eraseLead 0 with he | he
    ·
      conv_lhs => rw [← p.eraseLead_add_C_mul_X_pow, he, zero_add]
      exact hmono _ _ (leadingCoeff_ne_zero.mpr hp)
    ·
      have hlt : p.eraseLead.natDegree < p.natDegree := by
        rcases p.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
        · exact h
        · exact absurd h he
      have hIH : v.ord (φ p.eraseLead) = p.eraseLead.natDegree * v.ord (φ X) :=
        ih _ hlt rfl he
      have hlead : v.ord (φ (C p.leadingCoeff * X ^ p.natDegree))
          = p.natDegree * v.ord (φ X) := hmono _ _ (leadingCoeff_ne_zero.mpr hp)
      have hcast : (p.eraseLead.natDegree : ℤ) < (p.natDegree : ℤ) := by exact_mod_cast hlt
      have hne : v.ord (φ p.eraseLead) ≠ v.ord (φ (C p.leadingCoeff * X ^ p.natDegree)) := by
        rw [hIH, hlead]
        nlinarith
      have he2 : φ (C p.leadingCoeff * X ^ p.natDegree) ≠ 0 := fun hcon =>
        mul_ne_zero (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)) (pow_ne_zero _ X_ne_zero)
          (hφinj (hcon.trans (_root_.map_zero φ).symm))
      have he1 : φ p.eraseLead ≠ 0 := fun hcon => he (hφinj (hcon.trans (_root_.map_zero φ).symm))
      conv_lhs => rw [← p.eraseLead_add_C_mul_X_pow]
      rw [map_add, v.ord_add_eq_min he1 he2 hne, hIH, hlead]
      have h1 : (p.natDegree : ℤ) * v.ord (φ X) ≤ (p.eraseLead.natDegree : ℤ) * v.ord (φ X) := by
        nlinarith
      omega

/-- Pin `Place.le_ord_ringHom_of_natDegree_le`
(`S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean:1184`). -/
theorem le_ord_ringHom_of_natDegree_le {φ : K[X] →+* F} (hφinj : Function.Injective φ)
    (hφC : ∀ c : K, φ (C c) = algebraMap K F c) (hz : v.ord (φ X) < 0)
    {p : K[X]} {d : ℕ} (hd : p.natDegree ≤ d) :
    (d : ℤ) * v.ord (φ X) ≤ v.ord (φ p) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [_root_.map_zero, Place.ord_zero]
    nlinarith [hz]
  rw [v.ord_ringHom_eq_natDegree_mul hφinj hφC hz hp]
  have h1 : (p.natDegree : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  nlinarith

variable (v : Place K F)

/-- Pin `Place.evalAt_zero`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:8367`). -/
@[scoped simp]
theorem evalAt_zero : v.evalAt (0 : F) = 0 := by
  rw [← (algebraMap K F).map_zero, v.evalAt_algebraMap]

/-- Pin `Place.evalAt_add`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:8370`). -/
theorem evalAt_add (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

/-- Pin `Place.evalAt_neg`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:8378`). -/
theorem evalAt_neg (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [_root_.map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← _root_.map_neg]
  rfl

/-- Pin `Place.evalAt_sub`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:8384`). -/
theorem evalAt_sub (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [sub_eq_add_neg, v.evalAt_add hv hf (neg_mem hg), v.evalAt_neg hv hg, sub_eq_add_neg]

/-- Pin `Place.ord_sub_evalAt_pos`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:3313`). -/
theorem ord_sub_evalAt_pos (hrat : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring :=
    sub_mem hf (v.algebraMap_mem' _)
  rcases eq_or_ne (v.ord (f - algebraMap K F (v.evalAt f))) 0 with h0 | h0
  ·
    exfalso
    refine v.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K v.ResidueField
        (v.evalAt (f - algebraMap K F (v.evalAt f))) = 0 := by
      rw [v.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (v.evalAt f), hmem⟩ : v.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) := by
        refine Subtype.ext ?_
        show f - algebraMap K F (v.evalAt f)
          = f - (algebraMap K v.toValuationSubring (v.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← v.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres
  · have hnonneg := v.ord_nonneg_of_mem hmem
    omega

/-- Pin `Place.evalAt_sum`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:9104`). -/
theorem evalAt_sum (hv : v.IsRational) {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ s, f i) = ∑ i ∈ s, v.evalAt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [v.evalAt_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      v.evalAt_add hv (hf a (Finset.mem_insert_self a s))
        (Subring.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Pin `Place.evalAt_pow`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:9116`). -/
theorem evalAt_pow (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [v.evalAt_one]
  | succ n ih =>
    rw [pow_succ, v.evalAt_mul hv (pow_mem hf n) hf, ih, pow_succ]

/-- Pin `Place.evalAt_natCast`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:9123`). -/
theorem evalAt_natCast (n : ℕ) : v.evalAt (n : F) = n := by
  rw [show (n : F) = algebraMap K F (n : K) from (map_natCast (algebraMap K F) n).symm,
    v.evalAt_algebraMap]

/-- Pin `Place.evalAt_ofNat`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:9126`). -/
theorem evalAt_ofNat (n : ℕ) [n.AtLeastTwo] :
    v.evalAt (ofNat(n) : F) = ofNat(n) := by
  rw [← Nat.cast_ofNat, v.evalAt_natCast, Nat.cast_ofNat]

/-- Pin `Place.evalAt_div'`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:9130`). -/
theorem evalAt_div' (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg0 : g ≠ 0) (hg : v.ord g = 0) :
    v.evalAt (f / g) = v.evalAt f / v.evalAt g := by
  have hginv : g⁻¹ ∈ v.toValuationSubring := v.mem_of_ord_nonneg (inv_ne_zero hg0)
    (by rw [v.ord_inv, hg]; exact le_of_eq (_root_.neg_zero).symm)
  rw [div_eq_mul_inv, v.evalAt_mul hv hf hginv, v.evalAt_inv hv hg0 hg, div_eq_mul_inv]

/-- Pin `Place.ord_smul_of_fixed`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:8829`). -/
theorem ord_smul_of_fixed (σ : F ≃ₐ[K] F) (v : Place K F) {g : F} (hg : σ g = g) :
    (σ • v).ord g = v.ord g := by
  conv_lhs => rw [← hg]
  exact ord_smul σ v g

/-- Pin `Place.ord_nonneg_of_ord_smul_nonneg`
(`S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean:8834`). -/
theorem ord_nonneg_of_ord_smul_nonneg (σ : F ≃ₐ[K] F) (v : Place K F) {g : F}
    (hg : σ g = g) (h : 0 ≤ (σ • v).ord g) : 0 ≤ v.ord g :=
  (ord_smul_of_fixed σ v hg) ▸ h

end Place

end AlgebraicCurve
